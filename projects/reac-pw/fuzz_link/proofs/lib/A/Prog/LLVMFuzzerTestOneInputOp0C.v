(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: new walk for libreac/fuzz_pcap (a Theorem Labs lane). The generic helpers pe_land_m32,
   pe_denot_and_m32(_add0), pe_trim_* / pe_submem_to / pe_prreg_raw / pe_add_fact / pe_sregion are cgif_file_fuzzer
   lib/A/ACer.v's (origin/ossv/recipes c8557374ad2e) as a Theorem Labs lane's lib/A/Prog/PcapSourceOpen.v restates them
   (a working branch f0d76b020fe); pe_U_srl, pe_cbyte .. pe_word_at and pe_saved_of are
   a Theorem Labs lane's lib/A/Prog/GrantEntryHead.v (a working branch b83b8251684) restated over PAImg pcap_listing. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/A/Prog/PcapHarnessPE.v, with its module paths, module names and numbers changed; 1072 of its 1332 lines of code are new or changed and 1047 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/LLVMFuzzerTestOneInputEntry.v, with its module paths and module names changed; 434 of its 480 lines of code are new or changed and 1286 lines of the source are left out. *)
(* LLVMFuzzerTestOneInput on image A, the op_read arm: its two size bytes (+0xd14 .. +0xdac).
   Offsets from 0x827d4; listing (internal path) (internal record, sha256 e84d6f0c6974).

     +0xd14  a2 := N (the cursor's length, s1 + 0x120); N = 0     -> +0xda4: s2 := 0, s4 := 0
     +0xd1c  a1 := P (s1 + 0x118); the instrumented check of [P]; cursor := (P + 1, N - 1)
     +0xd40  s2 := b0 - 40 * ((b0 * 0xcd) >> 13) = b0 mod 40, b0 = [P]; N - 1 = 0     -> +0xda8: s4 := 0
     +0xd60  the instrumented check of [P + 1]; cursor := (P + 2, N - 2)
     +0xd80  s4 := b1 - 40 * (((b1 & 0xff) * 0xcd) >> 13) = b1 mod 40, b1 = [P + 1]
     +0xdac  a0 := &cursor; jal kernel (the op_read loop's Op0K.v r_kcall)

   r_sizes : forall POST i, 0 <= i <= 47 -> FROM POST (r_d_inv .. i) -> FROM POST (sel_join .. LR_j 22%bv i)
   (Sel.v's join at +0xd14 with the name in s6, to Op0Cut.v's cut at +0xdac). The error paths of the two
   instrumented checks are not reached: the payload bytes under the cursor are addressable (the SH entries, from
   the payload's block). The b mod 40 arithmetic is closed by computation over the 256 byte values.

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
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputArmK.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputHead.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputSel.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputOp0Cut.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

(* atoms: 32 = P (the cursor's pointer), 33 = N (its length), 34 = the byte b0 at P, 35 = the byte b1 at P + 1 *)
Definition c_cur (vN : sv) : YP09.region :=
  YP09.mkRegion (Some 9%nat) LS_P (LS_N + 8) LS_P (LS_N + 8)
    [YP09.mkChunk LS_P (CVal 8 (SOff 32 0)); YP09.mkChunk LS_N (CVal 8 vN)].
Definition c_b1 : YP09.region := YP09.mkRegion (Some 32%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 34 0))].
Definition c_b2 : YP09.region :=
  YP09.mkRegion (Some 32%nat) 0 2 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 34 0)); YP09.mkChunk 1 (CVal 1 (SOff 35 0))].
(* N = 0 *)
Definition c_ss0 : sstate :=
  mkSS LR_j sr_atoms [c_cur (SLit 0)] None (mkFacts [(9%nat, mkAF (2 ^ 46) (2 ^ 47) 5)] [] []).
(* N = 1: one byte *)
Definition c_facts1 : facts :=
  mkFacts [(9%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (27%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
           (32%nat, mkAF 4096 (2 ^ 47 - 2) 0); (34%nat, mkAF 0 255 0)] [] [].
Definition c_ss1 : sstate := mkSS LR_j sr_atoms [c_cur (SLit 1); c_b1] None c_facts1.
Definition c_SH1 : list shent := [mkSHE 32 0 1].
(* N >= 2: two bytes *)
Definition c_facts2 : facts :=
  mkFacts [(9%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (27%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
           (32%nat, mkAF 4096 (2 ^ 47 - 2) 0); (33%nat, mkAF 2 (2 ^ 64 - 1) 0); (34%nat, mkAF 0 255 0);
           (35%nat, mkAF 0 255 0)] [] [].
Definition c_ss2 : sstate := mkSS LR_j sr_atoms [c_cur (SOff 33 0); c_b2] None c_facts2.
Definition c_SH2 : list shent := [mkSHE 32 0 2].

(* a register the run leaves as an expression of one byte atom n is f of that byte, by computation over the
   256 values (Head.v hd_mod_val's method) *)
Lemma c_byte_val : forall (X : sv) (n : nat) (f : Z -> Z) E b,
  YFen.sv_atoms_in (fun m => Nat.eqb m n) X = true ->
  forallb (fun b => Z.eqb (bv_unsigned (sv_denot (hd_Eb b) X)) (f b)) (map Z.of_nat (seq 0 256)) = true ->
  (forall b, 0 <= b < 256 -> 0 <= f b < 2 ^ 64) ->
  ew E n = Z_to_bv 64 b -> 0 <= b < 256 ->
  sv_denot E X = Z_to_bv 64 (f b).
Proof.
  intros X n f E b HA HF Hf HE Hb.
  rewrite (YFen.sv_denot_agree_on (fun m => Nat.eqb m n) (hd_Eb b) E X);
    [| intros m Hm; apply Nat.eqb_eq in Hm; subst m; exact HE | exact HA].
  pose proof (proj1 (forallb_forall _ _) HF b ltac:(apply in_map_iff; exists (Z.to_nat b);
    split; [apply Z2Nat.id; lia | apply in_seq; lia])) as H. apply Z.eqb_eq in H.
  apply bv_eq. rewrite H, unsigned_lit_small by (apply Hf; exact Hb). reflexivity.
Qed.

Ltac c_awr E9 S1u :=
  try cbn [ss_mem];
  repeat (apply awr_ok_x_cons;
    [unfold c_cur, c_b1, c_b2; cbn [r_base r_wlo r_whi base_val];
     repeat rewrite ew_ewset_other by lia;
     try rewrite E9, S1u; intros ?a ?Ha;
     first [lia | left; split; [left; unfold LS_P, LS_N, LLVMF_STK, LF_MFRAME in *; lia | lia]] |]);
  apply awr_ok_x_nil.

Ltac c_inw E9 S1u :=
  let a := fresh "a" in let r := fresh "r" in let Hi := fresh "Hi" in let Hr := fresh "Hr" in
  intros a _ (r & Hi & Hr); cbn [ss_mem c_ss0 c_ss1 c_ss2] in Hi;
  repeat (destruct Hi as [<- | Hi];
    [unfold c_cur, c_b1, c_b2 in Hr; cbn [r_base r_wlo r_whi base_val] in Hr;
     repeat rewrite ew_ewset_other in Hr by lia;
     rewrite ?E9, ?S1u in Hr; cbv beta; unfold LS_P, LS_N in *; lia |]);
  destruct Hi.

Ltac c_kag cx HFr E9 S1u KN :=
  let K0 := fresh "K0" in
  pose proof (lf_frame_kagree _ _ _ _ (fun a => lf_sp1 cx + LS_P <= a < lf_sp1 cx + LS_N + 8) HFr) as K0;
  lazymatch type of K0 with _ -> kagree ?s _ ?m1 ?m2 =>
    assert (KN : kagree s (fun a => lf_sp1 cx + LS_P <= a mod 2 ^ 64 < lf_sp1 cx + LS_N + 8) m1 m2)
      by (apply K0; c_inw E9 S1u)
  end; clear K0.

(* a cursor slot's value from the run's final spill region: P + c or N + c, or a literal *)
Ltac c_val E32B E33B :=
  lazymatch goal with
  | |- sv_denot _ (SLit ?z) = Z_to_bv 64 ?v => replace v with z by lia; reflexivity
  | |- sv_denot ?EB (SOff 32 ?c) = Z_to_bv 64 ?v =>
      lazymatch type of E32B with ew _ 32 = Z_to_bv 64 ?p =>
        replace v with (p + c) by lia; apply (lf_sv_off EB 32 p c E32B); lia end
  | |- sv_denot ?EB (SOff 33 ?c) = Z_to_bv 64 ?v =>
      lazymatch type of E33B with ew _ 33 = Z_to_bv 64 ?p =>
        replace v with (p + c) by lia; apply (lf_sv_off EB 33 p c E33B); lia end
  end.
Ltac c_slot fy W3 EB ssB msB cx HS S9B E32B E33B :=
  first [ eapply (hd_slot_of fy W3 EB ssB msB cx 0%nat _ _ _ _ HS eq_refl eq_refl S9B)
        | eapply (hd_slot_of fy W3 EB ssB msB cx 1%nat _ _ _ _ HS eq_refl eq_refl S9B) ];
  [ hd_inch | c_val E32B E33B | lia ].

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
Hypothesis LAWS : AR_laws pa_segs B.

Local Notation FROM := (lf_from SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END).
#[local] Notation BASEF cx := (@lf_base fx rc SK PI B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx).
#[local] Notation JRN cx fp ly S W mem mdl k :=
  (ajournal_gx SEGS B G_HARNESS 0 [] LLVMF_STK (spZ (c_regs cx)) (amf_harness_fp (c_T cx))
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(LF_CID, fp)] ly S W mem mdl k).

(* the cut at +0xdac from a run's end state: the join's memory clauses kept off the cursor's two words *)
Lemma c_close : forall i cx (fy : YK11.FPState) fp k2 ly3 S3 W3 ms3 md3 msB md4 md mk P' N' s nm kc ac
    kbs mbs gbs T3,
  BASEF cx -> JRN cx fp ly3 S3 W3 (ms_mem ms3) md3 k2 -> frames S3 = [(LF_CID, fp)] -> 0 <= i <= 47 ->
  lf_saved cx W3 ms3 -> lf_header cx fp W3 ms3 -> lf_fshadow cx fp W3 ms3 LF_SH0 -> lf_slots cx md mk fp W3 ms3 ->
  lf_jbk B MT MS la_nul cx fp k2 (lf_ev i) (lf_mo LF_MO_SET LF_MO_OP i) (lf_wl i) LF_LIVE_HELD ly3 S3 W3 ms3 md3 T3
    [(md, MD_SIZE); (mk, MK_SIZE)] ->
  lf_blocks B cx md mk T3 ly3 S3 (rdW W3 (ms_mem ms3)) ->
  lf_data cx md mk kbs mbs gbs (rdW W3 (ms_mem ms3)) -> nk_opened kbs <= 64 * i ->
  lf_core cx ms3 -> sel_lregs 22%bv cx md fp i ms3 -> getr (ms_regs ms3) 22%bv = w64 s -> w_name s nm ->
  lf_shape fy LR_kcall msB ->
  (forall r : bv 5, In r [2%bv; 8%bv; 9%bv; 3%bv; 4%bv; 19%bv; 21%bv; 22%bv; 23%bv; 24%bv; 25%bv; 26%bv; 27%bv] ->
     getr (ms_regs msB) r = getr (ms_regs ms3) r) ->
  getr (ms_regs msB) 18%bv = w64 kc -> getr (ms_regs msB) 20%bv = w64 ac -> 0 <= kc < 40 -> 0 <= ac < 40 ->
  kagree SEGS (fun a => lf_sp1 cx + LS_P <= a mod 2 ^ 64 < lf_sp1 cx + LS_N + 8)
    (rdW W3 (ms_mem ms3)) (rdW W3 (ms_mem msB)) ->
  mem_grows (rdW W3 (ms_mem ms3)) (rdW W3 (ms_mem msB)) ->
  m_fds md4 = m_fds md3 -> m_fs md4 = m_fs md3 ->
  lf_cur cx W3 msB P' N' ->
  r_d_inv B MT MS la_nul LF_MO_SET LF_MO_OP i cx fy fp k2 ly3 S3 W3 msB md4.
Proof.
  intros i cx fy fp k2 ly3 S3 W3 ms3 md3 msB md4 md mk P' N' s nm kc ac kbs mbs gbs T3
    HB HJ Hfr Hi Hsv Hhd Hfs Hsl Hjbk Hblk Hdat Hop Hcore Hlr Hs Hnm Hsh KR R18 R20 Hkc Hac KBm GBm Fd Fs Hcur.
  pose proof (lf_sp1_le cx) as (P1 & P2).
  assert (XN : forall a, lf_cut_fp MS la_nul cx fp md mk T3 a ->
            ~ (lf_sp1 cx + LS_P <= a mod 2 ^ 64 < lf_sp1 cx + LS_N + 8)).
  { intros a Ha. assert (HFR : In (LF_CID, fp) (frames S3)) by (rewrite Hfr; left; reflexivity).
    pose proof asan_consts as ((C1a & C1b) & _).
    destruct (lf_frame_facts SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx fp ly3 S3 W3
      (ms_mem ms3) md3 k2 HB HJ) as (H16 & Hceil & Hslo & Hshi & Hs47 & _ & _).
    assert (Hs1 : spZ (c_regs cx) - LF_MFRAME - 16 <= lf_sp1 cx).
    { unfold lf_sp1. pose proof (lf_sp1_range (spZ (c_regs cx)) ltac:(unfold LF_MFRAME, LLVMF_STK in *; lia) H16)
        as (R & _). lia. }
    destruct (lf_cut_fp_place SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END LAWS cx fp k2
      ly3 S3 W3 (ms_mem ms3) md3 _ _ _ _ ms3 md3 md mk T3 _ a HB HJ HFR Hjbk Hblk Ha) as [Hp | [Hp | Hp]];
      rewrite Z.mod_small by (unfold LF_MFRAME, LLVMF_STK in *; lia); unfold LS_P, LS_N, LF_MFRAME, LLVMF_STK in *; lia. }
  destruct (lf_cut_keep B MT MS la_nul _ cx fp k2 _ _ _ _ md mk kbs mbs gbs T3 _ ly3 S3 W3 ms3 md3
    W3 msB md4 KBm (wcarry_on_grows _ _ _ GBm) Fd Fs XN Hsv Hhd Hfs Hsl Hjbk Hblk Hdat)
    as (Hsv' & Hhd' & Hfs' & Hsl' & Hjbk' & Hblk' & Hdat').
  pose proof Hcore as (C2 & C8 & C9 & C3 & C4).
  destruct Hlr as (L19 & L21 & _ & L23 & L24 & L25 & L26 & L27).
  destruct L19 as [Habs | L19]; [apply (f_equal (@bv_unsigned 5)) in Habs; discriminate Habs|].
  destruct L21 as [Habs | L21]; [apply (f_equal (@bv_unsigned 5)) in Habs; discriminate Habs|].
  exists md, mk, P', N', kbs, mbs, gbs, T3, s, nm, kc, ac.
  split; [exact Hsh|].
  split.
  { unfold r_regs. split; [exact R18|]. split; [rewrite KR by sel_inbv; exact L19|].
    split; [exact R20|]. split; [rewrite KR by sel_inbv; exact L21|].
    split; [rewrite KR by sel_inbv; exact Hs|].
    repeat split; rewrite KR by sel_inbv; assumption. }
  split; [exact Hnm|]. split; [exact Hkc|]. split; [exact Hac|].
  split; [exact Hi|].
  split; [unfold lf_core; rewrite !KR by sel_inbv; repeat split; assumption|].
  split; [exact Hsv'|]. split; [exact Hhd'|]. split; [exact Hfs'|]. split; [exact Hsl'|].
  split; [exact Hcur|]. split; [exact Hjbk'|]. split; [exact Hblk'|]. split; [exact Hdat' | exact Hop].
Qed.

Lemma r_sizes : forall POST i, 0 <= i <= 47 ->
  FROM POST (r_d_inv B MT MS la_nul LF_MO_SET LF_MO_OP i) ->
  FROM POST (sel_join SK B MT MS la_nul LF_MO_SET LF_MO_OP LR_j 22%bv i).
Proof.
  intros POST i Hi HK cx fy fp k2 ly3 S3 W3 ms3 md3 HB Hfx HJ Hfr GI.
  pose proof HJ as HJ0.
  destruct GI as (md & mk & P & N & s & nm & kbs & mbs & gbs & T3 & _ & Hsh & Hcore & Hlr & Hs & Hnm & HAK & Hcur
    & Hop).
  destruct HAK as (_ & _ & Hsv & Hhd & Hfs & Hsl & Hjbk & Hblk & Hdat).
  pose proof HB as (_ & _ & HGX & _).
  pose proof Hcore as (C2 & C8 & C9 & C3 & C4).
  pose proof Hcur as (HcP & HcN & (q & Hq & EP & EN)).
  destruct (lf_frame_facts SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx fp ly3 S3 W3
    (ms_mem ms3) md3 k2 HB HJ) as (H16 & Hceil & _ & Hshi & Hs47 & Hpres & HAR).
  pose proof (hd_sp1 cx) as (P1 & P2 & P3).
  pose proof (kp_rdword_range _ _ _ (kp_aview_range SEGS (w_H W3) (ms_mem ms3)) HcP) as RP.
  pose proof (kp_rdword_range _ _ _ (kp_aview_range SEGS (w_H W3) (ms_mem ms3)) HcN) as RN.
  pose proof asan_consts as ((C1a & C1b) & _).
  assert (S1r : alloc_ceiling <= lf_sp1 cx) by (unfold LLVMF_STK, LF_MFRAME in *; lia).
  assert (S1u : bv_unsigned (getr (ms_regs ms3) 9) = lf_sp1 cx).
  { rewrite C9. unfold w64. apply unsigned_lit_small. unfold LF_MFRAME in *. lia. }
  assert (S1f : forall E, ew E 9 = getr (ms_regs ms3) 9 -> afact_ok E 9 (mkAF (2 ^ 46) (2 ^ 47) 5)).
  { intros E HE. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HE, S1u.
    split; [unfold LF_MFRAME in *; lia|]. split; [|lia].
    unfold lf_sp1, lf_sp1_of. rewrite Z.mul_comm. change (2 ^ 5) with 32. apply Z_mod_mult. }
  pose proof Hlr as (_ & _ & _ & L23 & L24 & L25 & L26 & L27).
  (* the cut, from any state the runs end in *)
  assert (CLOSE : forall (msB : machine_state) md4 kc ac P' N',
    JRN cx fp ly3 S3 W3 (ms_mem msB) md4 k2 ->
    lf_shape fy LR_kcall msB ->
    (forall r : bv 5, In r [2%bv; 8%bv; 9%bv; 3%bv; 4%bv; 19%bv; 21%bv; 22%bv; 23%bv; 24%bv; 25%bv; 26%bv; 27%bv] ->
       getr (ms_regs msB) r = getr (ms_regs ms3) r) ->
    getr (ms_regs msB) 18%bv = w64 kc -> getr (ms_regs msB) 20%bv = w64 ac -> 0 <= kc < 40 -> 0 <= ac < 40 ->
    kagree SEGS (fun a => lf_sp1 cx + LS_P <= a mod 2 ^ 64 < lf_sp1 cx + LS_N + 8)
      (rdW W3 (ms_mem ms3)) (rdW W3 (ms_mem msB)) ->
    mem_grows (rdW W3 (ms_mem ms3)) (rdW W3 (ms_mem msB)) ->
    m_fds md4 = m_fds md3 -> m_fs md4 = m_fs md3 ->
    lf_cur cx W3 msB P' N' ->
    SRr SEGS W3 (mkCfg msB md4) (POST cx)).
  { intros msB md4 kc ac P' N' HJB HSB KR R18 R20 Hkc Hac KB GB Fd Fs HcB.
    apply (HK cx fy fp k2 ly3 S3 W3 msB md4 HB Hfx HJB Hfr).
    exact (c_close i cx fy fp k2 ly3 S3 W3 ms3 md3 msB md4 md mk P' N' s nm kc ac kbs mbs gbs T3
      HB HJ0 Hfr Hi Hsv Hhd Hfs Hsl Hjbk Hblk Hdat Hop Hcore Hlr Hs Hnm HSB KR R18 R20 Hkc Hac KB GB Fd Fs HcB). }
  rewrite (lf_shape_eta fy LR_j ms3 Hsh).
  pose proof (@paj_run_to_x fy rc SK link_listing PL_link PI B LAWS G_HARNESS HGX 0 []) as RUNTO.
  destruct (Z.eq_dec N 0) as [HN0 | HN0].
  - (* N = 0: beqz to +0xda4, both sizes 0 *)
    set (E := Eimg (Ereg (ms_regs ms3) [w64 P])).
    assert (HEI : img_env pa_val A_LIM E) by apply Eimg_env.
    assert (E9 : ew E 9 = getr (ms_regs ms3) 9) by (apply ew_Eimg_Ereg_nat; reflexivity).
    assert (E32 : ew E 32 = Z_to_bv 64 P) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); reflexivity).
    assert (HS : st_ok_pi (fx := fy) pa_segs pa_val E c_ss0
      (restrict (w_H W3) (@mkst fy (ms_regs ms3) (Z_to_bv 64 (BASE + LR_j)) (ms_mem ms3) (seg_rom SEGS)))).
    { rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
      - apply regs_ok_Eimg_Ereg.
      - reflexivity.
      - constructor; [|constructor].
        unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks c_cur base_val]. rewrite E9, S1u.
        unfold LS_N, LS_P, LF_MFRAME in *.
        split; [lia|]. split; [lia|]. split.
        + intros o Ho. apply (apresent_writable SEGS). apply Hpres. unfold LLVMF_STK. lia.
        + constructor; [|constructor; [|constructor]].
          * apply (hd_chunk cx W3 ms3 E 0x118 (SOff 32 0) P HcP). rewrite (lf_sv_off E 32 P 0 E32) by lia.
            rewrite Z.add_0_r. reflexivity.
          * apply (hd_chunk cx W3 ms3 E 0x120 (SLit 0) N HcN). rewrite HN0. reflexivity.
      - cbn. tauto.
      - split; [|split; exact I]. cbn [f_atoms atoms_ok]. split; [exact (S1f E E9) | exact I]. }
    assert (SHOK : sh_ok pa_segs (SLit 0) [] E
      (mrestrict (w_H W3) (ms_mem (@mkst fy (ms_regs ms3) (Z_to_bv 64 (BASE + LR_j)) (ms_mem ms3) (seg_rom SEGS)))))
      by (unfold sh_ok; apply Forall_nil).
    paj_run_to_tok RUNTO HS HJ SHOK (0, 0) LR_kcall; [c_awr E9 S1u|].
    rename ms into msB, HF into HFB, HFr into HFrB, HG into HGB.
    c_kag cx HFrB E9 S1u KB.
    lazymatch type of HS with st_ok_pi _ _ ?EB ?ssB _ =>
      assert (HAE : env_agree 32 (Ereg (ms_regs ms3) []) EB)
        by (split; [intros n Hn; repeat rewrite ew_ewset_other by lia; subst E;
                    rewrite Eimg_low by (unfold A_TEXT; lia); rewrite !ew_Ereg_lt by lia; reflexivity
                   | reflexivity]);
      assert (S9B : bv_unsigned (ew EB 9) = lf_sp1 cx) by (repeat rewrite ew_ewset_other by lia; rewrite E9; exact S1u);
      assert (E32B : ew EB 32 = Z_to_bv 64 P) by (repeat rewrite ew_ewset_other by lia; exact E32);
      lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdx |} _ => set (mdX := mdx) in * end;
      apply (CLOSE msB mdX 0 0 P N);
      [ exact HJ | exact (lf_shape_of_st_ok fy W3 _ ssB msB HS eq_refl)
      | intros r Hr; apply (lf_reg_atom fy W3 _ ssB msB _ r HS HAE);
        repeat (destruct Hr as [<- | Hr]; [vm_compute; reflexivity|]); destruct Hr
      | rewrite (st_ok_pi_restrict_reg (fx := fy) (w_H W3) _ _ msB 18%bv HS); vm_compute; reflexivity
      | rewrite (st_ok_pi_restrict_reg (fx := fy) (w_H W3) _ _ msB 20%bv HS); vm_compute; reflexivity
      | lia | lia
      | exact KB
      | exact HGB
      | subst mdX; rewrite !lf_wvb_fds; reflexivity
      | subst mdX; rewrite !lf_wvb_fs; reflexivity
      | split; [|split; [|exists q; lia]]; c_slot fy W3 EB ssB msB cx HS S9B E32B E32B ]
    end.
  - (* N >= 1: the byte b0 at P *)
    assert (HN1' : 1 <= N) by lia.
    pose proof Hjbk as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & J13 & J14 & J15).
    destruct J14 as (Pl0 & Pl1 & Pl2).
    assert (Hqn : (Z.to_nat q < length (c_pl cx))%nat) by (unfold c_n in *; lia).
    pose proof (Pl2 (Z.to_nat q) Hqn) as Hb0. rewrite Z2Nat.id in Hb0 by lia. rewrite <- EP in Hb0.
    destruct (nth_error (c_pl cx) (Z.to_nat q)) as [b0|] eqn:Eb0; [|apply nth_error_None in Eb0; lia].
    pose proof (bv_unsigned_in_range _ b0) as Rb0. change (bv_modulus 8) with 256 in Rb0.
    assert (Hin : In (c_p cx, c_n cx) (ablocks B ly3 S3))
      by (apply (lf_input_block SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END LAWS cx fp
                   ly3 S3 W3 (ms_mem ms3) md3 k2 HB HJ); lia).
    destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hin) as (_ & Pb0 & Pbc & Pbapp & _).
    assert (Rn : req_size (c_n cx) = c_n cx)
      by (unfold req_size; destruct (c_n cx =? 0) eqn:En; [apply Z.eqb_eq in En; lia | reflexivity]).
    rewrite Rn in Pbc, Pbapp.
    pose proof (blk_off_imgP B ly3 S3 W3 (ms_mem ms3) md3 (c_p cx) (c_n cx) HAR Hin) as Hoff.
    rewrite Rn in Hoff. unfold off_img, YImgTop.IMG_LO, YImgTop.IMG_TOP in Hoff.
    pose proof alloc_ceiling_lt as CL.
    destruct (Z.eq_dec N 1) as [HN1 | HN1].
    + (* N = 1: s2 := b0 mod 40, then N - 1 = 0: s4 := 0 *)
      set (E := Eimg (Ereg (ms_regs ms3) [w64 P; w64 N; Z_to_bv 64 (bv_unsigned b0)])).
      assert (HEI : img_env pa_val A_LIM E) by apply Eimg_env.
      assert (E9 : ew E 9 = getr (ms_regs ms3) 9) by (apply ew_Eimg_Ereg_nat; reflexivity).
      assert (E27 : ew E 27 = Z_to_bv 64 SHADOW_OFF)
        by (transitivity (getr (ms_regs ms3) 27); [apply ew_Eimg_Ereg_nat; reflexivity | exact L27]).
      assert (E32 : ew E 32 = Z_to_bv 64 P) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); reflexivity).
      assert (E33 : ew E 33 = Z_to_bv 64 N) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); reflexivity).
      assert (E34 : ew E 34 = Z_to_bv 64 (bv_unsigned b0))
        by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); reflexivity).
      assert (HS : st_ok_pi (fx := fy) pa_segs pa_val E c_ss1
        (restrict (w_H W3) (@mkst fy (ms_regs ms3) (Z_to_bv 64 (BASE + LR_j)) (ms_mem ms3) (seg_rom SEGS)))).
      { rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
        - apply regs_ok_Eimg_Ereg.
        - reflexivity.
        - constructor; [|constructor; [|constructor]].
          + unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks c_cur base_val]. rewrite E9, S1u.
            unfold LS_N, LS_P, LF_MFRAME in *.
            split; [lia|]. split; [lia|]. split.
            * intros o Ho. apply (apresent_writable SEGS). apply Hpres. unfold LLVMF_STK. lia.
            * constructor; [|constructor; [|constructor]].
              -- apply (hd_chunk cx W3 ms3 E 0x118 (SOff 32 0) P HcP). rewrite (lf_sv_off E 32 P 0 E32) by lia.
                 rewrite Z.add_0_r. reflexivity.
              -- apply (hd_chunk cx W3 ms3 E 0x120 (SLit 1) N HcN). rewrite HN1. reflexivity.
          + unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks c_b1 base_val].
            rewrite E32, unsigned_lit_small by lia.
            split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
            constructor; [|constructor].
            apply (chunk_ok_val SEGS E _ P 0 1 (SOff 34 0) (bv_unsigned b0)); [| cbn; lia | cbn; lia |].
            * rewrite (lf_sv_off E 34 (bv_unsigned b0) 0 E34) by lia. rewrite Z.add_0_r. reflexivity.
            * rewrite Z.add_0_r. exact (hd_val_mem1 _ _ _ _ Hb0).
        - apply pairwise_disjoint_of_extents. cbn -[E].
          repeat match goal with |- _ /\ _ => split end; try exact I;
          unfold zdisj, extent_of_region; cbn [r_base r_lo r_hi c_cur c_b1 base_val fst snd];
          rewrite ?E9, ?S1u, ?E32; rewrite ?unsigned_lit_small by lia;
          unfold LS_P, LS_N, LF_MFRAME in *; lia.
        - split; [|split; exact I]. cbn [c_facts1 f_atoms atoms_ok].
          split; [exact (S1f E E9)|].
          unfold afact_ok; cbn [af_lo af_hi af_al2].
          rewrite E27, E32, E34, !unsigned_lit_small by (unfold SHADOW_OFF; lia).
          change (2 ^ 0) with 1. rewrite !Z.mod_1_r.
          unfold SHADOW_OFF in *. repeat split; try lia; try exact I. }
      assert (RA : range_addressable (aview SEGS (w_H W3) (ms_mem ms3)) SHADOW_OFF P 1)
        by (eapply range_addressable_of_block; [eassumption | eassumption | exact Hin | lia | rewrite Rn; lia]).
      assert (SHOK : sh_ok pa_segs hd_Bx c_SH1 E
        (mrestrict (w_H W3) (ms_mem (@mkst fy (ms_regs ms3) (Z_to_bv 64 (BASE + LR_j)) (ms_mem ms3) (seg_rom SEGS))))).
      { unfold sh_ok, c_SH1. constructor; [|constructor]. unfold shent_ok, app_apart, hd_Bx.
        cbn [she_m she_lo she_hi ms_mem mkst].
        rewrite (U_atom E 32 P E32) by lia. rewrite (U_atom E 27 SHADOW_OFF E27) by (unfold SHADOW_OFF; lia).
        split; [rewrite Z.add_0_r, Z.sub_0_r; exact RA|].
        intros a Ha. unfold in_app, kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *. lia. }
      paj_run_to_tok RUNTO HS HJ SHOK hd_span LR_kcall; [c_awr E9 S1u|].
      rename ms into msB, HF into HFB, HFr into HFrB, HG into HGB.
      c_kag cx HFrB E9 S1u KB.
      lazymatch type of HS with st_ok_pi _ _ ?EB ?ssB _ =>
        assert (HAE : env_agree 32 (Ereg (ms_regs ms3) []) EB)
          by (split; [intros n Hn; repeat rewrite ew_ewset_other by lia; subst E;
                      rewrite Eimg_low by (unfold A_TEXT; lia); rewrite !ew_Ereg_lt by lia; reflexivity
                     | reflexivity]);
        assert (S9B : bv_unsigned (ew EB 9) = lf_sp1 cx) by (repeat rewrite ew_ewset_other by lia; rewrite E9; exact S1u);
        assert (E32B : ew EB 32 = Z_to_bv 64 P) by (repeat rewrite ew_ewset_other by lia; exact E32);
        assert (E33B : ew EB 33 = Z_to_bv 64 N) by (repeat rewrite ew_ewset_other by lia; exact E33);
        assert (E34B : ew EB 34 = Z_to_bv 64 (bv_unsigned b0)) by (repeat rewrite ew_ewset_other by lia; exact E34);
        lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdx |} _ => set (mdX := mdx) in * end;
        apply (CLOSE msB mdX (bv_unsigned b0 mod 40) 0 (P + 1) (N - 1));
        [ exact HJ | exact (lf_shape_of_st_ok fy W3 _ ssB msB HS eq_refl)
        | intros r Hr; apply (lf_reg_atom fy W3 _ ssB msB _ r HS HAE);
          repeat (destruct Hr as [<- | Hr]; [vm_compute; reflexivity|]); destruct Hr
        | rewrite (st_ok_pi_restrict_reg (fx := fy) (w_H W3) _ _ msB 18%bv HS);
          let X := eval vm_compute in (sr_get (ss_regs ssB) 18%bv) in
          replace (sr_get (ss_regs ssB) 18%bv) with X by (vm_compute; reflexivity);
          exact (c_byte_val X 34 (fun b => b mod 40) EB (bv_unsigned b0) ltac:(vm_compute; reflexivity)
            ltac:(vm_compute; reflexivity)
            ltac:(intros bx Hbx; cbv beta; pose proof (Z.mod_pos_bound bx 40 ltac:(lia)); lia) E34B Rb0)
        | rewrite (st_ok_pi_restrict_reg (fx := fy) (w_H W3) _ _ msB 20%bv HS); vm_compute; reflexivity
        | pose proof (Z.mod_pos_bound (bv_unsigned b0) 40 ltac:(lia)); lia | lia
        | exact KB
        | exact HGB
        | subst mdX; rewrite !lf_wvb_fds; reflexivity
        | subst mdX; rewrite !lf_wvb_fs; reflexivity
        | split; [|split; [|exists (q + 1); lia]]; c_slot fy W3 EB ssB msB cx HS S9B E32B E33B ]
      end.
    + (* N >= 2: s2 := b0 mod 40, s4 := b1 mod 40 *)
      assert (HN2 : 2 <= N) by lia.
      assert (Hqn1 : (Z.to_nat (q + 1) < length (c_pl cx))%nat) by (unfold c_n in *; lia).
      pose proof (Pl2 (Z.to_nat (q + 1)) Hqn1) as Hb1. rewrite Z2Nat.id in Hb1 by lia.
      replace (c_p cx + (q + 1)) with (P + 1) in Hb1 by lia.
      destruct (nth_error (c_pl cx) (Z.to_nat (q + 1))) as [b1|] eqn:Eb1; [|apply nth_error_None in Eb1; lia].
      pose proof (bv_unsigned_in_range _ b1) as Rb1. change (bv_modulus 8) with 256 in Rb1.
      set (E := Eimg (Ereg (ms_regs ms3) [w64 P; w64 N; Z_to_bv 64 (bv_unsigned b0); Z_to_bv 64 (bv_unsigned b1)])).
      assert (HEI : img_env pa_val A_LIM E) by apply Eimg_env.
      assert (E9 : ew E 9 = getr (ms_regs ms3) 9) by (apply ew_Eimg_Ereg_nat; reflexivity).
      assert (E27 : ew E 27 = Z_to_bv 64 SHADOW_OFF)
        by (transitivity (getr (ms_regs ms3) 27); [apply ew_Eimg_Ereg_nat; reflexivity | exact L27]).
      assert (E32 : ew E 32 = Z_to_bv 64 P) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); reflexivity).
      assert (E33 : ew E 33 = Z_to_bv 64 N) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); reflexivity).
      assert (E34 : ew E 34 = Z_to_bv 64 (bv_unsigned b0))
        by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); reflexivity).
      assert (E35 : ew E 35 = Z_to_bv 64 (bv_unsigned b1))
        by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); reflexivity).
      assert (HS : st_ok_pi (fx := fy) pa_segs pa_val E c_ss2
        (restrict (w_H W3) (@mkst fy (ms_regs ms3) (Z_to_bv 64 (BASE + LR_j)) (ms_mem ms3) (seg_rom SEGS)))).
      { rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
        - apply regs_ok_Eimg_Ereg.
        - reflexivity.
        - constructor; [|constructor; [|constructor]].
          + unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks c_cur base_val]. rewrite E9, S1u.
            unfold LS_N, LS_P, LF_MFRAME in *.
            split; [lia|]. split; [lia|]. split.
            * intros o Ho. apply (apresent_writable SEGS). apply Hpres. unfold LLVMF_STK. lia.
            * constructor; [|constructor; [|constructor]].
              -- apply (hd_chunk cx W3 ms3 E 0x118 (SOff 32 0) P HcP). rewrite (lf_sv_off E 32 P 0 E32) by lia.
                 rewrite Z.add_0_r. reflexivity.
              -- apply (hd_chunk cx W3 ms3 E 0x120 (SOff 33 0) N HcN). rewrite (lf_sv_off E 33 N 0 E33) by lia.
                 rewrite Z.add_0_r. reflexivity.
          + unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks c_b2 base_val].
            rewrite E32, unsigned_lit_small by lia.
            split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
            constructor; [|constructor; [|constructor]].
            * apply (chunk_ok_val SEGS E _ P 0 1 (SOff 34 0) (bv_unsigned b0)); [| cbn; lia | cbn; lia |].
              -- rewrite (lf_sv_off E 34 (bv_unsigned b0) 0 E34) by lia. rewrite Z.add_0_r. reflexivity.
              -- rewrite Z.add_0_r. exact (hd_val_mem1 _ _ _ _ Hb0).
            * apply (chunk_ok_val SEGS E _ P 1 1 (SOff 35 0) (bv_unsigned b1)); [| cbn; lia | cbn; lia |].
              -- rewrite (lf_sv_off E 35 (bv_unsigned b1) 0 E35) by lia. rewrite Z.add_0_r. reflexivity.
              -- exact (hd_val_mem1 _ _ _ _ Hb1).
        - apply pairwise_disjoint_of_extents. cbn -[E].
          repeat match goal with |- _ /\ _ => split end; try exact I;
          unfold zdisj, extent_of_region; cbn [r_base r_lo r_hi c_cur c_b2 base_val fst snd];
          rewrite ?E9, ?S1u, ?E32; rewrite ?unsigned_lit_small by lia;
          unfold LS_P, LS_N, LF_MFRAME in *; lia.
        - split; [|split; exact I]. cbn [c_facts2 f_atoms atoms_ok].
          split; [exact (S1f E E9)|].
          unfold afact_ok; cbn [af_lo af_hi af_al2].
          rewrite E27, E32, E33, E34, E35, !unsigned_lit_small by (unfold SHADOW_OFF; lia).
          change (2 ^ 0) with 1. rewrite !Z.mod_1_r.
          unfold SHADOW_OFF in *. repeat split; try lia; try exact I. }
      assert (RA : range_addressable (aview SEGS (w_H W3) (ms_mem ms3)) SHADOW_OFF P 2)
        by (eapply range_addressable_of_block; [eassumption | eassumption | exact Hin | lia | rewrite Rn; lia]).
      assert (SHOK : sh_ok pa_segs hd_Bx c_SH2 E
        (mrestrict (w_H W3) (ms_mem (@mkst fy (ms_regs ms3) (Z_to_bv 64 (BASE + LR_j)) (ms_mem ms3) (seg_rom SEGS))))).
      { unfold sh_ok, c_SH2. constructor; [|constructor]. unfold shent_ok, app_apart, hd_Bx.
        cbn [she_m she_lo she_hi ms_mem mkst].
        rewrite (U_atom E 32 P E32) by lia. rewrite (U_atom E 27 SHADOW_OFF E27) by (unfold SHADOW_OFF; lia).
        split; [rewrite Z.add_0_r, Z.sub_0_r; exact RA|].
        intros a Ha. unfold in_app, kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *. lia. }
      paj_run_to_tok RUNTO HS HJ SHOK hd_span LR_kcall; [c_awr E9 S1u|].
      rename ms into msB, HF into HFB, HFr into HFrB, HG into HGB.
      c_kag cx HFrB E9 S1u KB.
      lazymatch type of HS with st_ok_pi _ _ ?EB ?ssB _ =>
        assert (HAE : env_agree 32 (Ereg (ms_regs ms3) []) EB)
          by (split; [intros n Hn; repeat rewrite ew_ewset_other by lia; subst E;
                      rewrite Eimg_low by (unfold A_TEXT; lia); rewrite !ew_Ereg_lt by lia; reflexivity
                     | reflexivity]);
        assert (S9B : bv_unsigned (ew EB 9) = lf_sp1 cx) by (repeat rewrite ew_ewset_other by lia; rewrite E9; exact S1u);
        assert (E32B : ew EB 32 = Z_to_bv 64 P) by (repeat rewrite ew_ewset_other by lia; exact E32);
        assert (E33B : ew EB 33 = Z_to_bv 64 N) by (repeat rewrite ew_ewset_other by lia; exact E33);
        assert (E34B : ew EB 34 = Z_to_bv 64 (bv_unsigned b0)) by (repeat rewrite ew_ewset_other by lia; exact E34);
        assert (E35B : ew EB 35 = Z_to_bv 64 (bv_unsigned b1)) by (repeat rewrite ew_ewset_other by lia; exact E35);
        lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdx |} _ => set (mdX := mdx) in * end;
        apply (CLOSE msB mdX (bv_unsigned b0 mod 40) (bv_unsigned b1 mod 40) (P + 2) (N - 2));
        [ exact HJ | exact (lf_shape_of_st_ok fy W3 _ ssB msB HS eq_refl)
        | intros r Hr; apply (lf_reg_atom fy W3 _ ssB msB _ r HS HAE);
          repeat (destruct Hr as [<- | Hr]; [vm_compute; reflexivity|]); destruct Hr
        | rewrite (st_ok_pi_restrict_reg (fx := fy) (w_H W3) _ _ msB 18%bv HS);
          let X := eval vm_compute in (sr_get (ss_regs ssB) 18%bv) in
          replace (sr_get (ss_regs ssB) 18%bv) with X by (vm_compute; reflexivity);
          exact (c_byte_val X 34 (fun b => b mod 40) EB (bv_unsigned b0) ltac:(vm_compute; reflexivity)
            ltac:(vm_compute; reflexivity)
            ltac:(intros bx Hbx; cbv beta; pose proof (Z.mod_pos_bound bx 40 ltac:(lia)); lia) E34B Rb0)
        | rewrite (st_ok_pi_restrict_reg (fx := fy) (w_H W3) _ _ msB 20%bv HS);
          let X := eval vm_compute in (sr_get (ss_regs ssB) 20%bv) in
          replace (sr_get (ss_regs ssB) 20%bv) with X by (vm_compute; reflexivity);
          exact (c_byte_val X 35 (fun b => b mod 40) EB (bv_unsigned b1) ltac:(vm_compute; reflexivity)
            ltac:(vm_compute; reflexivity)
            ltac:(intros bx Hbx; cbv beta; pose proof (Z.mod_pos_bound bx 40 ltac:(lia)); lia) E35B Rb1)
        | pose proof (Z.mod_pos_bound (bv_unsigned b0) 40 ltac:(lia)); lia
        | pose proof (Z.mod_pos_bound (bv_unsigned b1) 40 ltac:(lia)); lia
        | exact KB
        | exact HGB
        | subst mdX; rewrite !lf_wvb_fds; reflexivity
        | subst mdX; rewrite !lf_wvb_fs; reflexivity
        | split; [|split; [|exists (q + 2); lia]]; c_slot fy W3 EB ssB msB cx HS S9B E32B E33B ]
      end.
Qed.

End a.
