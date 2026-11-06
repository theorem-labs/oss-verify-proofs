(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YC85.v for libreac/fuzz_boxreg's program walk (as fuzz_identity's lib/A/Prog/YC85.v, ea5560a967b, carries it): the listing's names are bsym; module paths changed. No image numeral occurs in this file. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_boxreg/lib/A/Prog/YC85.v, with its module paths and module names changed; 313 of its 404 lines of code are new or changed and 320 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/LLVMFuzzerTestOneInputFree.v, with its module paths and module names changed; 444 of its 488 lines of code are new or changed and 360 lines of the source are left out. *)
(* LLVMFuzzerTestOneInput on image A: op_write's name selector (operation byte mod 6 = 1, entry +0x8e4, to the
   join +0xffc). Offsets from 0x827d4; listing
   (internal path) (internal record, sha256 e84d6f0c6974).

     +0x8e4  N - 1 = 0 (no byte left)        -> +0x99c: a0 := 0, the g_names path: s5 := g_names
     +0x8ec  byte b := [P + 1] (an instrumented 1-byte load), cursor := (P + 2, N - 2)
     +0x918  b = 0xff                          -> s5 := 0
     +0xa78  b <= 0x3f                         -> +0xa7c: s5 := g_names + 8 b
             b >  0x3f                         -> +0xfc0: a0 := LA_ODD + 8 (b mod 6) (mulhu by 0x2aaaaaaaaaaaaaab,
                                                  the constant at .rodata + 0xa0), an instrumented 8-byte load
                                                  s5 := odd[b mod 6]

   w_sel : forall POST i, 0 <= i <= 47 -> FROM POST (sel_join .. LF_wj 21%bv i) -> FROM POST (lf_arm_inv .. 1 i)
   (Sel.v's join at +0xffc with the name in s5). The error paths of the two instrumented checks are not reached:
   the payload byte and the odd table are addressable (the SH entries).

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
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

Definition LF_wj : Z := AF_LLVMFuzzerTestOneInput + 0xffc.
(* atoms: 32 = P1 (the byte's address), 33 = N1, 34 = the byte, 35 = LA_ODD *)
Definition w_odd_rg : YP09.region :=
  YP09.mkRegion (Some 9%nat) LS_ODD (LS_ODD + 8) LS_ODD LS_ODD [YP09.mkChunk LS_ODD (CVal 8 (SOff 35 0))].
Definition w_cur_rg (vP vN : sv) : YP09.region :=
  YP09.mkRegion (Some 9%nat) LS_P (LS_N + 8) LS_P (LS_N + 8) [YP09.mkChunk LS_P (CVal 8 vP); YP09.mkChunk LS_N (CVal 8 vN)].
Definition w_byte_rg : YP09.region := YP09.mkRegion (Some 32%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 34 0))].
Definition w_facts1 : facts :=
  mkFacts [(9%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (27%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
           (32%nat, mkAF 4096 (2 ^ 47 - 2) 0); (33%nat, mkAF 1 (2 ^ 64 - 1) 0); (34%nat, mkAF 0 255 0);
           (35%nat, mkAF LA_ODD LA_ODD 0)] [] [].
Definition w_facts0 : facts :=
  mkFacts [(9%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (32%nat, mkAF 4096 (2 ^ 47 - 2) 0); (33%nat, mkAF 0 0 0)] [] [].
Definition w_ss0 : sstate := mkSS LF_op1 sr_atoms [w_cur_rg (SOff 32 0) (SOff 33 0)] None w_facts0.
Definition w_ss1 : sstate := mkSS LF_op1 sr_atoms [w_odd_rg; w_cur_rg (SOff 32 0) (SOff 33 0); w_byte_rg] None w_facts1.
Definition w_SH : list shent := [mkSHE 32 0 1; mkSHE 35 0 48].




Ltac w_awr E9 S1u :=
  try cbn [ss_mem];
  repeat (apply awr_ok_x_cons;
    [unfold w_odd_rg, w_cur_rg, w_byte_rg, w_c6_rg, w_odd_tab; cbn [r_base r_wlo r_whi base_val];
     repeat rewrite ew_ewset_other by lia;
     try rewrite E9, S1u; intros ?a ?Ha;
     first [lia | left; split; [left; unfold LS_P, LS_N, LLVMF_STK, LF_MFRAME in *; lia | lia]] |]);
  apply awr_ok_x_nil.

Ltac w_inw E9 S1u :=
  let a := fresh "a" in let r := fresh "r" in let Hi := fresh "Hi" in let Hr := fresh "Hr" in
  intros a _ (r & Hi & Hr); cbn [ss_mem w_ss1 w_ss0] in Hi;
  repeat (destruct Hi as [<- | Hi];
    [unfold w_odd_rg, w_cur_rg, w_byte_rg, w_c6_rg, w_odd_tab in Hr; cbn [r_base r_wlo r_whi base_val] in Hr;
     repeat rewrite ew_ewset_other in Hr by lia;
     rewrite ?E9, ?S1u in Hr; cbv beta; unfold LS_P, LS_N, LS_ODD in *; lia |]);
  destruct Hi.
Ltac w_kag cx HFr E9 S1u KN :=
  let K0 := fresh "K0" in
  pose proof (lf_frame_kagree _ _ _ _ (fun a => lf_sp1 cx + LS_P <= a < lf_sp1 cx + LS_N + 8) HFr) as K0;
  lazymatch type of K0 with _ -> kagree ?s _ ?m1 ?m2 =>
    assert (KN : kagree s (fun a => lf_sp1 cx + LS_P <= a mod 2 ^ 64 < lf_sp1 cx + LS_N + 8) m1 m2)
      by (apply K0; w_inw E9 S1u)
  end; clear K0.

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
Hypothesis TB : PcapSyms B.
Hypothesis HSEGS : pa_segs = tfibsegs.
Hypothesis LV : LinkVals (PI := PI).

Local Notation FROM := (lf_from SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END).











Lemma w_sel : forall POST i, 0 <= i <= 47 ->
  FROM POST (sel_join SK B MT MS la_nul LF_MO_SET LF_MO_OP LF_wj 21%bv i) ->
  FROM POST (lf_arm_inv B MT MS la_nul LF_MO_SET LF_MO_OP 1 i).
Proof.
  intros POST i Hi HJN cx fy fp k2 ly3 S3 W3 ms3 md3 HB Hfx HJ Hfr GI.
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
  (* the join, from any state the selector's runs end in *)
  assert (CLOSE : forall (msX : machine_state) mdX s nm P' N',
    ajournal_gx SEGS B G_HARNESS 0 [] LLVMF_STK (spZ (c_regs cx)) (amf_harness_fp (c_T cx))
      (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(LF_CID, fp)] ly3 S3 W3 (ms_mem msX) mdX k2 ->
    lf_shape fy LF_wj msX ->
    (forall r : bv 5, In r [2%bv; 8%bv; 9%bv; 3%bv; 4%bv; 19%bv; 21%bv; 22%bv; 23%bv; 24%bv; 25%bv; 26%bv; 27%bv] ->
       r <> 21%bv -> getr (ms_regs msX) r = getr (ms_regs ms3) r) ->
    getr (ms_regs msX) 21%bv = w64 s -> w_name s nm ->
    kagree SEGS (fun a => lf_sp1 cx + LS_P <= a mod 2 ^ 64 < lf_sp1 cx + LS_N + 8)
      (rdW W3 (ms_mem ms3)) (rdW W3 (ms_mem msX)) ->
    mem_grows (rdW W3 (ms_mem ms3)) (rdW W3 (ms_mem msX)) ->
    m_fds mdX = m_fds md3 -> m_fs mdX = m_fs md3 ->
    lf_cur cx W3 msX P' N' ->
    SRr SEGS W3 (mkCfg msX mdX) (POST cx)).
  { intros msX mdX s nm P' N' HJX HSX KRX HsX HnmX KX GX FdX FsX HcX.
    apply (HJN cx fy fp k2 ly3 S3 W3 msX mdX HB Hfx HJX Hfr).
    exact (sel_close SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END LAWS LF_wj 21%bv i cx fy fp k2
      ly3 S3 W3 ms3 md3 msX mdX md mk P' N' s nm kbs mbs gbs T3 HB HJ0 Hfr Hi Hsv Hhd Hfs Hsl Hjbk Hblk Hdat Hop
      Hcore Hlr HJX HSX (or_intror (or_introl eq_refl)) KRX HsX HnmX KX GX FdX FsX HcX). }
  rewrite (lf_shape_eta fy (lf_op_pc 1) ms3 Hsh).
  destruct (Z.eq_dec (N - 1) 0) as [HN0 | HN0].
  - (* N - 1 = 0: +0x99c, a0 := 0, the g_names path with s5 := g_names *)
    set (E := Eimg (Ereg (ms_regs ms3) [w64 (P + 1); w64 (N - 1)])).
    assert (HEI : img_env pa_val A_LIM E) by apply Eimg_env.
    assert (E9 : ew E 9 = getr (ms_regs ms3) 9) by (apply ew_Eimg_Ereg_nat; reflexivity).
    assert (E32 : ew E 32 = Z_to_bv 64 (P + 1)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); reflexivity).
    assert (E33 : ew E 33 = Z_to_bv 64 (N - 1)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); reflexivity).
    assert (HS : st_ok_pi (fx := fy) pa_segs pa_val E w_ss0
      (restrict (w_H W3) (@mkst fy (ms_regs ms3) (Z_to_bv 64 (BASE + LF_op1)) (ms_mem ms3) (seg_rom SEGS)))).
    { rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
      - apply regs_ok_Eimg_Ereg.
      - reflexivity.
      - constructor; [|constructor].
        unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks w_cur_rg base_val]. rewrite E9, S1u.
        unfold LS_N, LS_P, LF_MFRAME in *.
        split; [lia|]. split; [lia|]. split.
        * intros o Ho. apply (apresent_writable SEGS). apply Hpres. unfold LLVMF_STK. lia.
        * constructor; [|constructor; [|constructor]].
          -- apply (hd_chunk cx W3 ms3 E LS_P (SOff 32 0) (P + 1) HcP).
             rewrite (lf_sv_off E 32 (P + 1) 0 E32) by lia. rewrite Z.add_0_r. reflexivity.
          -- apply (hd_chunk cx W3 ms3 E LS_N (SOff 33 0) (N - 1) HcN).
             rewrite (lf_sv_off E 33 (N - 1) 0 E33) by lia. rewrite Z.add_0_r. reflexivity.
      - apply pairwise_disjoint_of_extents. cbn -[E]. tauto.
      - split; [|split; exact I]. cbn [w_facts0 f_atoms atoms_ok].
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
    pose proof (@paj_run_to_x fy rc SK link_listing PL_link PI B LAWS G_HARNESS HGX 0 []) as RUNTO.
    pose proof (paj_branch (fx := fy) (PI := PI)) as BR.
    assert (SHOK : sh_ok pa_segs hd_Bx [] E
      (mrestrict (w_H W3) (ms_mem (@mkst fy (ms_regs ms3) (Z_to_bv 64 (BASE + LF_op1)) (ms_mem ms3) (seg_rom SEGS)))))
      by (unfold sh_ok; apply Forall_nil).
    paj_run_tok RUN HS HJ SHOK hd_span; [w_awr E9 S1u|].
    rename ms into msA, HF into HFA, HFr into HFrA, HG into HGA.
    psrr_branch_tok RUN BR HS SHOK hd_span.
    + paj_run_to_tok RUNTO HS HJ SHOK hd_span LF_wj; [w_awr E9 S1u|].
      rename ms into msB, HF into HFB, HFr into HFrB, HG into HGB.
      w_kag cx HFrA E9 S1u KA. w_kag cx HFrB E9 S1u KB.
      lazymatch type of HS with st_ok_pi _ _ ?EB ?ssB _ =>
          assert (HAE : env_agree 32 (Ereg (ms_regs ms3) []) EB)
            by (split; [intros n Hn; repeat rewrite ew_ewset_other by lia; subst E;
                        rewrite Eimg_low by (unfold A_TEXT; lia); rewrite !ew_Ereg_lt by lia; reflexivity
                       | reflexivity]);
          assert (S9B : bv_unsigned (ew EB 9) = lf_sp1 cx) by (repeat rewrite ew_ewset_other by lia; rewrite E9; exact S1u);
          lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdx |} _ => set (mdX := mdx) in * end;
          eapply (CLOSE msB mdX (LA_G_NAMES + 8 * 0) _ (P + 1) (N - 1));
          [ exact HJ | exact (lf_shape_of_st_ok fy W3 _ ssB msB HS eq_refl) | intros r Hr Hne; apply (lf_reg_atom fy W3 _ ssB msB _ r HS HAE);
            repeat (destruct Hr as [<- | Hr]; [first [vm_compute; reflexivity | exfalso; apply Hne; reflexivity]|]);
            destruct Hr
          | rewrite (st_ok_pi_restrict_reg (fx := fy) (w_H W3) _ _ msB 21%bv HS);
            replace (sr_get (ss_regs ssB) 21%bv) with (SOff 246 0) by (vm_compute; reflexivity);
            rewrite (lf_sv_off E 246 LA_G_NAMES 0 (w_atom246 LV E HEI)) by (unfold LA_G_NAMES; lia);
            unfold w64; f_equal; lia
          | right; left; exists 0; split; [lia|]; split; [reflexivity | reflexivity]
          | exact (hd_kt _ _ _ _ _ KA KB)
          | intros x Hx; apply HGB, HGA, Hx
          | subst mdX; rewrite !lf_wvb_fds; reflexivity
          | subst mdX; rewrite !lf_wvb_fs; reflexivity
          | split; [|split; [|exists (q + 1); lia]];
            [ apply (hd_slot_of fy W3 EB ssB _ cx 0%nat _ LS_P (SOff 32 0) (P + 1) HS eq_refl eq_refl S9B);
              [ cbn [r_chunks In]; repeat (first [left; reflexivity | right])
              | rewrite (lf_sv_off EB 32 (P + 1) 0 ltac:(repeat rewrite ew_ewset_other by lia; exact E32) ltac:(lia) ltac:(lia));
                rewrite Z.add_0_r; reflexivity
              | lia ]
            | apply (hd_slot_of fy W3 EB ssB _ cx 0%nat _ LS_N (SOff 33 0) (N - 1) HS eq_refl eq_refl S9B);
              [ cbn [r_chunks In]; repeat (first [left; reflexivity | right])
              | rewrite (lf_sv_off EB 33 (N - 1) 0 ltac:(repeat rewrite ew_ewset_other by lia; exact E33) ltac:(lia) ltac:(lia));
                rewrite Z.add_0_r; reflexivity
              | lia ] ] ]
      end.
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
    assert (HS : st_ok_pi (fx := fy) pa_segs pa_val E w_ss1
      (restrict (w_H W3) (@mkst fy (ms_regs ms3) (Z_to_bv 64 (BASE + LF_op1)) (ms_mem ms3) (seg_rom SEGS)))).
    { rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
      - apply regs_ok_Eimg_Ereg.
      - reflexivity.
      - constructor; [|constructor; [|constructor; [|constructor]]].
        + unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks w_odd_rg base_val]. rewrite E9, S1u.
          unfold LS_ODD, LF_MFRAME in *.
          split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
          constructor; [|constructor].
          apply (hd_chunk cx W3 ms3 E 0x50 (SOff 35 0) LA_ODD SODD).
          rewrite (lf_sv_off E 35 LA_ODD 0 E35) by (unfold LA_ODD; lia). rewrite Z.add_0_r. reflexivity.
        + unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks w_cur_rg base_val]. rewrite E9, S1u.
          unfold LS_N, LS_P, LF_MFRAME in *.
          split; [lia|]. split; [lia|]. split.
          * intros o Ho. apply (apresent_writable SEGS). apply Hpres. unfold LLVMF_STK. lia.
          * constructor; [|constructor; [|constructor]].
            -- apply (hd_chunk cx W3 ms3 E LS_P (SOff 32 0) (P + 1) HcP).
               rewrite (lf_sv_off E 32 (P + 1) 0 E32) by lia. rewrite Z.add_0_r. reflexivity.
            -- apply (hd_chunk cx W3 ms3 E LS_N (SOff 33 0) (N - 1) HcN).
               rewrite (lf_sv_off E 33 (N - 1) 0 E33) by lia. rewrite Z.add_0_r. reflexivity.
        + unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks w_byte_rg base_val].
          rewrite E32, unsigned_lit_small by lia.
          split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
          constructor; [|constructor].
          apply (chunk_ok_val SEGS E _ (P + 1) 0 1 (SOff 34 0) (bv_unsigned bb)); [| cbn; lia | cbn; lia |].
          * rewrite (lf_sv_off E 34 (bv_unsigned bb) 0 E34) by lia. rewrite Z.add_0_r. reflexivity.
          * rewrite Z.add_0_r. exact (hd_val_mem1 _ _ _ _ Hb).
      - apply pairwise_disjoint_of_extents. cbn -[E].
        repeat match goal with |- _ /\ _ => split end; try exact I;
        unfold zdisj, extent_of_region; cbn [r_base r_lo r_hi w_odd_rg w_cur_rg w_byte_rg base_val fst snd];
        rewrite ?E9, ?S1u, ?E32; rewrite ?unsigned_lit_small by lia;
        unfold LS_ODD, LS_P, LS_N, LF_MFRAME in *; lia.
      - split; [|split; exact I]. cbn [w_facts1 f_atoms atoms_ok].
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
    assert (SHOK : sh_ok pa_segs hd_Bx w_SH E
      (mrestrict (w_H W3) (ms_mem (@mkst fy (ms_regs ms3) (Z_to_bv 64 (BASE + LF_op1)) (ms_mem ms3) (seg_rom SEGS))))).
    { unfold sh_ok, w_SH. constructor; [|constructor; [|constructor]]; unfold shent_ok, app_apart, hd_Bx;
        cbn [she_m she_lo she_hi ms_mem mkst].
      - rewrite (U_atom E 32 (P + 1) E32) by lia. rewrite (U_atom E 27 SHADOW_OFF E27) by (unfold SHADOW_OFF; lia).
        split; [rewrite Z.add_0_r, Z.sub_0_r; exact RA|].
        intros a Ha. unfold in_app, kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *. lia.
      - rewrite (U_atom E 35 LA_ODD E35) by (unfold LA_ODD; lia).
        rewrite (U_atom E 27 SHADOW_OFF E27) by (unfold SHADOW_OFF; lia).
        split; [rewrite Z.add_0_r, Z.sub_0_r; exact RO|].
        intros a Ha. unfold in_app, kLowShadowBeg, kHighMemBeg, SHADOW_OFF, LA_ODD in *. lia. }
    paj_run_tok RUN HS HJ SHOK hd_span; [w_awr E9 S1u|].
    rename ms into msA, HF into HFA, HFr into HFrA, HG into HGA.
    psrr_branch_tok RUN BR HS SHOK hd_span.
    + (* +0x918 taken: b <> 0xff *)
      paj_run_tok RUN HS HJ SHOK hd_span; [w_awr E9 S1u|].
      rename ms into msB, HF into HFB, HFr into HFrB, HG into HGB.
      rename Hc into Hc1.
      psrr_branch_tok RUN BR HS SHOK hd_span.
      * (* +0xa78 taken: 0x3f < b, odd[b mod 6] *)
        paj_run_tok RUN HS HJ SHOK hd_span; [w_awr E9 S1u|].
        rename ms into msC, HF into HFC, HFr into HFrC, HG into HGC.
        w_kag cx HFrA E9 S1u KA. w_kag cx HFrB E9 S1u KB. w_kag cx HFrC E9 S1u KC.
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
        paj_run_to_tok RUNTO HS1 HJ SHOK hd_span (AF_LLVMFuzzerTestOneInput + 0xfe8); [w_awr E9 S1u|].
        rename ms into msD, HF into HFD, HFr into HFrD, HG into HGD.
        w_kag cx HFrD E9 S1u KD.
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
        all: paj_run_to_tok RUNTO HS3 HJ SHOK hd_span LF_wj; [w_awr E9 S1u|].
        all: rename ms into msE, HF into HFE, HFr into HFrE, HG into HGE.
        all: rename HS3 into HS.
        all: w_kag cx HFrE E9 S1u KE.
        all: lazymatch type of HS with st_ok_pi _ _ ?EB ?ssB _ =>
          assert (HAE : env_agree 32 (Ereg (ms_regs ms3) []) EB)
            by (split; [intros n Hn; repeat rewrite ew_ewset_other by lia; subst E;
                        rewrite Eimg_low by (unfold A_TEXT; lia); rewrite !ew_Ereg_lt by lia; reflexivity
                       | reflexivity]);
          assert (S9B : bv_unsigned (ew EB 9) = lf_sp1 cx) by (repeat rewrite ew_ewset_other by lia; rewrite E9; exact S1u);
          lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdx |} _ => set (mdX := mdx) in * end;
          let v := eval vm_compute in (sr_get (ss_regs ssB) 21%bv) in
          (lazymatch v with SLit ?z => eapply (CLOSE msE mdX z _ (P + 2) (N - 2)) | _ => eapply (CLOSE msE mdX _ _ (P + 2) (N - 2)) end);
          [ exact HJ | exact (lf_shape_of_st_ok fy W3 _ ssB msE HS eq_refl) | intros r Hr Hne; apply (lf_reg_atom fy W3 _ ssB msE _ r HS HAE);
            repeat (destruct Hr as [<- | Hr]; [first [vm_compute; reflexivity | exfalso; apply Hne; reflexivity]|]);
            destruct Hr
          | rewrite (st_ok_pi_restrict_reg (fx := fy) (w_H W3) _ _ msE 21%bv HS); vm_compute; reflexivity
          | right; right; first [(exists 0%nat; split; [lia|]; split; [rewrite w_odd_ptrs; reflexivity | reflexivity]) | (exists 1%nat; split; [lia|]; split; [rewrite w_odd_ptrs; reflexivity | reflexivity]) | (exists 2%nat; split; [lia|]; split; [rewrite w_odd_ptrs; reflexivity | reflexivity]) | (exists 3%nat; split; [lia|]; split; [rewrite w_odd_ptrs; reflexivity | reflexivity]) | (exists 4%nat; split; [lia|]; split; [rewrite w_odd_ptrs; reflexivity | reflexivity]) | (exists 5%nat; split; [lia|]; split; [rewrite w_odd_ptrs; reflexivity | reflexivity])]
          | exact (hd_kt _ _ _ _ _ KAD KE)
          | intros x Hx; apply HGE, HGD, HGC, HGB, HGA, Hx
          | subst mdX; rewrite !lf_wvb_fds; reflexivity
          | subst mdX; rewrite !lf_wvb_fs; reflexivity
          | split; [|split; [|exists (q + 2); lia]];
            [ apply (hd_slot_of fy W3 EB ssB _ cx 3%nat _ LS_P (SOff 32 1) (P + 2) HS eq_refl eq_refl S9B);
              [ cbn [r_chunks In]; repeat (first [left; reflexivity | right])
              | replace (P + 2) with ((P + 1) + 1) by lia;
                exact (lf_sv_off EB 32 (P + 1) 1 ltac:(repeat rewrite ew_ewset_other by lia; exact E32) ltac:(lia) ltac:(lia))
              | lia ]
            | apply (hd_slot_of fy W3 EB ssB _ cx 3%nat _ LS_N (SOff 33 (-1)) (N - 2) HS eq_refl eq_refl S9B);
              [ cbn [r_chunks In]; repeat (first [left; reflexivity | right])
              | replace (N - 2) with ((N - 1) + -1) by lia;
                exact (lf_sv_off EB 33 (N - 1) (-1) ltac:(repeat rewrite ew_ewset_other by lia; exact E33) ltac:(lia) ltac:(lia))
              | lia ] ] ]
        end.
      * (* +0xa78 not taken: b <= 0x3f, g_names + 8 b *)
        paj_run_to_tok RUNTO HS HJ SHOK hd_span LF_wj; [w_awr E9 S1u|].
        rename ms into msC, HF into HFC, HFr into HFrC, HG into HGC.
        w_kag cx HFrA E9 S1u KA. w_kag cx HFrB E9 S1u KB. w_kag cx HFrC E9 S1u KC.
        assert (Hb63 : bv_unsigned bb <= 63).
        { lazymatch type of Hc with context [sv_denot ?EH (SOff 34 0)] =>
            rewrite (lf_sv_off EH 34 (bv_unsigned bb) 0 ltac:(repeat rewrite ew_ewset_other by lia; exact E34)
              ltac:(lia) ltac:(lia)) in Hc end.
          cbn [sv_denot] in Hc. rewrite YK0f.branch_ltu_lit_l, !unsigned_lit_small in Hc by lia.
          apply Z.ltb_ge in Hc. lia. }
        lazymatch type of HS with st_ok_pi _ _ ?EB ?ssB _ =>
          assert (HAE : env_agree 32 (Ereg (ms_regs ms3) []) EB)
            by (split; [intros n Hn; repeat rewrite ew_ewset_other by lia; subst E;
                        rewrite Eimg_low by (unfold A_TEXT; lia); rewrite !ew_Ereg_lt by lia; reflexivity
                       | reflexivity]);
          assert (S9B : bv_unsigned (ew EB 9) = lf_sp1 cx) by (repeat rewrite ew_ewset_other by lia; rewrite E9; exact S1u);
          lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdx |} _ => set (mdX := mdx) in * end;
          let v := eval vm_compute in (sr_get (ss_regs ssB) 21%bv) in
          (lazymatch v with SLit ?z => eapply (CLOSE msC mdX z _ (P + 2) (N - 2)) | _ => eapply (CLOSE msC mdX _ _ (P + 2) (N - 2)) end);
          [ exact HJ | exact (lf_shape_of_st_ok fy W3 _ ssB msC HS eq_refl) | intros r Hr Hne; apply (lf_reg_atom fy W3 _ ssB msC _ r HS HAE);
            repeat (destruct Hr as [<- | Hr]; [first [vm_compute; reflexivity | exfalso; apply Hne; reflexivity]|]);
            destruct Hr
          | rewrite (st_ok_pi_restrict_reg (fx := fy) (w_H W3) _ _ msC 21%bv HS); replace (sr_get (ss_regs ssB) 21%bv) with w_gn by (vm_compute; reflexivity); rewrite (w_gn_val EB (bv_unsigned bb) ltac:(repeat rewrite ew_ewset_other by lia; exact E34) (w_atom246 LV EB ltac:(assumption)) Rb); reflexivity
          | right; left; exists (bv_unsigned bb); split; [lia|]; split; [reflexivity | reflexivity]
          | exact (hd_kt _ _ _ _ _ (hd_kt _ _ _ _ _ KA KB) KC)
          | intros x Hx; apply HGC, HGB, HGA, Hx
          | subst mdX; rewrite !lf_wvb_fds; reflexivity
          | subst mdX; rewrite !lf_wvb_fs; reflexivity
          | split; [|split; [|exists (q + 2); lia]];
            [ apply (hd_slot_of fy W3 EB ssB _ cx 1%nat _ LS_P (SOff 32 1) (P + 2) HS eq_refl eq_refl S9B);
              [ cbn [r_chunks In]; repeat (first [left; reflexivity | right])
              | replace (P + 2) with ((P + 1) + 1) by lia;
                exact (lf_sv_off EB 32 (P + 1) 1 ltac:(repeat rewrite ew_ewset_other by lia; exact E32) ltac:(lia) ltac:(lia))
              | lia ]
            | apply (hd_slot_of fy W3 EB ssB _ cx 1%nat _ LS_N (SOff 33 (-1)) (N - 2) HS eq_refl eq_refl S9B);
              [ cbn [r_chunks In]; repeat (first [left; reflexivity | right])
              | replace (N - 2) with ((N - 1) + -1) by lia;
                exact (lf_sv_off EB 33 (N - 1) (-1) ltac:(repeat rewrite ew_ewset_other by lia; exact E33) ltac:(lia) ltac:(lia))
              | lia ] ] ]
        end.
    + (* +0x918 not taken: b = 0xff, s5 := 0 *)
      paj_run_to_tok RUNTO HS HJ SHOK hd_span LF_wj; [w_awr E9 S1u|].
      rename ms into msB, HF into HFB, HFr into HFrB, HG into HGB.
      w_kag cx HFrA E9 S1u KA. w_kag cx HFrB E9 S1u KB.
      lazymatch type of HS with st_ok_pi _ _ ?EB ?ssB _ =>
          assert (HAE : env_agree 32 (Ereg (ms_regs ms3) []) EB)
            by (split; [intros n Hn; repeat rewrite ew_ewset_other by lia; subst E;
                        rewrite Eimg_low by (unfold A_TEXT; lia); rewrite !ew_Ereg_lt by lia; reflexivity
                       | reflexivity]);
          assert (S9B : bv_unsigned (ew EB 9) = lf_sp1 cx) by (repeat rewrite ew_ewset_other by lia; rewrite E9; exact S1u);
          lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdx |} _ => set (mdX := mdx) in * end;
          let v := eval vm_compute in (sr_get (ss_regs ssB) 21%bv) in
          (lazymatch v with SLit ?z => eapply (CLOSE msB mdX z _ (P + 2) (N - 2)) | _ => eapply (CLOSE msB mdX _ _ (P + 2) (N - 2)) end);
          [ exact HJ | exact (lf_shape_of_st_ok fy W3 _ ssB msB HS eq_refl) | intros r Hr Hne; apply (lf_reg_atom fy W3 _ ssB msB _ r HS HAE);
            repeat (destruct Hr as [<- | Hr]; [first [vm_compute; reflexivity | exfalso; apply Hne; reflexivity]|]);
            destruct Hr
          | rewrite (st_ok_pi_restrict_reg (fx := fy) (w_H W3) _ _ msB 21%bv HS); vm_compute; reflexivity
          | left; split; reflexivity
          | exact (hd_kt _ _ _ _ _ KA KB)
          | intros x Hx; apply HGB, HGA, Hx
          | subst mdX; rewrite !lf_wvb_fds; reflexivity
          | subst mdX; rewrite !lf_wvb_fs; reflexivity
          | split; [|split; [|exists (q + 2); lia]];
            [ apply (hd_slot_of fy W3 EB ssB _ cx 1%nat _ LS_P (SOff 32 1) (P + 2) HS eq_refl eq_refl S9B);
              [ cbn [r_chunks In]; repeat (first [left; reflexivity | right])
              | replace (P + 2) with ((P + 1) + 1) by lia;
                exact (lf_sv_off EB 32 (P + 1) 1 ltac:(repeat rewrite ew_ewset_other by lia; exact E32) ltac:(lia) ltac:(lia))
              | lia ]
            | apply (hd_slot_of fy W3 EB ssB _ cx 1%nat _ LS_N (SOff 33 (-1)) (N - 2) HS eq_refl eq_refl S9B);
              [ cbn [r_chunks In]; repeat (first [left; reflexivity | right])
              | replace (N - 2) with ((N - 1) + -1) by lia;
                exact (lf_sv_off EB 33 (N - 1) (-1) ltac:(repeat rewrite ew_ewset_other by lia; exact E33) ltac:(lia) ltac:(lia))
              | lia ] ] ]
        end.
Qed.

End a.
