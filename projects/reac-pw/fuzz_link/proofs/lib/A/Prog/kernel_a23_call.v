(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YCbq.v, with its module paths changed. *)
(* Modified by Theorem Labs, 2026-10: off_img's image bounds cite this unit's own image (YImgTop.IMG_LO and YImgTop.IMG_TOP, which YImgTop.v of reac-pw/fuzz_rate gives as 0x10000 and 0x5fa000, both of this unit's ASan builds) in place of cgif's 0x10000 and 0x5fb000. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/libreac/fuzz_knock/lib/Reusable/YCbq.v at origin/ossv/recipes 6ebe35ba632 (fuzz_knock's released ASan tree); module paths changed to reac-pw/fuzz_rate. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_rate/lib/Reusable/YCbq.v, with its module paths and module names changed; 442 of its 486 lines of code are new or changed and 3116 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/kernel_k3.v; 113 of its 155 lines of code are new or changed and 444 lines of the source are left out. *)
(* reac-pw/fuzz_link, image A: the walk of kernel's attribute cases a % 6 in {2, 3}: the attr_text call, J6 (+0xdb8)
   -> J7 (+0xdcc). Listing (internal path) (internal record, sha256 7bc02d6772b3), +0xdb8 ..
   +0xdc8: a3 := s7 & 0x80; a1 := 1; a0 := s5 (w2); a2 := s11 (p); `jal attr_text`.
   ONE run (no memory access; the state is the registers alone) to the call; the cut at attr_text's entry is J6's
   (kernel_kit.v kat_frame_w2 with nothing written; the registers of the cut kept); then kernel_atcall.v kn_atcall,
   the string by kernel_atcall.v katstr_img over kac_tx_in (p is the texts word `ka_text cx a p` of the lane's cut).
   Section hypotheses used: LAWS, LV, KI, TB, ATEXT (kernel_atcall.v).
   Released proofs (rule 24): none of kernel's walk (lookups/walk-lookups.md (internal record, sha256 98fff7967d93): disposition none, written new; confirmed by
   the rule-24 walk check at 14:56Z).
   Proves no function (kind: segment lemma of kernel's walk). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YN3v YI04 YI16 YG0s YA0d YA0j.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC5d YC20.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkSyms LinkList LinkAddr LinkPa LinkPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import YC4b.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import
link_aaddr link_amem link_ajkit LinkWalk LinkWalkNlw LinkWalkPi LinkWalkSide.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import
PcapRelro kernel_c kernel_img kernel_defs kernel_kit kernel_next kernel_k3 kernel_a5 kernel_a23_defs attr_text_c
kernel_atcall.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Definition a23C_ss : sstate := mkSS (kpc A23_J6) sr_atoms [] None (mkFacts [] [] []).

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Section b.
Context {PI : PAImg link_listing}.
#[local] Abbreviation SEGS := (pa_segs).
#[local] Abbreviation BASE := (pa_val A_TEXT).
Variable B : asyms.
Hypothesis LAWS : AR_laws pa_segs B.
Hypothesis LV : LinkVals.
Hypothesis KI : KernImg pa_segs B.
Hypothesis TB : AF0m.PcapSyms B.     (* AF0m.v; discharged at the frame's B by AD2l.PcapB_syms *)
Hypothesis ATEXT : attr_text_acontract SK pa_segs PCAP_RLO PCAP_RHI B.

Theorem a23_call : forall POST (Rc Rm Ra : kcx -> Z -> Prop),
  kfrom SK B POST (a23_at B Rc Rm Ra A23_J7) -> kfrom SK B POST (a23_at B Rc Rm Ra A23_J6).
Proof.
  intros POST Rc Rm Ra HN cx fpos k2 ly3 S3 W3 ms3 md3 HB HJ HFR HI.
  destruct HI as (qc & qci & qj & qm & qk & qn & qf & qadv & qhd & qkd & ql & qa & qp & qn0 & HRc & HRm & HRa & Hc
    & Hci & Hj & Hm & Hk & Hkd & Hl & Hhd & Ha & Htx & Hka & Hn0 & HW & HAT).
  pose proof HAT as (HMS & HR0 & HRL & _).
  destruct HMS as (Hpc & Hrv & Hsvc & Hrom & Hfrg & Hfcs).
  pose proof HB as ((_ & HGok & _) & _).
  remember (Eimg (Ereg (ms_regs ms3) [])) as E eqn:HEdef.
  assert (HEI : img_env pa_val A_LIM E) by (rewrite HEdef; apply Eimg_env).
  (* the state at J6: the registers alone *)
  assert (HS : st_ok_pi SEGS pa_val E a23C_ss (restrict (w_H W3) ms3)).
  { rewrite (kn_ms_shape ms3 (BASE + kpc A23_J6) Hpc Hrv Hsvc Hrom Hfrg Hfcs), restrict_mkst_fx. unfold a23C_ss.
    apply pa_entry_st_ok_full.
    - rewrite HEdef. apply regs_ok_Eimg_Ereg.
    - vm_compute. reflexivity.
    - apply Forall_nil.
    - cbn [pairwise_disjoint]. exact I.
    - unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok]. exact (conj I (conj I I)). }
  pose proof HS as HS0.
  assert (SHOK : sh_ok SEGS k3_Bx (@nil shent) E (mrestrict (w_H W3) (ms_mem ms3))) by apply Forall_nil.
  pose (RUN := paj_run_x SK B LAWS (k_G cx) HGok (k_XO cx) (k_OUT cx)).
  paj_run_tok RUN HS HJ SHOK k3_span; [apply awr_ok_x_nil|].
  lazymatch goal with HSx : st_ok _ _ _ (restrict _ ?m) |- _ => rename m into ms1; rename HSx into HS1 end.
  lazymatch goal with HFx : frame_of _ _ _ _ |- _ => rename HFx into HFr1 end.
  lazymatch goal with HGx : mem_grows _ _ |- _ => rename HGx into HG1 end.
  pose proof (a5_reg_same E _ _ (w_H W3) ms3 ms1 [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27] HS0 HS1
                ltac:(vm_compute; reflexivity)) as KEEP.
  sreg HS1 (10%bv : bv 5) R10. sreg HS1 (12%bv : bv 5) R12.
  prreg HS1 (1%bv : bv 5) R1.
  cbn [ms_regs restrict mkst] in R10, R12.
  pmkst HS1.
  rewrite (lv_sigma LV). change (LinkAddr.link_sigma LS_attr_text) with 0x86b18.
  set (msE := mkst (ms_regs ms1) (Z_to_bv 64 0x86b18) (ms_mem ms1) (seg_rom SEGS)).
  lazymatch goal with |- SRr _ _ (mkCfg _ ?mdx) _ => set (mdE := mdx) end.
  (* memory unchanged by the run *)
  assert (UN : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W3) (ms_mem msE) a = aview SEGS (w_H W3) (ms_mem ms3) a).
  { intros y Hy. cbn [ms_mem msE mkst].
    apply (kept_of_frame (segs := SEGS) E _ (w_H W3) (ms_mem ms3) (ms_mem ms1) (fun _ => False) HFr1);
      [ intros bb wlo whi x Hin; unfold a23C_ss, windows in Hin; cbn [ss_mem map In] in Hin; destruct Hin
      | exact Hy | intros [] ]. }
  assert (HP : forall a, apresent (w_H W3) (ms_mem ms3) a -> apresent (w_H W3) (ms_mem msE) a)
    by (intros y Hy; exact (k3_apres_grows _ _ _ y HG1 Hy)).
  (* the registers of the cut *)
  assert (HKr : forall r : nat, In r [19; 21; 24; 25; 22; 23; 27; 26]%nat ->
            getr (ms_regs msE) (Z_to_bv 5 (Z.of_nat r)) = getr (ms_regs ms3) (Z_to_bv 5 (Z.of_nat r))).
  { intros r Hr. cbn [ms_regs msE mkst]. apply KEEP. cbn [In] in Hr.
    repeat (destruct Hr as [<- | Hr]; [vm_compute; reflexivity|]). destruct Hr. }
  assert (HR0E : kregs0 cx msE).
  { apply (kregs0_keep cx ms3 msE); [|exact HR0].
    intros r Hr. cbn [ms_regs msE mkst]. apply KEEP. cbn [nx_keep0 In] in Hr.
    repeat (destruct Hr as [<- | Hr]; [vm_compute; reflexivity|]). destruct Hr. }
  assert (HRLE : kregs_eq msE (a23_rl cx fpos qa qp qn0 ql)).
  { unfold kregs_eq, a23_rl. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd];
      (rewrite HKr by kn_in; apply (kn_reg_of ms3 _ _ _ HRL); unfold a23_rl; kn_in). }
  assert (HMSE : kms KP_ATEXT msE).
  { unfold kms, msE. cbn [ms_pc_val ms_resv ms_svc_pending ms_rom ms_fregs ms_fcsr mkst].
    unfold w64. rewrite (lv_text LV). repeat split; reflexivity. }
  assert (HATE : kat B cx fpos KP_ATEXT (a23_rl cx fpos qa qp qn0 ql) (a23_sl cx fpos qc qci qm qk qhd qkd)
                   (kfsh 0xf8 0 0xf3) true qadv (Some qj) k2 ly3 S3 W3 msE mdE).
  { apply (kat_frame_w2 SK B LAWS 0 0 cx fpos A23_J6 _ _ _ true qadv (Some qj) k2 ly3 S3 W3 ms3 md3 KP_ATEXT _ _
             W3 msE mdE HB HAT HMSE HR0E HRLE (fun x Hx => Hx) ltac:(reflexivity) (kfsh_fits _ _ _)
             (proj1 (wvb_fds_fs _ _ _)) (proj2 (wvb_fds_fs _ _ _)) ltac:(lia) ltac:(unfold NW_SIZE; lia)).
    - intros q Hq _. exact (UN q Hq).
    - exact HP. }
  assert (HWE : kw_at W3 msE (kW2 cx fpos) qn qf).
  { apply (kn_kw_keep W3 ms3 msE (kW2 cx fpos) qn qf HW); [|exact HP].
    intros i Hi. apply UN.
    pose proof (kn_F SK B LAWS cx fpos k2 ly3 S3 md3 HB (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2
      (proj2 HAT))))))))) as (HF4 & HFc & _).
    pose proof asan_consts as ((C1a & C1b) & _).
    unfold kW2, KN_W2, NW_SIZE in *. lia. }
  assert (E21 : ew E 21%nat = w64 (kW2 cx fpos)).
  { rewrite HEdef, (ew_Eimg_Ereg_nat _ _ 21 (Z_to_bv 5 (Z.of_nat 21)) eq_refl).
    apply (kn_reg_of ms3 _ 21 _ HRL). unfold a23_rl. kn_in. }
  assert (E27 : ew E 27%nat = w64 qp).
  { rewrite HEdef, (ew_Eimg_Ereg_nat _ _ 27 (Z_to_bv 5 (Z.of_nat 27)) eq_refl).
    apply (kn_reg_of ms3 _ 27 _ HRL). unfold a23_rl. kn_in. }
  (* the string: a texts word, so one of kernel_img.v's strings (kernel_atcall.v kac_tx_in) *)
  assert (Hti : 0 <= (qa / 8) mod 11 < TEXTS_N) by (unfold TEXTS_N; apply Z.mod_pos_bound; lia).
  destruct (kac_tx_in SK B KI cx qa qp HB Ha Hka Htx) as (bs & Hbs).
  pose proof HATE as (_ & _ & _ & _ & _ & _ & _ & HJBE & HKKE & _).
  pose proof (katstr_img SK B LAWS KI TB cx fpos k2 ly3 S3 W3 msE mdE qp bs HB ltac:(assumption) HJBE HKKE Hbs Htx
    (fun s0 Hs0 x Hx => or_intror (or_intror (or_intror (or_intror (or_intror (or_intror (or_introl
       (ex_intro _ ((qa / 8) mod 11) (ex_intro _ qp (ex_intro _ s0 (conj Hti (conj Hka (conj Hs0 Hx))))))))))))))
    as HST.
  apply (kn_atcall SK B LAWS LV KI ATEXT POST cx fpos k2 ly3 S3 W3 msE mdE A23_J7 (a23_rl cx fpos qa qp qn0 ql)
           (a23_rl cx fpos qa qp qn0 ql) (a23_sl cx fpos qc qci qm qk qhd qkd) 0xf8 0xf3 qadv (Some qj) qn qf qp
           (map zb (removelast bs)) HB).
  - assumption.
  - exact HFR.
  - exact HATE.
  - exact HWE.
  - cbn [ms_regs msE mkst]. rewrite R1. reflexivity.
  - unfold kpc, AF_kernel, A23_J7. lia.
  - reflexivity.
  - cbn [ms_regs msE mkst]. rewrite R10. cbn [sv_denot]. rewrite E21, Z.add_0_r. unfold w64.
    apply Z_to_bv_bv_unsigned.
  - cbn [ms_regs msE mkst]. rewrite R12. cbn [sv_denot]. rewrite E27, Z.add_0_r. unfold w64.
    apply Z_to_bv_bv_unsigned.
  - exact HST.
  - apply incl_refl.
  - unfold a23_rl. repeat apply Forall_cons; try apply Forall_nil; cbn [fst]; unfold acallee_saved; cbn; lia.
  - reflexivity.
  - intros ly4 S4 W4 ms4 md4 n' f' HJ4 HF4 HAT4 HW4 Hle.
    apply (HN cx fpos k2 ly4 S4 W4 ms4 md4 HB HJ4 HF4).
    exists qc, qci, qj, qm, qk, n', f', qadv, qhd, qkd, ql, qa, qp, qn0.
    split; [exact HRc|]. split; [exact HRm|]. split; [exact HRa|]. split; [exact Hc|]. split; [exact Hci|].
    split; [exact Hj|]. split; [exact Hm|]. split; [exact Hk|]. split; [exact Hkd|]. split; [exact Hl|].
    split; [lia|]. split; [exact Ha|]. split; [exact Htx|]. split; [exact Hka|]. split; [lia|].
    split; [exact HW4 | exact HAT4].
Qed.

End b.
End a.
