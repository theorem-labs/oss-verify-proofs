(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YCbq.v, with its module paths changed. *)
(* Modified by Theorem Labs, 2026-10: off_img's image bounds cite this unit's own image (YImgTop.IMG_LO and YImgTop.IMG_TOP, which YImgTop.v of reac-pw/fuzz_rate gives as 0x10000 and 0x5fa000, both of this unit's ASan builds) in place of cgif's 0x10000 and 0x5fb000. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/libreac/fuzz_knock/lib/Reusable/YCbq.v at origin/ossv/recipes 6ebe35ba632 (fuzz_knock's released ASan tree); module paths changed to reac-pw/fuzz_rate. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_rate/lib/Reusable/YCbq.v, with its module paths and module names changed; 442 of its 486 lines of code are new or changed and 3116 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/kernel_k3.v, with its module names and numbers changed; 103 of its 148 lines of code are new or changed and 441 lines of the source are left out. *)
(* reac-pw/fuzz_link, image A: the walk of kernel (fuzz_link.asan 0x83d30), the message of kind 1
   (lib/A/Prog/kernel_defs.v kin_kind at kd = 1, +0x6d0) to the cut after a message (kin_next, +0x1b84). Listing
   (internal path) (internal record, sha256 7bc02d6772b3), +0x6d0 .. +0x6dc and +0x1b7c.

   THE CODE. Four instructions: a2 := -1, a0 := s5 = w2, a1 := 0, then `j +0x1b7c` and the `jal` of nl_error. The
   phase reads and writes no memory, so one run of the engine from the kind's entry reaches the call with the whole
   cut untouched. The engine stops at the call (PTS_call LS_nl_error) with the pc at nl_error's entry and ra at
   +0x1b80; that is the cut `kin_ncall` of kernel_k12_call.v, whose cut word a2 = 2 ^ 64 - 1 meets nl_error's
   premise by its second arm (2 ^ 63 <= a2). kernel_k12_call.v `kn_ncall` then does the call and the step to
   kin_next.

   THE STATE. The symbolic state at +0x6d0 has the registers `sr_atoms`, no region and no shadow entry; its only
   fact is s4 = SHADOW_OFF (the engine's shadow base, which every walk of this image carries). The run writes
   nothing, so the cut moves to the call by kernel_next.v `kat_move` with the memory equal.

   Callees: nl_error, through kernel_k12_call.v (ANLERR). Section hypotheses used: LAWS, LV, KI, ANLERR.
   Released proofs (rule 24): none of kernel's walk (lookups/walk-lookups.md (internal record, sha256 98fff7967d93): disposition none, written new; confirmed by
   the rule-24 walk check at 14:56Z).
   Proves no function (kind: segment lemma of kernel's walk). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From Stdlib Require Import FunctionalExtensionality.
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
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC5d YC20 YK1d.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkSyms LinkList LinkAddr LinkPa LinkPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import YC4b.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import
link_aaddr link_amem link_ajkit LinkWalk LinkWalkNlw LinkWalkPi LinkWalkSide.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import nl_error_c kernel_c kernel_img kernel_defs.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import
LinkWalkCall PcapRelro kernel_kit kernel_entry kernel_next kernel_ocall kernel_k12_call.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- the symbolic state at +0x6d0: no region, no shadow entry, s4 = SHADOW_OFF ---- *)
Definition k1_Bx : sv := SOff 20 0.
Definition k1_span : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
Definition k1_facts : facts := mkFacts [(20%nat, mkAF SHADOW_OFF SHADOW_OFF 0)] [] [].
Definition k1_ss : sstate := mkSS (kpc KP_K1) sr_atoms [] None k1_facts.

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
Hypothesis ANLERR : nl_error_acontract SK pa_segs PCAP_RLO PCAP_RHI B.

Theorem kn_k1 : forall POST (Rc Rm : kcx -> Z -> Prop),
  kfrom SK B POST (kin_next B Rc Rm) -> kfrom SK B POST (kin_kind B Rc Rm 1).
Proof.
  intros POST Rc Rm HN.
  pose proof (kn_ncall SK B LAWS LV KI ANLERR POST Rc Rm HN) as HC.
  intros cx fpos k2 ly3 S3 W3 ms3 md3 HB HJ HFR HI.
  destruct HI as (c & ci & j & m & k & n & f & adv & HRc & HRm & Hc & Hci & Hj & Hm & Hk & _ & HW & _ & HAT).
  change (kind_pc 1) with KP_K1 in HAT.
  pose proof HAT as (HMS & HR0 & HRL & _ & _ & _ & _ & HJB & _).
  destruct HMS as (Hpc & Hrv & Hsvc & Hrom & Hfrg & Hfcs).
  pose proof HB as ((_ & HGok & _) & _).
  pose proof HR0 as (R2 & R9 & R8 & R3 & R4 & R18 & R20).
  remember (Eimg (Ereg (ms_regs ms3) (@nil word))) as E eqn:HEdef.
  assert (HEI : img_env pa_val A_LIM E) by (rewrite HEdef; apply Eimg_env).
  assert (HAG : env_agree 32 (Ereg (ms_regs ms3) (@nil word)) E)
    by (rewrite HEdef; split; [intros q Hq; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  assert (ER : forall (jn : nat) (r : bv 5), Z.of_nat jn = bv_unsigned r -> ew E jn = getr (ms_regs ms3) r)
    by (intros jn r Hjr; rewrite HEdef; exact (ew_Eimg_Ereg_nat _ _ jn r Hjr)).
  assert (B20 : bv_unsigned (ew E 20%nat) = SHADOW_OFF)
    by (rewrite (ER 20%nat 20%bv eq_refl), R20; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
  assert (R21 : getr (ms_regs ms3) 21%bv = w64 (kW2 cx fpos))
    by exact (k12_getr ms3 _ 21%nat 21%bv (kW2 cx fpos) HRL ltac:(kn_in) eq_refl).
  assert (B21 : bv_unsigned (ew E 21%nat) = kW2 cx fpos).
  { rewrite (ER 21%nat 21%bv eq_refl), R21.
    apply unsigned_lit_small. unfold kW2, KN_W2.
    destruct (kn_F_facts B LAWS cx fpos k2 ly3 S3 md3 HJB) as (F1 & F2 & _).
    pose proof asan_consts as ((C1a & C1b) & _).
    change (fs_frame_bytes KN_CID) with 16384 in F2. lia. }
  assert (HS : st_ok_pi SEGS pa_val E k1_ss (restrict (w_H W3) ms3)).
  { rewrite (kn_ms_shape ms3 (BASE + kpc KP_K1) Hpc Hrv Hsvc Hrom Hfrg Hfcs).
    rewrite restrict_mkst_fx. unfold k1_ss. apply pa_entry_st_ok_full.
    - rewrite HEdef. apply regs_ok_Eimg_Ereg.
    - vm_compute. reflexivity.
    - apply Forall_nil.
    - cbn [pairwise_disjoint]. exact I.
    - unfold k1_facts, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
      split; [|split; [exact I | exact I]].
      split; [|exact I]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite B20.
      split; [lia|]. split; [change (2 ^ 0) with 1; apply Z.mod_1_r | lia]. }
  assert (SHOK : sh_ok SEGS k1_Bx (@nil shent) E (mrestrict (w_H W3) (ms_mem ms3))) by apply Forall_nil.
  pose (RUN := paj_run_x SK B LAWS (k_G cx) HGok (k_XO cx) (k_OUT cx)).
  paj_run_tok RUN HS HJ SHOK k1_span.
  { apply awr_ok_x_nil. }
  lazymatch goal with
  | HS' : st_ok _ _ ?ssx (restrict _ ?msn), HF' : frame_of _ _ (ms_mem ms3) (ms_mem ?msn)
    |- SRr _ _ (mkCfg ?msn ?mdn) _ =>
    assert (Hmem : ms_mem msn = ms_mem ms3)
      by (apply functional_extensionality; intros x; apply HF';
          intros (rr & Hin & _); exact (False_ind _ Hin));
    assert (HMS' : kms KP_NLERR msn)
      by (apply (k12_kms_of _ E ssx msn KP_NLERR HS');
          [vm_compute; reflexivity | cbn [ss_pc setpc]; exact k12_sigma_nlerr]);
    assert (HK0 : forall r, In r nx_keep0 -> getr (ms_regs msn) r = getr (ms_regs ms3) r)
      by exact (regs_kept_of_st_ok SEGS E ssx (restrict (w_H W3) msn) (ms_regs ms3) (@nil word) nx_keep0 HS'
                  HAG ltac:(vm_compute; reflexivity));
    assert (HKN : forall r, In r nx_keepN ->
              getr (ms_regs msn) (Z_to_bv 5 (Z.of_nat r)) = getr (ms_regs ms3) (Z_to_bv 5 (Z.of_nat r)))
      by (intros r Hr;
          exact (regs_kept_of_st_ok SEGS E ssx (restrict (w_H W3) msn) (ms_regs ms3) (@nil word)
                   (map (fun q : nat => Z_to_bv 5 (Z.of_nat q)) nx_keepN) HS' HAG
                   ltac:(vm_compute; reflexivity) _ (kn_in_map5 r nx_keepN Hr)));
    assert (Rr1 : getr (ms_regs msn) (Z_to_bv 5 (Z.of_nat 1)) = w64 (BASE + kpc KP_NLRET))
      by (rewrite (st_ok_restrict_reg SEGS (w_H W3) E ssx msn (Z_to_bv 5 (Z.of_nat 1)) HS');
          replace (sr_get (ss_regs ssx) (Z_to_bv 5 (Z.of_nat 1))) with (SOff 240 14052)
            by (vm_compute; reflexivity);
          cbn [sv_denot]; rewrite (img_env_codeptr E HEI 14052); unfold w64; f_equal;
          unfold kpc, AF_kernel, KP_NLRET; lia);
    assert (Rr10 : getr (ms_regs msn) (Z_to_bv 5 (Z.of_nat 10)) = w64 (kW2 cx fpos))
      by (rewrite (st_ok_restrict_reg SEGS (w_H W3) E ssx msn (Z_to_bv 5 (Z.of_nat 10)) HS');
          replace (sr_get (ss_regs ssx) (Z_to_bv 5 (Z.of_nat 10))) with (SOff 21 0)
            by (vm_compute; reflexivity);
          cbn [sv_denot]; rewrite B21, Z.add_0_r; reflexivity);
    assert (Rr12 : getr (ms_regs msn) (Z_to_bv 5 (Z.of_nat 12)) = w64 (2 ^ 64 - 1))
      by (rewrite (st_ok_restrict_reg SEGS (w_H W3) E ssx msn (Z_to_bv 5 (Z.of_nat 12)) HS');
          replace (sr_get (ss_regs ssx) (Z_to_bv 5 (Z.of_nat 12))) with (SLit (2 ^ 64 - 1))
            by (vm_compute; reflexivity);
          cbn [sv_denot]; reflexivity);
    assert (Hfds : m_fds mdn = m_fds md3) by exact (proj1 (wvb_fds_fs _ _ _));
    assert (Hfs : m_fs mdn = m_fs md3) by exact (proj2 (wvb_fds_fs _ _ _));
    apply (HC cx fpos k2 ly3 S3 W3 msn mdn HB ltac:(assumption) HFR)
  end.
  exists c, ci, j, m, k, n, f, adv, (2 ^ 64 - 1).
  split; [exact HRc|]. split; [exact HRm|]. split; [exact Hc|]. split; [exact Hci|]. split; [exact Hj|].
  split; [exact Hm|]. split; [exact Hk|]. split; [lia|]. split; [right; lia|].
  split; [unfold kw_at in *; rewrite Hmem; exact HW|].
  eapply kat_move;
    [ exact HAT | exact HMS' | | | exact Hmem | apply incl_refl | exact Hfds | exact Hfs ].
  - apply (kregs0_keep cx ms3); [exact HK0 | exact HR0].
  - unfold kregs_eq. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
    + exact Rr1.
    + exact Rr10.
    + exact Rr12.
    + rewrite HKN by (unfold nx_keepN; kn_in). apply (kn_reg_in ms3 _ _ _ HRL). kn_in.
    + rewrite HKN by (unfold nx_keepN; kn_in). apply (kn_reg_in ms3 _ _ _ HRL). kn_in.
    + rewrite HKN by (unfold nx_keepN; kn_in). apply (kn_reg_in ms3 _ _ _ HRL). kn_in.
    + rewrite HKN by (unfold nx_keepN; kn_in). apply (kn_reg_in ms3 _ _ _ HRL). kn_in.
Qed.

End b.
End a.

Print Assumptions kn_k1.
