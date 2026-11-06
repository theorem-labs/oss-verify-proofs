(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: new walk for libreac/fuzz_pcap (a Theorem Labs lane). The generic helpers pe_land_m32,
   pe_denot_and_m32(_add0), pe_trim_* / pe_submem_to / pe_prreg_raw / pe_add_fact / pe_sregion are cgif_file_fuzzer
   lib/A/ACer.v's (origin/ossv/recipes c8557374ad2e) as a Theorem Labs lane's lib/A/Prog/PcapSourceOpen.v restates them
   (a working branch f0d76b020fe); pe_U_srl, pe_cbyte .. pe_word_at and pe_saved_of are
   a Theorem Labs lane's lib/A/Prog/GrantEntryHead.v (a working branch b83b8251684) restated over PAImg pcap_listing. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/A/Prog/PcapHarnessPE.v, with its module paths, module names and numbers changed; 616 of its 728 lines of code are new or changed and 1195 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/reac_served_markHead.v; 115 of its 158 lines of code are new or changed and 685 lines of the source are left out. *)
(* reac_served_say_to (reac_served_mark.c:16-19) on image A (fuzz_link.asan 0x89504, 12 bytes, 3 instructions;
   listing (internal path) (internal record, sha256 52363ef41162)): the walk of
   lib/A/Prog/reac_served_say_to_c.v `reac_served_say_to_acontract` on link's program tables, through the walk kit
   lib/A/Prog/LinkWalk.v.

   The whole function is
     +0x00  auipc a1, 0x5a8                 (listing slot PHi 94: the auipc value A_HI 94 = 0x631504)
     +0x04  sd a0, -0x224(a1)               (= 0x631504 - 0x224 = 0x6312e0 = LA_G_SAY, the .bss word g_say)
     +0x08  ret
   No frame, no call, no instrumented check: K = 0, EV = 0, SIDE = [], and the store goes to a constant offset
   into a global, which the instrumentation leaves unchecked.

   The symbolic state is one region over the base atom 414 (= A_HI 94) covering the eight bytes
   [-0x224, -0x21c) of it, with no chunk at the entry (the code only writes) and the atom pinned to 0x631504 by
   a fact (the run refuses a write window whose base has no range fact: `cells_safe_b` of sh_static_ok asks the
   window to be provably outside the shadow band). After the run the region holds one chunk, the 8 bytes
   `CVal 8 (SOff 10 0)` = a0, and `field_of_region` of lib/A/Prog/YC4b.v reads the Post's `au64_at` straight off
   it. The walk never reads `arodata_okP`, so the contract is proved at every read-only window and the corollary
   states it at PCAP_RLO / PCAP_RHI, the window the frame's `in_ro` uses (the cross-lane rule).

   Callee contracts cited: none (reac_served_say_to calls nothing). Section hypotheses: the image instance
   (PI : PAImg link_listing), its value table (HV : LinkVals, discharged by computation at the instance that
   lib/A/Prog/LinkPaCheck.v certifies against the image) and the allocator laws (LAWS : AR_laws pa_segs B,
   the lib/A frame).

   Released proofs (rule 24): none of reac_served_say_to (link-a/index/SUMMARY.md (internal record, sha256 58ab2c29f038);
   `proof-index reac_served_say_to` 0 named, 0 by address, 0 released lemmas; the four-ref grep over
   origin/main, origin/ossv/recipes, origin/ossv/candidates and origin/release/pau-projects-recipes found no
   released walk).
   Proves function reac_served_say_to (image A, the asan build). *)
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
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkSyms LinkList LinkAddr LinkPa LinkPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import YC4b PcapRelro.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_aaddr link_amem LinkWalk
  reac_served_say_to_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Section b.
Context {PI : PAImg link_listing}.
Variable B : asyms.
Hypothesis LAWS : AR_laws pa_segs B.
Hypothesis HV : LinkVals.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).

(* the auipc value of the slot at +0x00: A_HI 94, and g_say is 0x224 below it *)
Definition LA_SAY_HI : Z := 0x631504.
Lemma LA_SAY_HI_g_say : LA_SAY_HI - 548 = LA_G_SAY. Proof. reflexivity. Qed.

Definition st_region : YP09.region :=
  YP09.mkRegion (Some 414%nat) (-548) (-540) (-548) (-540) [].   (* 414 = A_HI 94 *)
Definition st_facts : facts := mkFacts [(414%nat, mkAF LA_SAY_HI LA_SAY_HI 0)] [] [].
Definition st_ss : sstate := mkSS AF_reac_served_say_to sr_atoms [st_region] None st_facts.
Definition st_Bx : sv := SLit SHADOW_OFF.
Definition st_span : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).

Theorem reac_served_say_to_aproof : forall rlo rhi, reac_served_say_to_acontract SK pa_segs rlo rhi B.
Proof.
intros rlo rhi.
unfold reac_served_say_to_acontract, aleaf.
intros G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs HPRE HP.
destruct HPRE as (HJ & HGok & HROD & Hraw & Hra4 & Hgp & Htp & Hal16 & Hwlo & Hwhi & Hev & Hside & Hajw & Hnro).
pose proof HJ as HJ0.
(* HP : awrange pa_segs (rdW W memc) LA_G_SAY 8 *)
assert (HK : REAC_SERVED_SAY_TO_AK = 0) by reflexivity.
(* the environment: no extra atom is needed, the stored value is a0 itself *)
set (E := Eimg (Ereg regs (@nil word))).
assert (HEI : img_env pa_val A_LIM E) by (subst E; apply Eimg_env).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs (@nil word)) n)
  by (intros n Hn; subst E; apply Eimg_low; exact Hn).
assert (E1 : ew E 1%nat = getr regs 1)
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs (@nil word) 1 1%bv eq_refl)).
assert (E10 : ew E 10%nat = getr regs 10)
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs (@nil word) 10 10%bv eq_refl)).
assert (U10 : bv_unsigned (ew E 10%nat) = aarg regs 0) by (rewrite E10; reflexivity).
assert (EHI : ew E 414%nat = Z_to_bv 64 LA_SAY_HI).
{ subst E. change (414%nat) with (A_HI 94). rewrite Eimg_img by (unfold A_HI, A_TEXT, A_LIM; lia).
  rewrite (lv_hi HV 94%nat ltac:(unfold link_nhi; lia)). reflexivity. }
assert (UHI : bv_unsigned (ew E 414%nat) = LA_SAY_HI)
  by (rewrite EHI; apply unsigned_lit_small; unfold LA_SAY_HI; lia).
assert (HAE : env_agree 32 (Ereg regs (@nil word)) E)
  by (split; [intros n Hn; apply EL; unfold A_TEXT; lia | subst E; reflexivity]).
(* the entry state *)
assert (HS : st_ok_pi pa_segs pa_val E st_ss
   (restrict (w_H W) (mkst regs (Z_to_bv 64 (pa_val A_TEXT + AF_reac_served_say_to)) memc (seg_rom pa_segs)))).
{ rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  - subst E. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil].
    unfold st_region, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite UHI. split; [unfold LA_SAY_HI; lia|]. split; [unfold LA_SAY_HI; lia|].
    split; [|apply Forall_nil].
    intros o Ho. cbn [ms_mem restrict mkst].
    replace (LA_SAY_HI + o) with (LA_G_SAY + (o + 548)) by (unfold LA_SAY_HI, LA_G_SAY; lia).
    apply HP. lia.
  - cbn [pairwise_disjoint all_disjoint]. tauto.
  - split; [|split; exact I].
    cbn [st_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite UHI. rewrite ?Z.pow_0_r, ?Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; first [exact I | lia]. }
assert (SHOK : sh_ok pa_segs st_Bx (@nil shent) E (mrestrict (w_H W) memc)) by (apply Forall_nil).
assert (HCFG : cfg_at pa_segs REAC_SERVED_SAY_TO_A regs memc mdc
             = mkCfg (mkst regs (Z_to_bv 64 (pa_val A_TEXT + AF_reac_served_say_to)) memc (seg_rom pa_segs)) mdc).
{ unfold cfg_at. rewrite (lv_text HV). reflexivity. }
rewrite HCFG.
pose (RUN := paj_run_x SK B LAWS G HGok XO OUT).
pose (RET := paj_ret_at (PL := PL_link) (PI := PI)).
(* the auipc and the store, up to the `ret` *)
paj_run_tok RUN HS HJ SHOK st_span.
{ apply awr_ok_x_cons; [|apply awr_ok_x_nil].
  intros a Ha. unfold st_region in Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite UHI in Ha.
  apply (Hajw a). exists (LA_G_SAY, LA_G_SAY + 8).
  split; [left; reflexivity|]. cbn [fst snd]. unfold LA_SAY_HI, LA_G_SAY in *. lia. }
(* what the run wrote: the eight bytes of g_say *)
assert (UN : forall a, 0 <= a < 2 ^ 64 -> ~ (LA_G_SAY <= a < LA_G_SAY + 8) ->
   aview pa_segs (w_H W) (ms_mem ms) a = aview pa_segs (w_H W) memc a).
{ apply (kept_of_frame (segs := pa_segs) E (ss_mem st_ss) (w_H W) memc (ms_mem ms)
          (fun a => LA_G_SAY <= a < LA_G_SAY + 8) HFr).
  intros bb wlo whi aa Hin Hrr. vm_compute in Hin.
  repeat (destruct Hin as [Hq | Hin];
          [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite UHI in Hrr;
           unfold LA_SAY_HI, LA_G_SAY in *; lia |]).
  destruct Hin. }
(* the stored word, off the region's chunk *)
lazymatch type of HS with
| st_ok_pi _ _ _ ?ssx (restrict _ ?msx) =>
  let r0 := eval vm_compute in (nth 0 (ss_mem ssx) st_region) in
  pose proof (st_ok_region_nth E (abs_ss pa_val ssx) (restrict (w_H W) msx) 0%nat r0 HS
                ltac:(vm_compute; reflexivity)) as HRg
end.
cbn [ms_mem restrict mkst] in HRg.
pose proof (field_of_region E _ 414%nat LA_SAY_HI _ _ _ _ _ (-548) 8%N (SOff 10 0) (aarg regs 0)
              HRg UHI ltac:(cbn [In]; repeat (first [left; reflexivity | right]))
              ltac:(cbn [sv_denot]; rewrite E10, Z.add_0_r, Z_to_bv_bv_unsigned;
                    unfold aarg, argZ; rewrite Z_to_bv_bv_unsigned; reflexivity)
              ltac:(unfold aarg, argZ;
                    match goal with |- 0 <= bv_unsigned ?x < _ => pose proof (u64_range x) end;
                    cbn [Z.of_N Z.mul]; lia)
              ltac:(cbn; lia)) as VSAY.
replace (LA_SAY_HI + -548) with LA_G_SAY in VSAY by (unfold LA_SAY_HI, LA_G_SAY; lia).
(* the return *)
lazymatch goal with
| HSf : st_ok_pi _ _ _ ?ssx (restrict _ ?msc) |- _ =>
  prreg HSf (1%bv : bv 5) R1;
  eapply (RET W _ _ _ _ _ HSf eq_refl ltac:(vm_compute; reflexivity));
  intros mat'
end.
rewrite R1, E1. unfold YK0s.ret_ok in Hraw. rewrite Hraw.
eapply (apost_leaf SK pa_segs B LAWS pa_segs_low REAC_SERVED_SAY_TO_AK 0
          (fun a => inFP (reac_served_say_to_awr regs (rdW W memc)) a)
          G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs _ _ _ _
          HJ0).
- apply ajournal_gx_materialize; first [exact LAWS | exact pa_segs_low | exact HJ].
- lia.
- lia.
- lia.
- repeat rewrite (proj1 (wvb_fds_fs _ _ _)). reflexivity.
- repeat rewrite (proj2 (wvb_fds_fs _ _ _)). reflexivity.
- eapply (aregs_preserved_of_st_ok pa_segs (w_H W) E _ _ regs (@nil word));
    [exact HS | exact HAE | vm_compute; reflexivity].
- intros a Ha _ HnE. apply UN; [exact Ha|].
  intros Hr. apply HnE. exists (LA_G_SAY, LA_G_SAY + 8).
  split; [left; reflexivity | cbn [fst snd]; exact Hr].
- intros a Hp. exact (apresent_grows (w_H W) memc (ms_mem ms) a HG Hp).
- intros a Ha. exfalso. lia.
- intros x (r & Hin & Hr). cbn [In] in Hin. destruct Hin as [<- | []]. cbn [fst snd] in Hr.
  unfold LA_G_SAY, SHADOW_OFF in *. lia.
- split; [symmetry; apply set_fs_self|]. split; [apply Permutation_refl|].
  unfold reac_served_say_to_apost, au64_at. exact VSAY.
Qed.

(* at the window the frame's `in_ro` uses (lib/A/ACeg.v:62), the form every caller takes *)
Corollary reac_served_say_to_aproof_pcap :
  reac_served_say_to_acontract SK pa_segs PCAP_RLO PCAP_RHI B.
Proof. exact (reac_served_say_to_aproof PCAP_RLO PCAP_RHI). Qed.
End b.
End a.
