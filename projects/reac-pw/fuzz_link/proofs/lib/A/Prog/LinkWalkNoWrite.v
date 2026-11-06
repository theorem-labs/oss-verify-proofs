(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_decode/lib/A/Prog/LLVMFuzzerTestOneInput_seg_up.v, with its module paths and module names changed; 264 of its 309 lines of code are new or changed and 2644 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/fuzz_recv_cp.v; 126 of its 165 lines of code are new or changed and 270 lines of the source are left out. *)
(* reac-pw/fuzz_link, image A: the pieces of a walk of a leaf whose write set is empty (the check_*
   walks; any leaf with `Wr := fun _ _ => []`), at link's listing over ajournal_gx (LinkWalk.v paj_run_x):
   - lf_ss / lf_E / lf_entry: the entry state of a run whose only memory is the function's own frame
     (stack_region F) with sp's range fact and the shadow base pinned as atom 32 (so SOff 32 0 is a valid Bx);
   - lf_awr: the run's write permission when its only write window is the frame;
   - lf_kept / lf_fold: the bytes outside [sp - K, sp) a run keeps, chained from the call;
   - lf_finish0: the contract's apost at the `ret` (LinkWalk.v apost_leaf at E := inFP []).
   Proves no function (kind: segment lemma). *)
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
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import YC81 YC4b.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_aaddr link_amem link_ajkit LinkWalk.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

(* the entry state: the frame of F bytes below sp; atom 32 is the shadow base *)
Definition lf_facts : facts := mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (32%nat, mkAF SB SB 0)] [] [].
Definition lf_ss (AF F : Z) : sstate := mkSS AF sr_atoms [stack_region F] None lf_facts.

(* the bytes a walk with an empty write set may change: its window *)
Definition lf_Zs (K sp a : Z) : Prop := sp - K <= a < sp.

(* a register atom's unsigned value, as a branch condition reads it *)
Lemma lf_U_reg : forall E n, U E (SOff n 0) = bv_unsigned (ew E n).
Proof.
  intros E n. rewrite U_SOff, Z.add_0_r. apply YP0m.zcanon_small.
  pose proof (bv_unsigned_in_range 64 (ew E n)) as H. change (bv_modulus 64) with (2 ^ 64) in H. lia.
Qed.

Section w. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Context {PI : PAImg link_listing}.
#[local] Notation SEGS := (@pa_segs _ link_listing PI).
#[local] Notation VAL := (@pa_val _ link_listing PI).
#[local] Notation BASE := (@pa_val _ link_listing PI A_TEXT).
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
Definition lf_E (regs : bvmap 5 word) : env := Eimg (Ereg regs [Z_to_bv 64 SB]).
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.

Lemma lf_entry : forall AF F G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word),
  regions_wf [stack_region F] = true -> 0 <= F ->
  ajournal_gx SEGS B G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - F -> spZ regs <= sp0 ->
  st_ok_pi SEGS VAL (lf_E regs) (lf_ss AF F)
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF)) memc (seg_rom SEGS))).
Proof.
intros AF F G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs Hwf HF HJ H16 Hwlo Hwhi.
destruct HJ as (HSTK & HXO & (memS & HJi & _) & _).
pose proof HJi as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
unfold lf_E. set (E := Eimg (Ereg regs [Z_to_bv 64 SB])).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs [Z_to_bv 64 SB]) n)
  by (intros n Hn; apply Eimg_low; exact Hn).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
rewrite restrict_mkst_fx. unfold lf_ss. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- exact Hwf.
- apply Forall_cons; [|apply Forall_nil]. unfold region_ok, stack_region.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  fold E. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
  intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
- apply pairwise_disjoint_of_extents. unfold stack_region, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi zpairwise_disjoint zall_disjoint]. tauto.
- split; [|split; [exact I | exact I]].
  cbn [lf_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  fold E. rewrite Usp, E32. rewrite unsigned_lit_small by (unfold SB; lia).
  change (2 ^ 4) with 16. rewrite Z.pow_0_r, Z.mod_1_r. unfold SB.
  repeat match goal with |- _ /\ _ => split end; first [exact I | lia].
Qed.

(* THE END: the contract's apost at the `ret` of a leaf with an empty write set *)
Lemma lf_finish0 : forall K G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs regs2 : bvmap 5 word)
    mem2 md2 (P : Prop),
  ajournal_gx SEGS B G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  ajournal_gx SEGS B G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem2 md2 k ->
  0 <= K -> sp0 - STK <= spZ regs - K -> spZ regs <= sp0 ->
  m_fds md2 = m_fds mdc -> m_fs md2 = m_fs mdc ->
  aregs_preserved regs regs2 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ lf_Zs K (spZ regs) a -> aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) memc a) ->
  mem_grows (rdW W memc) (rdW W mem2) ->
  P ->
  apost SK SEGS B K 0 (fun a => inFP [] a) G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs
    (fun ly2 S2 W2 regs2 mem2 md2 => S2 = set_fs (st_fs S2) Sc /\ Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) /\ P)
    W (mkCfg (mkst regs2 (getr regs 1) mem2 (seg_rom SEGS)) md2).
Proof.
intros K G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs regs2 mem2 md2 P
  HJ HJ2 HK Hlo Hhi Hfd Hfs HP UN HGr HPost.
pose proof HJ2 as (_ & HXO2 & (memS2 & HJ2i & _) & _).
pose proof HJ2i as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres2 & _).
apply (apost_leaf SK SEGS B LAWS pa_segs_low K 0 (fun a => inFP [] a)
  G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs regs2 mem2 md2 _ HJ HJ2);
  [lia | lia | lia | exact Hfd | exact Hfs | exact HP | | | | | ].
- intros a Ha Hw _. exact (UN a Ha Hw).
- intros a Hp. exact (apresent_grows _ _ _ _ HGr Hp).
- intros a Ha. apply Hpres2. clear - Ha Hlo Hhi HXO2. lia.
- intros x ((lo, hi) & [] & _).
- cbv beta. split; [destruct Sc; reflexivity|]. split; [apply Permutation_refl | exact HPost].
Qed.
End w.

(* the run's write permission when every write window is the frame (or empty) *)
Ltac lf_awr :=
  lazymatch goal with |- awr_ok_x _ ?rs _ _ _ _ _ _ _ _ _ _ =>
    let rs' := eval vm_compute in rs in change rs with rs' end;
  repeat (apply awr_ok_x_cons;
    [ intros ?a ?Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite ?ew_ewset_other in Ha by lia;
      first
      [ lia
      | lazymatch type of Ha with context [ew _ 2%nat] =>
          match goal with U : bv_unsigned (ew _ 2%nat) = _ |- _ => rewrite U in Ha end;
          left; split; [left; lia | lia] end ]
    | ]);
  apply awr_ok_x_nil.

(* the bytes outside [sp - K, sp) a run left as they were (YC4b.v kept_of_frame) *)
Ltac lf_kept_side K sp :=
  let bb := fresh "bb" in let wlo := fresh "wlo" in let whi := fresh "whi" in let aa := fresh "aa" in
  let Hin := fresh "Hin" in let Hrr := fresh "Hrr" in
  intros bb wlo whi aa Hin Hrr; vm_compute in Hin;
  repeat (let Hq := fresh "Hq" in destruct Hin as [Hq | Hin];
          [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?ew_ewset_other in Hrr by lia;
           repeat match goal with U : bv_unsigned (ew _ ?n) = _ |- _ =>
             lazymatch type of Hrr with context [ew _ n] => rewrite U in Hrr end end;
           unfold lf_Zs; lia |]);
  destruct Hin.
Ltac lf_kept HFr W K sp UN :=
  let sg := lazymatch type of W with world ?s => s end in
  pose proof (kept_of_frame (segs := sg) _ _ _ _ _ (lf_Zs K sp) HFr ltac:(lf_kept_side K sp)) as UN.

(* chain a run's kept bytes and growth onto those since the call *)
Ltac lf_fold UN HGc UNk HG W memc K sp :=
  lazymatch type of UNk with forall a, _ -> _ -> aview ?sg _ ?mN a = aview _ _ ?mO a =>
    let UN' := fresh "UN" in
    assert (UN' : forall a, 0 <= a < 2 ^ 64 -> ~ lf_Zs K sp a ->
              aview sg (w_H W) mN a = aview sg (w_H W) memc a)
      by (let x := fresh "x" in let Hx := fresh "Hx" in let Hzx := fresh "Hzx" in
          intros x Hx Hzx; rewrite (UNk _ Hx Hzx); exact (UN _ Hx Hzx));
    clear UN UNk; rename UN' into UN end;
  lazymatch type of HG with mem_grows _ (mrestrict _ ?mN) =>
    let HG' := fresh "HGc" in
    assert (HG' : mem_grows (mrestrict (w_H W) memc) (mrestrict (w_H W) mN))
      by (eapply mem_grows_trans; [exact HGc | exact HG]);
    clear HGc HG; rename HG' into HGc end.

(* at the `ret` of a leaf with an empty write set whose Post is True: read ra back, return, and close with
   lf_finish0. HS: the run's last state; HAE: the entry env agrees with the run's on the 32 registers; E1: the entry
   env's ra; Hret: ra is a return address; HJ0 / HJ: the call's / the run's journal; UN / HGc: the chained kept
   bytes and growth. *)
Ltac lf_ret PI LAWS W regs extra HS HAE E1 Hret HJ0 HJ Hwlo Hwhi UN HGc :=
  lazymatch type of HS with st_ok_pi ?sg _ ?Ef _ (restrict _ ?msF) =>
    let R1 := fresh "R1" in prreg HS (1%bv : bv 5) R1;
    let HPr := fresh "HPr" in
    pose proof (aregs_preserved_of_st_ok sg _ Ef _ _ regs extra HS HAE ltac:(vm_compute; reflexivity)) as HPr;
    eapply (paj_ret_at (PL := PL_link) (PI := PI) W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity));
    intros ?mat';
    rewrite R1; rewrite ?ew_ewset_other by lia; rewrite E1, Hret;
    eapply lf_finish0;
    [ exact LAWS | exact HJ0 | apply (ajournal_gx_materialize sg _ LAWS pa_segs_low); exact HJ | lia
    | exact Hwlo | exact Hwhi
    | repeat rewrite (proj1 (wvb_fds_fs _ _ _));
      repeat match goal with Hs : same_but_materialized _ ?b |- context [m_fds ?b] =>
        rewrite (same_but_materialized_wvb _ _ Hs); repeat rewrite (proj1 (wvb_fds_fs _ _ _)) end;
      first [reflexivity | assumption]
    | repeat rewrite (proj2 (wvb_fds_fs _ _ _));
      repeat match goal with Hs : same_but_materialized _ ?b |- context [m_fs ?b] =>
        rewrite (same_but_materialized_wvb _ _ Hs); repeat rewrite (proj2 (wvb_fds_fs _ _ _)) end;
      first [reflexivity | assumption]
    | exact HPr | exact UN | exact HGc | exact I ]
  end.
