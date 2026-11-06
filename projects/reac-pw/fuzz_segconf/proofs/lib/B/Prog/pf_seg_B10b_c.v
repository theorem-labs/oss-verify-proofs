(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the program walk of check_round_trip on the ASan build of plugin-hostd/fuzz_command
   (0x87fd8, 286 instructions), proving tcheck_round_trip_spec (check_round_trip_c.v), in the shape of cgif_file_fuzzer's
   walks (lib/A/AChc.v, ACh1..ACh8.v, AChf.v): one statement per point between two calls (ST_B .. ST_EPI below), each
   segment proved by a run of the symbolic executor over the position-abstract listing (CmdPaLib.v) from a fresh seed,
   the inline checks removed by the shadow tokens (PaShadow.v), and the call at its end composed into the journal:
   the class-5 side-stack frame by aj_stack_malloc_atS (PaCall.v) and, from check_round_trip_k.v, aj_set_shadow_atS
   (__asan_set_shadow_f8/_00) and aj_stack_free_cls_atS (__asan_stack_free_5); the strdup wrapper by crts4_strdup_sub,
   the free wrapper by afree04_sub (PaCall.v), the strcmp wrapper by aj_art_at (PaArt.v); the program callees
   rec_calls_copy, joined, send_message and rec_calls_free by cl_callS_wide and rec_calls_equal by cl_callS_na
   (PaNoChain.v), each with its contract as a Section hypothesis. The skip path (no word, or the daemon did not act)
   joins the epilogue at 0x88314; the abort edges (0x8838c) are excluded by rt_okA and the callees' posts.
   Re-fit to statement passes 4, 4b and 5: the callee and runtime hypotheses hold at every
   FP state (forall fx0) and the segments use them at the ambient fx. send_message reaches the printf wrappers, so the
   points before its return (ST_B .. ST_F) prove the FP-existential post crt_postF (apost_baseF); crt_s6 calls
   send_message by PaFx.v's cl_callS_wideF with the rounding-mode premise HFRM and goes on at the FP state fx1 it
   returns (srr_after_callF_base). The points after it (ST_G .. ST_EPI) prove apost_base at the ambient FP state, so
   once the sections close they hold at fx1 (crt_G, used so by tcheck_round_trip_spec_holds). The skip path lifts
   ST_EPI's post by apost_baseF_of_base (crts3_skip). Pass 5 removed astack_pres: s0 is the frame pointer sp0 at every
   call, so each call's frame chain is the prologue's frame record (ra at sp0 - 8, the entry s0 at sp0 - 16, from
   crt_frame) on afn_pre's chain (achain_push, crt_chain), and chain_pre for the runtime allocation entries is
   achain_chain_pre of it. joined's new premises at its call: len's 8 bytes present (the journal's window), and
   (pass 5b) the stack from len - 16 present, from the statement's astack_pres kept by astack_pres_journal. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/check_round_trip.v, with its module paths and module names changed; 665 of its 733 lines of code are new or changed and 4985 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, image B (fuzz_segconf.asan-ubsan, pin c3796c0b38f3, twin 80e82127e8ca): the compare piece of
   segment B10b of reac_segconf_parse_file's walk, pb10_c_ok : PB10_C B (lib/B/Prog/pf_seg_B10b_k.v:
   HA_ROLEV n -> HA_BAD n -> H_INTENT n). A B10b sub-lane of the image-B G3 walk owner, 2026-10-30. proves no function
   (kind: segment lemma of reac_segconf_parse_file's walk, piece PB10_C of segment B10b).
   ADAPTED from a working branch's lib/A/Prog/pf_a10b_b2.v (image A's bcmp-call helpers, 861a42d8f0c4),
   501c0d516c69 proofs/plugin-hostd/fuzz_command/lib/A/Prog/check_arity_s7.v (ca_bcmp_step: the run stops at the
   trampoline, aj_bcmp_at, the `beqz a0` after it) and image B's lib/B/Prog/pf_seg_B10b_j.v (the B10b segment lane,
   961c19ce3f65: the seed on a cut, the keep lemmas) and pf_seg_B5_r2.v (the B5 segment lane, 2305ce2c2c85: a branch
   after a run, psrr_branch_pi), re-derived on image B's code.
   THE CODE (reac_segconf_parse_file.fuzz_segconf.asan-ubsan.s; listing lib/B/Prog/SegList.v :3836-3866):
   site k = 0 .. 4 at pc_k = 0x888e4 + 0x18 k:
     auipc a0; addi a1,a0,imm  (a1 = listing object A_OBJ (55 + k) = seg_litA_rc w_k, b10c_lit: 0x21ae0 S_auto,
                                0x21b00 S_master, 0x21b20 S_slave, 0x21b40 S_tap, 0x21b60 S_box)
     li a2,n_k                 (n_k = S (length w_k) = 5, 7, 6, 4, 4)
     [site 4 only: 0x88950 li s3,4]
     mv a0,s7                  (s7 = low = F + 0x280, INV_INTENT)
     jal bcmp                  (pa_sigma SS___interceptor_trampoline_bcmp; return pc_k + 0x14, site 4 0x8895c)
     beqz a0                   (k = 0 -> 0x88980 `li s3,0; j 0x88d6c`; k = 1 -> 0x88a48 `li s3,1; j 0x88d6c`;
                                k = 2 -> 0x88c80 `li s3,2; j 0x88d6c`; k = 3 -> 0x88d68 `li s3,3` falls in;
                                k = 4 -> 0x88d6c = ROLEV directly, s3 = 4 already)
   the box compare's beqz not taken falls into 0x88960 = BAD.
   Instructions walked: 0x888e4 .. 0x8895c (31), 0x88980 - 0x88984 (2), 0x88a48 - 0x88a4c (2), 0x88c80 - 0x88c84 (2),
   0x88d68 (1) = 38. No instrumented check and no UBSan trap site lies in them (B10b's B#31, B#32 and T30 are
   piece PB10_S's).
   THE PROOF, per site (b10c_call<k>, b10c_br<k>): a seed on INV_INTENT at pc_k (every register its own atom, no
   region: the code stores nothing), a plain run to the call, INV_INTENT re-seated at the call (b10c_move: the run
   kept memory and the registers of b10c_RL), the bcmp step (pf_seg_B10b_ck.v b10c_bcmp: aj_bcmp_at under SRr_bind,
   a0 = 0 exactly when strcmp (r_low val 0 64) w_k = 0), a fresh seed at the return, psrr_branch_pi on the beqz:
   taken -> a run to ROLEV, INV_ROLEV with r = k (b10b_role_some: the k earlier compares were unequal), HA_ROLEV at
   the ambient FP state; not taken -> a run to pc_{k+1} (INV_INTENT and one more unequal word), or for k = 4 to
   BAD with INV_BAD (b10b_role_none), HA_BAD.
   SECTION HYPOTHESES (pf_seg_B10b_k.v brief section 3): ABCMP (the kit's abcmp_realizes at
   pa_sigma SS___interceptor_trampoline_bcmp, every FP state) and OBJ (B's SegObj.seg_val_objs: the five literal
   atoms). Positional names checked against image B's own tables: listing objects 55 .. 59 are checked by
   computation against seg_litA_rc of the five words (b10c_lit); no region letter or STK row of an A table is used. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI00 YI04.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI16.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pf_pieces_spec pfA_facts.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaRun PaShadow PaJournal SegSyms SegList
SegAddr SegPa SegObj SegGlob.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPaLib PaDenot PaLibG PaLibF PaLibH PaCall
PaCallRun.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import refuse_c reac_segconf_parse_file_c SegInstB.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import pf_pieces pf_seg_B10b_k pf_seg_B10b_f
  pf_seg_B10b_ck.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ---------- tools ---------- *)
Ltac b10c_rreg HS :=
 lazymatch goal with |- getr (ms_regs ?ms) ?r = _ =>
 lazymatch type of HS with
 | st_ok_pi _ _ ?E ?ss (restrict ?Hh ms) =>
  rewrite (st_ok_pi_restrict_reg Hh E ss ms r HS);
  let v := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with v
 | st_ok ?sg ?E ?ss (restrict ?Hh ms) =>
  rewrite (st_ok_restrict_reg sg Hh E ss ms r HS);
  let v := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with v
 end end.
Ltac b10c_clear_md := repeat match goal with |- context [with_vm_backing (m_vm_lazy ?m) ?x ?m] =>
  let mdv := fresh "mdv" in set (mdv := with_vm_backing (m_vm_lazy m) x m) in *; clearbody mdv end.
(* the beqz a0 (beq a0, x0): taken exactly when a0 is 0 *)
Lemma b10c_beq_t : forall E a b (x : word), sv_denot E a = x -> sv_denot E b = Z_to_bv 64 0 ->
  branch_taken BC_EQ (sv_denot E a) (sv_denot E b) = true -> x = w64 0.
Proof.
intros E a b x Ha Hb Hc. pose proof (branch_eq_U E a b) as Hq. rewrite Hc in Hq. symmetry in Hq.
apply Z.eqb_eq in Hq. unfold U in Hq. rewrite Ha, Hb in Hq. unfold w64. apply bv_eq. exact Hq.
Qed.
Lemma b10c_beq_f : forall E a b (x : word), sv_denot E a = x -> sv_denot E b = Z_to_bv 64 0 ->
  branch_taken BC_EQ (sv_denot E a) (sv_denot E b) = false -> x <> w64 0.
Proof.
intros E a b x Ha Hb Hc Hx. pose proof (branch_eq_U E a b) as Hq. rewrite Hc in Hq. symmetry in Hq.
unfold U in Hq. rewrite Ha, Hb, Hx in Hq. unfold w64 in Hq. rewrite Z.eqb_refl in Hq. discriminate Hq.
Qed.

Section d. Context {rc : YM05.RunCeil} {SK : YI16.sink_head} {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Variable B : asyms.
(* bcmp: the kit's abcmp_realizes at the trampoline, every FP state (pf_seg_B10b_k.v brief section 3) *)
Hypothesis ABCMP : forall fx0 : YK11.FPState,
  @abcmp_realizes fx0 rc SEGS B (pa_sigma SS___interceptor_trampoline_bcmp).
(* the listing's object atoms (B's SegObj.v), for the five literals' addresses *)
Hypothesis OBJ : seg_val_objs (PI := PI).

(* the literal of role word k is listing object 55 + k (SegList.v :3837 .. :3861) *)
Lemma b10c_lit : forall E, img_env VAL A_LIM E -> forall k w, nth_error PB10_WORDS k = Some w ->
  sv_denot E (SOff (A_OBJ (55 + k)) 0) = w64 (seg_litA_rc w).
Proof.
intros E HE k w Hk. unfold PB10_WORDS in Hk.
destruct k as [|[|[|[|[|k]]]]]; cbn [nth_error] in Hk;
  [| | | | | destruct k; cbn in Hk; discriminate Hk];
  injection Hk as <-;
  rewrite b10c_den_atom0, (img_env_atomP E _ HE) by (unfold A_OBJ, A_TEXT, A_LIM; lia);
  (rewrite OBJ by (apply Nat.ltb_lt; vm_compute; reflexivity));
  unfold w64; f_equal; vm_compute; reflexivity.
Qed.

Section x. Context {fx : YK11.FPState}.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Let b10c_RUNP := SRr_run_pi_AJ (fx := fx) B LAWS.
Let b10c_RUNC := SRr_run_pi_AJ_call (fx := fx) B LAWS.
Let b10c_RUNTO := SRr_run_to_pi_AJ (fx := fx) B LAWS.

(* ---------- the seed: every register its own atom, no region ---------- *)
Definition b10c_ss (pc : Z) : sstate := mkSS pc sr_atoms [] None (mkFacts [] [] []).
Lemma b10c_seed : forall pc (Wc : world SEGS) (rX : bvmap 5 word) memc,
  st_ok_pi SEGS VAL (Eimg (Ereg rX [])) (b10c_ss pc)
    (restrict (w_H Wc) (mkst rX (Z_to_bv 64 (BASE + pc)) memc (seg_rom SEGS))).
Proof.
intros pc Wc rX memc. rewrite restrict_mkst_fx. unfold b10c_ss. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_nil.
- cbn. tauto.
- unfold facts_ok; cbn; repeat split; first [exact I | apply Forall_nil | constructor].
Qed.

(* ---------- small tactics (names passed explicitly) ---------- *)
(* a0 from the branch condition of the beqz *)
Ltac b10c_br_t rX EE :=
  lazymatch goal with Hc : branch_taken BC_EQ (sv_denot ?Ex ?a) (sv_denot _ ?b) = true |- _ =>
    let Ha := fresh "Ha" in let H0 := fresh "H0" in
    assert (Ha : sv_denot Ex a = getr rX (Z_to_bv 5 10)) by (rewrite b10c_den_atom0; apply EE; reflexivity);
    assert (H0 : getr rX (Z_to_bv 5 10) = w64 0) by (exact (b10c_beq_t Ex a b _ Ha eq_refl Hc));
    clear Hc Ha end.
Ltac b10c_br_f rX EE :=
  lazymatch goal with Hc : branch_taken BC_EQ (sv_denot ?Ex ?a) (sv_denot _ ?b) = false |- _ =>
    let Ha := fresh "Ha" in let H0 := fresh "H0" in
    assert (Ha : sv_denot Ex a = getr rX (Z_to_bv 5 10)) by (rewrite b10c_den_atom0; apply EE; reflexivity);
    assert (H0 : getr rX (Z_to_bv 5 10) <> w64 0) by (exact (b10c_beq_f Ex a b _ Ha eq_refl Hc));
    clear Hc Ha end.
(* the goal's configuration at the listing offset of the cut P *)
Ltac b10c_at_cut P :=
  lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg (Z_to_bv 64 (_ + ?kk)) ?mm ?rom) ?mdx) _ =>
    change (mkCfg (mkst rg (Z_to_bv 64 (BASE + kk)) mm rom) mdx) with (cfg_at SEGS (BASE + P) rg mm mdx) end.

(* site 0 (0x888e4): the run to the jal, INV_INTENT at the call, the bcmp step with S_auto *)
Lemma b10c_call0 : forall n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val Q,
  INV_INTENT B n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val ->
  (forall rX2 mem2 md2, INV_INTENT B n v pos lyc Sc Wc rX2 mem2 md2 cf nm o ln d gi vp val ->
     (getr rX2 (Z_to_bv 5 10) = w64 0 <-> strcmp (r_low val 0 64) S_auto = 0) ->
     SRr SEGS Wc (cfg_at SEGS (BASE + (PF_INTENT + 0x14)) rX2 mem2 md2) Q) ->
  SRr SEGS Wc (cfg_at SEGS (BASE + PF_INTENT) rX memc mdc) Q.
Proof.
intros n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val Q HI Kc.
pose proof HI as (HB & _ & _ & _ & _ & _ & _ & HRG).
pose proof HB as (_ & HFI & _).
pose proof HFI as (HJ & _).
pose proof (b10c_seed PF_INTENT Wc rX memc) as HS.
set (E := Eimg (Ereg rX [])) in HS.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n0 (r : bv 5), Z.of_nat n0 = bv_unsigned r -> ew E n0 = getr rX r)
  by (intros n0 r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
unfold cfg_at, w64.
paj_run_shc b10c_RUNP b10c_RUNC HS HJ.
{ intros a (r & Hr & _). vm_compute in Hr. destruct Hr. }
b10c_clear_md.
assert (K1 : b10c_kept v (rdW Wc memc) (rdW Wc (ms_mem ms))).
{ intros a Ha _.
  lazymatch type of HFr with frame_of ?Ex ?rs _ _ =>
    apply (kept_of_frame (segs := SEGS) Ex rs (w_H Wc) memc (ms_mem ms) (fun _ => False) HFr);
    [|exact Ha | tauto] end.
  intros b wlo whi a' Hin' _. vm_compute in Hin'. destruct Hin'. }
assert (QK : forall r, In r b10c_RL -> getr (ms_regs ms) (Z_to_bv 5 r) = getr rX (Z_to_bv 5 r)).
{ intros r Hr. unfold b10c_RL in Hr. cbn [In] in Hr.
  repeat (destruct Hr as [<- | Hr]; [b10c_rreg HS; rewrite b10c_den_atom0; apply EE; reflexivity |]).
  destruct Hr. }
pose proof (b10c_move B n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val (ms_regs ms) (ms_mem ms) mdv
  HI HJ K1 QK) as HIT.
assert (A10 : getr (ms_regs ms) (Z_to_bv 5 10) = w64 (pf_F v pos + PF_O_LOW)).
{ b10c_rreg HS. rewrite b10c_den_atom0, (EE 23%nat (Z_to_bv 5 23) eq_refl).
  exact (b10c_rg rX _ 23 _ HRG ltac:(unfold PF_RL, PF_RM; b10c_in)). }
assert (A11 : getr (ms_regs ms) (Z_to_bv 5 11) = w64 (seg_litA_rc S_auto)).
{ b10c_rreg HS. exact (b10c_lit E HEI 0%nat S_auto eq_refl). }
assert (A12 : getr (ms_regs ms) (Z_to_bv 5 12) = w64 (Z.of_nat (S (length S_auto)))).
{ b10c_rreg HS. first [reflexivity | vm_compute; reflexivity]. }
assert (A1 : getr (ms_regs ms) (Z_to_bv 5 1) = Z_to_bv 64 (BASE + (PF_INTENT + 0x14))).
{ b10c_rreg HS. exact (codeptr_val E (PF_INTENT + 0x14) HEI). }
assert (Hrk : 0 <= (PF_INTENT + 0x14) < 2 ^ 40) by (unfold PF_INTENT, AF_reac_segconf_parse_file; lia).
assert (Hrk2 : ((PF_INTENT + 0x14)) mod 2 = 0) by (vm_compute; reflexivity).
pmkst HS.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg ?pw ?mm ?rom) ?mdx) _ =>
  change (mkCfg (mkst rg pw mm rom) mdx)
    with (cfg_at SEGS (pa_sigma SS___interceptor_trampoline_bcmp) rg mm mdx) end.
apply (b10c_bcmp B ABCMP n v pos lyc Sc Wc (ms_regs ms) (ms_mem ms) mdv cf nm o ln d gi vp val S_auto
  ((PF_INTENT + 0x14)) Q HIT b10f_in0 A10 A11 A12 A1 Hrk Hrk2).
intros rX2 mem2 md2 HI2 HP HIFF. exact (Kc rX2 mem2 md2 HI2 HIFF).
Qed.

(* site 0, from the return (0x888f8): the beqz; taken -> 0x88980 `li s3,0; j` ROLEV with s3 = 0, not taken -> 0x888fc *)
Lemma b10c_br0 : forall n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val,
  HA_ROLEV B n ->
  INV_INTENT B n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val -> b10c_ne val 0 ->
  (getr rX (Z_to_bv 5 10) = w64 0 <-> strcmp (r_low val 0 64) S_auto = 0) ->
  (forall rX' memc' mdc', INV_INTENT B n v pos lyc Sc Wc rX' memc' mdc' cf nm o ln d gi vp val ->
     b10c_ne val 1 ->
     SRr SEGS Wc (cfg_at SEGS (BASE + (PF_INTENT + 0x18)) rX' memc' mdc')
       (pf_postm B v (pf_role_step cf gi nm (ln + 1) val) o ln)) ->
  SRr SEGS Wc (cfg_at SEGS (BASE + (PF_INTENT + 0x14)) rX memc mdc)
    (pf_postm B v (pf_role_step cf gi nm (ln + 1) val) o ln).
Proof.
intros n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val HROLEV HI HNE HIFF Kc.
pose proof HI as (HB & _). pose proof HB as (_ & HFI & _). pose proof HFI as (HJ & _).
pose proof (b10c_seed (PF_INTENT + 0x14) Wc rX memc) as HS.
set (E := Eimg (Ereg rX [])) in HS.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n0 (r : bv 5), Z.of_nat n0 = bv_unsigned r -> ew E n0 = getr rX r)
  by (intros n0 r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
unfold cfg_at, w64.
psrr_branch_pi b10c_RUNP paj_branch HS.
- (* taken *)
  b10c_br_t rX EE. pose proof (proj1 HIFF H0) as Heq.
  paj_run_to_sh b10c_RUNTO HS HJ PF_ROLEV.
  { intros a (r & Hr & _). vm_compute in Hr. destruct Hr. }
  cbn [ms_mem mkst] in HFr, HG, HF.
  b10c_clear_md.
  assert (K1 : b10c_kept v (rdW Wc memc) (rdW Wc (ms_mem ms))).
  { intros a Ha _.
    lazymatch type of HFr with frame_of ?Ex ?rs _ _ =>
      apply (kept_of_frame (segs := SEGS) Ex rs (w_H Wc) memc (ms_mem ms) (fun _ => False) HFr);
      [|exact Ha | tauto] end.
    intros b wlo whi a' Hin' _. vm_compute in Hin'. destruct Hin'. }
  assert (QK : forall r, In r b10c_RL -> getr (ms_regs ms) (Z_to_bv 5 r) = getr rX (Z_to_bv 5 r)).
  { intros r Hr. unfold b10c_RL in Hr. cbn [In] in Hr.
    repeat (destruct Hr as [<- | Hr]; [b10c_rreg HS; rewrite b10c_den_atom0; apply EE; reflexivity |]).
    destruct Hr. }
  pose proof (b10c_move B n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val (ms_regs ms) (ms_mem ms) mdv
    HI HJ K1 QK) as HI'.
  assert (H19 : getr (ms_regs ms) (Z_to_bv 5 19) = w64 (Z.of_nat 0)) by (b10c_rreg HS; reflexivity).
  pmkst HS.
  b10c_at_cut PF_ROLEV.
  exact (HROLEV fx v pos lyc Sc Wc (ms_regs ms) (ms_mem ms) mdv cf nm o ln d gi val (Z.of_nat 0)
    (b10c_to_rolev B n v pos lyc Sc Wc _ _ _ cf nm o ln d gi vp val _ HI' H19
      (b10b_role_some (r_low val 0 64) 0 S_auto eq_refl HNE Heq))).
- (* not taken *)
  b10c_br_f rX EE.
  assert (Hne : strcmp (r_low val 0 64) S_auto <> 0) by (intros Heq; exact (H0 (proj2 HIFF Heq))).
  paj_run_to_sh b10c_RUNTO HS HJ (PF_INTENT + 0x18).
  { intros a (r & Hr & _). vm_compute in Hr. destruct Hr. }
  cbn [ms_mem mkst] in HFr, HG, HF.
  b10c_clear_md.
  assert (K1 : b10c_kept v (rdW Wc memc) (rdW Wc (ms_mem ms))).
  { intros a Ha _.
    lazymatch type of HFr with frame_of ?Ex ?rs _ _ =>
      apply (kept_of_frame (segs := SEGS) Ex rs (w_H Wc) memc (ms_mem ms) (fun _ => False) HFr);
      [|exact Ha | tauto] end.
    intros b wlo whi a' Hin' _. vm_compute in Hin'. destruct Hin'. }
  assert (QK : forall r, In r b10c_RL -> getr (ms_regs ms) (Z_to_bv 5 r) = getr rX (Z_to_bv 5 r)).
  { intros r Hr. unfold b10c_RL in Hr. cbn [In] in Hr.
    repeat (destruct Hr as [<- | Hr]; [b10c_rreg HS; rewrite b10c_den_atom0; apply EE; reflexivity |]).
    destruct Hr. }
  pose proof (b10c_move B n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val (ms_regs ms) (ms_mem ms) mdv
    HI HJ K1 QK) as HI'.
  pmkst HS.
  b10c_at_cut (PF_INTENT + 0x18).
  exact (Kc (ms_regs ms) (ms_mem ms) mdv HI' (b10c_ne_step val 0 S_auto eq_refl HNE Hne)).
Qed.

(* site 1 (0x888fc): the run to the jal, INV_INTENT at the call, the bcmp step with S_master *)
Lemma b10c_call1 : forall n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val Q,
  INV_INTENT B n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val ->
  (forall rX2 mem2 md2, INV_INTENT B n v pos lyc Sc Wc rX2 mem2 md2 cf nm o ln d gi vp val ->
     (getr rX2 (Z_to_bv 5 10) = w64 0 <-> strcmp (r_low val 0 64) S_master = 0) ->
     SRr SEGS Wc (cfg_at SEGS (BASE + (PF_INTENT + 0x2c)) rX2 mem2 md2) Q) ->
  SRr SEGS Wc (cfg_at SEGS (BASE + (PF_INTENT + 0x18)) rX memc mdc) Q.
Proof.
intros n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val Q HI Kc.
pose proof HI as (HB & _ & _ & _ & _ & _ & _ & HRG).
pose proof HB as (_ & HFI & _).
pose proof HFI as (HJ & _).
pose proof (b10c_seed (PF_INTENT + 0x18) Wc rX memc) as HS.
set (E := Eimg (Ereg rX [])) in HS.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n0 (r : bv 5), Z.of_nat n0 = bv_unsigned r -> ew E n0 = getr rX r)
  by (intros n0 r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
unfold cfg_at, w64.
paj_run_shc b10c_RUNP b10c_RUNC HS HJ.
{ intros a (r & Hr & _). vm_compute in Hr. destruct Hr. }
b10c_clear_md.
assert (K1 : b10c_kept v (rdW Wc memc) (rdW Wc (ms_mem ms))).
{ intros a Ha _.
  lazymatch type of HFr with frame_of ?Ex ?rs _ _ =>
    apply (kept_of_frame (segs := SEGS) Ex rs (w_H Wc) memc (ms_mem ms) (fun _ => False) HFr);
    [|exact Ha | tauto] end.
  intros b wlo whi a' Hin' _. vm_compute in Hin'. destruct Hin'. }
assert (QK : forall r, In r b10c_RL -> getr (ms_regs ms) (Z_to_bv 5 r) = getr rX (Z_to_bv 5 r)).
{ intros r Hr. unfold b10c_RL in Hr. cbn [In] in Hr.
  repeat (destruct Hr as [<- | Hr]; [b10c_rreg HS; rewrite b10c_den_atom0; apply EE; reflexivity |]).
  destruct Hr. }
pose proof (b10c_move B n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val (ms_regs ms) (ms_mem ms) mdv
  HI HJ K1 QK) as HIT.
assert (A10 : getr (ms_regs ms) (Z_to_bv 5 10) = w64 (pf_F v pos + PF_O_LOW)).
{ b10c_rreg HS. rewrite b10c_den_atom0, (EE 23%nat (Z_to_bv 5 23) eq_refl).
  exact (b10c_rg rX _ 23 _ HRG ltac:(unfold PF_RL, PF_RM; b10c_in)). }
assert (A11 : getr (ms_regs ms) (Z_to_bv 5 11) = w64 (seg_litA_rc S_master)).
{ b10c_rreg HS. exact (b10c_lit E HEI 1%nat S_master eq_refl). }
assert (A12 : getr (ms_regs ms) (Z_to_bv 5 12) = w64 (Z.of_nat (S (length S_master)))).
{ b10c_rreg HS. first [reflexivity | vm_compute; reflexivity]. }
assert (A1 : getr (ms_regs ms) (Z_to_bv 5 1) = Z_to_bv 64 (BASE + (PF_INTENT + 0x2c))).
{ b10c_rreg HS. exact (codeptr_val E (PF_INTENT + 0x2c) HEI). }
assert (Hrk : 0 <= (PF_INTENT + 0x2c) < 2 ^ 40) by (unfold PF_INTENT, AF_reac_segconf_parse_file; lia).
assert (Hrk2 : ((PF_INTENT + 0x2c)) mod 2 = 0) by (vm_compute; reflexivity).
pmkst HS.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg ?pw ?mm ?rom) ?mdx) _ =>
  change (mkCfg (mkst rg pw mm rom) mdx)
    with (cfg_at SEGS (pa_sigma SS___interceptor_trampoline_bcmp) rg mm mdx) end.
apply (b10c_bcmp B ABCMP n v pos lyc Sc Wc (ms_regs ms) (ms_mem ms) mdv cf nm o ln d gi vp val S_master
  ((PF_INTENT + 0x2c)) Q HIT b10f_in1 A10 A11 A12 A1 Hrk Hrk2).
intros rX2 mem2 md2 HI2 HP HIFF. exact (Kc rX2 mem2 md2 HI2 HIFF).
Qed.

(* site 1, from the return (0x88910): the beqz; taken -> 0x88a48 `li s3,1; j` ROLEV with s3 = 1, not taken -> 0x88914 *)
Lemma b10c_br1 : forall n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val,
  HA_ROLEV B n ->
  INV_INTENT B n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val -> b10c_ne val 1 ->
  (getr rX (Z_to_bv 5 10) = w64 0 <-> strcmp (r_low val 0 64) S_master = 0) ->
  (forall rX' memc' mdc', INV_INTENT B n v pos lyc Sc Wc rX' memc' mdc' cf nm o ln d gi vp val ->
     b10c_ne val 2 ->
     SRr SEGS Wc (cfg_at SEGS (BASE + (PF_INTENT + 0x30)) rX' memc' mdc')
       (pf_postm B v (pf_role_step cf gi nm (ln + 1) val) o ln)) ->
  SRr SEGS Wc (cfg_at SEGS (BASE + (PF_INTENT + 0x2c)) rX memc mdc)
    (pf_postm B v (pf_role_step cf gi nm (ln + 1) val) o ln).
Proof.
intros n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val HROLEV HI HNE HIFF Kc.
pose proof HI as (HB & _). pose proof HB as (_ & HFI & _). pose proof HFI as (HJ & _).
pose proof (b10c_seed (PF_INTENT + 0x2c) Wc rX memc) as HS.
set (E := Eimg (Ereg rX [])) in HS.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n0 (r : bv 5), Z.of_nat n0 = bv_unsigned r -> ew E n0 = getr rX r)
  by (intros n0 r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
unfold cfg_at, w64.
psrr_branch_pi b10c_RUNP paj_branch HS.
- (* taken *)
  b10c_br_t rX EE. pose proof (proj1 HIFF H0) as Heq.
  paj_run_to_sh b10c_RUNTO HS HJ PF_ROLEV.
  { intros a (r & Hr & _). vm_compute in Hr. destruct Hr. }
  cbn [ms_mem mkst] in HFr, HG, HF.
  b10c_clear_md.
  assert (K1 : b10c_kept v (rdW Wc memc) (rdW Wc (ms_mem ms))).
  { intros a Ha _.
    lazymatch type of HFr with frame_of ?Ex ?rs _ _ =>
      apply (kept_of_frame (segs := SEGS) Ex rs (w_H Wc) memc (ms_mem ms) (fun _ => False) HFr);
      [|exact Ha | tauto] end.
    intros b wlo whi a' Hin' _. vm_compute in Hin'. destruct Hin'. }
  assert (QK : forall r, In r b10c_RL -> getr (ms_regs ms) (Z_to_bv 5 r) = getr rX (Z_to_bv 5 r)).
  { intros r Hr. unfold b10c_RL in Hr. cbn [In] in Hr.
    repeat (destruct Hr as [<- | Hr]; [b10c_rreg HS; rewrite b10c_den_atom0; apply EE; reflexivity |]).
    destruct Hr. }
  pose proof (b10c_move B n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val (ms_regs ms) (ms_mem ms) mdv
    HI HJ K1 QK) as HI'.
  assert (H19 : getr (ms_regs ms) (Z_to_bv 5 19) = w64 (Z.of_nat 1)) by (b10c_rreg HS; reflexivity).
  pmkst HS.
  b10c_at_cut PF_ROLEV.
  exact (HROLEV fx v pos lyc Sc Wc (ms_regs ms) (ms_mem ms) mdv cf nm o ln d gi val (Z.of_nat 1)
    (b10c_to_rolev B n v pos lyc Sc Wc _ _ _ cf nm o ln d gi vp val _ HI' H19
      (b10b_role_some (r_low val 0 64) 1 S_master eq_refl HNE Heq))).
- (* not taken *)
  b10c_br_f rX EE.
  assert (Hne : strcmp (r_low val 0 64) S_master <> 0) by (intros Heq; exact (H0 (proj2 HIFF Heq))).
  paj_run_to_sh b10c_RUNTO HS HJ (PF_INTENT + 0x30).
  { intros a (r & Hr & _). vm_compute in Hr. destruct Hr. }
  cbn [ms_mem mkst] in HFr, HG, HF.
  b10c_clear_md.
  assert (K1 : b10c_kept v (rdW Wc memc) (rdW Wc (ms_mem ms))).
  { intros a Ha _.
    lazymatch type of HFr with frame_of ?Ex ?rs _ _ =>
      apply (kept_of_frame (segs := SEGS) Ex rs (w_H Wc) memc (ms_mem ms) (fun _ => False) HFr);
      [|exact Ha | tauto] end.
    intros b wlo whi a' Hin' _. vm_compute in Hin'. destruct Hin'. }
  assert (QK : forall r, In r b10c_RL -> getr (ms_regs ms) (Z_to_bv 5 r) = getr rX (Z_to_bv 5 r)).
  { intros r Hr. unfold b10c_RL in Hr. cbn [In] in Hr.
    repeat (destruct Hr as [<- | Hr]; [b10c_rreg HS; rewrite b10c_den_atom0; apply EE; reflexivity |]).
    destruct Hr. }
  pose proof (b10c_move B n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val (ms_regs ms) (ms_mem ms) mdv
    HI HJ K1 QK) as HI'.
  pmkst HS.
  b10c_at_cut (PF_INTENT + 0x30).
  exact (Kc (ms_regs ms) (ms_mem ms) mdv HI' (b10c_ne_step val 1 S_master eq_refl HNE Hne)).
Qed.

(* site 2 (0x88914): the run to the jal, INV_INTENT at the call, the bcmp step with S_slave *)
Lemma b10c_call2 : forall n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val Q,
  INV_INTENT B n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val ->
  (forall rX2 mem2 md2, INV_INTENT B n v pos lyc Sc Wc rX2 mem2 md2 cf nm o ln d gi vp val ->
     (getr rX2 (Z_to_bv 5 10) = w64 0 <-> strcmp (r_low val 0 64) S_slave = 0) ->
     SRr SEGS Wc (cfg_at SEGS (BASE + (PF_INTENT + 0x44)) rX2 mem2 md2) Q) ->
  SRr SEGS Wc (cfg_at SEGS (BASE + (PF_INTENT + 0x30)) rX memc mdc) Q.
Proof.
intros n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val Q HI Kc.
pose proof HI as (HB & _ & _ & _ & _ & _ & _ & HRG).
pose proof HB as (_ & HFI & _).
pose proof HFI as (HJ & _).
pose proof (b10c_seed (PF_INTENT + 0x30) Wc rX memc) as HS.
set (E := Eimg (Ereg rX [])) in HS.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n0 (r : bv 5), Z.of_nat n0 = bv_unsigned r -> ew E n0 = getr rX r)
  by (intros n0 r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
unfold cfg_at, w64.
paj_run_shc b10c_RUNP b10c_RUNC HS HJ.
{ intros a (r & Hr & _). vm_compute in Hr. destruct Hr. }
b10c_clear_md.
assert (K1 : b10c_kept v (rdW Wc memc) (rdW Wc (ms_mem ms))).
{ intros a Ha _.
  lazymatch type of HFr with frame_of ?Ex ?rs _ _ =>
    apply (kept_of_frame (segs := SEGS) Ex rs (w_H Wc) memc (ms_mem ms) (fun _ => False) HFr);
    [|exact Ha | tauto] end.
  intros b wlo whi a' Hin' _. vm_compute in Hin'. destruct Hin'. }
assert (QK : forall r, In r b10c_RL -> getr (ms_regs ms) (Z_to_bv 5 r) = getr rX (Z_to_bv 5 r)).
{ intros r Hr. unfold b10c_RL in Hr. cbn [In] in Hr.
  repeat (destruct Hr as [<- | Hr]; [b10c_rreg HS; rewrite b10c_den_atom0; apply EE; reflexivity |]).
  destruct Hr. }
pose proof (b10c_move B n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val (ms_regs ms) (ms_mem ms) mdv
  HI HJ K1 QK) as HIT.
assert (A10 : getr (ms_regs ms) (Z_to_bv 5 10) = w64 (pf_F v pos + PF_O_LOW)).
{ b10c_rreg HS. rewrite b10c_den_atom0, (EE 23%nat (Z_to_bv 5 23) eq_refl).
  exact (b10c_rg rX _ 23 _ HRG ltac:(unfold PF_RL, PF_RM; b10c_in)). }
assert (A11 : getr (ms_regs ms) (Z_to_bv 5 11) = w64 (seg_litA_rc S_slave)).
{ b10c_rreg HS. exact (b10c_lit E HEI 2%nat S_slave eq_refl). }
assert (A12 : getr (ms_regs ms) (Z_to_bv 5 12) = w64 (Z.of_nat (S (length S_slave)))).
{ b10c_rreg HS. first [reflexivity | vm_compute; reflexivity]. }
assert (A1 : getr (ms_regs ms) (Z_to_bv 5 1) = Z_to_bv 64 (BASE + (PF_INTENT + 0x44))).
{ b10c_rreg HS. exact (codeptr_val E (PF_INTENT + 0x44) HEI). }
assert (Hrk : 0 <= (PF_INTENT + 0x44) < 2 ^ 40) by (unfold PF_INTENT, AF_reac_segconf_parse_file; lia).
assert (Hrk2 : ((PF_INTENT + 0x44)) mod 2 = 0) by (vm_compute; reflexivity).
pmkst HS.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg ?pw ?mm ?rom) ?mdx) _ =>
  change (mkCfg (mkst rg pw mm rom) mdx)
    with (cfg_at SEGS (pa_sigma SS___interceptor_trampoline_bcmp) rg mm mdx) end.
apply (b10c_bcmp B ABCMP n v pos lyc Sc Wc (ms_regs ms) (ms_mem ms) mdv cf nm o ln d gi vp val S_slave
  ((PF_INTENT + 0x44)) Q HIT b10f_in2 A10 A11 A12 A1 Hrk Hrk2).
intros rX2 mem2 md2 HI2 HP HIFF. exact (Kc rX2 mem2 md2 HI2 HIFF).
Qed.

(* site 2, from the return (0x88928): the beqz; taken -> 0x88c80 `li s3,2; j` ROLEV with s3 = 2, not taken -> 0x8892c *)
Lemma b10c_br2 : forall n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val,
  HA_ROLEV B n ->
  INV_INTENT B n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val -> b10c_ne val 2 ->
  (getr rX (Z_to_bv 5 10) = w64 0 <-> strcmp (r_low val 0 64) S_slave = 0) ->
  (forall rX' memc' mdc', INV_INTENT B n v pos lyc Sc Wc rX' memc' mdc' cf nm o ln d gi vp val ->
     b10c_ne val 3 ->
     SRr SEGS Wc (cfg_at SEGS (BASE + (PF_INTENT + 0x48)) rX' memc' mdc')
       (pf_postm B v (pf_role_step cf gi nm (ln + 1) val) o ln)) ->
  SRr SEGS Wc (cfg_at SEGS (BASE + (PF_INTENT + 0x44)) rX memc mdc)
    (pf_postm B v (pf_role_step cf gi nm (ln + 1) val) o ln).
Proof.
intros n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val HROLEV HI HNE HIFF Kc.
pose proof HI as (HB & _). pose proof HB as (_ & HFI & _). pose proof HFI as (HJ & _).
pose proof (b10c_seed (PF_INTENT + 0x44) Wc rX memc) as HS.
set (E := Eimg (Ereg rX [])) in HS.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n0 (r : bv 5), Z.of_nat n0 = bv_unsigned r -> ew E n0 = getr rX r)
  by (intros n0 r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
unfold cfg_at, w64.
psrr_branch_pi b10c_RUNP paj_branch HS.
- (* taken *)
  b10c_br_t rX EE. pose proof (proj1 HIFF H0) as Heq.
  paj_run_to_sh b10c_RUNTO HS HJ PF_ROLEV.
  { intros a (r & Hr & _). vm_compute in Hr. destruct Hr. }
  cbn [ms_mem mkst] in HFr, HG, HF.
  b10c_clear_md.
  assert (K1 : b10c_kept v (rdW Wc memc) (rdW Wc (ms_mem ms))).
  { intros a Ha _.
    lazymatch type of HFr with frame_of ?Ex ?rs _ _ =>
      apply (kept_of_frame (segs := SEGS) Ex rs (w_H Wc) memc (ms_mem ms) (fun _ => False) HFr);
      [|exact Ha | tauto] end.
    intros b wlo whi a' Hin' _. vm_compute in Hin'. destruct Hin'. }
  assert (QK : forall r, In r b10c_RL -> getr (ms_regs ms) (Z_to_bv 5 r) = getr rX (Z_to_bv 5 r)).
  { intros r Hr. unfold b10c_RL in Hr. cbn [In] in Hr.
    repeat (destruct Hr as [<- | Hr]; [b10c_rreg HS; rewrite b10c_den_atom0; apply EE; reflexivity |]).
    destruct Hr. }
  pose proof (b10c_move B n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val (ms_regs ms) (ms_mem ms) mdv
    HI HJ K1 QK) as HI'.
  assert (H19 : getr (ms_regs ms) (Z_to_bv 5 19) = w64 (Z.of_nat 2)) by (b10c_rreg HS; reflexivity).
  pmkst HS.
  b10c_at_cut PF_ROLEV.
  exact (HROLEV fx v pos lyc Sc Wc (ms_regs ms) (ms_mem ms) mdv cf nm o ln d gi val (Z.of_nat 2)
    (b10c_to_rolev B n v pos lyc Sc Wc _ _ _ cf nm o ln d gi vp val _ HI' H19
      (b10b_role_some (r_low val 0 64) 2 S_slave eq_refl HNE Heq))).
- (* not taken *)
  b10c_br_f rX EE.
  assert (Hne : strcmp (r_low val 0 64) S_slave <> 0) by (intros Heq; exact (H0 (proj2 HIFF Heq))).
  paj_run_to_sh b10c_RUNTO HS HJ (PF_INTENT + 0x48).
  { intros a (r & Hr & _). vm_compute in Hr. destruct Hr. }
  cbn [ms_mem mkst] in HFr, HG, HF.
  b10c_clear_md.
  assert (K1 : b10c_kept v (rdW Wc memc) (rdW Wc (ms_mem ms))).
  { intros a Ha _.
    lazymatch type of HFr with frame_of ?Ex ?rs _ _ =>
      apply (kept_of_frame (segs := SEGS) Ex rs (w_H Wc) memc (ms_mem ms) (fun _ => False) HFr);
      [|exact Ha | tauto] end.
    intros b wlo whi a' Hin' _. vm_compute in Hin'. destruct Hin'. }
  assert (QK : forall r, In r b10c_RL -> getr (ms_regs ms) (Z_to_bv 5 r) = getr rX (Z_to_bv 5 r)).
  { intros r Hr. unfold b10c_RL in Hr. cbn [In] in Hr.
    repeat (destruct Hr as [<- | Hr]; [b10c_rreg HS; rewrite b10c_den_atom0; apply EE; reflexivity |]).
    destruct Hr. }
  pose proof (b10c_move B n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val (ms_regs ms) (ms_mem ms) mdv
    HI HJ K1 QK) as HI'.
  pmkst HS.
  b10c_at_cut (PF_INTENT + 0x48).
  exact (Kc (ms_regs ms) (ms_mem ms) mdv HI' (b10c_ne_step val 2 S_slave eq_refl HNE Hne)).
Qed.

(* site 3 (0x8892c): the run to the jal, INV_INTENT at the call, the bcmp step with S_tap *)
Lemma b10c_call3 : forall n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val Q,
  INV_INTENT B n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val ->
  (forall rX2 mem2 md2, INV_INTENT B n v pos lyc Sc Wc rX2 mem2 md2 cf nm o ln d gi vp val ->
     (getr rX2 (Z_to_bv 5 10) = w64 0 <-> strcmp (r_low val 0 64) S_tap = 0) ->
     SRr SEGS Wc (cfg_at SEGS (BASE + (PF_INTENT + 0x5c)) rX2 mem2 md2) Q) ->
  SRr SEGS Wc (cfg_at SEGS (BASE + (PF_INTENT + 0x48)) rX memc mdc) Q.
Proof.
intros n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val Q HI Kc.
pose proof HI as (HB & _ & _ & _ & _ & _ & _ & HRG).
pose proof HB as (_ & HFI & _).
pose proof HFI as (HJ & _).
pose proof (b10c_seed (PF_INTENT + 0x48) Wc rX memc) as HS.
set (E := Eimg (Ereg rX [])) in HS.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n0 (r : bv 5), Z.of_nat n0 = bv_unsigned r -> ew E n0 = getr rX r)
  by (intros n0 r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
unfold cfg_at, w64.
paj_run_shc b10c_RUNP b10c_RUNC HS HJ.
{ intros a (r & Hr & _). vm_compute in Hr. destruct Hr. }
b10c_clear_md.
assert (K1 : b10c_kept v (rdW Wc memc) (rdW Wc (ms_mem ms))).
{ intros a Ha _.
  lazymatch type of HFr with frame_of ?Ex ?rs _ _ =>
    apply (kept_of_frame (segs := SEGS) Ex rs (w_H Wc) memc (ms_mem ms) (fun _ => False) HFr);
    [|exact Ha | tauto] end.
  intros b wlo whi a' Hin' _. vm_compute in Hin'. destruct Hin'. }
assert (QK : forall r, In r b10c_RL -> getr (ms_regs ms) (Z_to_bv 5 r) = getr rX (Z_to_bv 5 r)).
{ intros r Hr. unfold b10c_RL in Hr. cbn [In] in Hr.
  repeat (destruct Hr as [<- | Hr]; [b10c_rreg HS; rewrite b10c_den_atom0; apply EE; reflexivity |]).
  destruct Hr. }
pose proof (b10c_move B n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val (ms_regs ms) (ms_mem ms) mdv
  HI HJ K1 QK) as HIT.
assert (A10 : getr (ms_regs ms) (Z_to_bv 5 10) = w64 (pf_F v pos + PF_O_LOW)).
{ b10c_rreg HS. rewrite b10c_den_atom0, (EE 23%nat (Z_to_bv 5 23) eq_refl).
  exact (b10c_rg rX _ 23 _ HRG ltac:(unfold PF_RL, PF_RM; b10c_in)). }
assert (A11 : getr (ms_regs ms) (Z_to_bv 5 11) = w64 (seg_litA_rc S_tap)).
{ b10c_rreg HS. exact (b10c_lit E HEI 3%nat S_tap eq_refl). }
assert (A12 : getr (ms_regs ms) (Z_to_bv 5 12) = w64 (Z.of_nat (S (length S_tap)))).
{ b10c_rreg HS. first [reflexivity | vm_compute; reflexivity]. }
assert (A1 : getr (ms_regs ms) (Z_to_bv 5 1) = Z_to_bv 64 (BASE + (PF_INTENT + 0x5c))).
{ b10c_rreg HS. exact (codeptr_val E (PF_INTENT + 0x5c) HEI). }
assert (Hrk : 0 <= (PF_INTENT + 0x5c) < 2 ^ 40) by (unfold PF_INTENT, AF_reac_segconf_parse_file; lia).
assert (Hrk2 : ((PF_INTENT + 0x5c)) mod 2 = 0) by (vm_compute; reflexivity).
pmkst HS.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg ?pw ?mm ?rom) ?mdx) _ =>
  change (mkCfg (mkst rg pw mm rom) mdx)
    with (cfg_at SEGS (pa_sigma SS___interceptor_trampoline_bcmp) rg mm mdx) end.
apply (b10c_bcmp B ABCMP n v pos lyc Sc Wc (ms_regs ms) (ms_mem ms) mdv cf nm o ln d gi vp val S_tap
  ((PF_INTENT + 0x5c)) Q HIT b10f_in3 A10 A11 A12 A1 Hrk Hrk2).
intros rX2 mem2 md2 HI2 HP HIFF. exact (Kc rX2 mem2 md2 HI2 HIFF).
Qed.

(* site 3, from the return (0x88940): the beqz; taken -> 0x88d68 `li s3,3` (falls in) ROLEV with s3 = 3, not taken -> 0x88944 *)
Lemma b10c_br3 : forall n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val,
  HA_ROLEV B n ->
  INV_INTENT B n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val -> b10c_ne val 3 ->
  (getr rX (Z_to_bv 5 10) = w64 0 <-> strcmp (r_low val 0 64) S_tap = 0) ->
  (forall rX' memc' mdc', INV_INTENT B n v pos lyc Sc Wc rX' memc' mdc' cf nm o ln d gi vp val ->
     b10c_ne val 4 ->
     SRr SEGS Wc (cfg_at SEGS (BASE + (PF_INTENT + 0x60)) rX' memc' mdc')
       (pf_postm B v (pf_role_step cf gi nm (ln + 1) val) o ln)) ->
  SRr SEGS Wc (cfg_at SEGS (BASE + (PF_INTENT + 0x5c)) rX memc mdc)
    (pf_postm B v (pf_role_step cf gi nm (ln + 1) val) o ln).
Proof.
intros n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val HROLEV HI HNE HIFF Kc.
pose proof HI as (HB & _). pose proof HB as (_ & HFI & _). pose proof HFI as (HJ & _).
pose proof (b10c_seed (PF_INTENT + 0x5c) Wc rX memc) as HS.
set (E := Eimg (Ereg rX [])) in HS.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n0 (r : bv 5), Z.of_nat n0 = bv_unsigned r -> ew E n0 = getr rX r)
  by (intros n0 r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
unfold cfg_at, w64.
psrr_branch_pi b10c_RUNP paj_branch HS.
- (* taken *)
  b10c_br_t rX EE. pose proof (proj1 HIFF H0) as Heq.
  paj_run_to_sh b10c_RUNTO HS HJ PF_ROLEV.
  { intros a (r & Hr & _). vm_compute in Hr. destruct Hr. }
  cbn [ms_mem mkst] in HFr, HG, HF.
  b10c_clear_md.
  assert (K1 : b10c_kept v (rdW Wc memc) (rdW Wc (ms_mem ms))).
  { intros a Ha _.
    lazymatch type of HFr with frame_of ?Ex ?rs _ _ =>
      apply (kept_of_frame (segs := SEGS) Ex rs (w_H Wc) memc (ms_mem ms) (fun _ => False) HFr);
      [|exact Ha | tauto] end.
    intros b wlo whi a' Hin' _. vm_compute in Hin'. destruct Hin'. }
  assert (QK : forall r, In r b10c_RL -> getr (ms_regs ms) (Z_to_bv 5 r) = getr rX (Z_to_bv 5 r)).
  { intros r Hr. unfold b10c_RL in Hr. cbn [In] in Hr.
    repeat (destruct Hr as [<- | Hr]; [b10c_rreg HS; rewrite b10c_den_atom0; apply EE; reflexivity |]).
    destruct Hr. }
  pose proof (b10c_move B n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val (ms_regs ms) (ms_mem ms) mdv
    HI HJ K1 QK) as HI'.
  assert (H19 : getr (ms_regs ms) (Z_to_bv 5 19) = w64 (Z.of_nat 3)) by (b10c_rreg HS; reflexivity).
  pmkst HS.
  b10c_at_cut PF_ROLEV.
  exact (HROLEV fx v pos lyc Sc Wc (ms_regs ms) (ms_mem ms) mdv cf nm o ln d gi val (Z.of_nat 3)
    (b10c_to_rolev B n v pos lyc Sc Wc _ _ _ cf nm o ln d gi vp val _ HI' H19
      (b10b_role_some (r_low val 0 64) 3 S_tap eq_refl HNE Heq))).
- (* not taken *)
  b10c_br_f rX EE.
  assert (Hne : strcmp (r_low val 0 64) S_tap <> 0) by (intros Heq; exact (H0 (proj2 HIFF Heq))).
  paj_run_to_sh b10c_RUNTO HS HJ (PF_INTENT + 0x60).
  { intros a (r & Hr & _). vm_compute in Hr. destruct Hr. }
  cbn [ms_mem mkst] in HFr, HG, HF.
  b10c_clear_md.
  assert (K1 : b10c_kept v (rdW Wc memc) (rdW Wc (ms_mem ms))).
  { intros a Ha _.
    lazymatch type of HFr with frame_of ?Ex ?rs _ _ =>
      apply (kept_of_frame (segs := SEGS) Ex rs (w_H Wc) memc (ms_mem ms) (fun _ => False) HFr);
      [|exact Ha | tauto] end.
    intros b wlo whi a' Hin' _. vm_compute in Hin'. destruct Hin'. }
  assert (QK : forall r, In r b10c_RL -> getr (ms_regs ms) (Z_to_bv 5 r) = getr rX (Z_to_bv 5 r)).
  { intros r Hr. unfold b10c_RL in Hr. cbn [In] in Hr.
    repeat (destruct Hr as [<- | Hr]; [b10c_rreg HS; rewrite b10c_den_atom0; apply EE; reflexivity |]).
    destruct Hr. }
  pose proof (b10c_move B n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val (ms_regs ms) (ms_mem ms) mdv
    HI HJ K1 QK) as HI'.
  pmkst HS.
  b10c_at_cut (PF_INTENT + 0x60).
  exact (Kc (ms_regs ms) (ms_mem ms) mdv HI' (b10c_ne_step val 3 S_tap eq_refl HNE Hne)).
Qed.

(* site 4 (0x88944): the run to the jal, INV_INTENT at the call, the bcmp step with S_box *)
Lemma b10c_call4 : forall n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val Q,
  INV_INTENT B n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val ->
  (forall rX2 mem2 md2, INV_INTENT B n v pos lyc Sc Wc rX2 mem2 md2 cf nm o ln d gi vp val ->
     (getr rX2 (Z_to_bv 5 10) = w64 0 <-> strcmp (r_low val 0 64) S_box = 0) ->
     getr rX2 (Z_to_bv 5 19) = w64 4 ->
     SRr SEGS Wc (cfg_at SEGS (BASE + (PF_INTENT + 0x78)) rX2 mem2 md2) Q) ->
  SRr SEGS Wc (cfg_at SEGS (BASE + (PF_INTENT + 0x60)) rX memc mdc) Q.
Proof.
intros n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val Q HI Kc.
pose proof HI as (HB & _ & _ & _ & _ & _ & _ & HRG).
pose proof HB as (_ & HFI & _).
pose proof HFI as (HJ & _).
pose proof (b10c_seed (PF_INTENT + 0x60) Wc rX memc) as HS.
set (E := Eimg (Ereg rX [])) in HS.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n0 (r : bv 5), Z.of_nat n0 = bv_unsigned r -> ew E n0 = getr rX r)
  by (intros n0 r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
unfold cfg_at, w64.
paj_run_shc b10c_RUNP b10c_RUNC HS HJ.
{ intros a (r & Hr & _). vm_compute in Hr. destruct Hr. }
b10c_clear_md.
assert (K1 : b10c_kept v (rdW Wc memc) (rdW Wc (ms_mem ms))).
{ intros a Ha _.
  lazymatch type of HFr with frame_of ?Ex ?rs _ _ =>
    apply (kept_of_frame (segs := SEGS) Ex rs (w_H Wc) memc (ms_mem ms) (fun _ => False) HFr);
    [|exact Ha | tauto] end.
  intros b wlo whi a' Hin' _. vm_compute in Hin'. destruct Hin'. }
assert (QK : forall r, In r b10c_RL -> getr (ms_regs ms) (Z_to_bv 5 r) = getr rX (Z_to_bv 5 r)).
{ intros r Hr. unfold b10c_RL in Hr. cbn [In] in Hr.
  repeat (destruct Hr as [<- | Hr]; [b10c_rreg HS; rewrite b10c_den_atom0; apply EE; reflexivity |]).
  destruct Hr. }
pose proof (b10c_move B n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val (ms_regs ms) (ms_mem ms) mdv
  HI HJ K1 QK) as HIT.
assert (A10 : getr (ms_regs ms) (Z_to_bv 5 10) = w64 (pf_F v pos + PF_O_LOW)).
{ b10c_rreg HS. rewrite b10c_den_atom0, (EE 23%nat (Z_to_bv 5 23) eq_refl).
  exact (b10c_rg rX _ 23 _ HRG ltac:(unfold PF_RL, PF_RM; b10c_in)). }
assert (A11 : getr (ms_regs ms) (Z_to_bv 5 11) = w64 (seg_litA_rc S_box)).
{ b10c_rreg HS. exact (b10c_lit E HEI 4%nat S_box eq_refl). }
assert (A12 : getr (ms_regs ms) (Z_to_bv 5 12) = w64 (Z.of_nat (S (length S_box)))).
{ b10c_rreg HS. first [reflexivity | vm_compute; reflexivity]. }
assert (A1 : getr (ms_regs ms) (Z_to_bv 5 1) = Z_to_bv 64 (BASE + (PF_INTENT + 0x78))).
{ b10c_rreg HS. exact (codeptr_val E (PF_INTENT + 0x78) HEI). }
assert (A19 : getr (ms_regs ms) (Z_to_bv 5 19) = w64 4) by (b10c_rreg HS; reflexivity).
assert (Hrk : 0 <= (PF_INTENT + 0x78) < 2 ^ 40) by (unfold PF_INTENT, AF_reac_segconf_parse_file; lia).
assert (Hrk2 : ((PF_INTENT + 0x78)) mod 2 = 0) by (vm_compute; reflexivity).
pmkst HS.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg ?pw ?mm ?rom) ?mdx) _ =>
  change (mkCfg (mkst rg pw mm rom) mdx)
    with (cfg_at SEGS (pa_sigma SS___interceptor_trampoline_bcmp) rg mm mdx) end.
apply (b10c_bcmp B ABCMP n v pos lyc Sc Wc (ms_regs ms) (ms_mem ms) mdv cf nm o ln d gi vp val S_box
  ((PF_INTENT + 0x78)) Q HIT b10f_in4 A10 A11 A12 A1 Hrk Hrk2).
intros rX2 mem2 md2 HI2 HP HIFF. apply (Kc rX2 mem2 md2 HI2 HIFF).
rewrite (HP 19 ltac:(unfold acallee_saved; lia)). exact A19.
Qed.

(* site 4, from the return (0x8895c): the beqz; taken -> ROLEV with s3 = 4, not taken -> BAD 0x88960 *)
Lemma b10c_br4 : forall n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val,
  HA_ROLEV B n -> HA_BAD B n ->
  INV_INTENT B n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val -> b10c_ne val 4 ->
  (getr rX (Z_to_bv 5 10) = w64 0 <-> strcmp (r_low val 0 64) S_box = 0) ->
  getr rX (Z_to_bv 5 19) = w64 4 ->
  
  SRr SEGS Wc (cfg_at SEGS (BASE + (PF_INTENT + 0x78)) rX memc mdc)
    (pf_postm B v (pf_role_step cf gi nm (ln + 1) val) o ln).
Proof.
intros n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val HROLEV HBAD HI HNE HIFF H4.
pose proof HI as (HB & _). pose proof HB as (_ & HFI & _). pose proof HFI as (HJ & _).
pose proof (b10c_seed (PF_INTENT + 0x78) Wc rX memc) as HS.
set (E := Eimg (Ereg rX [])) in HS.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n0 (r : bv 5), Z.of_nat n0 = bv_unsigned r -> ew E n0 = getr rX r)
  by (intros n0 r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
unfold cfg_at, w64.
psrr_branch_pi b10c_RUNP paj_branch HS.
- (* taken *)
  b10c_br_t rX EE. pose proof (proj1 HIFF H0) as Heq.
  paj_run_to_sh b10c_RUNTO HS HJ PF_ROLEV.
  { intros a (r & Hr & _). vm_compute in Hr. destruct Hr. }
  cbn [ms_mem mkst] in HFr, HG, HF.
  b10c_clear_md.
  assert (K1 : b10c_kept v (rdW Wc memc) (rdW Wc (ms_mem ms))).
  { intros a Ha _.
    lazymatch type of HFr with frame_of ?Ex ?rs _ _ =>
      apply (kept_of_frame (segs := SEGS) Ex rs (w_H Wc) memc (ms_mem ms) (fun _ => False) HFr);
      [|exact Ha | tauto] end.
    intros b wlo whi a' Hin' _. vm_compute in Hin'. destruct Hin'. }
  assert (QK : forall r, In r b10c_RL -> getr (ms_regs ms) (Z_to_bv 5 r) = getr rX (Z_to_bv 5 r)).
  { intros r Hr. unfold b10c_RL in Hr. cbn [In] in Hr.
    repeat (destruct Hr as [<- | Hr]; [b10c_rreg HS; rewrite b10c_den_atom0; apply EE; reflexivity |]).
    destruct Hr. }
  pose proof (b10c_move B n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val (ms_regs ms) (ms_mem ms) mdv
    HI HJ K1 QK) as HI'.
  assert (H19 : getr (ms_regs ms) (Z_to_bv 5 19) = w64 (Z.of_nat 4)) by (b10c_rreg HS; rewrite b10c_den_atom0, (EE 19%nat (Z_to_bv 5 19) eq_refl); exact H4).
  pmkst HS.
  b10c_at_cut PF_ROLEV.
  exact (HROLEV fx v pos lyc Sc Wc (ms_regs ms) (ms_mem ms) mdv cf nm o ln d gi val (Z.of_nat 4)
    (b10c_to_rolev B n v pos lyc Sc Wc _ _ _ cf nm o ln d gi vp val _ HI' H19
      (b10b_role_some (r_low val 0 64) 4 S_box eq_refl HNE Heq))).
- (* not taken *)
  b10c_br_f rX EE.
  assert (Hne : strcmp (r_low val 0 64) S_box <> 0) by (intros Heq; exact (H0 (proj2 HIFF Heq))).
  paj_run_to_sh b10c_RUNTO HS HJ (PF_BAD).
  { intros a (r & Hr & _). vm_compute in Hr. destruct Hr. }
  cbn [ms_mem mkst] in HFr, HG, HF.
  b10c_clear_md.
  assert (K1 : b10c_kept v (rdW Wc memc) (rdW Wc (ms_mem ms))).
  { intros a Ha _.
    lazymatch type of HFr with frame_of ?Ex ?rs _ _ =>
      apply (kept_of_frame (segs := SEGS) Ex rs (w_H Wc) memc (ms_mem ms) (fun _ => False) HFr);
      [|exact Ha | tauto] end.
    intros b wlo whi a' Hin' _. vm_compute in Hin'. destruct Hin'. }
  assert (QK : forall r, In r b10c_RL -> getr (ms_regs ms) (Z_to_bv 5 r) = getr rX (Z_to_bv 5 r)).
  { intros r Hr. unfold b10c_RL in Hr. cbn [In] in Hr.
    repeat (destruct Hr as [<- | Hr]; [b10c_rreg HS; rewrite b10c_den_atom0; apply EE; reflexivity |]).
    destruct Hr. }
  pose proof (b10c_move B n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val (ms_regs ms) (ms_mem ms) mdv
    HI HJ K1 QK) as HI'.
  pmkst HS.
  b10c_at_cut (PF_BAD).
  exact (HBAD fx v pos lyc Sc Wc (ms_regs ms) (ms_mem ms) mdv cf nm o ln d gi vp val
    (b10c_to_bad B n v pos lyc Sc Wc _ _ _ cf nm o ln d gi vp val HI'
      (b10b_role_none _ (b10c_ne_all val (b10c_ne_step val 4 S_box eq_refl HNE Hne))))).
Qed.

(* ---------- the piece: INTENT -> ROLEV / BAD through the five sites ---------- *)
Lemma b10c_intent : forall n, HA_ROLEV B n -> HA_BAD B n -> H_INTENT (fx := fx) B n.
Proof.
intros n HROLEV HBAD v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val HI.
apply (b10c_call0 n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val _ HI).
intros rX1 mem1 md1 HI1 HF1.
apply (b10c_br0 n v pos lyc Sc Wc rX1 mem1 md1 cf nm o ln d gi vp val HROLEV HI1 (b10c_ne0 val) HF1).
intros rX2 mem2 md2 HI2 HN2.
apply (b10c_call1 n v pos lyc Sc Wc rX2 mem2 md2 cf nm o ln d gi vp val _ HI2).
intros rX3 mem3 md3 HI3 HF3.
apply (b10c_br1 n v pos lyc Sc Wc rX3 mem3 md3 cf nm o ln d gi vp val HROLEV HI3 HN2 HF3).
intros rX4 mem4 md4 HI4 HN4.
apply (b10c_call2 n v pos lyc Sc Wc rX4 mem4 md4 cf nm o ln d gi vp val _ HI4).
intros rX5 mem5 md5 HI5 HF5.
apply (b10c_br2 n v pos lyc Sc Wc rX5 mem5 md5 cf nm o ln d gi vp val HROLEV HI5 HN4 HF5).
intros rX6 mem6 md6 HI6 HN6.
apply (b10c_call3 n v pos lyc Sc Wc rX6 mem6 md6 cf nm o ln d gi vp val _ HI6).
intros rX7 mem7 md7 HI7 HF7.
apply (b10c_br3 n v pos lyc Sc Wc rX7 mem7 md7 cf nm o ln d gi vp val HROLEV HI7 HN6 HF7).
intros rX8 mem8 md8 HI8 HN8.
apply (b10c_call4 n v pos lyc Sc Wc rX8 mem8 md8 cf nm o ln d gi vp val _ HI8).
intros rX9 mem9 md9 HI9 HF9 H49.
exact (b10c_br4 n v pos lyc Sc Wc rX9 mem9 md9 cf nm o ln d gi vp val HROLEV HBAD HI9 HN8 HF9 H49).
Qed.
End x.

(* the piece of pf_seg_B10b_k.v at every FP state *)
Theorem pb10_c_ok : PB10_C B.
Proof. intros f0 n HR HB. exact (b10c_intent (fx := f0) n HR HB). Qed.
End d.
