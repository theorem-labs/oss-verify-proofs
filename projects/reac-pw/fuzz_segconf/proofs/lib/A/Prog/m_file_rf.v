(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC95.v:145-147;
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC9z.v:176-178; projects/cgif/cgif_file_fuzzer/proofs/lib/A/AChd.v:180-183, 357-361,
   for libreac/fuzz_identity's ASan build (lib/A). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/reac_box_catalogue.v, with its module paths and numbers changed; 204 of its 254 lines of code are new or changed and 319 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/A/Prog/check_ignore.v, with its module paths and module names changed; 325 of its 356 lines of code are new or changed and 223 lines of the source are left out. *)
(* m_file on fuzz_segconf.asan (image A, 0x85ebc): the m_refuse call step every segment walk of m_file shares
   (the ONE shared copy, the m_file cut-statement lane's decision (c) at m_file_m.v change 3), stated over m_file_m.v's cut predicates.
   The LONGP / KKNOCKP segment lane of the G2 walk owner's G2.
   mf_refuse_step: m_file's eight `jal m_refuse` sites (0x861ec LONGP, 0x863ac KEYA, 0x8653c / 0x86bd4 HDRA, 0x86b14
   HDRB, 0x867a8 KROLE, 0x86bf4 / 0x86ccc KKNOCKP, KMOD, KIGNP; MF-CUTS-A.md section 4), at the listing offset j of
   the `jal` (slot `PCall SS_m_refuse 1`): from the cut facts there (mf_cx, m_file_k.v's mf_corek: the block holding mcc and
   the pending knock flag, mf_cells, mf_np, sp / gp / tp / s0, mf_loop at the lines consumed `line`, a0 = c,
   a1 = line + 1, the number of the line being refused), m_refuse_contract
   (lib/A/Prog/m_refuse_c.v) taken through PaFx.cl_callSF, the walk goes on at j + 4 at the FP state fx1 the call
   returns, with mf_ls / mf_core / mf_cells / mf_np / mf_loop re-established (mf_core for the block's new model
   m_refuse mcc (line + 1) knock), and every callee-saved register as at the `jal` (mf_regs_at_kept rebuilds
   mf_regs_at). mf_loop is taken at a model mcl whose refused counter is mcc's (mcl = mcc at every site but HDRB's
   0x86bd4, where the block already holds overflow + 1 and mcl is the line head's model), and is given back at mcl:
   the next line's mf_loop comes from m_file_k.v's mf_loop_next.
   mf_refuse_core is the call itself: mf_jal_step (the `jal`), cl_callSF with the callee's afn_pre from the walk's
   journal and the frame chain extended by m_file's own record (m_file_k.v's mf_chain_k, as fuzz_command's
   check_reply_s2.v cr2_chain), m_refuse_pre from the block facts, and m_refuse_W inside M_FILE_FP of the final
   model because kept never shrinks along the lines (the caller gives
   `length (mc_kept (m_refuse mcc (line + 1) knock)) <= length (mc_kept (mf_final v))`; m_file_mdl.v's
   mf_kept_le_refuse proves it from the cut's model equation). mf_refuse_step0 adds the cut facts after the call from
   the callee's kept set (m_file_k.v's mf_keep_win_k); mf_refuse_step is it at a site with the next-line slot fact
   mf_np (every site but LONGP's 0x861ec, which uses mf_refuse_step0).
   Section hypotheses, from the shared list of m_file_m.v change 3 (decision (a), amended), verbatim: LAWS (a Let),
   SIGP, SSP, RELRO (the read-only window inside the image, for m_file_k.v's mf_rod_now_k), and M_REFUSE
   (m_refuse_contract at every FP state at its listing entry and SegInstA's STK_m_refuse; this file fixes its
   text). *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI00 YI04 YI09 YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal SegSyms SegList SegPa SegPaLib PaCall PaDenot.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaLibG PaLibF PaLibH PaSB PaCallRun.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaNoChain PaArt PaFx SegPgBase SegBase SegObj SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require SegInstA.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import m_file_c m_file_m m_refuse_c m_file_k.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

(* image A's pure parameters (lib/A/Prog/SegInstA.v), local names of this file (as m_file_m.v's) *)
#[local] Notation MF_STK := SegInstA.STK_m_file.
#[local] Notation RLO := SegInstA.RLO_A.
#[local] Notation RHI := SegInstA.RHI_A.
#[local] Notation lit := SegInstA.seg_litA_fz.
#[local] Notation GOTW := SegInstA.gotwA.
#[local] Notation GUARD := SegInstA.guardA.

(* the bytes m_refuse may write (m_refuse_contract's sa_kept set) *)
Definition mf_refuse_E (c : Z) (mc : mconf) (a : Z) : Prop :=
  (Z.of_nat (length (mc_kept mc)) < 8 /\
   seg_spec.kept_addr c (length (mc_kept mc)) <= a <
   seg_spec.kept_addr c (length (mc_kept mc)) + seg_spec.MC_KEPT_LEN) \/
  (Z.of_nat (length (mc_kept mc)) < 8 /\ c + seg_spec.MC_NKEPT <= a < c + seg_spec.MC_NKEPT + 4) \/
  c + seg_spec.MC_REFUSED <= a < c + seg_spec.MC_REFUSED + 4.

(* the link register after `jal ra, f` and every other register as before *)
Lemma mf_getr_upd1 : forall (regs : bvmap 5 word) v (r : bv 5), r <> 1%bv -> getr (regupd regs 1%bv v) r = getr regs r.
Proof. intros regs v r Hr. unfold getr. destruct (bv_eqb r 0); [reflexivity|]. apply regupd_other. exact Hr. Qed.
Lemma mf_getr_upd1_same : forall (regs : bvmap 5 word) v, getr (regupd regs 1%bv v) 1%bv = v.
Proof. intros regs v. unfold getr. cbn. apply regupd_same. Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

(* the registers of a site with mf_regs_at: the four the call needs, and mf_regs_at again from the callee-saved
   registers the call keeps *)
Lemma mf_regs_at_call : forall B v lyc pos regs1, mf_regs_at B v lyc pos regs1 ->
  getr regs1 2 = w64 (mf_s1 (mv_sp v)) /\ getr regs1 3 = w64 (as_gp B) /\ getr regs1 4 = w64 (as_tp B) /\
  getr regs1 8 = w64 (mv_sp v).
Proof. intros B v lyc pos regs1 (R2 & R3 & R4 & R8 & _). auto. Qed.
Lemma mf_regs_at_kept : forall B v lyc pos regs1 regs2, mf_regs_at B v lyc pos regs1 ->
  (forall r, acallee_saved r -> getr regs2 (Z_to_bv 5 r) = getr regs1 (Z_to_bv 5 r)) ->
  mf_regs_at B v lyc pos regs2.
Proof.
intros B v lyc pos regs1 regs2 (R2 & R3 & R4 & R8 & R9 & R18 & R19 & R25 & R26) K.
assert (K2 : getr regs2 2 = getr regs1 2) by exact (K 2 ltac:(unfold acallee_saved; lia)).
assert (K3 : getr regs2 3 = getr regs1 3) by exact (K 3 ltac:(unfold acallee_saved; lia)).
assert (K4 : getr regs2 4 = getr regs1 4) by exact (K 4 ltac:(unfold acallee_saved; lia)).
assert (K8 : getr regs2 8 = getr regs1 8) by exact (K 8 ltac:(unfold acallee_saved; lia)).
assert (K9 : getr regs2 9 = getr regs1 9) by exact (K 9 ltac:(unfold acallee_saved; lia)).
assert (K18 : getr regs2 18 = getr regs1 18) by exact (K 18 ltac:(unfold acallee_saved; lia)).
assert (K19 : getr regs2 19 = getr regs1 19) by exact (K 19 ltac:(unfold acallee_saved; lia)).
assert (K25 : getr regs2 25 = getr regs1 25) by exact (K 25 ltac:(unfold acallee_saved; lia)).
assert (K26 : getr regs2 26 = getr regs1 26) by exact (K 26 ltac:(unfold acallee_saved; lia)).
unfold mf_regs_at. rewrite K2, K3, K4, K8, K9, K18, K19, K25, K26.
auto 10.
Qed.

(* `jal ra, f` at listing offset j (the slot `PCall s 1`): one machine step to f's entry, ra = BASE + j + 4, the
   memory unchanged (fuzz_command's SegPaLib.SRr_jalr_call_pi for a direct jal; the slot's instruction from the
   listing check, PaTable.pi_slot_check) *)
Lemma mf_jal_step : forall (W : world SEGS) (regs : bvmap 5 word) mem md Q j s,
  plookup pl_tpi j = Some (PCall s 1%bv) -> j + 4 < 2 ^ 40 ->
  (forall mat', SRr SEGS W (mkCfg (mkst (regupd regs 1%bv (Z_to_bv 64 (BASE + (j + 4)))) (Z_to_bv 64 (pa_sigma s)) mem
    (seg_rom SEGS)) (with_vm_backing (m_vm_lazy md) mat' md)) Q) ->
  SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + j)) mem (seg_rom SEGS)) md) Q.
Proof.
intros W regs mem md Q j s Hpl Hj40 HK.
pose proof pa_B_ok as (HB0 & HB1 & HB4).
assert (Hpl' := Hpl). rewrite <- pl_tpi_eq in Hpl'.
destruct (cert_slot ssym (clookup pa_tbl) VAL pa_sigma seg_listing pa_cert _ _ Hpl') as (Hck & Hk0 & Hk4).
unfold pi_slot_check in Hck.
destruct (clookup pa_tbl (VAL A_TEXT + j)) as [wz|] eqn:Hl; [|discriminate Hck].
destruct (decode_any (Z_to_bv 32 wz)) as [[i isz]|] eqn:Hdec; [|discriminate Hck].
apply andb_prop in Hck as [Hsz Hck]. apply Z.eqb_eq in Hsz. subst isz.
destruct i; try discriminate Hck.
apply andb_prop in Hck as [Hck Ht]. apply andb_prop in Hck as [Hrd Hnz]. apply reg_eqb_eq in Hrd. subst rd.
apply Z.eqb_eq in Ht.
pose proof (pa_val_range A_TEXT) as HBr.
eapply (SRr_step SEGS pa_wx W); [reflexivity | |].
- rewrite restrict_mkst_fx.
  eapply (step_jal_link SEGS _ _ _ _ (Z_to_bv 32 wz) 1%bv imm).
  + exact (pa_fetch_ok _ _ Hl).
  + eapply not_ecall_of_decode; [exact Hdec | discriminate].
  + exact Hdec.
- intros model' Hsame. rewrite (same_but_materialized_wvb md model' Hsame).
  cbn [ms_regs ms_mem mkst]. rewrite unrestrict_mkst_mrestrict.
  replace (bv_eqb (1%bv : bv 5) 0) with false by reflexivity.
  assert (Ev : v_addi (Z_to_bv 64 (BASE + j)) 4 = Z_to_bv 64 (BASE + (j + 4))).
  { unfold v_addi. rewrite unsigned_lit_small by lia. f_equal. lia. }
  assert (Et : btgt (Z_to_bv 64 (BASE + j)) (bv_signed imm) = Z_to_bv 64 (pa_sigma s)).
  { unfold btgt, v_addi. rewrite unsigned_lit_small by lia. rewrite <- Ht. unfold zcanon, M64.
    apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
    rewrite Z.mod_mod by lia. reflexivity. }
  rewrite Ev, Et. exact (HK _).
Qed.

Section e.
Variable B : asyms.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
(* the shared hypotheses (m_file_m.v change 3, decision (a), amended) this file needs, verbatim *)
Hypothesis SIGP : seg_sig_prog.
Hypothesis SSP : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md -> sa_ssp (rdW W mem) SegInstA.gotwA SegInstA.guardA.
Hypothesis RELRO : forall a, SegInstA.RLO_A <= a < SegInstA.RHI_A -> in_img SEGS a.
(* the callee, at every FP state (the shared list's M_REFUSE) *)
Hypothesis M_REFUSE : forall fx0 : YK11.FPState, m_refuse_contract (fx := fx0) SEGS B (BASE + AF_m_refuse)
  SegInstA.STK_m_refuse SegInstA.RLO_A SegInstA.RHI_A SegInstA.seg_litA_fz SegInstA.gotwA SegInstA.guardA.


(* the call itself, from the facts the callee asks at the `jal`: the jal step, cl_callSF with m_refuse_contract, and
   the walk at j + 4 at the returned FP state from the callee's journal, post and kept set *)
Lemma mf_refuse_core : forall v lyc Sc Wc (regs1 : bvmap 5 word) memc mdc pos (mcc : mconf) (knock : bool)
  (line : Z) (j : Z) ch1,
  mf_cx B v -> sa_frm0 ->
  ajournal SEGS B MF_STK (mv_sp v) (M_FILE_FP (mv_c v) (mv_k0 v) (mf_final v)) (mv_ly v) (mv_S v) (mv_W v)
    (mv_mem v) (mv_md v) [(1, pos)] lyc Sc Wc memc mdc 0 ->
  Permutation (ablocks B lyc Sc) (ablocks B (mv_ly v) (mv_S v)) ->
  sa_mconfp knock (rdW Wc memc) (mv_c v) mcc -> sa_addr (rdW Wc memc) (mv_c v) seg_spec.SEG_M_SIZE ->
  sa_tail (rdW Wc memc) (mv_c v + seg_spec.SEG_M_SIZE - 1) ->
  achain lyc (rdW Wc memc) (mf_s1 (mv_sp v)) (mv_sp v) ch1 ->
  arodata_okP SEGS RLO RHI B (rdW Wc memc) ->
  (forall x, In x M_REFUSE_LITS -> sa_lit SEGS B (rdW Wc memc) (lit x) x) ->
  getr regs1 2 = w64 (mf_s1 (mv_sp v)) -> getr regs1 3 = w64 (as_gp B) -> getr regs1 4 = w64 (as_tp B) ->
  getr regs1 8 = w64 (mv_sp v) ->
  plookup pl_tpi j = Some (PCall SS_m_refuse 1%bv) -> j + 4 < 2 ^ 40 ->
  getr regs1 10 = w64 (mv_c v) -> getr regs1 11 = w64 (line + 1) -> 0 <= line + 1 <= 65536 ->
  mc_refused mcc + 1 < 2 ^ 32 ->
  (mv_k0 v <= length (mc_kept mcc))%nat ->
  (length (mc_kept (m_refuse mcc (line + 1) knock)) <= length (mc_kept (mf_final v)))%nat ->
  (forall (fx1 : YK11.FPState) ly2 S2 (W2 : world SEGS) (regs2 : bvmap 5 word) mem2 md2,
    fxrel fx fx1 -> wle Wc W2 ->
    ajournal SEGS B MF_STK (mv_sp v) (M_FILE_FP (mv_c v) (mv_k0 v) (mf_final v)) (mv_ly v) (mv_S v) (mv_W v)
      (mv_mem v) (mv_md v) [(1, pos)] ly2 S2 W2 mem2 md2 0 ->
    sa_noalloc B lyc Sc ly2 S2 ->
    (forall r, acallee_saved r -> getr regs2 (Z_to_bv 5 r) = getr regs1 (Z_to_bv 5 r)) ->
    (forall a, 0 <= a < 2 ^ 64 -> ~ (mf_s1 (mv_sp v) - SegInstA.STK_m_refuse <= a < mf_s1 (mv_sp v)) ->
     ~ mf_refuse_E (mv_c v) mcc a -> rdW W2 mem2 a = rdW Wc memc a) ->
    sa_mconf (rdW W2 mem2) (mv_c v) (m_refuse mcc (line + 1) knock) ->
    mf_at (fx := fx1) B v W2 regs2 mem2 md2 (j + 4)) ->
  mf_at B v Wc regs1 memc mdc j.
Proof.
intros v lyc Sc Wc regs1 memc mdc pos mcc knock line j ch1 CX FRM HJ HPm MC ADDR TAIL CH ROD LITS
  R2 R3 R4 R8 Hslot Hj40 R10 R11 Hline Href Hk0 HKEPT K.
unfold mf_at.
pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HSTK : SegInstA.STK_m_file = 8560) by reflexivity.
assert (HSTK1 : SegInstA.STK_m_refuse = 8240) by reflexivity.
destruct (mf_s1_facts B v CX) as (Hs1 & Hs32 & _).
destruct (mf_sp0 B v CX) as (Sp1 & Sp2 & Sp3). rewrite HSTK in Sp1.
pose proof CX as (HPRE & _ & _ & _ & _ & _ & _ & _ & H10e & Hc64 & _ & _ & _ & _ & HMP & HEV).
pose proof HMP as (Hc0 & Hc16 & _ & HHEAP & _).
pose proof HJ as (HAR & _ & _ & _ & _ & _ & Hnev & _).
destruct (mf_c_entry B v CX) as (bc & mbc & Hbc & Hbc1 & Hbc2 & Hbc3 & Hbc4 & Hbc5).
assert (Hbc' : In (bc, mbc) (ablocks B lyc Sc)) by (apply (Permutation_in _ (Permutation_sym HPm)); exact Hbc).
assert (Hj : 0 <= j /\ j mod 4 = 0).
{ pose proof Hslot as Hs'. rewrite <- pl_tpi_eq in Hs'.
  destruct (cert_slot ssym (clookup pa_tbl) VAL pa_sigma seg_listing pa_cert _ _ Hs') as (_ & Hk0' & Hk4). lia. }
(* the jal *)
apply (mf_jal_step Wc regs1 memc mdc _ j SS_m_refuse Hslot Hj40). intros mat'.
assert (SIGR : pa_sigma SS_m_refuse = BASE + AF_m_refuse).
{ rewrite (SIGP SS_m_refuse) by (unfold seg_prog_syms; cbn [In]; tauto). f_equal; try (vm_compute; reflexivity). }
rewrite SIGR.
set (regsc := regupd regs1 1%bv (Z_to_bv 64 (BASE + (j + 4)))).
set (mdc' := with_vm_backing (m_vm_lazy mdc) mat' mdc).
pose proof (ajournal_materialize SEGS B LAWS Hsegs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mat' HJ) as HJ'. fold mdc' in HJ'.
assert (GR : forall r : bv 5, r <> 1%bv -> getr regsc r = getr regs1 r) by (intros r Hr; apply mf_getr_upd1; exact Hr).
assert (Q1 : getr regsc 1 = Z_to_bv 64 (BASE + (j + 4))) by apply mf_getr_upd1_same.
assert (Q2 : getr regsc 2 = w64 (mf_s1 (mv_sp v))) by (rewrite GR by discriminate; exact R2).
assert (Q3 : getr regsc 3 = w64 (as_gp B)) by (rewrite GR by discriminate; exact R3).
assert (Q4 : getr regsc 4 = w64 (as_tp B)) by (rewrite GR by discriminate; exact R4).
assert (Q8 : getr regsc 8 = w64 (mv_sp v)) by (rewrite GR by discriminate; exact R8).
assert (Q10 : getr regsc 10 = w64 (mv_c v)) by (rewrite GR by discriminate; exact R10).
assert (Q11 : getr regsc 11 = w64 (line + 1)) by (rewrite GR by discriminate; exact R11).
assert (Hsp : spZ regsc = mv_sp v + (mf_s1 (mv_sp v) - mv_sp v)).
{ unfold spZ. rewrite Q2. unfold w64. rewrite unsigned_lit_small by lia. lia. }
assert (Ho16 : (mf_s1 (mv_sp v) - mv_sp v) mod 16 = 0).
{ destruct Hs1 as [E1|E1]; rewrite E1; [replace (mv_sp v - 288 - mv_sp v) with (-288) by lia
  | replace (mv_sp v - 304 - mv_sp v) with (-304) by lia]; reflexivity. }
unfold MF_POST.
eapply srr_after_callF.
{ eapply (cl_callSF B LAWS Wc regsc memc (Z_to_bv 64 (BASE + AF_m_refuse)) MF_STK (mv_sp v)
    (M_FILE_FP (mv_c v) (mv_k0 v) (mf_final v)) (mv_ly v) (mv_S v) (mv_W v) (mv_mem v) (mv_md v) [(1, pos)] lyc Sc
    mdc' 0 SegInstA.STK_m_refuse (m_refuse_W (mv_c v) mcc) EV_m_refuse (mf_s1 (mv_sp v) - mv_sp v)
    (Z_to_bv 64 (BASE + (j + 4))) ch1
    (fun ly2 S2 W2 regs2 mem2 md2 =>
       sa_mconf (rdW W2 mem2) (mv_c v) (m_refuse mcc (line + 1) knock) /\
       sa_kept SEGS Wc memc W2 mem2 regsc SegInstA.STK_m_refuse
         (fun a =>
          (Z.of_nat (length (mc_kept mcc)) < 8 /\
           seg_spec.kept_addr (mv_c v) (length (mc_kept mcc)) <= a <
           seg_spec.kept_addr (mv_c v) (length (mc_kept mcc)) + seg_spec.MC_KEPT_LEN) \/
          (Z.of_nat (length (mc_kept mcc)) < 8 /\ mv_c v + seg_spec.MC_NKEPT <= a < mv_c v + seg_spec.MC_NKEPT + 4) \/
          mv_c v + seg_spec.MC_REFUSED <= a < mv_c v + seg_spec.MC_REFUSED + 4) /\
       sa_noalloc B lyc Sc ly2 S2)
    HJ' Hsp Ho16).
  - destruct Hs1 as [E1|E1]; rewrite E1; lia.
  - lia.
  - rewrite HSTK, HSTK1. destruct Hs1 as [E1|E1]; rewrite E1; lia.
  - exact Q3.
  - exact Q4.
  - exact Q1.
  - apply ret_ok_codeptr_v; [lia|]. pose proof (Z.div_mod j 4 ltac:(lia)). replace (j + 4) with (2 * (2 * (j / 4) + 2)) by lia.
    rewrite Z.mul_comm. apply Z_mod_mult.
  - rewrite unsigned_lit_small by lia. lia.
  - replace (mv_sp v + (mf_s1 (mv_sp v) - mv_sp v)) with (mf_s1 (mv_sp v)) by lia.
    unfold s0Z. rewrite Q8. unfold w64. rewrite unsigned_lit_small by lia. exact CH.
  - intros HPRE1. eapply SRr_mono.
    + apply (M_REFUSE fx lyc Sc Wc regsc memc mdc' ch1 (mv_c v) (line + 1) mcc knock HPRE1 ROD Q10 Hc64 Q11).
      * unfold m_refuse_pre. split; [exact Hc0|]. split; [exact Hc16|].
        split; [destruct HHEAP as (b0 & m0 & Hb0 & Hb01 & Hb02); exists b0, m0;
          split; [apply (Permutation_in _ (Permutation_sym HPm)); exact Hb0 | lia]|].
        split; [exact ADDR|]. split; [exact MC|]. split; [exact TAIL|]. split; [lia|]. split; [lia|].
        split; [exact FRM|]. split; [exact (SSP _ _ _ _ _ HAR)|]. exact LITS.
      * unfold EV_m_refuse, EV_m_file in *. lia.
    + cbv beta. intros W2 c2 _ (fx1 & ly2 & S2 & regs2 & mem2 & md2 & Hc & Hf1 & Hf2 & HJc & HPr & HKc).
      exists fx1, ly2, S2, regs2, mem2, md2. rewrite Q1 in Hc.
      split; [exact Hc|]. split; [exact Hf1|]. split; [exact Hf2|]. split; [exact HJc|]. split; [exact HPr | exact HKc].
  - intros a Ha.
    assert (Hlen : Z.of_nat (length (mc_kept mcc)) < 8 ->
      length (mc_kept (m_refuse mcc (line + 1) knock)) = S (length (mc_kept mcc))).
    { intros Hl8. unfold m_refuse. cbv zeta. cbn [mc_kept]. rewrite (proj2 (Z.ltb_lt _ _) Hl8).
      rewrite length_app. cbn [length]. lia. }
    assert (HIN : inFP (M_FILE_FP (mv_c v) (mv_k0 v) (mf_final v)) a /\ mv_c v <= a < mv_c v + seg_spec.SEG_M_SIZE).
    { destruct Ha as (r & Hr & Hra). unfold m_refuse_W in Hr. apply in_app_iff in Hr.
      destruct Hr as [Hr | [<- | []]].
      - destruct (Z.of_nat (length (mc_kept mcc)) <? 8) eqn:E8; [|destruct Hr].
        apply Z.ltb_lt in E8. specialize (Hlen E8).
        destruct Hr as [<- | [<- | []]]; cbn [fst snd] in Hra.
        + split.
          * eexists; split; [cbn [M_FILE_FP In]; right; right; left; reflexivity|]. cbn [fst snd].
            unfold seg_spec.kept_addr, seg_spec.MC_KEPT, seg_spec.MC_KEPT_LEN in *. lia.
          * unfold seg_spec.kept_addr, seg_spec.MC_KEPT, seg_spec.MC_KEPT_LEN, seg_spec.SEG_M_SIZE in *. lia.
        + split.
          * eexists; split; [cbn [M_FILE_FP In]; right; right; right; right; left; reflexivity|]. cbn [fst snd].
            unfold seg_spec.MC_NKEPT, seg_spec.MC_READING in *. lia.
          * unfold seg_spec.MC_NKEPT, seg_spec.SEG_M_SIZE in *. lia.
      - cbn [fst snd] in Hra. split.
        + eexists; split; [cbn [M_FILE_FP In]; right; left; reflexivity|]. cbn [fst snd].
          unfold seg_spec.MC_N, seg_spec.MC_REFUSED in *. lia.
        + unfold seg_spec.MC_REFUSED, seg_spec.SEG_M_SIZE in *. lia. }
    left. split; [exact (proj1 HIN)|]. exists bc, mbc. split; [exact Hbc'|].
    pose proof (proj2 HIN). unfold seg_spec.SEG_M_SIZE in *. lia. }
cbv beta. intros fx1 ly2 S2 W2 regs2 mem2 md2 Hle Hfx (AJo & AJi & HPr & MC2 & KEPT2 & NOAL2).
apply (K fx1 ly2 S2 W2 regs2 mem2 md2 Hfx Hle).
- exact AJo.
- exact NOAL2.
- intros r Hr. rewrite (HPr r Hr). apply GR.
  assert (Hc : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
    r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by (unfold acallee_saved in Hr; lia).
  intros E. apply (f_equal bv_unsigned) in E.
  repeat (destruct Hc as [-> | Hc]; [vm_compute in E; discriminate E |]). subst r. vm_compute in E. discriminate E.
- intros a Ha Hw HE. apply KEPT2; [exact Ha | rewrite Hsp; replace (mv_sp v + (mf_s1 (mv_sp v) - mv_sp v)) with (mf_s1 (mv_sp v)) by lia; exact Hw | exact HE].
- exact MC2.
Qed.
(* m_refuse from the `jal` at listing offset j: the walk goes on at j + 4, at the FP state fx1 the call returns.
   Of the registers the call needs only sp = s1, gp, tp and s0 = sp0 (the frame chain): a site where s8 or s10 is
   borrowed (KROLE 0x867a8, HDRA 0x8653c) uses it as is; every callee-saved register comes back as it was at the
   `jal` (mf_regs_at_call / mf_regs_at_kept above for a site with mf_regs_at). *)
Definition MF_REFUSE_STEP : Prop :=
forall v lyc Sc Wc (regs1 : bvmap 5 word) memc mdc pos lowsh (mcc mcl : mconf) (knock : bool)
  (cur : option nat) (line p : Z) (rest : list Z) (np : Z) (j : Z),
  mf_cx B v -> mf_ls v lyc Sc -> sa_frm0 ->
  mf_corek B knock v lyc Sc Wc memc mdc pos lowsh mcc -> mf_cells v lyc pos memc Wc cur -> mf_np v memc Wc np ->
  getr regs1 2 = w64 (mf_s1 (mv_sp v)) -> getr regs1 3 = w64 (as_gp B) -> getr regs1 4 = w64 (as_tp B) ->
  getr regs1 8 = w64 (mv_sp v) ->
  mf_loop v Wc memc mcl cur line p rest -> rest <> [] ->
  mc_refused mcc = mc_refused mcl -> (mv_k0 v <= length (mc_kept mcc))%nat ->
  plookup pl_tpi j = Some (PCall SS_m_refuse 1%bv) -> j + 4 < 2 ^ 40 ->
  getr regs1 10 = w64 (mv_c v) -> getr regs1 11 = w64 (line + 1) ->
  (length (mc_kept (m_refuse mcc (line + 1) knock)) <= length (mc_kept (mf_final v)))%nat ->
  (forall (fx1 : YK11.FPState) ly2 S2 (W2 : world SEGS) (regs2 : bvmap 5 word) mem2 md2,
    fxrel fx fx1 ->
    mf_ls v ly2 S2 -> mf_core B v ly2 S2 W2 mem2 md2 pos lowsh (m_refuse mcc (line + 1) knock) ->
    mf_cells v ly2 pos mem2 W2 cur -> mf_np v mem2 W2 np -> mf_loop v W2 mem2 mcl cur line p rest ->
    (forall r, acallee_saved r -> getr regs2 (Z_to_bv 5 r) = getr regs1 (Z_to_bv 5 r)) ->
    mf_at (fx := fx1) B v W2 regs2 mem2 md2 (j + 4)) ->
  mf_at B v Wc regs1 memc mdc j.

(* the same step at a site with no next-line slot fact (LONGP 0x861ec: 144(s1) is not yet written there); the
   continuation keeps any value the slot holds *)
Definition MF_REFUSE_STEP0 : Prop :=
forall v lyc Sc Wc (regs1 : bvmap 5 word) memc mdc pos lowsh (mcc mcl : mconf) (knock : bool)
  (cur : option nat) (line p : Z) (rest : list Z) (j : Z),
  mf_cx B v -> mf_ls v lyc Sc -> sa_frm0 ->
  mf_corek B knock v lyc Sc Wc memc mdc pos lowsh mcc -> mf_cells v lyc pos memc Wc cur ->
  getr regs1 2 = w64 (mf_s1 (mv_sp v)) -> getr regs1 3 = w64 (as_gp B) -> getr regs1 4 = w64 (as_tp B) ->
  getr regs1 8 = w64 (mv_sp v) ->
  mf_loop v Wc memc mcl cur line p rest -> rest <> [] ->
  mc_refused mcc = mc_refused mcl -> (mv_k0 v <= length (mc_kept mcc))%nat ->
  plookup pl_tpi j = Some (PCall SS_m_refuse 1%bv) -> j + 4 < 2 ^ 40 ->
  getr regs1 10 = w64 (mv_c v) -> getr regs1 11 = w64 (line + 1) ->
  (length (mc_kept (m_refuse mcc (line + 1) knock)) <= length (mc_kept (mf_final v)))%nat ->
  (forall (fx1 : YK11.FPState) ly2 S2 (W2 : world SEGS) (regs2 : bvmap 5 word) mem2 md2,
    fxrel fx fx1 ->
    mf_ls v ly2 S2 -> mf_core B v ly2 S2 W2 mem2 md2 pos lowsh (m_refuse mcc (line + 1) knock) ->
    mf_cells v ly2 pos mem2 W2 cur -> (forall np, mf_np v memc Wc np -> mf_np v mem2 W2 np) ->
    mf_loop v W2 mem2 mcl cur line p rest ->
    (forall r, acallee_saved r -> getr regs2 (Z_to_bv 5 r) = getr regs1 (Z_to_bv 5 r)) ->
    mf_at (fx := fx1) B v W2 regs2 mem2 md2 (j + 4)) ->
  mf_at B v Wc regs1 memc mdc j.

Lemma mf_refuse_step0 : MF_REFUSE_STEP0.
Proof.
intros v lyc Sc Wc regs1 memc mdc pos lowsh mcc mcl knock cur line p rest j
  CX LS FRM CORE CELLS R2 R3 R4 R8 LOOP Hne Href Hk0 Hslot Hj40 R10 R11 HKEPT K.
pose proof CORE as (HJ & HPm & _ & _ & _ & _ & MC & ADDR & TAIL).
pose proof LOOP as (_ & _ & _ & _ & _ & _ & _ & Hl0 & Hl1 & Hl2 & _).
assert (Hr1 : (1 <= length rest)%nat) by (destruct rest; [contradiction | cbn [length]; lia]).
destruct (mf_chain_k B knock v lyc Sc Wc memc mdc pos lowsh mcc CX CORE) as (ch1 & CH).
apply (mf_refuse_core v lyc Sc Wc regs1 memc mdc pos mcc knock line j ch1 CX FRM HJ HPm MC ADDR TAIL CH).
- exact (mf_rod_now_k B RELRO knock v lyc Sc Wc memc mdc pos lowsh mcc CX CORE).
- intros x Hx. apply (mf_lit_now_k B knock v lyc Sc Wc memc mdc pos lowsh mcc x CX CORE).
  unfold M_REFUSE_LITS in Hx. unfold M_FILE_LITS. cbn [In] in Hx |- *. tauto.
- exact R2.
- exact R3.
- exact R4.
- exact R8.
- exact Hslot.
- exact Hj40.
- exact R10.
- exact R11.
- lia.
- lia.
- exact Hk0.
- exact HKEPT.
- intros fx1 ly2 S2 W2 regs2 mem2 md2 Hfx Hle HJ2 NOAL HPr KEPT MC2.
  pose proof NOAL as (HP2 & Ely2 & _). subst ly2.
  destruct (mf_keep_win_k B knock v lyc Sc Wc memc mdc pos lowsh mcc cur S2 W2 mem2 md2
    (mf_s1 (mv_sp v) - SegInstA.STK_m_refuse) (mf_s1 (mv_sp v)) (mf_refuse_E (mv_c v) mcc)
    (m_refuse mcc (line + 1) knock) CX CORE CELLS HJ2 HP2) as (CORE2 & CELLS2 & NP2 & LOOP2).
  + destruct (mf_s1_facts B v CX) as (Hs1 & _ & _).
    assert (E1 : SegInstA.STK_m_refuse = 8240) by reflexivity.
    assert (E2 : SegInstA.STK_m_file = 8560) by reflexivity.
    rewrite E1, E2. destruct Hs1 as [Hs1|Hs1]; rewrite Hs1; lia.
  + lia.
  + exact KEPT.
  + intros a Ha. unfold mf_refuse_E in Ha.
    unfold seg_spec.kept_addr, seg_spec.MC_KEPT, seg_spec.MC_KEPT_LEN, seg_spec.MC_NKEPT, seg_spec.MC_REFUSED,
      seg_spec.SEG_M_SIZE in *. lia.
  + exact MC2.
  + apply (K fx1 lyc S2 W2 regs2 mem2 md2 Hfx).
    * exact (mf_ls_keep B v lyc Sc lyc S2 LS NOAL).
    * exact CORE2.
    * exact CELLS2.
    * exact NP2.
    * exact (LOOP2 mcl cur line p rest LOOP).
    * exact HPr.
Qed.

Lemma mf_refuse_step : MF_REFUSE_STEP.
Proof.
intros v lyc Sc Wc regs1 memc mdc pos lowsh mcc mcl knock cur line p rest np j
  CX LS FRM CORE CELLS NP R2 R3 R4 R8 LOOP Hne Href Hk0 Hslot Hj40 R10 R11 HKEPT K.
apply (mf_refuse_step0 v lyc Sc Wc regs1 memc mdc pos lowsh mcc mcl knock cur line p rest j
  CX LS FRM CORE CELLS R2 R3 R4 R8 LOOP Hne Href Hk0 Hslot Hj40 R10 R11 HKEPT).
intros fx1 ly2 S2 W2 regs2 mem2 md2 Hfx LS2 CORE2 CELLS2 NP2 LOOP2 HPr.
exact (K fx1 ly2 S2 W2 regs2 mem2 md2 Hfx LS2 CORE2 CELLS2 (NP2 np NP) LOOP2 HPr).
Qed.

End e.
End f.
End d.
