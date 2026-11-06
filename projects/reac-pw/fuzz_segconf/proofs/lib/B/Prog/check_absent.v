(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the ASan walk of check_refusal (plugin-hostd/fuzz_command, 0x87f08, 52 instructions), in the form of proofs/cgif/cgif_file_fuzzer/lib/A/ACbk.v (pb_wcb: entry, branch, return) and A/ACh2.v:122-290 (a program call through cl_callS and back). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/check_refusal.v, with its module paths and module names changed; 515 of its 561 lines of code are new or changed and 270 lines of the source are left out. *)
(* the image-B port of lib/A/Prog/check_absent.v (commit 5ed426e78b84): the walk of
   check_absent on reac-pw/fuzz_segconf image B (fuzz_segconf.asan-ubsan, pin c3796c0b38f3, entry 0x875f0 =
   BASE + AF_check_absent = 0x84dc0 + 0x2830; code: the neutral image-B excerpt
   check_absent.fuzz_segconf.asan-ubsan.s) against
   check_absent_contract (lib/B/Prog/check_absent_c.v, image B's copy of the FINAL contract 6f783602b5e3).
   RELOCATION: image B's 29 words are image A's 28 at +8 bytes, the only changed words the six pc-relative `jal`s,
   plus one UBSan trap word `unimp` (c0001073) at 0x87660 after `jal abort`. A-to-B map: every A address a in
   [0x875e8, 0x87654] is B's a + 8; the call targets are B's own (find 0x89a84, role 0x89be0, ignored 0x89b78,
   model 0x89e04, the no-return hook 0x5df0c, abort 0x910c4), reached through the B listing's PCall slots and
   seg_sig_prog. The proof text is image A's; what changes: the module paths (lib.A.Prog -> lib.B.Prog, the 44 kit
   modules copied for image B -> lib.B), the window numbers (image B's, image B's instance file SegInstB.v's), the
   read-only window (SegInstB.RLO_A / RHI_A, image B's SegGlob.SEG_RLO / SEG_RHI = 0xa1c60 / 0xa3f08) and the
   addresses in comments.
   0x875f0 .. 0x87604: a 32-byte real-stack frame (ra at sp0-8, s0 at sp0-16, s1 at sp0-24); s0 := name, s1 := c.
   0x87608, 0x8761c, 0x8762c, 0x8763c: reac_segconf_find(c, name), reac_segconf_role(c, name, NULL),
   reac_segconf_ignored(c, name), reac_segconf_model(c, name), each at sp0 - 32 and each followed by `bnez a0`
   (0x8760c, 0x87620, 0x87630, 0x87640) to 0x87658, the call of the no-return hook, then `jal abort` at 0x8765c.
   ABORT ARM: dead under the contract's premise absent rcs nm = true (check_absent_pre's second conjunct): by
   ca_absent_none each callee's post gives a0 = 0 (find_ptr = 0, role 0, b2z false = 0, model_ptr = 0), so each
   `bnez a0` is refuted at its branch and 0x87658 / 0x8765c are never reached.
   UBSAN TRAP 0x87660 (`unimp`): no branch of the function targets it (the four `bnez` target 0x87658) and the only
   fall-through into it is from `jal abort` at 0x8765c, which does not return and is itself unreached once the abort
   arm is dead: no path reaches the trap.
   0x87644 .. 0x87654: ra, s0, s1 loaded back from the frame, sp := sp0, ret.
   No instrumented check of its own (program.asan-ubsan.tsv: 0 checks); the walk's shadow table is empty.
   The callees' premises at each call site are the entry's, carried by ca_kept (check_absent_lem.v). *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI00 YI04.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YK06 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal SegSyms SegList SegPa SegPaLib PaCall PaDenot PaSB.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegObj SegGlob SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import
reac_segconf_find_c reac_segconf_role_c reac_segconf_ignored_c reac_segconf_model_c check_absent_c
check_absent_lem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require SegInstB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* Image B's stack windows, image B's instance file's (lib/B/Prog/SegInstB.v), under the names the proofs below
   use. Each is the function's real-stack frame (the `addi sp,sp,-N` at its entry in
   the neutral image-B excerpt <fn>.fuzz_segconf.asan-ubsan.s) plus the deepest window below
   it. *)
(* reac_segconf_find 0x89a84: frame 64 (`addi sp,sp,-64`) and the strcmp wrapper's window (0x89b18, in a loop) *)
#[local] Notation STK_reac_segconf_find_B := SegInstB.STK_reac_segconf_find (only parsing).
(* reac_segconf_ignored 0x89b78 and reac_segconf_model 0x89e04: frame 16 and find's window (0x89b90, 0x89e1c) *)
#[local] Notation STK_reac_segconf_ignored_B := SegInstB.STK_reac_segconf_ignored (only parsing).
#[local] Notation STK_reac_segconf_model_B := SegInstB.STK_reac_segconf_model (only parsing).
(* reac_segconf_role 0x89be0: frame 32 and find's window (0x89c00) *)
#[local] Notation STK_reac_segconf_role_B := SegInstB.STK_reac_segconf_role (only parsing).
(* check_absent 0x875f0: frame 32 and the deepest of its four queries (find 0x87608, role 0x8761c, ignored 0x8762c,
   model 0x8763c), role's *)
#[local] Notation STK_check_absent_B := SegInstB.STK_check_absent (only parsing).
Lemma STK_check_absent_B_value : STK_check_absent_B = 8320 /\ STK_reac_segconf_find_B = 8256 /\
  STK_reac_segconf_role_B = 8288 /\ STK_reac_segconf_ignored_B = 8272 /\ STK_reac_segconf_model_B = 8272.
Proof. unfold STK_check_absent_B, STK_reac_segconf_role_B, STK_reac_segconf_ignored_B, STK_reac_segconf_model_B,
  STK_reac_segconf_find_B, ESTACK. repeat split; reflexivity. Qed.

(* the symbolic entry state: the stack pointer (atom 2) and the 32-byte frame below it. Atom 32 is the shadow
   base the engine's shadow table is indexed by; this function has no instrumented check, so the table is empty
   and no entry of it is used. *)
Definition CA_SB : Z := 0x7fff8000.
Definition CAx : sv := SOff 32 0.
Definition CAspan : Z * Z := (CA_SB, CA_SB + 2 ^ 44 - 1).
Definition ca_regions : smem := [stack_region 32].
Definition ca_facts : facts := mkFacts [(2%nat, mkAF (2^46) (2^47) 4); (32%nat, mkAF CA_SB CA_SB 0)] [] [].
Definition ss_ca : sstate := mkSS AF_check_absent sr_atoms ca_regions None ca_facts.
Definition ca_SH : list shent := [].
Definition ca_extra : list word := [Z_to_bv 64 CA_SB].

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation SIG s := (@pa_sigma _ seg_listing PI s).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Definition ca_E (regs : bvmap 5 word) : env := Eimg (Ereg regs ca_extra).

Lemma ca_entry : forall (W : world SEGS) (regs : bvmap 5 word) mem ly STK,
  astk_ok STK ly (spZ regs) -> 32 <= STK ->
  (forall a, spZ regs - STK <= a < spZ regs -> apresent (w_H W) mem a) ->
  st_ok_pi SEGS VAL (ca_E regs) ss_ca
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_check_absent)) mem (seg_rom SEGS)))
  /\ sh_ok SEGS CAx ca_SH (ca_E regs) (mrestrict (w_H W) mem).
Proof using.
  intros W regs mem ly STK Hstk H32 Hpres.
  pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof alloc_ceiling_value as [[CMIN CMAX] CMOD].
  set (E := ca_E regs).
  assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs ca_extra) n)
    by (intros n Hn; subst E; unfold ca_E; apply Eimg_low; exact Hn).
  assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
  assert (E32 : ew E 32 = Z_to_bv 64 CA_SB) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
  assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
  split.
  - unfold ss_ca. rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
    + subst E. unfold ca_E. apply regs_ok_Eimg_Ereg.
    + vm_compute. reflexivity.
    + unfold ca_regions, stack_region.
      repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
      cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
    + apply pairwise_disjoint_of_extents. unfold ca_regions, stack_region, extent_of_region.
      cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. cbn [zpairwise_disjoint zall_disjoint]. repeat split.
    + split; [|split; [exact I | exact I]].
      cbn [ca_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite Usp, E32, !unsigned_lit_small by (unfold CA_SB; lia).
      unfold CA_SB. change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
      revert Hslo Hshi H47 Hceil Hal16 Hstk0 C1 CMIN CMAX. clear. intros.
      repeat match goal with |- _ /\ _ => split end; first [exact I | lia | reflexivity].
  - unfold sh_ok, ca_SH. constructor.
Qed.

Section e.
Variable B : asyms.
Hypothesis FIND : reac_segconf_find_contract SEGS B (BASE + AF_reac_segconf_find) SegInstB.STK_reac_segconf_find
  SegInstB.RLO_A SegInstB.RHI_A.
Hypothesis ROLE : reac_segconf_role_contract SEGS B (BASE + AF_reac_segconf_role) SegInstB.STK_reac_segconf_role
  SegInstB.RLO_A SegInstB.RHI_A.
Hypothesis IGN : reac_segconf_ignored_contract SEGS B (BASE + AF_reac_segconf_ignored)
  SegInstB.STK_reac_segconf_ignored SegInstB.RLO_A SegInstB.RHI_A.
Hypothesis MDL : reac_segconf_model_contract SEGS B (BASE + AF_reac_segconf_model) SegInstB.STK_reac_segconf_model
  SegInstB.RLO_A SegInstB.RHI_A.
(* the per-binary facts every walk of this tree takes: the allocator record's laws and the listing's call
   targets (SegObj.v) *)
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis SIGP : seg_sig_prog.
Let RUN := paj_run B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_seg) (PI := PI).

Theorem check_absent_walk :
  check_absent_contract SEGS B (BASE + AF_check_absent) SegInstB.STK_check_absent SegInstB.RLO_A SegInstB.RHI_A.
Proof using B FIND IGN LAWS MDL ROLE SIGP.
unfold check_absent_contract.
intros ly S W regs mem md ch c name rcs nm HPRE HROD H10 Rc H11 Rn (QP & AB) HEV.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE.
pose proof pa_base_lo as HBLO. pose proof (pa_img_range (L := seg_listing)) as HIMG.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof alloc_ceiling_value as [[CMIN CMAX] CMOD].
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
(* image B's window of this call (STK_check_absent_B above) *)
assert (WS : STK_check_absent_B = 8320) by (pose proof STK_check_absent_B_value as V; tauto).
assert (LOWSP : alloc_ceiling <= spZ regs - STK_check_absent_B) by lia.
assert (IMGLOW : forall a, in_img SEGS a -> 4096 <= a < alloc_ceiling)
  by (intros a Ha; pose proof (HIMG a Ha) as [L1 L2]; unfold kImgEnd in L2; lia).
(* the model: every callee answers 0, so every `bnez a0` falls through *)
destruct (ca_absent_none rcs nm AB) as (RF & RR & RI & RM).
assert (FP0 : seg_spec.find_ptr c rcs nm = 0) by (unfold seg_spec.find_ptr; rewrite RF; reflexivity).
assert (MP0 : seg_spec.model_ptr c rcs nm = 0) by (unfold seg_spec.model_ptr; rewrite RF; reflexivity).
assert (IP0 : seg_spec.b2z (r_ignored rcs nm) = 0) by (rewrite RI; reflexivity).
(* where the query's two objects lie *)
pose proof QP as (Qc0 & Qc16 & Qrc & Qheap & Qaddr & Qn0 & Qstr & Qloc & Qaddrn & Qlen).
destruct (ca_loc_low SEGS B LAWS ly S W mem md c seg_spec.SEG_C_SIZE HAR IMGLOW (or_introl Qheap)
  ltac:(unfold seg_spec.SEG_C_SIZE; lia)) as [CLO CHI].
destruct (ca_loc_low SEGS B LAWS ly S W mem md name (Z.of_nat (length nm) + 1) HAR IMGLOW Qloc ltac:(lia))
  as [NLO NHI].
(* every read-only byte of the image lies below the window *)
assert (ROLOW : forall a, in_roP SEGS SegInstB.RLO_A SegInstB.RHI_A a -> 0 <= a < 2 ^ 64 /\
  a < spZ regs - STK_check_absent_B).
{ intros a [(sg & Hin & _ & Hr) | Hr].
  - assert (Hi : in_img SEGS a) by (exists sg; split; [exact Hin | exact Hr]).
    pose proof (IMGLOW a Hi). lia.
  - unfold SegInstB.RLO_A, SegInstB.RHI_A, SEG_RLO, SEG_RHI in Hr. lia. }
destruct (ca_entry W regs mem ly STK_check_absent_B Hstk ltac:(lia) Hpres) as [HS SHOK].
assert (HJ : ajournal SEGS B STK_check_absent_B (spZ regs) [] ly S W mem md [] ly S W mem md 0)
  by (eapply ajournal_init; exact HPRE).
unfold cfg_at, w64.
set (E := ca_E regs) in *.
assert (HEI : img_env VAL A_LIM E) by (unfold E, ca_E; apply Eimg_env).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs ca_extra) n)
  by (intros n Hn; unfold E, ca_E; apply Eimg_low; exact Hn).
assert (EEo : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs rr).
{ intros n rr Hn. pose proof (bv_unsigned_in_range 5 rr) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  rewrite EL by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn. }
assert (E1 : ew E 1 = getr regs 1) by (apply EEo; reflexivity).
assert (E2 : ew E 2 = getr regs 2) by (apply EEo; reflexivity).
assert (E3 : ew E 3 = getr regs 3) by (apply EEo; reflexivity).
assert (E4 : ew E 4 = getr regs 4) by (apply EEo; reflexivity).
assert (E10 : ew E 10 = Z_to_bv 64 c) by (rewrite (EEo 10%nat 10%bv eq_refl); exact H10).
assert (E11 : ew E 11 = Z_to_bv 64 name) by (rewrite (EEo 11%nat 11%bv eq_refl); exact H11).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (HAE : env_agree 32 (Ereg regs ca_extra) E).
{ split; [intros n Hn; rewrite EL by (unfold A_TEXT; lia); reflexivity | reflexivity]. }

clearbody E. clear EL EEo.
unfold EV_check_absent in HEV.
rewrite WS in HPRE, Hstk, Hpres, HJ, LOWSP, ROLOW |- *.
(* ---- 0x875f0 .. 0x87608: the frame, s0 := name, s1 := c, jal reac_segconf_find ---- *)
paj_run_tok RUN HS HJ SHOK CAspan.
{ awr_ok_tac. exact Usp. }
lazymatch goal with Hfr : frame_of E _ (mrestrict _ _) (mrestrict _ _) |- _ =>
assert (K1 : ca_kept (rdW W mem) (rdW W (ms_mem ms)) (spZ regs - 8320) (spZ regs))
by (intros a Ha Hn; apply (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun a => spZ regs - 8320 <= a < spZ regs) Hfr);
  [ intros b wlo whi a' Hin Hrr; vm_compute in Hin;
    repeat (destruct Hin as [Hq0 | Hin]; [injection Hq0 as <- <- <-; cbn [base_val] in Hrr; rewrite ?Usp in Hrr; lia|]);
    destruct Hin
  | lia | exact Hn ]) end.
clear HF HFr HG.
assert (ROD1 : arodata_okP SEGS SegInstB.RLO_A SegInstB.RHI_A B (rdW W (ms_mem ms)))
  by (eapply ca_rodata_kept; [exact K1 | exact ROLOW | exact HROD]).
assert (QP1 : query_pre SEGS B ly S (rdW W (ms_mem ms)) c name rcs nm).
{ eapply ca_qp_kept;
  [ exact (ca_kept_low _ _ _ _ K1 LOWSP) | apply Permutation_refl | reflexivity
  | intros f Hf; exact Hf | exact CLO | exact CHI | exact NLO | exact NHI | exact QP ]. }
pmkst HS.
prreg HS (1%bv : bv 5) P1. prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
prreg HS (8%bv : bv 5) P8. prreg HS (10%bv : bv 5) P10. prreg HS (11%bv : bv 5) P11.
assert (HspT : spZ (ms_regs ms) = spZ regs + -32)
  by (unfold spZ at 1; rewrite P2, Usp, unsigned_lit_small by lia; reflexivity).
assert (P3' : getr (ms_regs ms) 3 = Z_to_bv 64 (as_gp B)) by (rewrite P3, E3; exact Hgp).
assert (P4' : getr (ms_regs ms) 4 = Z_to_bv 64 (as_tp B)) by (rewrite P4, E4; exact Htp).
assert (P10' : getr (ms_regs ms) 10 = Z_to_bv 64 c) by (rewrite P10; exact E10).
assert (P11' : getr (ms_regs ms) 11 = Z_to_bv 64 name) by (rewrite P11; exact E11).
assert (HraT : YK0s.ret_ok (getr (ms_regs ms) 1)) by (rewrite P1; apply ret_ok_codeptr_v; [lia | reflexivity]).
assert (Hra4T : 4096 <= bv_unsigned (getr (ms_regs ms) 1)) by (rewrite P1, unsigned_lit_small by lia; lia).
assert (HchT : achain ly (rdW W (ms_mem ms)) (spZ regs + -32) (s0Z (ms_regs ms)) [])
  by (apply achain_low; unfold s0Z; rewrite P8, E11, unsigned_lit_small by lia; lia).
rewrite (SIGP SS_reac_segconf_find ltac:(unfold seg_prog_syms; cbn [In]; repeat (first [left; reflexivity | right]))).
replace (seg_af SS_reac_segconf_find) with AF_reac_segconf_find by (vm_compute; reflexivity).
eapply SRr_bind.
{ eapply (cl_callS B LAWS W (ms_regs ms) (ms_mem ms) _ 8320 (spZ regs) [] ly S W mem md [] ly S _ 0
    STK_reac_segconf_find_B [] 0 (-32) (getr (ms_regs ms) 1) []
    (fun ly2 S2 W2 regs2 mem2 md2 =>
      getr regs2 10 = Z_to_bv 64 0 /\
      ca_kept (rdW W (ms_mem ms)) (rdW W2 mem2) (spZ regs - 8320) (spZ regs) /\
      sa_noalloc B ly S ly2 S2)
    HJ HspT).
  - reflexivity.
  - lia.
  - unfold STK_reac_segconf_find_B, ESTACK; lia.
  - unfold STK_reac_segconf_find_B, ESTACK; lia.
  - exact P3'.
  - exact P4'.
  - reflexivity.
  - exact HraT.
  - exact Hra4T.
  - exact HchT.
  - intros HPRE1. eapply SRr_mono.
    + apply (FIND ly S W (ms_regs ms) (ms_mem ms) _ [] c name rcs nm HPRE1 ROD1 P10' Rc P11' Rn QP1).
      unfold EV_reac_segconf_find. lia.
    + cbv beta. unfold apost_base.
      intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HP2 & (A0 & HKP & NA)).
      exists ly2, S2, regs2, mem2, md2. split; [reflexivity|]. split; [exact HJ2|]. split; [exact HP2|].
      split; [rewrite A0, FP0; reflexivity|]. split; [|exact NA].
      intros a Ha Hn. apply HKP; [lia | | intros []].
      rewrite HspT. unfold STK_reac_segconf_find_B, ESTACK. lia.
  - intros a Ha. exfalso. exact (inFP_nil a Ha). }
cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJa & HJia & HPa & (A0a & KCa & NAa)).
assert (K2 : ca_kept (rdW W mem) (rdW W2 mem2) (spZ regs - 8320) (spZ regs))
  by (eapply ca_kept_trans; [exact K1 | exact KCa]).
assert (FRa : forall f, In f (frames S) -> In f (frames S2))
  by (pose proof HJa as (_ & _ & _ & _ & _ & Hf6 & _); intros f Hf; rewrite Hf6; cbn [app]; exact Hf).
assert (NEVa : st_nev S2 <= st_nev S)
  by (pose proof HJa as (_ & _ & _ & _ & _ & _ & Hnv & _); lia).
assert (Elya : ly2 = ly) by (destruct NAa as (_ & Hx & _); exact Hx). subst ly2.
assert (PERMa : Permutation (ablocks B ly S2) (ablocks B ly S)) by (destruct NAa as (Hx & _); exact Hx).
jafter_call_keep_pi HS 40%nat regs2 (mrestrict (w_H W2) mem2) HPa [0]%nat HS2.
match type of HS2 with ?t -> _ => assert (HRK : t); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; [| apply Forall_nil].
  eapply (region_kept_stack_sub SEGS B); [exact HJia | exact HJa | exact Usp | lia | lia | lia | lia | lia |].
  intros a _ (r & Hr & _). destruct Hr. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
assert (A44 : ew (havoc E 40 (map (getr regs2) CLOB)) 44 = getr regs2 10) by reflexivity.
remember (havoc E 40 (map (getr regs2) CLOB)) as Ea eqn:HEa.
assert (HEIa : img_env VAL A_LIM Ea) by (rewrite HEa; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLDa : forall n, (n < 40)%nat -> ew Ea n = ew E n)
  by (intros n Hn; rewrite HEa; apply YN3v.ew_havoc_old; exact Hn).
assert (HAEa : env_agree 32 (Ereg regs ca_extra) Ea).
{ destruct HAE as [HA1 HA2]. split; [intros n Hn; rewrite OLDa by lia; exact (HA1 n Hn) | rewrite HEa; exact HA2]. }
clear HEa.
assert (Uspa : bv_unsigned (ew Ea 2) = spZ regs) by (rewrite OLDa by lia; exact Usp).
assert (SHOKa : sh_ok SEGS CAx ca_SH Ea (mrestrict (w_H W2) mem2)) by (unfold sh_ok, ca_SH; constructor).
rewrite P1.
(* 0x8760c bnez a0: find answered 0, so the arm to the no-return hook is not taken *)
psrr_branch_tok RUN BR HS SHOKa CAspan.
{ exfalso. rewrite branch_ne_U in Hc. apply negb_true_iff in Hc. apply Z.eqb_neq in Hc. apply Hc.
  assert (Hz : ew Ea 44 = Z_to_bv 64 0) by (rewrite A44; exact A0a).
  unfold U. cbn [sv_denot]. rewrite Hz. vm_compute. reflexivity. }
clear Hc.
(* ---- 0x87610 .. 0x8761c: a0 := c, a1 := name, a2 := 0, jal reac_segconf_role ---- *)
paj_run_tok RUN HS HJa SHOKa CAspan.
{ awr_ok_tac. exact Uspa. }
lazymatch goal with Hfr : frame_of Ea _ (mrestrict _ _) (mrestrict _ _) |- _ =>
assert (K3 : ca_kept (rdW W2 mem2) (rdW W2 (ms_mem ms0)) (spZ regs - 8320) (spZ regs))
by (intros a Ha Hn; apply (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun a => spZ regs - 8320 <= a < spZ regs) Hfr);
  [ intros b wlo whi a' Hin Hrr; vm_compute in Hin;
    repeat (destruct Hin as [Hq0 | Hin]; [injection Hq0 as <- <- <-; cbn [base_val] in Hrr; rewrite ?Uspa in Hrr; lia|]);
    destruct Hin
  | lia | exact Hn ]) end.
clear HF HFr HG.
assert (K4 : ca_kept (rdW W mem) (rdW W2 (ms_mem ms0)) (spZ regs - 8320) (spZ regs))
  by (eapply ca_kept_trans; [exact K2 | exact K3]).
assert (ROD2 : arodata_okP SEGS SegInstB.RLO_A SegInstB.RHI_A B (rdW W2 (ms_mem ms0)))
  by (eapply ca_rodata_kept; [exact K4 | exact ROLOW | exact HROD]).
assert (QP2 : query_pre SEGS B ly S2 (rdW W2 (ms_mem ms0)) c name rcs nm).
{ eapply ca_qp_kept;
  [ exact (ca_kept_low _ _ _ _ K4 LOWSP) | exact PERMa | reflexivity
  | exact FRa | exact CLO | exact CHI | exact NLO | exact NHI | exact QP ]. }
pmkst HS.
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
prreg HS (8%bv : bv 5) Q8. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11.
prreg HS (12%bv : bv 5) Q12.
assert (HspU : spZ (ms_regs ms0) = spZ regs + -32)
  by (unfold spZ at 1; rewrite Q2, OLDa by lia; rewrite Usp, unsigned_lit_small by lia; reflexivity).
assert (Q3' : getr (ms_regs ms0) 3 = Z_to_bv 64 (as_gp B)) by (rewrite Q3, OLDa by lia; rewrite E3; exact Hgp).
assert (Q4' : getr (ms_regs ms0) 4 = Z_to_bv 64 (as_tp B)) by (rewrite Q4, OLDa by lia; rewrite E4; exact Htp).
assert (Q10' : getr (ms_regs ms0) 10 = Z_to_bv 64 c) by (rewrite Q10, OLDa by lia; exact E10).
assert (Q11' : getr (ms_regs ms0) 11 = Z_to_bv 64 name) by (rewrite Q11, OLDa by lia; exact E11).
assert (Q12' : getr (ms_regs ms0) 12 = Z_to_bv 64 0) by (rewrite Q12; reflexivity).
assert (HraU : YK0s.ret_ok (getr (ms_regs ms0) 1)) by (rewrite Q1; apply ret_ok_codeptr_v; [lia | reflexivity]).
assert (Hra4U : 4096 <= bv_unsigned (getr (ms_regs ms0) 1)) by (rewrite Q1, unsigned_lit_small by lia; lia).
assert (HchU : achain ly (rdW W2 (ms_mem ms0)) (spZ regs + -32) (s0Z (ms_regs ms0)) [])
  by (apply achain_low; unfold s0Z; rewrite Q8, OLDa by lia; rewrite E11, unsigned_lit_small by lia; lia).
rewrite (SIGP SS_reac_segconf_role ltac:(unfold seg_prog_syms; cbn [In]; repeat (first [left; reflexivity | right]))).
replace (seg_af SS_reac_segconf_role) with AF_reac_segconf_role by (vm_compute; reflexivity).
eapply SRr_bind.
{ eapply (cl_callS B LAWS W2 (ms_regs ms0) (ms_mem ms0) _ 8320 (spZ regs) [] ly S W mem md [] ly S2 _ 0
    STK_reac_segconf_role_B (role_W 0 (r_role rcs nm)) 0 (-32) (getr (ms_regs ms0) 1) []
    (fun ly3 S3 W3 regs3 mem3 md3 =>
      getr regs3 10 = Z_to_bv 64 0 /\
      ca_kept (rdW W2 (ms_mem ms0)) (rdW W3 mem3) (spZ regs - 8320) (spZ regs) /\
      sa_noalloc B ly S2 ly3 S3)
    HJa HspU).
  - reflexivity.
  - lia.
  - unfold STK_reac_segconf_role_B, STK_reac_segconf_find_B, ESTACK; lia.
  - unfold STK_reac_segconf_role_B, STK_reac_segconf_find_B, ESTACK; lia.
  - exact Q3'.
  - exact Q4'.
  - reflexivity.
  - exact HraU.
  - exact Hra4U.
  - exact HchU.
  - intros HPRE2. eapply SRr_mono.
    + apply (ROLE ly S2 W2 (ms_regs ms0) (ms_mem ms0) _ [] c name 0 rcs nm HPRE2 ROD2 Q10' Rc Q11' Rn Q12'
        ltac:(lia) (conj QP2 (or_introl eq_refl))).
      unfold EV_reac_segconf_role. lia.
    + cbv beta. unfold apost_base.
      intros W3 c3 _ (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ3 & HP3 & (A0 & _ & HKP & NA)).
      exists ly3, S3, regs3, mem3, md3. split; [reflexivity|]. split; [exact HJ3|]. split; [exact HP3|].
      split; [rewrite A0, RR; reflexivity|]. split; [|exact NA].
      intros a Ha Hn. apply HKP; [lia | | intros (Hz & _); exact (Hz eq_refl)].
      rewrite HspU. unfold STK_reac_segconf_role_B, STK_reac_segconf_find_B, ESTACK. lia.
  - intros a Ha. rewrite RR in Ha. cbn [role_W] in Ha. exfalso. exact (inFP_nil a Ha). }
cbv beta. intros W3 c3 _ (ly3 & S3 & regs3 & mem3 & md3 & -> & HJb & HJib & HPb & (A0b & KCb & NAb)).
assert (K5 : ca_kept (rdW W mem) (rdW W3 mem3) (spZ regs - 8320) (spZ regs))
  by (eapply ca_kept_trans; [exact K4 | exact KCb]).
assert (FRb : forall f, In f (frames S) -> In f (frames S3))
  by (pose proof HJb as (_ & _ & _ & _ & _ & Hf6 & _); intros f Hf; rewrite Hf6; cbn [app]; exact Hf).
assert (NEVb : st_nev S3 <= st_nev S)
  by (pose proof HJb as (_ & _ & _ & _ & _ & _ & Hnv & _); lia).
assert (Elyb : ly3 = ly) by (destruct NAb as (_ & Hx & _); exact Hx). subst ly3.
assert (PERMb : Permutation (ablocks B ly S3) (ablocks B ly S))
  by (destruct NAb as (Hx & _); eapply Permutation_trans; [exact Hx | exact PERMa]).
jafter_call_keep_pi HS 60%nat regs3 (mrestrict (w_H W3) mem3) HPb [0]%nat HS3.
match type of HS3 with ?t -> _ => assert (HRK : t); [|specialize (HS3 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; [| apply Forall_nil].
  eapply (region_kept_stack_sub SEGS B); [exact HJib | exact HJb | exact Uspa | lia | lia | lia | lia | lia |].
  intros a _ Hin. rewrite RR in Hin. cbn [role_W] in Hin. destruct Hin as (r & Hr & _). destruct Hr. }
clear HS. rewrite <- restrict_mkst_fx in HS3. rename HS3 into HS.
assert (A64 : ew (havoc Ea 60 (map (getr regs3) CLOB)) 64 = getr regs3 10) by reflexivity.
remember (havoc Ea 60 (map (getr regs3) CLOB)) as Eb eqn:HEb.
assert (HEIb : img_env VAL A_LIM Eb) by (rewrite HEb; apply img_env_havoc; [exact HEIa | cbv; lia]).
assert (OLDb : forall n, (n < 60)%nat -> ew Eb n = ew Ea n)
  by (intros n Hn; rewrite HEb; apply YN3v.ew_havoc_old; exact Hn).
assert (HAEb : env_agree 32 (Ereg regs ca_extra) Eb).
{ destruct HAEa as [HA1 HA2]. split; [intros n Hn; rewrite OLDb by lia; exact (HA1 n Hn) | rewrite HEb; exact HA2]. }
clear HEb.
assert (Uspb : bv_unsigned (ew Eb 2) = spZ regs) by (rewrite OLDb by lia; exact Uspa).
assert (SHOKb : sh_ok SEGS CAx ca_SH Eb (mrestrict (w_H W3) mem3)) by (unfold sh_ok, ca_SH; constructor).
rewrite Q1.
(* 0x87620 bnez a0: role answered 0 *)
psrr_branch_tok RUN BR HS SHOKb CAspan.
{ exfalso. rewrite branch_ne_U in Hc. apply negb_true_iff in Hc. apply Z.eqb_neq in Hc. apply Hc.
  assert (Hz : ew Eb 64 = Z_to_bv 64 0) by (rewrite A64; exact A0b).
  unfold U. cbn [sv_denot]. rewrite Hz. vm_compute. reflexivity. }
clear Hc.
(* ---- 0x87624 .. 0x8762c: a0 := c, a1 := name, jal reac_segconf_ignored ---- *)
paj_run_tok RUN HS HJb SHOKb CAspan.
{ awr_ok_tac. exact Uspb. }
lazymatch goal with Hfr : frame_of Eb _ (mrestrict _ _) (mrestrict _ _) |- _ =>
assert (K6 : ca_kept (rdW W3 mem3) (rdW W3 (ms_mem ms1)) (spZ regs - 8320) (spZ regs))
by (intros a Ha Hn; apply (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun a => spZ regs - 8320 <= a < spZ regs) Hfr);
  [ intros b wlo whi a' Hin Hrr; vm_compute in Hin;
    repeat (destruct Hin as [Hq0 | Hin]; [injection Hq0 as <- <- <-; cbn [base_val] in Hrr; rewrite ?Uspb in Hrr; lia|]);
    destruct Hin
  | lia | exact Hn ]) end.
clear HF HFr HG.
assert (K7 : ca_kept (rdW W mem) (rdW W3 (ms_mem ms1)) (spZ regs - 8320) (spZ regs))
  by (eapply ca_kept_trans; [exact K5 | exact K6]).
assert (ROD3 : arodata_okP SEGS SegInstB.RLO_A SegInstB.RHI_A B (rdW W3 (ms_mem ms1)))
  by (eapply ca_rodata_kept; [exact K7 | exact ROLOW | exact HROD]).
assert (QP3 : query_pre SEGS B ly S3 (rdW W3 (ms_mem ms1)) c name rcs nm).
{ eapply ca_qp_kept;
  [ exact (ca_kept_low _ _ _ _ K7 LOWSP) | exact PERMb | reflexivity
  | exact FRb | exact CLO | exact CHI | exact NLO | exact NHI | exact QP ]. }
pmkst HS.
prreg HS (1%bv : bv 5) R1. prreg HS (2%bv : bv 5) R2. prreg HS (3%bv : bv 5) R3. prreg HS (4%bv : bv 5) R4.
prreg HS (8%bv : bv 5) R8. prreg HS (10%bv : bv 5) R10. prreg HS (11%bv : bv 5) R11.
assert (HspV : spZ (ms_regs ms1) = spZ regs + -32)
  by (unfold spZ at 1; rewrite R2, OLDb, OLDa by lia; rewrite Usp, unsigned_lit_small by lia; reflexivity).
assert (R3' : getr (ms_regs ms1) 3 = Z_to_bv 64 (as_gp B))
  by (rewrite R3, OLDb, OLDa by lia; rewrite E3; exact Hgp).
assert (R4' : getr (ms_regs ms1) 4 = Z_to_bv 64 (as_tp B))
  by (rewrite R4, OLDb, OLDa by lia; rewrite E4; exact Htp).
assert (R10' : getr (ms_regs ms1) 10 = Z_to_bv 64 c) by (rewrite R10, OLDb, OLDa by lia; exact E10).
assert (R11' : getr (ms_regs ms1) 11 = Z_to_bv 64 name) by (rewrite R11, OLDb, OLDa by lia; exact E11).
assert (HraV : YK0s.ret_ok (getr (ms_regs ms1) 1)) by (rewrite R1; apply ret_ok_codeptr_v; [lia | reflexivity]).
assert (Hra4V : 4096 <= bv_unsigned (getr (ms_regs ms1) 1)) by (rewrite R1, unsigned_lit_small by lia; lia).
assert (HchV : achain ly (rdW W3 (ms_mem ms1)) (spZ regs + -32) (s0Z (ms_regs ms1)) [])
  by (apply achain_low; unfold s0Z; rewrite R8, OLDb, OLDa by lia; rewrite E11, unsigned_lit_small by lia; lia).
rewrite (SIGP SS_reac_segconf_ignored ltac:(unfold seg_prog_syms; cbn [In]; repeat (first [left; reflexivity | right]))).
replace (seg_af SS_reac_segconf_ignored) with AF_reac_segconf_ignored by (vm_compute; reflexivity).
eapply SRr_bind.
{ eapply (cl_callS B LAWS W3 (ms_regs ms1) (ms_mem ms1) _ 8320 (spZ regs) [] ly S W mem md [] ly S3 _ 0
    STK_reac_segconf_ignored_B [] 0 (-32) (getr (ms_regs ms1) 1) []
    (fun ly4 S4 W4 regs4 mem4 md4 =>
      getr regs4 10 = Z_to_bv 64 0 /\
      ca_kept (rdW W3 (ms_mem ms1)) (rdW W4 mem4) (spZ regs - 8320) (spZ regs) /\
      sa_noalloc B ly S3 ly4 S4)
    HJb HspV).
  - reflexivity.
  - lia.
  - unfold STK_reac_segconf_ignored_B, STK_reac_segconf_find_B, ESTACK; lia.
  - unfold STK_reac_segconf_ignored_B, STK_reac_segconf_find_B, ESTACK; lia.
  - exact R3'.
  - exact R4'.
  - reflexivity.
  - exact HraV.
  - exact Hra4V.
  - exact HchV.
  - intros HPRE3. eapply SRr_mono.
    + apply (IGN ly S3 W3 (ms_regs ms1) (ms_mem ms1) _ [] c name rcs nm HPRE3 ROD3 R10' Rc R11' Rn QP3).
      unfold EV_reac_segconf_ignored. lia.
    + cbv beta. unfold apost_base.
      intros W4 c4 _ (ly4 & S4 & regs4 & mem4 & md4 & -> & HJ4 & HP4 & (A0 & HKP & NA)).
      exists ly4, S4, regs4, mem4, md4. split; [reflexivity|]. split; [exact HJ4|]. split; [exact HP4|].
      split; [rewrite A0, IP0; reflexivity|]. split; [|exact NA].
      intros a Ha Hn. apply HKP; [lia | | intros []].
      rewrite HspV. unfold STK_reac_segconf_ignored_B, STK_reac_segconf_find_B, ESTACK. lia.
  - intros a Ha. exfalso. exact (inFP_nil a Ha). }
cbv beta. intros W4 c4 _ (ly4 & S4 & regs4 & mem4 & md4 & -> & HJc & HJic & HPc & (A0c & KCc & NAc)).
assert (K8 : ca_kept (rdW W mem) (rdW W4 mem4) (spZ regs - 8320) (spZ regs))
  by (eapply ca_kept_trans; [exact K7 | exact KCc]).
assert (FRc : forall f, In f (frames S) -> In f (frames S4))
  by (pose proof HJc as (_ & _ & _ & _ & _ & Hf6 & _); intros f Hf; rewrite Hf6; cbn [app]; exact Hf).
assert (NEVc : st_nev S4 <= st_nev S)
  by (pose proof HJc as (_ & _ & _ & _ & _ & _ & Hnv & _); lia).
assert (Elyc : ly4 = ly) by (destruct NAc as (_ & Hx & _); exact Hx). subst ly4.
assert (PERMc : Permutation (ablocks B ly S4) (ablocks B ly S))
  by (destruct NAc as (Hx & _); eapply Permutation_trans; [exact Hx | exact PERMb]).
jafter_call_keep_pi HS 80%nat regs4 (mrestrict (w_H W4) mem4) HPc [0]%nat HS4.
match type of HS4 with ?t -> _ => assert (HRK : t); [|specialize (HS4 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; [| apply Forall_nil].
  eapply (region_kept_stack_sub SEGS B); [exact HJic | exact HJc | exact Uspb | lia | lia | lia | lia | lia |].
  intros a _ (r & Hr & _). destruct Hr. }
clear HS. rewrite <- restrict_mkst_fx in HS4. rename HS4 into HS.
assert (A84 : ew (havoc Eb 80 (map (getr regs4) CLOB)) 84 = getr regs4 10) by reflexivity.
remember (havoc Eb 80 (map (getr regs4) CLOB)) as Ec eqn:HEc.
assert (HEIc : img_env VAL A_LIM Ec) by (rewrite HEc; apply img_env_havoc; [exact HEIb | cbv; lia]).
assert (OLDc : forall n, (n < 80)%nat -> ew Ec n = ew Eb n)
  by (intros n Hn; rewrite HEc; apply YN3v.ew_havoc_old; exact Hn).
assert (HAEc : env_agree 32 (Ereg regs ca_extra) Ec).
{ destruct HAEb as [HA1 HA2]. split; [intros n Hn; rewrite OLDc by lia; exact (HA1 n Hn) | rewrite HEc; exact HA2]. }
clear HEc.
assert (Uspc : bv_unsigned (ew Ec 2) = spZ regs) by (rewrite OLDc by lia; exact Uspb).
assert (SHOKc : sh_ok SEGS CAx ca_SH Ec (mrestrict (w_H W4) mem4)) by (unfold sh_ok, ca_SH; constructor).
rewrite R1.
(* 0x87630 bnez a0: ignored answered 0 *)
psrr_branch_tok RUN BR HS SHOKc CAspan.
{ exfalso. rewrite branch_ne_U in Hc. apply negb_true_iff in Hc. apply Z.eqb_neq in Hc. apply Hc.
  assert (Hz : ew Ec 84 = Z_to_bv 64 0) by (rewrite A84; exact A0c).
  unfold U. cbn [sv_denot]. rewrite Hz. vm_compute. reflexivity. }
clear Hc.
(* ---- 0x87634 .. 0x8763c: a0 := c, a1 := name, jal reac_segconf_model ---- *)
paj_run_tok RUN HS HJc SHOKc CAspan.
{ awr_ok_tac. exact Uspc. }
lazymatch goal with Hfr : frame_of Ec _ (mrestrict _ _) (mrestrict _ _) |- _ =>
assert (K9 : ca_kept (rdW W4 mem4) (rdW W4 (ms_mem ms2)) (spZ regs - 8320) (spZ regs))
by (intros a Ha Hn; apply (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun a => spZ regs - 8320 <= a < spZ regs) Hfr);
  [ intros b wlo whi a' Hin Hrr; vm_compute in Hin;
    repeat (destruct Hin as [Hq0 | Hin]; [injection Hq0 as <- <- <-; cbn [base_val] in Hrr; rewrite ?Uspc in Hrr; lia|]);
    destruct Hin
  | lia | exact Hn ]) end.
clear HF HFr HG.
assert (K10 : ca_kept (rdW W mem) (rdW W4 (ms_mem ms2)) (spZ regs - 8320) (spZ regs))
  by (eapply ca_kept_trans; [exact K8 | exact K9]).
assert (ROD4 : arodata_okP SEGS SegInstB.RLO_A SegInstB.RHI_A B (rdW W4 (ms_mem ms2)))
  by (eapply ca_rodata_kept; [exact K10 | exact ROLOW | exact HROD]).
assert (QP4 : query_pre SEGS B ly S4 (rdW W4 (ms_mem ms2)) c name rcs nm).
{ eapply ca_qp_kept;
  [ exact (ca_kept_low _ _ _ _ K10 LOWSP) | exact PERMc | reflexivity
  | exact FRc | exact CLO | exact CHI | exact NLO | exact NHI | exact QP ]. }
pmkst HS.
prreg HS (1%bv : bv 5) T1. prreg HS (2%bv : bv 5) T2. prreg HS (3%bv : bv 5) T3. prreg HS (4%bv : bv 5) T4.
prreg HS (8%bv : bv 5) T8. prreg HS (10%bv : bv 5) T10. prreg HS (11%bv : bv 5) T11.
assert (HspX : spZ (ms_regs ms2) = spZ regs + -32)
  by (unfold spZ at 1; rewrite T2, OLDc, OLDb, OLDa by lia; rewrite Usp, unsigned_lit_small by lia; reflexivity).
assert (T3' : getr (ms_regs ms2) 3 = Z_to_bv 64 (as_gp B))
  by (rewrite T3, OLDc, OLDb, OLDa by lia; rewrite E3; exact Hgp).
assert (T4' : getr (ms_regs ms2) 4 = Z_to_bv 64 (as_tp B))
  by (rewrite T4, OLDc, OLDb, OLDa by lia; rewrite E4; exact Htp).
assert (T10' : getr (ms_regs ms2) 10 = Z_to_bv 64 c) by (rewrite T10, OLDc, OLDb, OLDa by lia; exact E10).
assert (T11' : getr (ms_regs ms2) 11 = Z_to_bv 64 name) by (rewrite T11, OLDc, OLDb, OLDa by lia; exact E11).
assert (HraX : YK0s.ret_ok (getr (ms_regs ms2) 1)) by (rewrite T1; apply ret_ok_codeptr_v; [lia | reflexivity]).
assert (Hra4X : 4096 <= bv_unsigned (getr (ms_regs ms2) 1)) by (rewrite T1, unsigned_lit_small by lia; lia).
assert (HchX : achain ly (rdW W4 (ms_mem ms2)) (spZ regs + -32) (s0Z (ms_regs ms2)) [])
  by (apply achain_low; unfold s0Z; rewrite T8, OLDc, OLDb, OLDa by lia; rewrite E11, unsigned_lit_small by lia; lia).
rewrite (SIGP SS_reac_segconf_model ltac:(unfold seg_prog_syms; cbn [In]; repeat (first [left; reflexivity | right]))).
replace (seg_af SS_reac_segconf_model) with AF_reac_segconf_model by (vm_compute; reflexivity).
eapply SRr_bind.
{ eapply (cl_callS B LAWS W4 (ms_regs ms2) (ms_mem ms2) _ 8320 (spZ regs) [] ly S W mem md [] ly S4 _ 0
    STK_reac_segconf_model_B [] 0 (-32) (getr (ms_regs ms2) 1) []
    (fun ly5 S5 W5 regs5 mem5 md5 =>
      getr regs5 10 = Z_to_bv 64 0 /\
      ca_kept (rdW W4 (ms_mem ms2)) (rdW W5 mem5) (spZ regs - 8320) (spZ regs) /\
      sa_noalloc B ly S4 ly5 S5)
    HJc HspX).
  - reflexivity.
  - lia.
  - unfold STK_reac_segconf_model_B, STK_reac_segconf_find_B, ESTACK; lia.
  - unfold STK_reac_segconf_model_B, STK_reac_segconf_find_B, ESTACK; lia.
  - exact T3'.
  - exact T4'.
  - reflexivity.
  - exact HraX.
  - exact Hra4X.
  - exact HchX.
  - intros HPRE4. eapply SRr_mono.
    + apply (MDL ly S4 W4 (ms_regs ms2) (ms_mem ms2) _ [] c name rcs nm HPRE4 ROD4 T10' Rc T11' Rn QP4).
      unfold EV_reac_segconf_model. lia.
    + cbv beta. unfold apost_base.
      intros W5 c5 _ (ly5 & S5 & regs5 & mem5 & md5 & -> & HJ5 & HP5 & (A0 & HKP & NA)).
      exists ly5, S5, regs5, mem5, md5. split; [reflexivity|]. split; [exact HJ5|]. split; [exact HP5|].
      split; [rewrite A0, MP0; reflexivity|]. split; [|exact NA].
      intros a Ha Hn. apply HKP; [lia | | intros []].
      rewrite HspX. unfold STK_reac_segconf_model_B, STK_reac_segconf_find_B, ESTACK. lia.
  - intros a Ha. exfalso. exact (inFP_nil a Ha). }
cbv beta. intros W5 c5 _ (ly5 & S5 & regs5 & mem5 & md5 & -> & HJd & HJid & HPd & (A0d & KCd & NAd)).
assert (Elyd : ly5 = ly) by (destruct NAd as (_ & Hx & _); exact Hx). subst ly5.
jafter_call_keep_pi HS 100%nat regs5 (mrestrict (w_H W5) mem5) HPd [0]%nat HS5.
match type of HS5 with ?t -> _ => assert (HRK : t); [|specialize (HS5 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; [| apply Forall_nil].
  eapply (region_kept_stack_sub SEGS B); [exact HJid | exact HJd | exact Uspc | lia | lia | lia | lia | lia |].
  intros a _ (r & Hr & _). destruct Hr. }
clear HS. rewrite <- restrict_mkst_fx in HS5. rename HS5 into HS.
assert (A104 : ew (havoc Ec 100 (map (getr regs5) CLOB)) 104 = getr regs5 10) by reflexivity.
remember (havoc Ec 100 (map (getr regs5) CLOB)) as Ed eqn:HEd.
assert (HEId : img_env VAL A_LIM Ed) by (rewrite HEd; apply img_env_havoc; [exact HEIc | cbv; lia]).
assert (OLDd : forall n, (n < 100)%nat -> ew Ed n = ew Ec n)
  by (intros n Hn; rewrite HEd; apply YN3v.ew_havoc_old; exact Hn).
assert (HAEd : env_agree 32 (Ereg regs ca_extra) Ed).
{ destruct HAEc as [HA1 HA2]. split; [intros n Hn; rewrite OLDd by lia; exact (HA1 n Hn) | rewrite HEd; exact HA2]. }
clear HEd.
assert (Uspd : bv_unsigned (ew Ed 2) = spZ regs) by (rewrite OLDd by lia; exact Uspc).
assert (SHOKd : sh_ok SEGS CAx ca_SH Ed (mrestrict (w_H W5) mem5)) by (unfold sh_ok, ca_SH; constructor).
rewrite T1.
(* 0x87640 bnez a0: model answered 0 *)
psrr_branch_tok RUN BR HS SHOKd CAspan.
{ exfalso. rewrite branch_ne_U in Hc. apply negb_true_iff in Hc. apply Z.eqb_neq in Hc. apply Hc.
  assert (Hz : ew Ed 104 = Z_to_bv 64 0) by (rewrite A104; exact A0d).
  unfold U. cbn [sv_denot]. rewrite Hz. vm_compute. reflexivity. }
clear Hc.
(* ---- 0x87644 .. 0x87654: ra, s0, s1 back from the frame, sp := sp0, ret ---- *)
paj_run_tok RUN HS HJd SHOKd CAspan.
{ awr_ok_tac. exact Uspd. }
assert (K11 : ca_kept (rdW W mem) (rdW W5 mem5) (spZ regs - 8320) (spZ regs))
  by (eapply ca_kept_trans; [exact K10 | exact KCd]).
lazymatch goal with Hfr : frame_of Ed _ (mrestrict _ _) (mrestrict _ _) |- _ =>
assert (K12 : ca_kept (rdW W5 mem5) (rdW W5 (ms_mem ms3)) (spZ regs - 8320) (spZ regs))
by (intros a Ha Hn; apply (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun a => spZ regs - 8320 <= a < spZ regs) Hfr);
  [ intros b wlo whi a' Hin Hrr; vm_compute in Hin;
    repeat (destruct Hin as [Hq0 | Hin]; [injection Hq0 as <- <- <-; cbn [base_val] in Hrr; rewrite ?Uspd in Hrr; lia|]);
    destruct Hin
  | lia | exact Hn ]) end.
assert (K13 : ca_kept (rdW W mem) (rdW W5 (ms_mem ms3)) (spZ regs - 8320) (spZ regs))
  by (eapply ca_kept_trans; [exact K11 | exact K12]).
prreg HS (1%bv : bv 5) F1.
eapply (RET W5 _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros mat'. unfold apost_base.
lazymatch goal with |- exists _ _ _ _ _, mkCfg (mkst ?r _ ?m _) ?d = _ /\ _ => exists ly, S5, r, m, d end.
split; [rewrite F1, OLDd, OLDc, OLDb, OLDa by lia; rewrite E1;
        unfold YK0s.ret_ok in Hra; rewrite Hra; reflexivity|].
split; [apply (ajournal_materialize SEGS B LAWS Hsegs); exact HJd|].
split; [eapply (aregs_preserved_of_st_ok SEGS _ Ed _ _ regs ca_extra HS); [exact HAEd | vm_compute; reflexivity]|].
split.
- intros a Ha Hn _. exact (K13 a Ha Hn).
- eapply ca_noalloc_trans; [eapply ca_noalloc_trans; [eapply ca_noalloc_trans; [exact NAa | exact NAb] | exact NAc]
    | exact NAd].
Qed.
End e.
End f.
End d.

(* evidence for the lane's answer: the walk rests only on the standard library axioms the released
   plugin-hostd/fuzz_command walks show, and keeps exactly the Section hypotheses the contract names. *)
Print Assumptions check_absent_walk.
About check_absent_walk.
