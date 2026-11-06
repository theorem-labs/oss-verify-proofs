(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the ASan+UBSan walk of sup_pool_config (plugin-hostd/fuzz_command, image
   fuzz_command.asan-ubsan, entry BASE + AF_sup_pool_config = 0x8bed0, 127 instructions): it proves a Theorem Labs lane's
   `tsup_pool_config_spec` (lib/B/Prog/sup_pool_config_c.v, a working branch 707acd856cb; the same text as at
   f490061c104) in the form of
   cgif_file_fuzzer's per-function walks: afn_pre at the entry, the symbolic executor over the position-abstract
   listing up to each call, the runtime's rules at the runtime calls (__asan_stack_malloc_0, the snprintf wrapper,
   the frame's release by its flag byte), the callee contracts record_c, arg_s_c, rec_shape_of_c and answer_c at the
   program calls (through cl_callS_wide / cl_callS_na), the return through paj_ret_at, and apost_base at the end.

   It is the B re-walk of the A walk lib/A/Prog/sup_pool_config.v (a working branch c4f188792bb),
   whose B code differs: B calls record() and arg_s() where A inlined record() and called xstrdup, and B inlines
   arg_i, so this function owns arg_i's class-0 side-stack frame (64 bytes, b = frame + 32) and its snprintf. The
   frame code (prologue, realignment `andi sp,sp,-32`, __asan_stack_malloc_0, header and shadow f1 f1 f1 f1 | f8 f8 |
   f3 f3, b unpoisoned around the snprintf and the second arg_s, the release through the flag byte) is arg_i's ASan
   walk's (lib/A/Prog/arg_i.v, a working branch 12dc52bfe84) and answer_code's ASan walk's
   (lib/A/Prog/answer_code.v, a working branch 2ba4488ce71); the B kit usage is socket_send's B walk
   (lib/B/Prog/socket_send.v, a working branch a470f91dbfb).

   Report and trap edges: none. The function has no `jal __asan_report_*`, no `unimp`, no UBSan handler call
   (capstone over the pin's .symtab, gen/traps.B.summary row `sup_pool_config 0`). Its branches: 0x8bf30 `beqz a2`
   on the use-after-return flag, read through the GOT word 0xa5fa8 at the record's const cell 0xb0c40 (= 1, lib/B/YF0m.v
   z4 (ANum 0xb0c40) 0x1, AR's const-cell law al_const; the executor decides it not taken); 0x8bf4c `bnez s2` and
   0x8c040 `beqz s2` on the side-stack frame (nonzero, __asan_stack_malloc_0's post; decided by the frame atom's
   fact), so the real-stack fallback 0x8bf50-0x8bf68 with its page probe and the real-stack release 0x8c074-0x8c090
   are not reached. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/B/Prog/sup_pool_config.v, with its module paths and module names changed; 234 of its 315 lines of code are new or changed and 1983 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/A/Prog/LLVMFuzzerTestOneInput_s10k.v, with its module paths and module names changed; 220 of its 256 lines of code are new or changed and 279 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, image A (fuzz_segconf.asan): the end of piece KWOK of segment A7 of
   reac_segconf_parse_file's walk, from strlen's return to the exits (segment A7's proof, 2026-10-30).
     w3_to_fun        0x88360 / 0x88798  `j 0x88064`: the return of either refuse call, to the funnel FUN (H_FUN)
     w3_after_strlen  0x8833c  addi a1, zero, 0x10; bltu a0, a1, 0x887a4:
                        |name| < 16: SEG 0x887a4 (H_SEG, the step pf_seg_step by pf_a7_w3_k.v w3_post_seg);
                        else 0x88344 .. 0x8835c: a2 = F_toolong's literal (listing object 49), a4 = 15, a0 = c,
                        a1 = lineno, a3 = the name, refuse (pf_a7_w3_c.v w3_refuse_step with pf_a7_s.v's site lemma
                        a7_refuse_site_8835c), then w3_to_fun at refuse's FP state (the step by w3_post_toolong).
   Each run is seeded by pf_a7_q.v's a7_seed (nothing writable), so the memory after it is the memory before it.
   Section hypotheses: REF (refuse), SIGP and OBJ (the listing's call targets and object atoms), VRO and SSPX only for
   w3_refuse_step's a6_base_move after the refuse call (pf_a7_w3_c.v's head comment). *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI00 YI04 YI09 YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pf_pieces_spec pfA_facts.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaRun PaShadow PaJournal SegSyms SegList
SegAddr SegPa SegObj SegGlob.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPaLib PaDenot PaLibG PaLibF PaLibH PaSB
PaCall PaCallRun PaArt PaFx.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPgBase SegABase refuse_c trim_c
  reac_segconf_parse_file_c SegInstA pf_pieces pf_a5_d pf_a5_k pf_a6_k pf_a7_f pf_a7_d pf_a7_m pf_a7_q pf_a7_s
  pf_a7_w3_k pf_a7_w3_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* the return addresses of the two refuse calls and of the strlen call (listing offsets) *)
Definition A7_RET_TOOLONG : Z := AF_reac_segconf_parse_file + 0x8e8.   (* 0x88360 *)
Definition A7_RET_NONAME : Z := AF_reac_segconf_parse_file + 0xd20.    (* 0x88798 *)
Definition A7_RET_STRLEN : Z := AF_reac_segconf_parse_file + 0x8c4.    (* 0x8833c *)

(* membership in a concrete list whose wanted element is syntactically there *)
Ltac w3_in := cbn [In]; repeat (first [left; reflexivity | right]).
(* a run that writes nothing: every region of the state has an empty write window *)
Ltac w3_awr :=
  lazymatch goal with |- awr_ok ?sg ?bb ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr0 ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok sg bb Ex rs' stk spx fp b0 bc fr0 lyx own) end;
  repeat (apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|]); apply awr_ok_nil.
(* after such a run the memory is the memory before it *)
Ltac w3_mem HF Hmem msx memx :=
  assert (Hmem : ms_mem msx = memx);
  [ apply functional_extensionality; let x := fresh "x" in intros x; unfold frame_of in HF; rewrite HF; [reflexivity|];
    let r := fresh "r" in let Hr := fresh "Hr" in let Ha := fresh "Ha" in
    intros (r & Hr & Ha);
    lazymatch type of Hr with In _ ?l => let l' := eval vm_compute in l in change (In r l') in Hr end;
    cbn [In] in Hr;
    repeat (destruct Hr as [<- | Hr]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; lia|]); destruct Hr
  | ].
(* the same, finding the run's frame fact HF : frame_of _ _ m0 (ms_mem m1) itself: ms_mem m1 = m0 *)
Ltac w3_memf Hmem :=
  lazymatch goal with HF : frame_of _ _ ?m0 (ms_mem ?m1) |- _ =>
    w3_mem HF Hmem m1 m0; clear HF end.
(* a register of a cut's list the run kept *)
Ltac w3_kept KEEP SRC :=
  rewrite KEEP by w3_in; eapply a5_rg_get; [exact SRC | cbn [PF_RL PF_RM a5_FI app]; w3_in].

Section d. Context {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Hypothesis REF : forall fx0 : YK11.FPState,
  @refuse_contract fx0 rc SK SEGS B (BASE + AF_refuse) STK_refuse RLO_A RHI_A seg_litA_rc gotwA guardA.
Hypothesis SIGP : seg_sig_prog (PI := PI).
Hypothesis OBJ : seg_val_objs (PI := PI).
(* FORCED by pf_a6_k.v's a6_base_move after a refuse call (w3_refuse_step), used nowhere else *)
Hypothesis VRO : seg_val_relro (PI := PI).
Hypothesis SSPX : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md -> sa_ssp (rdW W mem) gotwA guardA.

(* the literal a2 holds at 0x8835c: listing object 49 is F_toolong's text (SegInstA.v's map) *)
Lemma w3_lit_toolong : forall E, img_env VAL A_LIM E -> ew E (A_OBJ 49) = w64 (seg_litA_rc F_toolong).
Proof.
intros E HE. rewrite (img_env_atomP E (A_OBJ 49) HE) by (unfold A_OBJ, A_TEXT, A_LIM; lia).
rewrite (OBJ 49%nat ltac:(apply Nat.ltb_lt; vm_compute; reflexivity)).
unfold w64; f_equal; vm_compute; reflexivity.
Qed.
(* the literal a2 holds at 0x88794: listing object 66 is F_noname's text *)
Lemma w3_lit_noname : forall E, img_env VAL A_LIM E -> ew E (A_OBJ 66) = w64 (seg_litA_rc F_noname).
Proof.
intros E HE. rewrite (img_env_atomP E (A_OBJ 66) HE) by (unfold A_OBJ, A_TEXT, A_LIM; lia).
rewrite (OBJ 66%nat ltac:(apply Nat.ltb_lt; vm_compute; reflexivity)).
unfold w64; f_equal; vm_compute; reflexivity.
Qed.

(* the registers a run left as their own atoms keep the seed's values (any environment that agrees below 32) *)
Lemma w3_kept_st : forall (fx : YK11.FPState) E ss ms rX ex (l : list Z),
  st_ok (fx := fx) SEGS E ss ms -> env_agree 32 (Ereg rX ex) E ->
  forallb (fun r : bv 5 => sv_eqb (sr_get (ss_regs ss) r) (SOff (Z.to_nat (bv_unsigned r)) 0)) (map (Z_to_bv 5) l)
    = true ->
  forall k, In k l -> getr (ms_regs ms) (Z_to_bv 5 k) = getr rX (Z_to_bv 5 k).
Proof.
intros fx E ss ms rX ex l HS HA Hl k Hk.
exact (regs_kept_of_st_ok SEGS E ss ms rX ex (map (Z_to_bv 5) l) HS HA Hl (Z_to_bv 5 k) (in_map _ _ _ Hk)).
Qed.

(* pf_base after a run that wrote nothing: the run's journal, the run's registers *)
Lemma w3_base_step : forall (fx : YK11.FPState) v pos lyc Sc Wc rX rX' memc mdc mdc' sc,
  pf_base (fx := fx) B v pos lyc Sc Wc rX memc mdc sc ->
  ajournal SEGS B STK_reac_segconf_parse_file (pf_sp0 v) (seg_spec.RC_PARSE_W (p_c v)) (p_ly v) (p_S v) (p_W v)
    (p_mem v) (p_md v) [(5, pos)] lyc Sc Wc memc mdc' 0 ->
  pf_rg rX' (a5_FI B v) ->
  pf_base (fx := fx) B v pos lyc Sc Wc rX' memc mdc' sc.
Proof.
intros fx v pos lyc Sc Wc rX rX' memc mdc mdc' sc (CX & (_ & H2 & H3 & H4 & H5 & H6 & H7 & _) & OBJ0 & SL & FSH) HJ HR.
exact (conj CX (conj (conj HJ (conj H2 (conj H3 (conj H4 (conj H5 (conj H6 (conj H7 HR))))))) (conj OBJ0 (conj SL FSH)))).
Qed.

(* the callee-saved registers a run kept *)
Lemma w3_pres_of_keep : forall rX rX',
  (forall k, In k [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27] ->
     getr rX' (Z_to_bv 5 k) = getr rX (Z_to_bv 5 k)) ->
  aregs_preserved rX rX'.
Proof. intros rX rX' H r Hr. apply H. unfold acallee_saved in Hr. cbn [In]. lia. Qed.

(* the loop's registers at SEG are callee-saved *)
Lemma w3_seg_cs : forall v pos o ln np,
  Forall (fun rv => acallee_saved (fst rv)) (PF_RL v pos ++ PF_RM v o ln ++ [(25, np)]).
Proof.
  intros v pos o ln np. apply Forall_app; split; [apply a5_RL_cs|]. apply Forall_app; split; [apply a5_RM_cs|].
  repeat apply Forall_cons; try apply Forall_nil; cbn [fst]; unfold acallee_saved; lia.
Qed.
Lemma w3_fun_cs : forall v pos o ln, Forall (fun rv => acallee_saved (fst rv)) (PF_RL v pos ++ PF_RM v o ln).
Proof. intros v pos o ln. apply Forall_app; split; [apply a5_RL_cs | apply a5_RM_cs]. Qed.

Section x.
Context {fx : YK11.FPState}.

(** ** 0x88360 / 0x88798: `j 0x88064`, the return of a refuse call, to FUN *)
Lemma w3_to_fun : forall n k v pos lyc S2 (W2 : world SEGS) regs2 mem2 md2 cf' nm o ln d,
  k = A7_RET_TOOLONG \/ k = A7_RET_NONAME ->
  H_FUN B n ->
  pf_base B v pos lyc S2 W2 regs2 mem2 md2 PF_SC_LINE ->
  pf_mid v o ln d n ->
  pf_st0 v pos (rdW W2 mem2) cf' nm (length (skipn (pf_next (p_s v) o) (p_s v))) ->
  pf_rg regs2 (PF_RL v pos ++ PF_RM v o ln) ->
  SRr SEGS W2 (mkCfg (mkst regs2 (Z_to_bv 64 (BASE + k)) mem2 (seg_rom SEGS)) md2) (pf_postm B v (cf', None, nm) o ln).
Proof.
intros n k v pos lyc S2 W2 regs2 mem2 md2 cf' nm o ln d Hk HF0 HB HMID HST HRG.
pose proof (a5_fi_regs B v pos lyc S2 W2 regs2 mem2 md2 PF_SC_LINE HB) as HFI.
pose proof HB as (_ & (HJ & _) & _).
assert (HEI : img_env VAL A_LIM (a7_E regs2 v pos)) by apply a7_E_img.
pose proof (SRr_run_to_pi_AJ B LAWS) as RUNTOP.
pose proof (a7_seed B v pos lyc S2 W2 regs2 mem2 md2 k false HB) as HS.
destruct Hk as [-> | ->].
all: paj_run_to_sh RUNTOP HS HJ A7_FUN; [w3_awr|].
all: w3_mem HF Hmem ms mem2.
all: pmkst HS; rewrite Hmem in HJ |- *.
all: pose proof (a7_regs_kept regs2 v pos _ _ _ [2; 3; 4; 8; 9; 18; 19; 21; 22; 24; 26; 27] HS
    ltac:(vm_compute; reflexivity)) as KEEP.
all: apply (HF0 v pos lyc S2 W2 (ms_regs ms) mem2 _ cf' nm o ln d).
all: split; [|split; [exact HMID | split; [exact HST|]]].
all: try (apply (w3_base_step fx v pos lyc S2 W2 regs2 (ms_regs ms) mem2 md2 _ PF_SC_LINE HB HJ);
    unfold a5_FI, pf_rg; repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; w3_kept KEEP HFI).
all: unfold PF_RL, PF_RM, pf_rg; cbn [app]; repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
all: w3_kept KEEP HRG.
Qed.
End x.

Section y.
Context {fx : YK11.FPState}.

(** ** 0x8833c: strlen's return, the length test, SEG or the F_toolong refusal *)
Lemma w3_after_strlen : forall n v pos lyc Sc Wc regs3 mem3 md3 cf nm o ln d ci np,
  HA_FUN B n -> H_SEG B n ->
  pf_base B v pos lyc Sc Wc regs3 mem3 md3 PF_SC_LINE ->
  pf_mid v o ln d n ->
  pf_st0 v pos (rdW Wc mem3) cf nm (length (skipn o (p_s v))) ->
  strchr (pf_tline (p_s v) o) RBR = Some ci -> nth (S ci) (pf_tline (p_s v) o) 0 = 0 ->
  strncasecmp (a7_body (pf_tline (p_s v) o) ci) S_segment 7 = 0 ->
  nth 7 (a7_body (pf_tline (p_s v) o) ci) 0 = 32 \/ nth 7 (a7_body (pf_tline (p_s v) o) ci) 0 = 9 ->
  hd0 (a7_name (a7_body (pf_tline (p_s v) o) ci)) <> 0 ->
  sa_str (rdW Wc mem3) np (a7_name (a7_body (pf_tline (p_s v) o) ci)) ->
  pf_inb (pf_F v pos + PF_O_BUF) np (a7_name (a7_body (pf_tline (p_s v) o) ci)) ->
  pf_rg regs3 (PF_RL v pos ++ PF_RM v o ln ++ [(25, np)]) ->
  getr regs3 10 = w64 (Z.of_nat (length (a7_name (a7_body (pf_tline (p_s v) o) ci)))) ->
  SRr SEGS Wc (mkCfg (mkst regs3 (Z_to_bv 64 (BASE + A7_RET_STRLEN)) mem3 (seg_rom SEGS)) md3)
    (pf_postm B v (r_header cf nm (ln + 1) (pf_tline (p_s v) o)) o ln).
Proof.
intros n v pos lyc Sc Wc regs3 mem3 md3 cf nm o ln d ci np HFUN HSEG HB HMID HST HCL HNUL HKW H7 Hhd
  HSTR HINB HRG H10.
set (name := a7_name (a7_body (pf_tline (p_s v) o) ci)) in *.
pose proof (a5_fi_regs B v pos lyc Sc Wc regs3 mem3 md3 PF_SC_LINE HB) as HFI.
pose proof HB as (_ & (HJ & _ & _ & _ & _ & _ & HFRM & _) & _).
pose proof HMID as (Ho & _ & _).
pose proof HST as (HRC & HNM & HCNT).
pose proof HINB as (HI1 & HI2).
pose proof (proj1 (a5_rg_app _ _ _) HRG) as (HRL & HRG').
pose proof (proj1 (a5_rg_app _ _ _) HRG') as (HRM & H25).
pose proof pa_base_lo as HBLO. pose proof pa_B_ok as (HB1 & HB2 & HB3).
assert (Hln64 : 0 <= Z.of_nat (length name) < 2 ^ 64) by (unfold PF_O_BUF in *; lia).
pose proof (a7_seed B v pos lyc Sc Wc regs3 mem3 md3 A7_RET_STRLEN false HB) as HS.
assert (HEI : img_env VAL A_LIM (a7_E regs3 v pos)) by apply a7_E_img.
assert (E10 : ew (a7_E regs3 v pos) 10 = Z_to_bv 64 (Z.of_nat (length name)))
  by (rewrite (a7_ew_reg regs3 v pos 10 10%bv eq_refl); exact H10).
assert (SHOK : sh_ok SEGS a7_Bx [] (a7_E regs3 v pos) (mrestrict (w_H Wc) mem3)) by constructor.
pose proof (paj_run B LAWS) as RUN. pose proof (paj_run_to B LAWS) as RUNTO. pose proof (paj_branch (PI := PI)) as BR.
(* 0x8833c addi a1, zero, 0x10 *)
paj_run_tok RUN HS HJ SHOK Bspan.
{ w3_awr. }
w3_memf Hmem. clear HFr HG.
(* 0x88340 bltu a0, a1 *)
psrr_branch_tok RUN BR HS SHOK Bspan.
- (* |name| < 16: SEG *)
  rewrite branch_ltu_U, (U_atom _ 10 _ E10 Hln64), U_lit in Hc by lia. apply Z.ltb_lt in Hc.
  assert (Hc' : (length name < 16)%nat) by lia. clear Hc.
  rewrite (w3_post_seg cf nm (ln + 1) (pf_tline (p_s v) o) ci HCL HNUL HKW H7 Hhd Hc').
  paj_run_to_tok RUNTO HS HJ SHOK Bspan PF_SEG.
  { w3_awr. }
  w3_memf Hmem2. rewrite Hmem in Hmem2. clear HFr HG.
  pmkst HS. rewrite Hmem2 in HJ |- *.
  lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ _ _) _) _ => set (rS := rg) in * end.
  pose proof (a7_regs_kept regs3 v pos _ _ _ [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27] HS
    ltac:(vm_compute; reflexivity)) as KEEP.
  pose proof (w3_pres_of_keep regs3 rS KEEP) as HPR.
  apply (HSEG v pos lyc Sc Wc rS mem3 _ cf nm o ln d np name).
  split; [exact (w3_base_step fx v pos lyc Sc Wc regs3 rS mem3 md3 _ PF_SC_LINE HB HJ
    (a5_rg_pres regs3 rS _ HPR (a5_FI_cs B v) HFI))|].
  split; [exact HMID|]. split; [exact HST|]. split; [exact HSTR|]. split; [exact HINB|].
  split; [exact (w3_name_len name Hhd Hc')|].
  exact (a5_rg_pres regs3 rS _ HPR (w3_seg_cs v pos o ln np) HRG).
- (* 16 bytes or more: the F_toolong refusal, 0x88344 .. 0x8835c *)
  rewrite branch_ltu_U, (U_atom _ 10 _ E10 Hln64), U_lit in Hc by lia. apply Z.ltb_ge in Hc.
  assert (Hc' : (16 <= length name)%nat) by lia. clear Hc.
  rewrite (w3_post_toolong cf nm (ln + 1) (pf_tline (p_s v) o) ci HCL HNUL HKW H7 Hhd Hc').
  paj_run_tok RUN HS HJ SHOK Bspan.
  { w3_awr. }
  w3_memf Hmem2. rewrite Hmem in Hmem2. clear HFr HG.
  pmkst HS. rewrite Hmem2 in HJ |- *.
  pose proof (w3_kept_st fx _ _ _ regs3 (a7_extra v pos) [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27] HS
    (a7_E_agree regs3 v pos) ltac:(vm_compute; reflexivity)) as KEEP.
  cbn [ms_regs restrict] in KEEP.
  prreg HS (1%bv : bv 5) N1. prreg HS (10%bv : bv 5) N10. prreg HS (11%bv : bv 5) N11.
  prreg HS (12%bv : bv 5) N12. prreg HS (13%bv : bv 5) N13. prreg HS (14%bv : bv 5) N14.
  lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ _ _) ?mm) _ => set (rS := rg) in *; set (mdS := mm) in * end.
  pose proof (w3_pres_of_keep regs3 rS KEEP) as HPR.
  rewrite (SIGP SS_refuse ltac:(unfold seg_prog_syms; cbn [In]; repeat (first [left; reflexivity | right]))).
  replace (seg_af SS_refuse) with AF_refuse by (vm_compute; reflexivity).
  assert (HBc : pf_base B v pos lyc Sc Wc rS mem3 mdS PF_SC_LINE)
    by exact (w3_base_step fx v pos lyc Sc Wc regs3 rS mem3 md3 mdS PF_SC_LINE HB HJ
      (a5_rg_pres regs3 rS _ HPR (a5_FI_cs B v) HFI)).
  assert (R10 : getr rS 10 = w64 (p_c v)).
  { rewrite N10, (a7_ew_reg regs3 v pos 24 24%bv eq_refl). exact (a5_rg_get regs3 _ 24 _ HRL ltac:(w3_in)). }
  assert (R11 : getr rS 11 = w64 (ln + 1)).
  { rewrite N11, (a7_ew_reg regs3 v pos 26 26%bv eq_refl). exact (a5_rg_get regs3 _ 26 _ HRM ltac:(w3_in)). }
  assert (R12 : getr rS 12 = w64 (seg_litA_rc F_toolong)).
  { rewrite N12. change 290%nat with (A_OBJ 49). exact (w3_lit_toolong _ HEI). }
  assert (R13 : getr rS 13 = w64 np).
  { rewrite N13, (a7_ew_reg regs3 v pos 25 25%bv eq_refl). exact (a5_rg_get regs3 _ 25 _ H25 ltac:(w3_in)). }
  assert (R14 : getr rS 14 = w64 15) by (rewrite N14; reflexivity).
  assert (R1 : getr rS 1 = Z_to_bv 64 (BASE + A7_RET_TOOLONG)).
  { rewrite N1. unfold A7_RET_TOOLONG, AF_reac_segconf_parse_file. reflexivity. }
  pose proof (a7_st_of_base B v pos lyc Sc Wc rS mem3 mdS HBc) as HA7.
  pose proof (a7_refuse_site_8835c B v pos lyc Sc Wc mem3 mdS rS cf o ln d n ci np HA7 HRC
    (a7_cnt_zero cf (p_s v) o Ho HCNT) HMID HFRM R10 R11 R12 R13 R14 HSTR HINB) as HCALL.
  apply (w3_refuse_step B REF VRO SSPX v pos lyc Sc Wc rS mem3 mdS (Z_to_bv 64 (BASE + A7_RET_TOOLONG))
    cf nm ln F_toolong [AS name; AI 15] _ o HBc HCALL HNM R1).
  + apply ret_ok_codeptr_v; [unfold A7_RET_TOOLONG, AF_reac_segconf_parse_file; lia | vm_compute; reflexivity].
  + rewrite unsigned_lit_small by (unfold A7_RET_TOOLONG, AF_reac_segconf_parse_file; lia).
    unfold A7_RET_TOOLONG, AF_reac_segconf_parse_file. lia.
  + intros fx1 S2 W2 regs2 mem2 md2 Hfx1 HBr HP2 HRC2 HNM2.
    apply (w3_to_fun (fx := fx1) n A7_RET_TOOLONG v pos lyc S2 W2 regs2 mem2 md2 _ nm o ln d
      (or_introl eq_refl) (HFUN fx1) HBr HMID).
    * split; [exact HRC2|]. split; [exact HNM2|].
      exact (a7_cnt_refuse_next cf (ln + 1) F_toolong [AS name; AI 15] (p_s v) o Ho HCNT).
    * apply (a5_rg_pres rS regs2 _ HP2 (w3_fun_cs v pos o ln)).
      apply (a5_rg_pres regs3 rS _ HPR (w3_fun_cs v pos o ln)).
      apply (proj2 (a5_rg_app _ _ _)). split; [exact HRL | exact HRM].
Qed.
End y.
End e.
End f.
End d.
