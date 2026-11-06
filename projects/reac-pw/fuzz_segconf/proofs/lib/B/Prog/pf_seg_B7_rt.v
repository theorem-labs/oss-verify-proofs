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
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/check_round_trip.v, with its module paths and module names changed; 683 of its 754 lines of code are new or changed and 4982 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/pf_seg_B8a.v, with its module paths, module names and numbers changed; 328 of its 385 lines of code are new or changed and 697 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, image B (fuzz_segconf.asan-ubsan, pin c3796c0b38f3): two pieces of segment B7 of
   reac_segconf_parse_file's walk, the third and fourth conjuncts of pf_seg_B7_m.v's B7_S_REF (the B7 segment lane of
    the image-B G3 walk owner, a piece sub-lane, 2026-10-30). proves no function (kind: segment lemma of reac_segconf_parse_file's walk).
     b7rt_reftl_ok  : forall f0 n, HA_CLR B n -> H_REFTL (fx := f0) B n     (pf_pieces.v)
     b7rt_noname_ok : forall f0 n, HA_CLR B n -> H_NONAME (fx := f0) B n    (pf_seg_B7_m.v)
   The code (reac_segconf_parse_file.fuzz_segconf.asan-ubsan.s), no inline check, no UBSan trap branch:
     REFTL  0x887cc  ld a0,200(s1)        a0 = c (slot 0xc8, pf_fi); a2 = f's literal and a4 = k set before the cut
            0x887d0  mv a1,s6             a1 = lineno = ln + 1 (PF_RM)
            0x887d4  mv a3,s7             a3 = the name
            0x887d8  jal refuse           returns at 0x887dc (BASE + 0x3a1c)
            0x887dc  j 0x885fc            CLR
     NONAME 0x88c88  auipc a0,0xfff99
            0x88c8c  addi a2,a0,-1896     a2 = 0x21520 = seg_litA_rc F_noname (listing object 66, A_OBJ 66 = 307)
            0x88c90  ld a0,200(s1)        a0 = c
            0x88c94  mv a1,s6             a1 = ln + 1
            0x88c98  jal refuse           no variadic argument; returns at 0x88c9c (BASE + 0x3edc)
            0x88c9c  j 0x885fc            CLR
   The proof, for each: a seed at the cut whose one read-only region is the slot s1 + 0xc8 (its 8 bytes are a fresh
   atom 32 = c), a plain run to the `jal` (PaCallRun.v paj_run_shc), refuse_contract's premises from
   pf_seg_B7_s.v's b7_refuse_site_887d8 / b7_refuse_site_88c98, the call by PaFx.v cl_callSF at o = s1 - sp0 with
   STK1 = STK_refuse, FP1 = refuse_W c cf (inside the block c: b7k_refuse_W_sub and pf_obj's sa_heap) and the frame
   chain of pf_seg_B7_ch.v's b7_chain; after the call (b7rt_call) pf_base is rebuilt at the return state by
   pf_seg_B7_k.v's b7k_keeps_refuse + b7k_base_move (the six registers 2 3 4 8 9 20 from aregs_preserved and the
   run), cur_name by b7k_nm_move, c's state from refuse's post, the counters' room from INV_REFTL's room after the
   line (REFTL) or pf_seg_B7_f.v's b7_cnt_refuse_next (NONAME); then one plain run of the `j` to CLR (b7rt_jclr)
   and H_CLR at the FP state refuse returned.
   Section hypotheses taken: VRO, SIGP, OBJ, SSPX, REFUSE (Let LAWS). *)
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
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0d_tail.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pf_pieces_spec pfA_facts.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaRun PaShadow PaJournal SegSyms SegList SegAddr SegPa SegObj SegGlob.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPaLib PaDenot PaLibG PaLibF PaLibH PaCall PaCallRun PaArt PaFx.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import refuse_c reac_segconf_parse_file_c SegInstB
  pf_pieces pf_seg_B7_f pf_seg_B7_d pf_seg_B7_s pf_seg_B7_k pf_seg_B7_ch pf_seg_B7_m.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* ---------- small tools (after pf_seg_B10b_j.v's b10j tools) ---------- *)
Lemma b7rt_den_atom0 : forall E n, sv_denot E (SOff n 0) = ew E n.
Proof. intros E n. cbn [sv_denot]. rewrite Z.add_0_r. apply Z_to_bv_bv_unsigned. Qed.
Lemma b7rt_rg : forall rX L r x, pf_rg rX L -> In (r, x) L -> getr rX (Z_to_bv 5 r) = w64 x.
Proof. intros rX L r x H Hin. exact (proj1 (Forall_forall _ _) H (r, x) Hin). Qed.
(* refuse's footprint lies inside any live block holding all of c *)
Lemma b7rt_fp_in : forall c cf a bc (mc : Z), inFP (refuse_W c cf) a -> bc <= c ->
  c + seg_spec.SEG_C_SIZE <= bc + req_size mc -> bc <= a < bc + req_size mc.
Proof.
intros c cf a bc mc Ha H1 H2. apply b7k_refuse_W_in_block in Ha.
unfold seg_spec.RC_REFUSAL, seg_spec.RC_OVERFLOW, seg_spec.SEG_C_SIZE in *. lia.
Qed.
Ltac b7rt_in := cbn [In app PF_RL PF_RM]; repeat first [left; reflexivity | right].
Ltac b7rt_clear_md := repeat match goal with |- context [with_vm_backing (m_vm_lazy ?m) ?x ?m] =>
  let mdv := fresh "mdv" in set (mdv := with_vm_backing (m_vm_lazy m) x m) in *; clearbody mdv end.

(* ---------- the seed at a refuse site: the slot s1 + 0xc8 holds c, the extra atom 32 ---------- *)
Definition b7rt_slot_r : YP09.region :=
  YP09.mkRegion (Some 9%nat) 0xc8 0xd0 0 0 [YP09.mkChunk 0xc8 (CVal 8 (SOff 32 0))].
Definition b7rt_ss (pc : Z) : sstate := mkSS pc sr_atoms [b7rt_slot_r] None (mkFacts [] [] []).
(* the seed after the call, at the return pc: every register its own atom, no region *)
Definition b7rt_jss (pc : Z) : sstate := mkSS pc sr_atoms [] None (mkFacts [] [] []).

Section d. Context {rc : YM05.RunCeil} {SK : YI16.sink_head} {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation SIG s := (@pa_sigma _ seg_listing PI s).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Variable B : asyms.
Hypothesis VRO : seg_val_relro (PI := PI).
Hypothesis SIGP : seg_sig_prog (PI := PI).
Hypothesis OBJ : seg_val_objs (PI := PI).
Hypothesis SSPX : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md -> sa_ssp (rdW W mem) gotwA guardA.
Hypothesis REFUSE : forall fx0 : YK11.FPState, refuse_contract (fx := fx0) SEGS B (BASE + AF_refuse) STK_refuse
  RLO_A RHI_A seg_litA_rc gotwA guardA.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.

Definition b7rt_E (rX : bvmap 5 word) (c : Z) : env := Eimg (Ereg rX [Z_to_bv 64 c]).
Lemma b7rt_ew32 : forall rX c, ew (b7rt_E rX c) 32 = Z_to_bv 64 c.
Proof.
intros rX c. unfold b7rt_E. rewrite Eimg_low by (unfold A_TEXT; lia).
exact (ew_Ereg_extra rX [Z_to_bv 64 c] 0).
Qed.

(* F_noname's literal: listing object 66 is .str.8 (0x21520) *)
Lemma b7rt_noname_atom : forall E, img_env VAL A_LIM E -> ew E 307%nat = w64 (seg_litA_rc F_noname).
Proof.
intros E HE. rewrite (img_env_atomP E 307%nat HE) by (unfold A_TEXT, A_LIM; lia).
change 307%nat with (A_OBJ 66). rewrite (OBJ 66%nat ltac:(apply Nat.ltb_lt; vm_compute; reflexivity)).
unfold w64; f_equal; vm_compute; reflexivity.
Qed.

Section x0. Context {fx : YK11.FPState}.
Lemma b7rt_seed : forall (Wc : world SEGS) (rX : bvmap 5 word) memc (pc s1 c : Z),
  getr rX (Z_to_bv 5 9) = w64 s1 -> 0 <= s1 -> s1 + 0xd0 <= 2 ^ 64 -> 0 <= c < 2 ^ 64 ->
  rdword (rdW Wc memc) (s1 + 0xc8) = Some c ->
  st_ok_pi SEGS VAL (b7rt_E rX c) (b7rt_ss pc)
    (restrict (w_H Wc) (mkst rX (Z_to_bv 64 (BASE + pc)) memc (seg_rom SEGS))).
Proof.
intros Wc rX memc pc s1 c R9 H0 H1 Hc HW.
assert (U9 : bv_unsigned (ew (b7rt_E rX c) 9) = s1).
{ unfold b7rt_E. rewrite (ew_Eimg_Ereg_nat rX [Z_to_bv 64 c] 9 (Z_to_bv 5 9) eq_refl), R9.
  unfold w64. apply unsigned_lit_small. lia. }
rewrite restrict_mkst_fx. unfold b7rt_ss. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- constructor; [|constructor].
  unfold region_ok, b7rt_slot_r.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite U9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  constructor; [|constructor].
  apply (chunk_ok_val SEGS _ _ s1 0xc8 8%N (SOff 32 0) c).
  + rewrite b7rt_den_atom0, b7rt_ew32. reflexivity.
  + change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
  + lia.
  + exact (val_mem_of_rdword SEGS (w_H Wc) memc _ _ HW).
- cbn. tauto.
- unfold facts_ok; cbn; repeat split; first [exact I | apply Forall_nil | constructor].
Qed.

(* pf_base with another journal model and registers that agree on pf_fi's six *)
Lemma b7rt_base_regs : forall v pos lyc Sc Wc rX rX' memc mdc mdc' sc,
  pf_base B v pos lyc Sc Wc rX memc mdc sc ->
  ajournal SEGS B STK_reac_segconf_parse_file (pf_sp0 v) (seg_spec.RC_PARSE_W (p_c v)) (p_ly v) (p_S v) (p_W v)
    (p_mem v) (p_md v) [(5, pos)] lyc Sc Wc memc mdc' 0 ->
  (forall r, In r [2; 3; 4; 8; 9; 20] -> getr rX' (Z_to_bv 5 r) = getr rX (Z_to_bv 5 r)) ->
  pf_base B v pos lyc Sc Wc rX' memc mdc' sc.
Proof.
intros v pos lyc Sc Wc rX rX' memc mdc mdc' sc
  (HCX & (HJ & Hly & HSc & HPERM & HSAV & HFLAG & HFRM & HTF & HC8 & HRG0) & HOBJ & HSL & HFSH) HJ' KR.
split; [exact HCX|]. split; [|split; [exact HOBJ | split; [exact HSL | exact HFSH]]].
split; [exact HJ'|]. split; [exact Hly|]. split; [exact HSc|]. split; [exact HPERM|]. split; [exact HSAV|].
split; [exact HFLAG|]. split; [exact HFRM|]. split; [exact HTF|]. split; [exact HC8|].
unfold pf_rg in *. rewrite Forall_forall in HRG0 |- *. intros rv Hin.
rewrite (KR (fst rv)); [exact (HRG0 rv Hin)|].
cbn [In] in Hin. repeat (destruct Hin as [<- | Hin]; [cbn [fst In]; tauto|]). destruct Hin.
Qed.

Let RUNTO := SRr_run_to_pi_AJ (fx := fx) B LAWS.

(* the `j 0x885fc` after each refuse call (0x887dc, 0x88c9c): from the return pc with CLR's state, to CLR *)
Lemma b7rt_jclr : forall n RET, H_CLR B n -> (RET = 0x3a1c \/ RET = 0x3edc) ->
  forall v pos lyc Sc Wc rX memc mdc cf nm o ln d,
  INV_CLR B n v pos lyc Sc Wc rX memc mdc cf nm o ln d ->
  SRr SEGS Wc (mkCfg (mkst rX (Z_to_bv 64 (BASE + RET)) memc (seg_rom SEGS)) mdc)
    (pf_postm B v (cf, None, nm) o ln).
Proof.
intros n RET HCLR HRET v pos lyc Sc Wc rX memc mdc cf nm o ln d HI.
pose proof HI as (HB & HMID & HST & HRG).
pose proof HB as (HCX & HFI & HOBJ & HSL & HFSH).
pose proof HFI as (HJ & Hly & HSc & HPERM & HSAV & HFLAG & HFRM & HTF & HC8 & HRG0).
assert (HS : st_ok_pi SEGS VAL (Eimg (Ereg rX [])) (b7rt_jss RET)
  (restrict (w_H Wc) (mkst rX (Z_to_bv 64 (BASE + RET)) memc (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold b7rt_jss. apply pa_entry_st_ok_full;
    [apply regs_ok_Eimg_Ereg | vm_compute; reflexivity | constructor | cbn; tauto | split; [exact I | split; exact I]]. }
assert (HEI : img_env VAL A_LIM (Eimg (Ereg rX []))) by apply Eimg_env.
assert (HA0 : env_agree 32 (Ereg rX []) (Eimg (Ereg rX [])))
  by (split; [intros n0 Hn0; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
revert HS HEI HA0. generalize (Eimg (Ereg rX [])) as E. intros E HS HEI HA0.
destruct HRET as [-> | ->].
all: paj_run_to_sh RUNTO HS HJ PF_CLR.
all: try (intros a (r & Hr & _); cbn [b7rt_jss ss_mem In] in Hr; destruct Hr; fail).
all: cbn [ms_mem mkst] in HFr, HG, HF.
all: b7rt_clear_md.
all: assert (EM : ms_mem ms = memc) by (eapply frame_of_read_only; [|exact HF]; vm_compute; reflexivity).
all: clear HFr HG HF.
all: assert (QK : forall r, In r [2; 3; 4; 8; 9; 20; 18; 21; 26; 25; 22] ->
       getr (ms_regs ms) (Z_to_bv 5 r) = getr rX (Z_to_bv 5 r)) by
       (intros r Hr; apply (regs_kept_of_st_ok_pi E _ (restrict (w_H Wc) ms) rX []
          (map (Z_to_bv 5) [2; 3; 4; 8; 9; 20; 18; 21; 26; 25; 22]) HS HA0 ltac:(vm_compute; reflexivity));
        apply in_map; exact Hr).
all: pmkst HS.
all: lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg (Z_to_bv 64 (_ + ?k)) ?mm ?rom) ?mdx) _ =>
       change (mkCfg (mkst rg (Z_to_bv 64 (BASE + k)) mm rom) mdx) with (cfg_at SEGS (BASE + PF_CLR) rg mm mdx) end.
all: rewrite EM in HJ |- *.
all: apply (HCLR v pos lyc Sc Wc (ms_regs ms) memc mdv cf nm o ln d).
all: split; [|split; [exact HMID | split; [exact HST|]]].
all: try (apply (b7rt_base_regs v pos lyc Sc Wc rX (ms_regs ms) memc mdc mdv PF_SC_LINE HB HJ);
          intros r Hr; apply QK; cbn [In] in Hr |- *; lia).
all: unfold pf_rg in HRG |- *; rewrite Forall_forall in HRG |- *; intros rv Hin;
     rewrite (QK (fst rv)); [exact (HRG rv Hin)|];
     unfold PF_RL, PF_RM in Hin; cbn [app In] in Hin;
     repeat (destruct Hin as [<- | Hin]; [cbn [fst In]; tauto|]); destruct Hin.
Qed.
End x0.

Section x1. Context {fx : YK11.FPState}.

(* THE CALL of refuse at sp = s1 (0x887d8 / 0x88c98), its return state rebuilt into INV_CLR, the `j` to CLR *)
Lemma b7rt_call : forall n RET v pos lyc Sc Wc rX regsc memc mdc mdc' cf nm o ln d f args,
  HA_CLR B n -> (RET = 0x3a1c \/ RET = 0x3edc) ->
  pf_base B v pos lyc Sc Wc rX memc mdc PF_SC_LINE ->
  ajournal SEGS B STK_reac_segconf_parse_file (pf_sp0 v) (seg_spec.RC_PARSE_W (p_c v)) (p_ly v) (p_S v) (p_W v)
    (p_mem v) (p_md v) [(5, pos)] lyc Sc Wc memc mdc' 0 ->
  pf_mid v o ln d n ->
  pf_nm (rdW Wc memc) (pf_F v pos + PF_O_CN) nm ->
  pf_cnt (refuse cf (ln + 1) f args) (length (skipn (pf_next (p_s v) o) (p_s v))) ->
  pf_rg rX (PF_RL v pos ++ PF_RM v o ln) ->
  b7_refuse_call B v lyc Sc Wc memc regsc cf ln f args ->
  (forall r, In r [2; 3; 4; 8; 9; 18; 20; 21; 22; 25; 26] -> getr regsc (Z_to_bv 5 r) = getr rX (Z_to_bv 5 r)) ->
  getr regsc 1 = Z_to_bv 64 (BASE + RET) ->
  SRr SEGS Wc (mkCfg (mkst regsc (Z_to_bv 64 (BASE + AF_refuse)) memc (seg_rom SEGS)) mdc')
    (pf_postm B v (refuse cf (ln + 1) f args, None, nm) o ln).
Proof.
intros n RET v pos lyc Sc Wc rX regsc memc mdc mdc' cf nm o ln d f args HCLR HRET HB HJ' HMID HNM HCNT HRG HRC KR Q1.
pose proof (b7rt_base_regs v pos lyc Sc Wc rX rX memc mdc mdc' PF_SC_LINE HB HJ' (fun r _ => eq_refl)) as HB'.
pose proof HB' as (HCX & HFI & HOBJ & HSL & HFSH).
pose proof HFI as (HJ & Hly & HSc & HPERM & HSAV & HFLAG & HFRM & HTF & HC8 & HRG0).
destruct (b7k_cx B v HCX) as (Hc0 & Hc16 & HLS & HDJ & Hceil & Hslo & H47 & Hsp16).
pose proof (b7k_s1 (pf_sp0 v) Hsp16) as (S1a & S1b & S1c & S1d). rewrite <- b7k_s1_eq in S1a, S1b, S1c, S1d.
destruct (b7_chain B v pos lyc Sc Wc rX memc mdc' _ HB') as [ch1 HCH].
pose proof pf_B_values as (_ & _ & _ & _ & _ & _ & SKR & SKP & _).
pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (AC & _).
destruct HRC as (HROD1 & R10 & Hc64 & R11 & Hl64 & R12 & Hf64 & HPRE & HROOM1 & HEV1).
assert (B2 : (2%bv : bv 5) = Z_to_bv 5 2) by (apply bv_eq; reflexivity).
assert (B3 : (3%bv : bv 5) = Z_to_bv 5 3) by (apply bv_eq; reflexivity).
assert (B4 : (4%bv : bv 5) = Z_to_bv 5 4) by (apply bv_eq; reflexivity).
assert (B8 : (8%bv : bv 5) = Z_to_bv 5 8) by (apply bv_eq; reflexivity).
assert (D16 := Z.div_mod (pf_s1 v - pf_sp0 v) 16 ltac:(lia)). rewrite S1d in D16.
eapply SRr_bind.
{ eapply (cl_callSF (fx := fx) B LAWS Wc regsc memc _ STK_reac_segconf_parse_file (pf_sp0 v)
    (seg_spec.RC_PARSE_W (p_c v)) (p_ly v) (p_S v) (p_W v) (p_mem v) (p_md v) [(5, pos)] lyc Sc mdc' 0
    STK_refuse (refuse_W (p_c v) cf) EV_refuse (pf_s1 v - pf_sp0 v) (Z_to_bv 64 (BASE + RET)) ch1
    (fun ly2 S2 W2 regs2 mem2 md2 =>
       sa_rconf (rdW W2 mem2) (p_c v) (refuse cf (ln + 1) f args) /\ sa_noalloc B lyc Sc ly2 S2) HJ).
  - unfold spZ. rewrite B2, KR by b7rt_in. rewrite (b7rt_rg rX _ 2 (pf_s1 v) HRG0) by b7rt_in.
    rewrite b7k_w64_u by lia. lia.
  - exact S1d.
  - lia.
  - rewrite SKR. lia.
  - rewrite SKR, SKP. lia.
  - rewrite B3, KR by b7rt_in. apply (b7rt_rg rX _ 3 _ HRG0). b7rt_in.
  - rewrite B4, KR by b7rt_in. apply (b7rt_rg rX _ 4 _ HRG0). b7rt_in.
  - exact Q1.
  - destruct HRET as [-> | ->]; (apply ret_ok_codeptr_v; [lia | reflexivity]).
  - destruct HRET as [-> | ->]; rewrite unsigned_lit_small by lia; lia.
  - replace (pf_sp0 v + (pf_s1 v - pf_sp0 v)) with (pf_s1 v) by lia.
    replace (s0Z regsc) with (pf_sp0 v); [exact HCH|].
    unfold s0Z. rewrite B8, KR by b7rt_in. rewrite (b7rt_rg rX _ 8 (pf_sp0 v) HRG0) by b7rt_in.
    rewrite b7k_w64_u by lia. reflexivity.
  - intros HPRE1. eapply SRr_mono.
    { apply (REFUSE fx lyc Sc Wc regsc memc mdc' ch1 (p_c v) (ln + 1) (seg_litA_rc f) (ln + 1) cf f args
        HPRE1 HROD1 R10 Hc64 R11 Hl64 R12 Hf64 HPRE HROOM1 HEV1). }
    cbv beta. intros W' c' _ (fx' & ly' & S' & regs' & mem' & md' & -> & Hf1 & Hf2 & HJ1 & HP1 & HK1).
    exists fx', ly', S', regs', mem', md'. split; [rewrite Q1; reflexivity|].
    split; [exact Hf1|]. split; [exact Hf2|]. split; [exact HJ1|]. split; [exact HP1 | exact HK1].
  - intros a Ha. left. split; [exact (b7k_refuse_W_sub _ _ _ Ha)|].
    pose proof HOBJ as (_ & _ & _ & _ & HCB & _).
    destruct (b7k_heap_bounds B lyc Sc Wc memc mdc' (p_c v) seg_spec.SEG_C_SIZE (proj1 HJ) HCB
      ltac:(unfold seg_spec.SEG_C_SIZE; lia)) as (bc & mc & Hinc & Hbc1 & Hbc2 & _).
    exists bc, mc. split; [exact Hinc|]. exact (b7rt_fp_in _ _ _ bc mc Ha Hbc1 Hbc2). }
cbv beta. intros W2 c2 _ (fx1 & ly2 & S2 & regs2 & mem2 & md2 & Hfx1 & -> & HJ2 & HJc2 & HP2 & (HRC2 & HNA2)).
destruct HNA2 as (HPERM2 & Hly2 & HS2e).
replace (pf_sp0 v + (pf_s1 v - pf_sp0 v)) with (pf_s1 v) in HJc2 by lia.
change (0 + EV_refuse) with 0 in HJ2.
pose proof (b7k_keeps_refuse B v pos lyc Sc Wc rX memc mdc' PF_SC_LINE cf ly2 S2 W2 mem2 md2 _ HB' HJc2 HPERM2)
  as KEEP.
pose proof KEEP as (K1 & K2 & K3 & K4).
assert (KR2 : forall r, In r [2; 3; 4; 8; 9; 20] -> getr regs2 (Z_to_bv 5 r) = getr rX (Z_to_bv 5 r)).
{ intros r Hr. cbn [In] in Hr. rewrite (HP2 r) by (unfold acallee_saved; lia). apply KR. cbn [In]. lia. }
pose proof (b7k_base_move B VRO SSPX fx1 v pos lyc Sc Wc rX memc mdc' PF_SC_LINE ly2 S2 W2 regs2 mem2 md2
  HB' Hfx1 HJ2 Hly2 HS2e HPERM2 KEEP KR2) as HB2.
assert (HCLR2 : INV_CLR (fx := fx1) B n v pos ly2 S2 W2 regs2 mem2 md2 (refuse cf (ln + 1) f args) nm o ln d).
{ split; [exact HB2|]. split; [exact HMID|]. split.
  - split; [exact HRC2|]. split; [|exact HCNT].
    apply (b7k_nm_move v pos (rdW Wc memc) (rdW W2 mem2) nm HNM).
    intros a Ha. apply K4. left. exact Ha.
  - unfold pf_rg in HRG |- *. rewrite Forall_forall in HRG |- *. intros rv Hin.
    assert (Hr : In (fst rv) [18; 21; 26; 25; 22]).
    { unfold PF_RL, PF_RM in Hin. cbn [app In] in Hin.
      repeat (destruct Hin as [<- | Hin]; [cbn [fst In]; tauto|]). destruct Hin. }
    cbn [In] in Hr.
    rewrite (HP2 (fst rv)) by (unfold acallee_saved; lia).
    rewrite KR by (cbn [In]; lia).
    exact (HRG rv Hin). }
unfold pf_postm, PF_POSTr.
eapply (srr_apost_baseF_lift (fx := fx) SEGS fx1); [exact Hfx1|].
exact (b7rt_jclr (fx := fx1) n RET (HCLR fx1) HRET v pos ly2 S2 W2 regs2 mem2 md2 _ nm o ln d HCLR2).
Qed.

Let RUNP := SRr_run_pi_AJ (fx := fx) B LAWS.
Let RUNC := SRr_run_pi_AJ_call (fx := fx) B LAWS.

(* REFTL 0x887cc -> refuse(c, ln + 1, f, name, k) -> CLR *)
Lemma b7rt_reftl_x : forall n, HA_CLR B n -> H_REFTL (fx := fx) B n.
Proof.
intros n HCLR v pos lyc Sc Wc rX memc mdc cf nm o ln d f fa k np name HI.
destruct HI as (HB & HMID & HST0 & HROOM & HRTL & HSTR & HINB & HRG).
pose proof HB as (HCX & HFI & HOBJ & HSL & HFSH).
pose proof HFI as (HJ & Hly & HSc & HPERM & HSAV & HFLAG & HFRM & HTF & HC8 & HRG0).
destruct HST0 as (HRC & HNM & HCNT).
destruct HRTL as (HFK & Hfa). subst fa.
pose proof HCX as (_ & _ & _ & Hc64 & _).
destruct (b7k_cx B v HCX) as (Hc0 & Hc16 & HLS & HDJ & Hceil & Hslo & H47 & Hsp16).
pose proof (b7k_s1 (pf_sp0 v) Hsp16) as (S1a & S1b & S1c & S1d). rewrite <- b7k_s1_eq in S1a, S1b, S1c, S1d.
pose proof asan_consts as (AC & _).
assert (R9 : getr rX (Z_to_bv 5 9) = w64 (pf_s1 v)) by (apply (b7rt_rg rX _ 9 _ HRG0); b7rt_in).
assert (R22 : getr rX (Z_to_bv 5 22) = w64 (ln + 1)) by (apply (b7rt_rg rX _ 22 _ HRG); b7rt_in).
assert (R12 : getr rX (Z_to_bv 5 12) = w64 (seg_litA_rc f)) by (apply (b7rt_rg rX _ 12 _ HRG); b7rt_in).
assert (R14 : getr rX (Z_to_bv 5 14) = w64 k) by (apply (b7rt_rg rX _ 14 _ HRG); b7rt_in).
assert (R23 : getr rX (Z_to_bv 5 23) = w64 np) by (apply (b7rt_rg rX _ 23 _ HRG); b7rt_in).
assert (HC8' : rdword (rdW Wc memc) (pf_s1 v + 0xc8) = Some (p_c v))
  by exact (proj1 (Forall_forall _ _) HC8 (0xc8, p_c v) (or_introl eq_refl)).
pose proof (b7rt_seed (fx := fx) Wc rX memc PF_REFTL (pf_s1 v) (p_c v) R9 ltac:(lia) ltac:(lia) Hc64 HC8') as HS.
assert (HEI : img_env VAL A_LIM (b7rt_E rX (p_c v))) by apply Eimg_env.
assert (HA0 : env_agree 32 (Ereg rX [Z_to_bv 64 (p_c v)]) (b7rt_E rX (p_c v)))
  by (split; [intros n0 Hn0; unfold b7rt_E; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EE : forall n0 (r : bv 5), Z.of_nat n0 = bv_unsigned r -> ew (b7rt_E rX (p_c v)) n0 = getr rX r)
  by (intros n0 r Hn0; unfold b7rt_E; apply ew_Eimg_Ereg_nat; exact Hn0).
pose proof (b7rt_ew32 rX (p_c v)) as E32.
revert HS HEI HA0 EE E32. generalize (b7rt_E rX (p_c v)) as E. intros E HS HEI HA0 EE E32.
unfold cfg_at. change (w64 (BASE + PF_REFTL)) with (Z_to_bv 64 (BASE + PF_REFTL)).
(* 0x887cc .. 0x887d8: a0 = c, a1 = ln + 1, a3 = the name, the call *)
paj_run_shc RUNP RUNC HS HJ.
{ cbn [b7rt_ss ss_mem]. apply awr_ok_cons_ro; [unfold b7rt_slot_r; cbn; lia | apply awr_ok_nil]. }
b7rt_clear_md.
assert (EM : ms_mem ms = memc) by (eapply frame_of_read_only; [|exact HF]; vm_compute; reflexivity).
clear HFr HG HF.
assert (QK : forall r, In r [2; 3; 4; 8; 9; 12; 14; 18; 20; 21; 22; 25; 26] ->
    getr (ms_regs ms) (Z_to_bv 5 r) = getr rX (Z_to_bv 5 r)).
{ intros r Hr. apply (regs_kept_of_st_ok SEGS E _ (restrict (w_H Wc) ms) rX [Z_to_bv 64 (p_c v)]
    (map (Z_to_bv 5) [2; 3; 4; 8; 9; 12; 14; 18; 20; 21; 22; 25; 26]) HS HA0 ltac:(vm_compute; reflexivity)).
  apply in_map. exact Hr. }
prreg HS (1%bv : bv 5) Q1. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11.
prreg HS (12%bv : bv 5) Q12. prreg HS (13%bv : bv 5) Q13. prreg HS (14%bv : bv 5) Q14.
assert (Q10' : getr (ms_regs ms) 10 = w64 (p_c v)) by (rewrite Q10, E32; reflexivity).
assert (Q11' : getr (ms_regs ms) 11 = w64 (ln + 1)) by (rewrite Q11, (EE 22%nat (Z_to_bv 5 22) eq_refl); exact R22).
assert (Q12' : getr (ms_regs ms) 12 = w64 (seg_litA_rc f))
  by (rewrite Q12, (EE 12%nat (Z_to_bv 5 12) eq_refl); exact R12).
assert (Q13' : getr (ms_regs ms) 13 = w64 np) by (rewrite Q13, (EE 23%nat (Z_to_bv 5 23) eq_refl); exact R23).
assert (Q14' : getr (ms_regs ms) 14 = w64 k) by (rewrite Q14, (EE 14%nat (Z_to_bv 5 14) eq_refl); exact R14).
pmkst HS.
rewrite (SIGP SS_refuse ltac:(unfold seg_prog_syms; cbn [In]; repeat (first [left; reflexivity | right]))).
replace (seg_af SS_refuse) with AF_refuse by (vm_compute; reflexivity).
rewrite EM in HJ |- *.
assert (HST7 : b7_st B v pos lyc Sc Wc memc mdv)
  by (constructor; [exact HCX | exact HJ | exact Hly | exact HPERM | exact HOBJ | exact HFSH]).
pose proof (b7_refuse_site_887d8 B v pos lyc Sc Wc memc mdv (ms_regs ms) cf o ln d n f k np name HST7 HRC
  (pf_cnt_mono cf _ 0 ltac:(lia) HCNT) HMID HFRM HFK Q10' Q11' Q12' Q13' Q14' HSTR HINB) as HCALL.
assert (HCNT' : pf_cnt (refuse cf (ln + 1) f [AS name; AI k]) (length (skipn (pf_next (p_s v) o) (p_s v)))).
{ unfold pf_cnt in *. rewrite pfa_refuse_refused.
  destruct (refuse_proj cf (ln + 1) f [AS name; AI k]) as (_ & Ho & _). rewrite Ho. lia. }
assert (HRG' : pf_rg rX (PF_RL v pos ++ PF_RM v o ln)).
{ unfold pf_rg in HRG |- *. rewrite app_assoc in HRG. apply Forall_app in HRG as [H1 _]. exact H1. }
apply (b7rt_call n 0x3a1c v pos lyc Sc Wc rX (ms_regs ms) memc mdc mdv cf nm o ln d f [AS name; AI k] HCLR
  (or_introl eq_refl) HB HJ HMID HNM HCNT' HRG' HCALL).
- intros r Hr. apply QK. cbn [In] in Hr |- *. lia.
- exact Q1.
Qed.

(* NONAME 0x88c88 -> refuse(c, ln + 1, F_noname) -> CLR *)
Lemma b7rt_noname_x : forall n, HA_CLR B n -> H_NONAME (fx := fx) B n.
Proof.
intros n HCLR v pos lyc Sc Wc rX memc mdc cf nm o ln d HI.
destruct HI as ((HB & HMID & HST0 & HLEN & HRG) & HRH).
unfold b7_post. rewrite HRH.
pose proof HB as (HCX & HFI & HOBJ & HSL & HFSH).
pose proof HFI as (HJ & Hly & HSc & HPERM & HSAV & HFLAG & HFRM & HTF & HC8 & HRG0).
destruct HST0 as (HRC & HNM & HCNT).
pose proof HMID as (Ho & _).
pose proof HCX as (_ & _ & _ & Hc64 & _).
destruct (b7k_cx B v HCX) as (Hc0 & Hc16 & HLS & HDJ & Hceil & Hslo & H47 & Hsp16).
pose proof (b7k_s1 (pf_sp0 v) Hsp16) as (S1a & S1b & S1c & S1d). rewrite <- b7k_s1_eq in S1a, S1b, S1c, S1d.
pose proof asan_consts as (AC & _).
assert (R9 : getr rX (Z_to_bv 5 9) = w64 (pf_s1 v)) by (apply (b7rt_rg rX _ 9 _ HRG0); b7rt_in).
assert (R22 : getr rX (Z_to_bv 5 22) = w64 (ln + 1)) by (apply (b7rt_rg rX _ 22 _ HRG); b7rt_in).
assert (HC8' : rdword (rdW Wc memc) (pf_s1 v + 0xc8) = Some (p_c v))
  by exact (proj1 (Forall_forall _ _) HC8 (0xc8, p_c v) (or_introl eq_refl)).
pose proof (b7rt_seed (fx := fx) Wc rX memc B7_NONAME (pf_s1 v) (p_c v) R9 ltac:(lia) ltac:(lia) Hc64 HC8') as HS.
assert (HEI : img_env VAL A_LIM (b7rt_E rX (p_c v))) by apply Eimg_env.
assert (HA0 : env_agree 32 (Ereg rX [Z_to_bv 64 (p_c v)]) (b7rt_E rX (p_c v)))
  by (split; [intros n0 Hn0; unfold b7rt_E; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EE : forall n0 (r : bv 5), Z.of_nat n0 = bv_unsigned r -> ew (b7rt_E rX (p_c v)) n0 = getr rX r)
  by (intros n0 r Hn0; unfold b7rt_E; apply ew_Eimg_Ereg_nat; exact Hn0).
pose proof (b7rt_ew32 rX (p_c v)) as E32.
revert HS HEI HA0 EE E32. generalize (b7rt_E rX (p_c v)) as E. intros E HS HEI HA0 EE E32.
unfold cfg_at. change (w64 (BASE + B7_NONAME)) with (Z_to_bv 64 (BASE + B7_NONAME)).
(* 0x88c88 .. 0x88c98: a2 = F_noname's literal, a0 = c, a1 = ln + 1, the call *)
paj_run_shc RUNP RUNC HS HJ.
{ cbn [b7rt_ss ss_mem]. apply awr_ok_cons_ro; [unfold b7rt_slot_r; cbn; lia | apply awr_ok_nil]. }
b7rt_clear_md.
assert (EM : ms_mem ms = memc) by (eapply frame_of_read_only; [|exact HF]; vm_compute; reflexivity).
clear HFr HG HF.
assert (QK : forall r, In r [2; 3; 4; 8; 9; 18; 20; 21; 22; 25; 26] ->
    getr (ms_regs ms) (Z_to_bv 5 r) = getr rX (Z_to_bv 5 r)).
{ intros r Hr. apply (regs_kept_of_st_ok SEGS E _ (restrict (w_H Wc) ms) rX [Z_to_bv 64 (p_c v)]
    (map (Z_to_bv 5) [2; 3; 4; 8; 9; 18; 20; 21; 22; 25; 26]) HS HA0 ltac:(vm_compute; reflexivity)).
  apply in_map. exact Hr. }
prreg HS (1%bv : bv 5) Q1. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11.
prreg HS (12%bv : bv 5) Q12.
assert (Q10' : getr (ms_regs ms) 10 = w64 (p_c v)) by (rewrite Q10, E32; reflexivity).
assert (Q11' : getr (ms_regs ms) 11 = w64 (ln + 1)) by (rewrite Q11, (EE 22%nat (Z_to_bv 5 22) eq_refl); exact R22).
assert (Q12' : getr (ms_regs ms) 12 = w64 (seg_litA_rc F_noname))
  by (rewrite Q12; apply b7rt_noname_atom; exact HEI).
pmkst HS.
rewrite (SIGP SS_refuse ltac:(unfold seg_prog_syms; cbn [In]; repeat (first [left; reflexivity | right]))).
replace (seg_af SS_refuse) with AF_refuse by (vm_compute; reflexivity).
rewrite EM in HJ |- *.
assert (HST7 : b7_st B v pos lyc Sc Wc memc mdv)
  by (constructor; [exact HCX | exact HJ | exact Hly | exact HPERM | exact HOBJ | exact HFSH]).
pose proof (b7_refuse_site_88c98 B v pos lyc Sc Wc memc mdv (ms_regs ms) cf o ln d n HST7 HRC
  (pf_cnt_mono cf _ 0 ltac:(lia) HCNT) HMID HFRM Q10' Q11' Q12') as HCALL.
pose proof (b7_cnt_refuse_next cf (ln + 1) F_noname [] (p_s v) o Ho HCNT) as HCNT'.
apply (b7rt_call n 0x3edc v pos lyc Sc Wc rX (ms_regs ms) memc mdc mdv cf nm o ln d F_noname [] HCLR
  (or_intror eq_refl) HB HJ HMID HNM HCNT' HRG HCALL).
- intros r Hr. apply QK. exact Hr.
- exact Q1.
Qed.

End x1.

(** ** The two pieces of B7_S_REF (pf_seg_B7_m.v), at every ambient FP state *)
Theorem b7rt_reftl_ok : forall (f0 : YK11.FPState) (n : nat), HA_CLR B n -> H_REFTL (fx := f0) B n.
Proof. intros f0 n HC. exact (b7rt_reftl_x (fx := f0) n HC). Qed.

Theorem b7rt_noname_ok : forall (f0 : YK11.FPState) (n : nat), HA_CLR B n -> H_NONAME (fx := f0) B n.
Proof. intros f0 n HC. exact (b7rt_noname_x (fx := f0) n HC). Qed.

End d.
