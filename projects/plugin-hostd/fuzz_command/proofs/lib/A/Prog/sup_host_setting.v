(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: check_reply's ASan walk (fuzz_command.asan, 0x86d78) assembled from its
   segments, as proofs/cgif/cgif_file_fuzzer/lib/A/ACh5.v assembles cgif_close's (pb_cgif_closeX):
     s1 the entry to the memchr call, s2 memchr / check_reply_answer / sup_reply_code, s3 the code's split,
     s4 snprintf, s4b rec_code_declared, s5 strcmp, s6 strlen / rec_shape_of, s7 syntax_reply_matches twice,
     s8 the frame's release and the return.
   snprintf is the only call that changes the FP state, so s4b, s5 and s8 (the segments after it) are taken at every
   FP state and s4 uses them at the state the wrapper returns.
   `pb_check_reply` is tcheck_reply_spec (lib/A/Prog/check_reply_c.v). The walk's facts at the entry that the
   statement no longer states come from its premises: the record's cells (replace_str flag byte, stack guard, errno)
   from CmdRecCells' cmd_rec_cells, the recorder's GOT words from cmd_ro_ok's RO_ptr_a70xx bytes, the read-only
   ranges from CmdRecRo's cmd_ro_in_img, and the words' shadow from AR's zshadow_ok of the stack window
   [ly_stk_lo, ly_stk_hi) (the words lie in it: spZ regs <= w and w + WORDS_W + 12 <= ly_stk_hi ly). The kit lemmas
   take the image facts IMG (cmd_img_facts); the segments take CmdRecImg's cmd_heap_tail_vis, and its
   cmd_prog_unowned and cmd_rom_view_on at IMG, so no record fact is a Section hypothesis (the walk hypotheses keep
   cgif's names; the record facts are lemmas of lib/A/Prog/CmdRecFacts.v). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/check_reply.v, with its module names changed; 206 of its 240 lines of code are new or changed and 118 lines of the source are left out. *)
(* The ASan walk of sup_host_setting on plugin-hostd/fuzz_command, assembled from the segment lemmas of
   lib/A/Prog/sup_host_setting_s3.v .. _s7.v in the shape of proofs/cgif/cgif_file_fuzzer/lib/A/ACh1.v .. ACh8.v and
   AChc.v (one statement per program point, each proved from the next); the two loops by induction on the tokens
   left. arg_i reaches the snprintf wrapper and returns at some FP state fx1: the walk from AI on (hs_walk_ai) is
   proved in a closed section, so it holds at fx1, and hs_seg_al lifts its apost_base to the statement's
   apost_baseF. *)

(* tsup_host_setting_holds : tsup_host_setting_spec B MT (lib/A/Prog/sup_host_setting_c.v, as of
   statement passes 4, 4b and 5).

   The statement's premises are rearranged into the walk's entry facts (hs_cx, lib/A/Prog/sup_host_setting_s0.v):
   each string argument in astr_argA's block-arm shape (hs_str: its start is not 0 because a live block starts at
   or above 4096), and each token's tail, which the strlen and strcat wrappers read, by cmd_heap_tail_vis (the
   terminator lies inside the token's block: the statement's G2 (b)).

   Section hypotheses besides the statement's, under the walks' shared names and cgif's names, for
   per-binary facts the statement does not carry and lib/A/Prog/CmdRecFacts.v does not yet prove: HB, TL, MTL, SIGP
   (cmd_sig_prog), cmd_prog_img, cmd_prog_writable, cmd_ro_ok_of_aro, RRO, RELRO_IMG, cmd_ro_prog_apart,
   cmd_atail_kept, cmd_heap_tail_vis, and the kit's image facts IMG (CmdRecBase.cmd_img_facts). The composition with
   a callee that writes g_rec / record.spill (CL_CALL_PG's form) is proved here from the kit's cl_callS_wide
   (lib/A/Prog/PaNoChain.v) at every FP state, the one for arg_i (FP-existential post) in sup_host_setting_s4.v from
   PaFx.v's cl_callS_wideF; the runtime entries' read-only view is the kit's CmdRecImg.cmd_rom_view_on at IMG. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaNoChain.
From Stdlib Require Import String ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI00 YI04 YG0s YO0f.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YG0q YC5d YM05 YI16.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs RtString RtAPI.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdPaLib PaCall PaCallRun PaDenot.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaLibF PaLibG PaLibH PaSB PaArt.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob CmdBase CmdRep CmdObj CmdRo CmdZsh.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
rec_calls_free_c arg_line_c arg_i_c xstrdup_c mix_call_c sup_host_setting_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
sup_host_setting_s1 sup_host_setting_s0 sup_host_setting_s3 sup_host_setting_s4 sup_host_setting_s5
sup_host_setting_s6 sup_host_setting_s7.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import RecBLemmas.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require CmdRecBase CmdRecImg.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation SIG s := (@pa_sigma _ cmd_listing PI s).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.

(* ---- the walk from AI on, after arg_i (at the FP state it returned: this section is closed below, so its lemmas
   hold at every FP state); the two loops by induction on the tokens left ---- *)
Section loops.
Hypothesis HH : hs_hyps B MT.

(* the join loop: from each token's strcat return to xstrdup *)
Lemma hs_loop2 : forall x, ST_XS B MT x ->
forall d n, (n + d + 1 = length (i_toks x))%nat -> ST_L2C B MT x n.
Proof.
intros x HXS d. induction d as [|d IH]; intros n Hn.
- apply (hs_seg_l2c B MT); try exact HH; [intros Hlt; lia | intros _; exact HXS].
- apply (hs_seg_l2c B MT); try exact HH; [|intros Heq; lia].
  intros _. apply (hs_seg_l2s B MT); try exact HH. apply IH. lia.
Qed.

(* the length loop: from each token's head to the malloc return *)
Lemma hs_loop1 : forall x, ST_MAL B MT x ->
forall d n, (n + d + 1 = length (i_toks x))%nat -> ST_L1H B MT x n.
Proof.
intros x HMAL d. induction d as [|d IH]; intros n Hn.
- apply (hs_seg_l1h B MT); try exact HH.
  apply (hs_seg_l1r B MT); try exact HH; [intros Hlt; lia | intros _; exact HMAL].
- apply (hs_seg_l1h B MT); try exact HH.
  apply (hs_seg_l1r B MT); try exact HH; [|intros Heq; lia].
  intros _. apply IH. lia.
Qed.

(* the walk from AI, back from arg_i, to the return *)
Lemma hs_walk_ai : forall x, (1 <= length (i_toks x))%nat -> ST_AI B MT x.
Proof.
intros x Hn.
assert (HMIX : ST_MIX B MT x) by (apply (hs_seg_mix B MT); try exact HH).
assert (HFR : ST_FR B MT x) by (apply (hs_seg_fr B MT); try exact HH; exact HMIX).
assert (HXS : ST_XS B MT x) by (apply (hs_seg_xs B MT); try exact HH; exact HFR).
pose proof (hs_loop2 x HXS (length (i_toks x) - 1) 0 ltac:(lia)) as HL2.
assert (HMAL : ST_MAL B MT x) by (apply (hs_seg_mal B MT); try exact HH; exact HL2).
pose proof (hs_loop1 x HMAL (length (i_toks x) - 1) 0 ltac:(lia)) as HL1.
apply (hs_seg_ai B MT); try exact HH; exact HL1.
Qed.
End loops.
End e.
End f.
End d.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation SIG s := (@pa_sigma _ cmd_listing PI s).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.

Section walk.
Hypothesis HH : hs_hyps B MT.
(* the whole walk, from the entry: arg_i returns at some fx1, and the walk from AI is hs_walk_ai at fx1 *)
Lemma hs_walk : forall x, hs_cx B MT x ->
SRr SEGS (i_W x) (cfg_at SEGS (BASE + AF_sup_host_setting) (i_regs x) (i_mem x) (i_md x)) (hs_postF B MT x).
Proof.
intros x HCX.
assert (Hn : (1 <= length (i_toks x) <= 64)%nat).
{ destruct x as [ly S W regs mem md ch pl ptok ps line toks R O]. cbn in HCX |- *.
  destruct HCX as (_ & _ & _ & _ & _ & _ & _ & _ & H & _). exact H. }
assert (HAI : forall fx1 : YK11.FPState, ST_AI (fx := fx1) B MT x)
  by (intros fx1; exact (hs_walk_ai (fx := fx1) B MT HH x ltac:(lia))).
assert (HAL : ST_AL B MT x) by (apply (hs_seg_al B MT); try exact HH; exact HAI).
assert (HJOIN : ST_JOIN B MT x) by (apply (hs_seg_join B MT); try exact HH; exact HAL).
assert (HRCF : ST_RCF B MT x) by (apply (hs_seg_rcf B MT); try exact HH; exact HJOIN).
apply (hs_seg_entry B MT); try exact HH; [exact HCX | exact HJOIN | exact HRCF].
Qed.
End walk.

(* ---- the theorem ---- *)
(* the statement's own hypotheses (sup_host_setting_c.v:84-93), at every FP state *)
Hypothesis TRCF : forall fx0 : YK11.FPState, @trec_calls_free_spec fx0 rc SK PI B MT.
Hypothesis TARG_LINE : forall fx0 : YK11.FPState, @targ_line_spec fx0 rc SK PI B MT.
Hypothesis TARG_I : forall fx0 : YK11.FPState, @targ_i_spec fx0 rc SK PI B MT.
Hypothesis TXSTRDUP : forall fx0 : YK11.FPState, @txstrdup_spec fx0 rc SK PI B MT.
Hypothesis TMIX_CALL : forall fx0 : YK11.FPState, @tmix_call_spec fx0 rc SK PI B MT.
Hypothesis AMALLOC4 : forall fx0 : YK11.FPState, @amalloc04_rule fx0 rc SK SEGS B MT.
Hypothesis AFREE4 : forall fx0 : YK11.FPState, @afree04_rule fx0 rc SK SEGS B MT.
Hypothesis ASTRLEN : forall fx0 : YK11.FPState, @astrlen_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_strlen).
Hypothesis ASTRCAT : forall fx0 : YK11.FPState, @astrcat_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_strcat).
Hypothesis VOBJS : cmd_val_objs.
(* the walk's: the per-binary record (lib/A/AF0m.v), the malloc/free trampolines and shadow-base cells, the meter's
   laws *)
Hypothesis HB : CmdBSyms B.
Hypothesis TL : PALib B.
Hypothesis MTL : ameter_laws MT.
(* CL_CALL_PG's form (cl_callS with the inner footprint widened to the program's
   statics; rec_calls_free and arg_line write g_rec / record.spill), from the kit's cl_callS_wide at every FP state:
   each such footprint byte is a byte the caller may write, and none lies in the caller's stack window *)
Lemma hs_cl_call_pg : forall (fx0 : YK11.FPState) W (regsc : bvmap 5 word) memc pc STK sp0 FP ly S W0 mem md own lyc Sc
  mdc k STK1 FP1 EV1 (o : Z) raw ch1
  (K : alayout -> astate -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop),
  ajournal SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W memc mdc k ->
  spZ regsc = sp0 + o -> o mod 16 = 0 -> o <= 0 -> 0 <= STK1 -> STK1 - o <= STK ->
  getr regsc 3 = w64 (as_gp B) -> getr regsc 4 = w64 (as_tp B) ->
  getr regsc 1 = raw -> YK0s.ret_ok raw -> 4096 <= bv_unsigned raw ->
  achain lyc (aview SEGS (w_H W) memc) (sp0 + o) (s0Z regsc) ch1 ->
  (afn_pre SEGS B STK1 lyc Sc W regsc memc mdc ch1 ->
   SRr SEGS W (mkCfg (@mkst fx0 regsc pc memc (seg_rom SEGS)) mdc)
   (fun W2 c2 => exists ly2 S2 regs2 mem2 md2,
    c2 = mkCfg (@mkst fx0 regs2 raw mem2 (seg_rom SEGS)) md2 /\
    ajournal SEGS B STK1 (spZ regsc) FP1 lyc Sc W memc mdc [] ly2 S2 W2 mem2 md2 EV1 /\
    aregs_preserved regsc regs2 /\ K ly2 S2 W2 regs2 mem2 md2)) ->
  (forall a, inFP FP1 a -> (inFP FP a /\ exists b n, In (b, n) (ablocks B lyc Sc) /\ b <= a < b + req_size n)
    \/ in_tmp_block (ablocks B ly S) (ablocks B lyc Sc) a
    \/ (inFP FP a /\ Exists (in_zr a) (as_prog_static B) /\ in_img SEGS a)) ->
  SRr SEGS W (mkCfg (@mkst fx0 regsc pc memc (seg_rom SEGS)) mdc)
  (fun W2 c2 => exists ly2 S2 regs2 mem2 md2,
   c2 = mkCfg (@mkst fx0 regs2 raw mem2 (seg_rom SEGS)) md2 /\
   ajournal SEGS B STK sp0 FP ly S W0 mem md own ly2 S2 W2 mem2 md2 (k + EV1) /\
   ajournal SEGS B STK1 (sp0 + o) FP1 lyc Sc W memc mdc [] ly2 S2 W2 mem2 md2 EV1 /\
   aregs_preserved regsc regs2 /\ K ly2 S2 W2 regs2 mem2 md2).
Proof.
intros fx0 W regsc memc pc STK sp0 FP ly S W0 mem md own lyc Sc mdc k STK1 FP1 EV1 o raw ch1 K
  HJ Hsp Hal Hneg Hs1 Hbud Hgp Htp Hra Hraw Hra4 Hch Hcallee HF.
pose proof (AR_laws_ok SEGS B) as LAWS.
pose proof asan_consts as (C1 & _).
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (_ & _ & Hceil & Hslo & _).
apply (cl_callS_wide (fx := fx0) B LAWS W regsc memc pc STK sp0 FP ly S W0 mem md own lyc Sc mdc k STK1 FP1 EV1 o raw ch1 K
  HJ Hsp Hal Hneg Hs1 Hbud Hgp Htp Hra Hraw Hra4 Hch Hcallee).
- intros a Ha. unfold awr_byte, awr_prog_or_caller.
  destruct (HF a Ha) as [H1 | [H2 | H3]].
  + right; left. exact H1.
  + right; right; left. exact H2.
  + right; right; right; right; left. exact H3.
- intros ly2 S2 W2 regs2 mem2 md2 _ a Ha Hw _. exfalso.
  destruct (HF a Ha) as [(_ & b & n & Hb & Hr) | [(b & n & Hb & _ & Hr) | (_ & _ & Himg)]].
  + destruct (al_blocks _ _ LAWS _ _ _ _ _ b n HAR Hb) as (_ & _ & Hbc & _). lia.
  + destruct (al_blocks _ _ LAWS _ _ _ _ _ b n HAR Hb) as (_ & _ & Hbc & _). lia.
  + pose proof (pa_img_range a Himg). lia.
Qed.
(* cmd_sig_prog (lib/A/Prog/CmdObj.v; the walk hypothesis SIGP) *)
Hypothesis SIGP : cmd_sig_prog.
(* the program's statics (the template's forms) *)
Hypothesis cmd_prog_img : forall a, Exists (in_zr a) recb_PG -> in_img SEGS a.
Hypothesis cmd_prog_writable : forall ly S (W : world SEGS) mem md a,
  AR SEGS B ly S W mem md -> Exists (in_zr a) recb_PG -> writable_at SEGS (mrestrict (w_H W) mem) a.
(* cmd_ro_ok at any AR state from arodata_okP; arodata_ok_journalP's facts (CmdBase.v); the
   read-only range off the program's statics (cmd_ro_prog_apart) *)
Hypothesis cmd_ro_ok_of_aro : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md ->
  arodata_okP SEGS RLO RHI B (rdW W mem) -> cmd_ro_ok (rdW W mem).
Hypothesis RRO : ro_below_ofl SEGS RLO RHI.
Hypothesis RELRO_IMG : forall a, RLO <= a < RHI -> in_img SEGS a.
Hypothesis cmd_ro_prog_apart : forall a, in_roP SEGS RLO RHI a -> in_img SEGS a /\ ~ Exists (in_zr a) recb_PG.
(* the shared walk facts cmd_atail_kept and cmd_heap_tail_vis *)
Hypothesis cmd_atail_kept : forall ly S (W : world SEGS) mem md ly' S' (W' : world SEGS) mem' md' p n e,
  AR SEGS B ly S W mem md -> AR SEGS B ly' S' W' mem' md' ->
  ((In (p, n) (ablocks B ly S) /\ In (p, n) (ablocks B ly' S') /\ p <= e < p + n) \/
   (in_roP SEGS RLO RHI e /\ ~ Exists (in_zr e) (as_owned_static B))) ->
  atail_vis SEGS W mem e -> atail_vis SEGS W' mem' e.
Hypothesis cmd_heap_tail_vis : forall ly S (W : world SEGS) mem md p n e,
  AR SEGS B ly S W mem md -> In (p, n) (ablocks B ly S) -> p <= e < p + n -> atail_vis SEGS W mem e.
(* the image facts of the binary (the kit's CmdRecBase.cmd_img_facts; RecBClosed closes it by cmd_img_facts_tfib):
   the runtime entries' read-only view (RtDefs.rt_rom_view) from arodata_okP is CmdRecImg.cmd_rom_view_on *)
Hypothesis IMG : CmdRecBase.cmd_img_facts SEGS B.

Let HH : hs_hyps B MT :=
  {| hh_rcf := TRCF; hh_arg_line := TARG_LINE; hh_arg_i := TARG_I; hh_xstrdup := TXSTRDUP; hh_mix := TMIX_CALL;
     hh_malloc := AMALLOC4; hh_free := AFREE4; hh_strlen := ASTRLEN; hh_strcat := ASTRCAT; hh_vobjs := VOBJS;
     hh_HB := HB; hh_TL := TL; hh_MTL := MTL; hh_CL := hs_cl_call_pg; hh_sigp := SIGP; hh_prog_img := cmd_prog_img;
     hh_prog_writable := cmd_prog_writable; hh_ro_ok_of_aro := cmd_ro_ok_of_aro;
     hh_RRO := RRO; hh_RELRO_IMG := RELRO_IMG; hh_ro_prog_apart := cmd_ro_prog_apart;
     hh_atail_kept := cmd_atail_kept;
     hh_heap_tail := cmd_heap_tail_vis;
     hh_rom_view := CmdRecImg.cmd_rom_view_on SEGS B (AR_laws_ok SEGS B) HB IMG RLO RHI |}.

(* a string argument as the statement states it is one in hs_str's shape: a live block starts at or above 4096 *)
Lemma hs_str_of_blk : forall ly S (W : world SEGS) mem md (O : list (Z * Z)) p (x : list byte),
  AR SEGS B ly S W mem md ->
  in_blockA (ablocks B ly S) p (Z.of_nat (length x) + 1) ->
  Forall (fun qk => iv_apart p (Z.of_nat (length x) + 1) (fst qk) (snd qk)) O ->
  astr_atR (rdW W mem) p x -> Z.of_nat (length x) + 1 <= LMAX + 1 ->
  hs_str B ly S (rdW W mem) O p x.
Proof.
intros ly S W mem md O p x HAR Hb Hap Hs Hl.
pose proof (AR_laws_ok SEGS B) as LAWS.
pose proof Hb as (p0 & k & Hin & Hlo & Hhi).
destruct (al_blocks _ _ LAWS _ _ _ _ _ p0 k HAR Hin) as (_ & H4096 & _).
unfold hs_str. split; [lia|]. split; [exact Hs|]. split; [exact Hl|]. split; [exact Hb | exact Hap].
Qed.

Lemma hs_forall2_impl : forall {X Y : Type} (P Q : X -> Y -> Prop) (l1 : list X) (l2 : list Y),
  Forall2 P l1 l2 -> (forall a b, P a b -> Q a b) -> Forall2 Q l1 l2.
Proof. intros X Y P Q l1 l2 H HPQ. induction H; constructor; [apply HPQ; exact H | exact IHForall2]. Qed.

Lemma hs_forall2_nth : forall {X Y : Type} (P : X -> Y -> Prop) (l1 : list X) (l2 : list Y) i a b,
  Forall2 P l1 l2 -> nth_error l1 i = Some a -> nth_error l2 i = Some b -> P a b.
Proof.
intros X Y P l1 l2 i a b H. revert i. induction H as [|x y l1 l2 Hxy H IH]; intros i E1 E2.
- destruct i; discriminate E1.
- destruct i as [|i]; cbn in E1, E2.
  + injection E1 as <-. injection E2 as <-. exact Hxy.
  + exact (IH i E1 E2).
Qed.

Theorem tsup_host_setting_holds : tsup_host_setting_spec B MT.
Proof.
unfold tsup_host_setting_spec.
intros ly S W regs mem md ch pl ptok ps line toks R O HPRE HRM HROD HRO H10 Hpl H11 Hptok H12 Hn
  (Hlb & Hlap & Hlstr & Hllm) Hp0 Hp8 HARR Hlen HPTR HTOKS HWL HREP HFR HEV HLIVE HMOK.
pose proof (proj1 HPRE) as HAR.
pose proof (hs_str_of_blk ly S W mem md O pl line HAR Hlb Hlap Hlstr Hllm) as HLINE.
assert (HT : Forall2 (fun p w => hs_str B ly S (rdW W mem) O p w) ps toks).
{ apply (hs_forall2_impl _ _ ps toks HTOKS). intros p w (H1 & H2 & H3 & H4).
  exact (hs_str_of_blk ly S W mem md O p w HAR H1 H2 H3 H4). }
assert (HP2 : forall i p, nth_error ps i = Some p -> aval_mem (rdW W mem) (ptok + 8 * Z.of_nat i) 8 p).
{ intros i p E. exact (proj2 (HPTR i p E)). }
assert (HTAIL : forall i p w, nth_error ps i = Some p -> nth_error toks i = Some w ->
  atail_vis SEGS W mem (p + Z.of_nat (length w))).
{ intros i p w Ep Ew.
  destruct (hs_forall2_nth _ ps toks i p w HTOKS Ep Ew) as ((p0 & k & Hin & Hlo & Hhi) & _ & _ & _).
  exact (cmd_heap_tail_vis ly S W mem md p0 k (p + Z.of_nat (length w)) HAR Hin ltac:(lia)). }
exact (hs_walk HH (mkHsIn ly S W regs mem md ch pl ptok ps line toks R O)
  (conj HPRE (conj HROD (conj HRO (conj HRM (conj (conj Hpl Hptok) (conj H10 (conj H11 (conj H12 (conj Hn
  (conj HLINE (conj Hp0 (conj Hp8 (conj HARR (conj Hlen (conj HP2 (conj HT (conj HWL (conj HREP (conj HFR
  (conj HEV (conj HLIVE (conj HMOK HTAIL))))))))))))))))))))))).
Qed.
End e.
End f.
End d.
