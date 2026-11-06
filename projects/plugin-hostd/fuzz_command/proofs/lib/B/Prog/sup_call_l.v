(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the body of sup_call's ASan walk (plugin-hostd/fuzz_command, 0x8a95c): from
   the join 0x8a9d0, where record() has picked the call slot c (sup_call_s3.v sc_mid), to answer's entry after the
   epilogue and `j answer` (0x8aa40), where the tail's SC_T_stmt gives sup_call's post.

   0x8a9d0 .. 0x8a9fc: the two inline checks of the slot (both removed by the join's shadow entry mkSHE 9 0 56)
   and the stores c->fn := REC_CALL and c->nargs := 0; 0x8aa00 .. 0x8aa08: arg_i(c, id); 0x8aa0c .. 0x8aa14:
   arg_line(c, line); 0x8aa18 .. 0x8aa3c: the shape "resp 0" (0x21ce0), changes = 1, a0 := c, the five saved
   registers reloaded and sp += 48; 0x8aa40: `j answer`.

   The two calls go through the kit's cl_callS_wide (PaNoChain.v): their footprints are the slot's nargs and
   args[m] fields, which are bytes of the program's writable statics inside sup_call's own footprint SC_FP O, so
   they pass awr_byte's program-static case; no footprint byte lies in sup_call's stack window, so the rule's
   VIS premise is vacuous. The recorder step at the end is sup_call_s2.v's sc_rep_slot (table arm) or
   sc_rep_spill (spill arm), whose premises about the bytes since the ENTRY state are the join's (sc_mid's arm
   facts) composed with what this walk keeps.

   Pass-4/5 re-fit: the callee contracts hold at every FP state (forall fx0). arg_i
   reaches the snprintf wrapper (post apost_baseF), so it goes through PaFx.v's cl_callS_wideF with the entry's
   rounding-mode-0 premise and returns at some fx1 with fxrel fx fx1; the walk goes on in place at fx1
   as follows: the symbolic state after the call is moved to fx1 by YL05.v's st_ok_xfx
   (st_ok reads the FP state only in the f registers and fcsr, which mkst fills from the FP state it is given),
   the run lemma is bound again at fx1 (paj_run (fx := fx1)), arg_line (post apost_base) is called at fx1, and
   the tail's statement is applied at fx1, its apost_baseF lifted to the entry's fx by srr_apost_baseF_lift.
   Statement pass 5 removed astack_pres: the walk no longer derives it for the two calls; their frame chains are
   the empty one (s0 holds the line, a heap pointer below alloc_ceiling: achain_low). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/sup_call_b.v, with its module paths and module names changed; 713 of its 787 lines of code are new or changed and 873 lines of the source are left out. *)
(* sup_call's walk on the ASan+UBSan build of plugin-hostd/fuzz_command, part l: 0x8b05c .. answer's entry. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI04 YI09 YG0s YI00 YI16.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q YG0v YI0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdSyms CmdList CmdPa CmdPaLib PaLibG PaDenot PaLibF PaLibH.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaSB PaCallRun PaCall PaNoChain PaCallPg PaFx.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob CmdBase CmdRep CmdObj CmdRo CmdZsh.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdRecBase CmdRecRo CmdRecRest CmdRecFacts RecBLemmas RecBridge.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs RtFormat.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import xmalloc_c rec_canonical_c hand_back_c mix_call_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import record_c arg_s_c arg_line_c answer_c sup_call_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import sup_call_s3 sup_call_s0 sup_call_s1.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
(* decidable equality of blocks, to split on whether a new block was one of the recorder's *)
Definition scl_pdec : forall x y : Z * Z, {x = y} + {x <> y}.
Proof. decide equality; apply Z.eq_dec. Defined.


(* after each symbolic run the model is left as `with_vm_backing (m_vm_lazy md) mat md`, which doubles over a chain
   of runs; make it opaque right after each run (sup_resp's collapse_md) *)
Ltac collapse_md :=
lazymatch goal with |- SRr _ _ (mkCfg _ ?mdl) _ =>
first [ is_var mdl | let mdv := fresh "mdv" in set (mdv := mdl) in *; clearbody mdv ] end.
(* a run's write windows are bytes of the walk's own frame (0, fp) at F (EFx : frame_addr ly 0 fp = F) or of its
   shadow; the other regions write nothing *)
Ltac scl_awr AG EFx fp :=
let a := fresh "a" in let r := fresh "r" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
intros a (r & Hin & Hr);
lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end;
cbn [In] in Hin;
repeat (destruct Hin as [<- | Hin];
  [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; revert Hr; evalE AG; intros Hr;
    first [ exfalso; clear - Hr; lia
          | right; right; right; left; exists 0, fp; split; [left; reflexivity|]; rewrite EFx;
            first [ left; unfold in_zr; cbn [fst snd]; change (fs_frame_bytes 0) with 64; lia
                  | right; unfold in_zr, shadow_addr; cbn [fst snd]; rewrite <- SB_SHADOW_OFF;
                    change (fs_frame_bytes 0 / 8) with 8; unfold SB in *; lia ] ] | ]);
try destruct Hin.

Section w. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation SIG s := (@pa_sigma _ cmd_listing PI s).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
Hypothesis TARG_S : forall fx0 : YK11.FPState, @targ_s_spec fx0 rc SK PI B MT.
Hypothesis TARG_LINE : forall fx0 : YK11.FPState, @targ_line_spec fx0 rc SK PI B MT.
Hypothesis VOBJS : cmd_val_objs.
Hypothesis HB : CmdBSyms B.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis TLF : PALibF B.
Hypothesis MTL : ameter_laws MT.
Hypothesis FFL : frame_flag_lawP SEGS B.
Hypothesis SIGP : cmd_sig_prog.
Hypothesis IMG : cmd_img_facts SEGS B.

Let RUNP := SRr_run_pi_AJ (PL := PL_cmd) (PI := PI) B LAWS.
Let RUNC := SRr_run_pi_AJ_call (PL := PL_cmd) (PI := PI) B LAWS.

(* the listing's call targets are the callees' entries in the statements' form *)
Lemma scl_sig_s : SIG CS_arg_s = BASE + AF_arg_s.
Proof. rewrite (SIGP CS_arg_s); [reflexivity|]. cbn [cmd_prog_syms In]; repeat (first [left; reflexivity | right]). Qed.
Lemma scl_sig_line : SIG CS_arg_line = BASE + AF_arg_line.
Proof. rewrite (SIGP CS_arg_line); [reflexivity|]. cbn [cmd_prog_syms In]; repeat (first [left; reflexivity | right]). Qed.
Lemma scl_sig_ans : SIG CS_answer = BASE + AF_answer.
Proof. rewrite (SIGP CS_answer); [reflexivity|]. cbn [cmd_prog_syms In]; repeat (first [left; reflexivity | right]). Qed.

(* the footprint of arg_s / arg_line on the slot c with m arguments recorded: c->nargs and c->args[m] *)
Definition scl_fp (c m : Z) : list (Z * Z) :=
[(c + CALL_OFF_NARGS, c + CALL_OFF_NARGS + 4); (c + CALL_OFF_ARGS + 8 * m, c + CALL_OFF_ARGS + 8 * m + 8)].

Lemma scl_slot_rng : forall c,
((exists i, 0 <= i < REC_CALLS_MAX /\ c = A_G_REC + OFF_CALLS + CALL_SIZE * i) \/ c = A_REC_SPILL) ->
A_G_REC + OFF_CALLS <= c /\ c + CALL_SIZE <= A_REC_SPILL + SC_SIZE.
Proof.
intros c [(i & Hi & ->) | ->]; unfold A_G_REC, OFF_CALLS, CALL_SIZE, A_REC_SPILL, SC_SIZE, REC_CALLS_MAX in *; lia.
Qed.

(* a byte of that footprint is a byte of sup_call's footprint and of the program's statics, in the image *)
Lemma scl_fp_slot : forall O c m a,
((exists i, 0 <= i < REC_CALLS_MAX /\ c = A_G_REC + OFF_CALLS + CALL_SIZE * i) \/ c = A_REC_SPILL) ->
0 <= m < REC_ARGS_MAX -> inFP (scl_fp c m) a ->
inFP (SC_FP O) a /\ Exists (in_zr a) (as_prog_static B) /\ in_img SEGS a /\ inFP cmd_PG a /\
A_G_REC + OFF_CALLS <= a < A_REC_SPILL + SC_SIZE /\ c + 4 <= a < c + CALL_SIZE.
Proof.
intros O c m a Hc Hm Ha.
assert (Hr : c + 4 <= a < c + CALL_SIZE).
{ unfold scl_fp in Ha. rewrite !inFP_cons in Ha. unfold CALL_OFF_NARGS, CALL_OFF_ARGS, CALL_SIZE, REC_ARGS_MAX in *.
  destruct Ha as [H | [H | H]]; [lia | lia | destruct (inFP_nil a H)]. }
destruct Hc as [(i & Hi & ->) | ->].
- assert (HPG : inFP cmd_PG a).
  { unfold cmd_PG. rewrite !inFP_cons. left. unfold A_G_REC, OFF_CALLS, CALL_SIZE, REC_CALLS_MAX in *. lia. }
  split; [unfold SC_FP; rewrite !inFP_cons; right; left; unfold A_G_REC, OFF_CALLS, OFF_ANSWER, CALL_SIZE, REC_CALLS_MAX in *; lia|].
  split; [rewrite (ts_prog B HB); unfold TFIB_PROG_STATIC; apply Exists_cons_hd; unfold in_zr; cbn [fst snd];
    unfold A_G_REC, OFF_CALLS, CALL_SIZE, REC_CALLS_MAX in *; lia|].
  split; [exact (cif_prog_img SEGS B IMG a HPG)|]. split; [exact HPG|].
  unfold A_G_REC, OFF_CALLS, CALL_SIZE, A_REC_SPILL, SC_SIZE, REC_CALLS_MAX in *. lia.
- assert (HPG : inFP cmd_PG a).
  { unfold cmd_PG. rewrite !inFP_cons. right; left. unfold A_REC_SPILL, CALL_SIZE in *. lia. }
  split; [unfold SC_FP; rewrite !inFP_cons; right; right; right; left; unfold A_REC_SPILL, SC_SIZE, CALL_SIZE in *; lia|].
  split; [rewrite (ts_prog B HB); unfold TFIB_PROG_STATIC; apply Exists_cons_tl, Exists_cons_hd; unfold in_zr; cbn [fst snd];
    unfold A_REC_SPILL, CALL_SIZE in *; lia|].
  split; [exact (cif_prog_img SEGS B IMG a HPG)|]. split; [exact HPG|].
  unfold A_G_REC, OFF_CALLS, CALL_SIZE, A_REC_SPILL, SC_SIZE in *. lia.
Qed.

(* a byte of a live block is apart from the walk's frame (0, fpos), its shadow and the image *)
Lemma scl_blk_apart : forall ly S (W : world SEGS) mem md fpos p n a,
AR SEGS B ly S W mem md -> In (0, fpos) (frames S) -> In (p, n) (ablocks B ly S) -> p <= a < p + req_size n ->
(a < frame_addr ly 0 fpos \/ frame_addr ly 0 fpos + 64 <= a) /\
(a < SB + frame_addr ly 0 fpos / 8 \/ SB + frame_addr ly 0 fpos / 8 + 8 <= a) /\
(a < 0x10000 \/ 0x606000 <= a) /\ 4096 <= a /\ a < alloc_ceiling.
Proof.
intros ly S W mem md fpos p n a HAR Hfin Hin Ha.
pose proof asan_consts as (C1 & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hin) as (_ & Hp4k & Hpceil & Hpapp & _).
pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ _ _ 0 fpos HAR Hin Hfin) as Hsep.
pose proof (blk_off_imgP B _ _ _ _ _ _ _ HAR Hin) as Himg.
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 0 fpos HAR Hfin) as (HF4096 & HFceil & _).
change (fs_frame_bytes 0) with 64 in *.
set (F := frame_addr ly 0 fpos) in *.
pose proof (Z.div_mod F 8 ltac:(lia)) as D. pose proof (Z.mod_pos_bound F 8 ltac:(lia)) as M.
unfold zdisjoint in Hsep. cbn [fst snd] in Hsep. unfold off_img in Himg.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hpapp.
unfold SB. split; [lia|]. split; [lia|]. split; [lia|]. split; lia.
Qed.

(* every block the recorder's representation names is live and of positive size (the donor's sc_rep_blocks,
   an earlier version of lib/A/Prog/sup_call_s2.v, lines 100-131, over B's representation) *)
Lemma scl_call_blocks : forall bl (rd : reader) a c P, acall_at bl rd a c P ->
forall pn, In pn P -> In pn bl /\ 0 < snd pn.
Proof.
intros bl rd a c P (_ & _ & HL & _ & _ & _ & H7) pn Hin.
apply In_nth_error in Hin as [k Hk].
assert (Hk' : (k < length (snd c))%nat) by (rewrite <- HL; apply nth_error_Some; rewrite Hk; discriminate).
destruct (nth_error (snd c) k) as [s|] eqn:Hs; [|apply nth_error_None in Hs; lia].
destruct (H7 k s pn Hs Hk) as (_ & _ & G3 & G4 & _). split; [exact G3 | lia].
Qed.

Lemma scl_rep_blocks : forall bl (rd : reader) gr sc R Q, arep_at bl rd gr sc R Q ->
forall pn, In pn (lay_blocks Q) -> In pn bl /\ 0 < snd pn.
Proof.
intros bl rd gr sc R Q (_ & _ & _ & (_ & HL & _ & HC & HS & _) & HA & HR & _) pn Hin.
unfold lay_blocks in Hin. rewrite !in_app_iff in Hin. destruct Hin as [Hin|[Hin|[Hin|Hin]]].
- apply in_concat in Hin. destruct Hin as (P & HP & Hpn).
  apply In_nth_error in HP as [i Hi].
  destruct (nth_error (r_calls R) i) as [c|] eqn:Hc.
  + exact (scl_call_blocks _ _ _ _ _ (proj1 (HC i c P Hc Hi)) pn Hpn).
  + apply nth_error_None in Hc.
    assert (Hlt : (i < length (l_calls Q))%nat) by (apply nth_error_Some; rewrite Hi; discriminate). lia.
- exact (scl_call_blocks _ _ _ _ _ HS pn Hin).
- destruct (r_answer R) as [x|], (l_answer Q) as [q|]; cbn [aanswer_at oblk In] in HA, Hin; try contradiction.
  destruct Hin as [<-|[]]. destruct HA as (_ & _ & H3 & H4 & _). split; [exact H3 | lia].
- destruct (r_reply R) as [x|], (l_reply Q) as [q|]; cbn [areply_at oblk In] in HR, Hin; try contradiction.
  destruct Hin as [<-|[]]. destruct HR as (_ & _ & _ & H4 & H5 & H6 & _). split; [exact H5|].
  destruct x as [|b x]; [exfalso; apply H4; reflexivity|]. cbn [length] in H6. lia.
Qed.

(* the registers sc_regs speaks of, kept *)
Lemma scl_regs : forall regs regsc regsx F, sc_regs regs regsc F ->
(forall r : bv 5, In r [2; 3; 4; 8; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regsx r = getr regsc r) ->
sc_regs regs regsx F.
Proof.
intros regs regsc regsx F (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13) K.
unfold sc_regs, spZ in *.
rewrite (K 2%bv), (K 8%bv), (K 18%bv), (K 24%bv), (K 19%bv), (K 20%bv), (K 21%bv), (K 23%bv), (K 25%bv),
  (K 3%bv), (K 4%bv), (K 26%bv), (K 27%bv) by (cbn [In]; tauto).
repeat split; assumption.
Qed.

(* the walk's frame facts at a later state of the walk: the journal from the entry, the registers, the bytes at
   and above sp1 (the saves) and the flag-byte word *)
Lemma scl_live : forall ly S (W : world SEGS) regs mem md ch O fpos F FL lyc Sc (Wc : world SEGS) regsc memc mdc k
  lyx Sx (Wx : world SEGS) regsx memx mdx kx,
afn_pre SEGS B SUP_CALL_STK ly S W regs mem md ch ->
sc_live B ly S W regs mem md O fpos F FL lyc Sc Wc regsc memc mdc k ->
ajournal SEGS B SUP_CALL_STK (spZ regs) (SC_FP O) ly S W mem md [(0, fpos)] lyx Sx Wx memx mdx kx ->
(forall r : bv 5, In r [2; 3; 4; 8; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regsx r = getr regsc r) ->
(forall a, sc_sp1 (spZ regs) <= a < 2 ^ 64 -> rdW Wx memx a = rdW Wc memc a) ->
rdword (rdW Wx memx) (F + 56) = Some FL ->
sc_live B ly S W regs mem md O fpos F FL lyx Sx Wx regsx memx mdx kx.
Proof.
intros ly S W regs mem md ch O fpos F FL lyc Sc Wc regsc memc mdc k lyx Sx Wx regsx memx mdx kx HPRE HL HJx HRK HKHI HFLx.
destruct HL as (HJ & EF & EFL & HR & HFR & HFLW).
pose proof HPRE as (HAR & _).
pose proof HJ as (_ & Hlyc & _). pose proof HJx as (_ & Hlyx & _).
destruct (al_layout _ _ LAWS _ _ _ _ _ lyc HAR Hlyc) as (_ & Efc & _).
destruct (al_layout _ _ LAWS _ _ _ _ _ lyx HAR Hlyx) as (_ & Efx & _).
pose proof (sc_sp1_bounds (spZ regs)) as (Hsp1 & _).
assert (Hspu : spZ regs < 2 ^ 64)
  by (unfold spZ; pose proof (bv_unsigned_in_range 64 (getr regs 2)) as Hb; change (bv_modulus 64) with (2 ^ 64) in Hb; lia).
specialize (Efc 0 fpos). specialize (Efx 0 fpos).
split; [exact HJx|].
split; [rewrite Efx, <- Efc; exact EF|].
split; [unfold frame_addr, flag_addr in *; lia|].
split; [exact (scl_regs regs regsc regsx F HR HRK)|].
split; [apply (sc_frame_ext (rdW Wc memc)); [intros a Ha; apply HKHI; lia | exact HFR]|].
exact HFLx.
Qed.

Lemma sc_stage_l : SC_L_stmt B MT -> SC_B_stmt B MT.
Proof.
intros SCL ly S W regs mem md ch id pl line R O fpos F FL lyc Sc Wc regsc memc mdc t HFRM HPRE HAT.
pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HPRE as (HAFN & Hfr7 & HROD0 & HRO0 & H10 & Hid & H11 & Hpl & HLN & HREP0 & HEV & HLIVE & HMOK).
destruct HLN as (HINB & HAPO & HSTR0 & HLEN).
pose proof HAFN as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
destruct HAT as (HL & H22 & O1 & HREP1 & HBLK1 & HBB1 & HMLE1 & HSTRL & HDEC & HSH4 & HSH5).
pose proof HL as (HJ & EF & EFL & HR & HFR & HFLW).
pose proof HR as (Esp & E8r & E18r & E24r & E19r & E20r & E21r & E23r & E25r & E3r & E4r & E26r & E27r).
pose proof HJ as (HARc & Hlyc & _ & _ & _ & Hfrsc & Hnevc & Hk0 & _).
assert (HOin : forall pn, In pn O -> In pn (ablocks B ly S)) by exact (sc_O_live B ly S _ R O HREP0).
assert (Hfin : In (0, fpos) (frames Sc)) by (rewrite Hfrsc; left; reflexivity).
destruct (al_frames _ _ LAWS _ _ _ _ _ 0 fpos HARc Hfin) as (HFal & [HFhi _] & HFpres & HFSpres).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 0 fpos HARc Hfin) as (HF4096 & HFceil & HFhigh).
destruct (frame_al64 SEGS B _ _ _ _ _ 0 fpos HARc Hfin) as (HF64 & _ & _).
change (fs_frame_bytes 0) with 64 in HFpres, HFSpres, HFceil, HFhigh.
rewrite EF in HFal, HFhi, HFpres, HFSpres, HF4096, HFceil, HFhigh, HF64.
unfold shadow_addr in HFSpres. rewrite <- SB_SHADOW_OFF in HFSpres. change (64 / 8) with 8 in HFSpres.
pose proof (sc_sp1_bounds (spZ regs)) as (Hsp1 & Hsp1al).
pose proof (Z.div_mod F 8 ltac:(lia)) as HF8d. pose proof (Z.mod_pos_bound F 8 ltac:(lia)) as HF8b.
assert (HF8z : F mod 8 = 0) by (clear - HF64; Z.div_mod_to_equations; lia).
assert (HF8 : 8 * (F / 8) = F) by lia.
assert (HF8lo : 512 <= F / 8) by lia.
assert (HF8hi : F / 8 < 17592186044416) by lia.
assert (FFS : SUP_CALL_STK = ltac:(let v := eval vm_compute in SUP_CALL_STK in exact v)) by reflexivity.
destruct (rec_bridge_slot B lyc Sc _ R REC_CALL [] O1 HREP1) as (Hslot & _ & _ & _).
destruct (scl_slot_rng _ Hslot) as (Hc1 & Hc2).
(* the frame state at 0x8b05c: b's shadow bytes 4, 5 are 00 *)
assert (HSHOK : sc_shadow_ok (rdW Wc memc) F [(4, 0); (5, 0)]).
{ unfold sc_shadow_ok. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; cbn [fst snd];
  (split; [lia | split; [lia | assumption]]). }
pose proof (sc_seed (fx := fx) B LAWS FFL SC_PC_B ly S W regs mem md O fpos F FL lyc Sc Wc regsc memc mdc (EV_RECORD R)
  [(4, 0); (5, 0)] 4 6 HL HSHOK ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia) ltac:(lia)) as HS.
rewrite <- (Z.add_assoc BASE AF_sup_call SC_PC_B).
remember (sc_mid_E regs regsc FL) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold sc_mid_E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regsc r)
  by (intros n r Hn; subst E; unfold sc_mid_E; rewrite Eimg_low by (pose proof (bv_unsigned_in_range 5 r) as Hr5;
      change (bv_modulus 5) with 32 in Hr5; unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hn).
assert (HAE : env_agree 32 (Ereg regsc (sc_mid_extra regs FL)) E)
  by (subst E; unfold sc_mid_E; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (E32 : ew E 32 = Z_to_bv 64 FL)
  by (subst E; unfold sc_mid_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsc _ 0)).
clear HE.
assert (E2 : ew E 2 = Z_to_bv 64 (sc_sp1 (spZ regs)))
  by (rewrite (EE 2%nat 2%bv eq_refl), <- Esp; unfold spZ; symmetry; apply Z_to_bv_bv_unsigned).
assert (E8 : ew E 8 = Z_to_bv 64 (spZ regs))
  by (rewrite (EE 8%nat 8%bv eq_refl), E8r; unfold spZ; symmetry; apply Z_to_bv_bv_unsigned).
assert (E19 : ew E 19 = Z_to_bv 64 pl) by (rewrite (EE 19%nat 19%bv eq_refl), E19r, H11; reflexivity).
assert (E21 : ew E 21 = Z_to_bv 64 (F + 32)) by (rewrite (EE 21%nat 21%bv eq_refl), E21r; reflexivity).
assert (E22 : ew E 22 = Z_to_bv 64 (rec_slot R)) by (rewrite (EE 22%nat 22%bv eq_refl), H22; reflexivity).
assert (E23 : ew E 23 = Z_to_bv 64 (SB + F / 8)) by (rewrite (EE 23%nat 23%bv eq_refl), E23r; reflexivity).
assert (E24 : ew E 24 = Z_to_bv 64 F) by (rewrite (EE 24%nat 24%bv eq_refl), E24r; reflexivity).
assert (U2 : bv_unsigned (ew E 2) = sc_sp1 (spZ regs)) by (rewrite E2; apply unsigned_lit_small; lia).
assert (U8 : bv_unsigned (ew E 8) = spZ regs) by (rewrite E8; apply unsigned_lit_small; lia).
assert (U23 : bv_unsigned (ew E 23) = SB + F / 8) by (rewrite E23; apply unsigned_lit_small; unfold SB; lia).
assert (U24 : bv_unsigned (ew E 24) = F) by (rewrite E24; apply unsigned_lit_small; lia).
assert (AG : forall n, (n < 32)%nat -> ew E n = ew E n) by (intros; reflexivity).
assert (AD : ed E = ed E) by reflexivity.
assert (HSBv : SB = 2147450880) by reflexivity.
(* the frame, its shadow and the image are pairwise apart *)
pose proof (frm_off_imgP B lyc Sc Wc memc mdc 0 fpos HARc Hfin) as HFimg.
rewrite EF in HFimg. change (fs_frame_bytes 0) with 64 in HFimg. unfold off_img in HFimg.
assert (HFsh : F + 64 <= SB + F / 8 \/ SB + F / 8 + 8 <= F).
{ clear - HFhigh HF8d HF8b HFceil C1. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFhigh.
  unfold SB. destruct HFhigh as (_ & [Hlo | (Hhi & Hhi2)]); [left | right]; lia. }
assert (HSHceil : SB + F / 8 + 8 < alloc_ceiling) by (clear - HF8d HF8b HFceil C1; unfold SB; lia).
assert (Hsp1lo : alloc_ceiling + 96 <= sc_sp1 (spZ regs)) by (rewrite FFS in Hslo; lia).
(* 0x8b05c .. 0x8b064: a0 := c, a1 := b, the call of arg_s *)
paj_run_shc RUNP RUNC HS HJ.
{ scl_awr AG EF fpos. }
pmkst HS. collapse_md.
rename ms into ms1. rename mdv into mdv1.
(* the bytes outside the run's write windows (b's shadow bytes 4, 5 and the frame header) are the entry's *)
pose proof (kept_of_frame (segs := SEGS) E _ (w_H Wc) memc (ms_mem ms1)
  (fun x => (SB + F / 8 + 4 <= x < SB + F / 8 + 6) \/ (F <= x < F + 24)) HFr
  ltac:(intros b wlo whi a' Hin Hrr; vm_compute in Hin;
        repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr;
          rewrite ?U23, ?U24, ?U8, ?U2 in Hrr; cbv beta; lia|]); destruct Hin)) as KEEP1'.
assert (KEEP1 : forall a, 0 <= a < 2 ^ 64 -> ~ (SB + F / 8 + 4 <= a < SB + F / 8 + 6) -> ~ (F <= a < F + 24) ->
  rdW Wc (ms_mem ms1) a = rdW Wc memc a).
{ intros a Ha0 Ha1 Ha2. apply (KEEP1' a Ha0). cbv beta. intros [Hx|Hx]; [exact (Ha1 Hx) | exact (Ha2 Hx)]. }
clear KEEP1'.
pose proof (proj1 HJ) as HAR1.
destruct (al_frames _ _ LAWS lyc Sc Wc (ms_mem ms1) mdv1 0 fpos HAR1 Hfin) as (_ & _ & HFpres1 & HFSpres1).
change (fs_frame_bytes 0) with 64 in HFpres1, HFSpres1. rewrite EF in HFpres1, HFSpres1.
unfold shadow_addr in HFSpres1. rewrite <- SB_SHADOW_OFF in HFSpres1. change (64 / 8) with 8 in HFSpres1.
(* the registers at the call *)
prreg HS (1%bv : bv 5) P1. prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
prreg HS (10%bv : bv 5) P10. prreg HS (11%bv : bv 5) P11.
assert (RK1 : forall r : bv 5, In r [2; 3; 4; 8; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv ->
  getr (ms_regs ms1) r = getr regsc r).
{ intros r Hr.
  exact (regs_kept_of_st_ok SEGS E _ (restrict (w_H Wc) ms1) regsc (sc_mid_extra regs FL)
    [2; 3; 4; 8; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv HS HAE ltac:(vm_compute; reflexivity) r Hr). }
assert (Hsp1c : spZ (ms_regs ms1) = spZ regs + (sc_sp1 (spZ regs) - spZ regs))
  by (unfold spZ at 1; rewrite P2, U2; lia).
assert (Hsp1al16 : sc_sp1 (spZ regs) mod 16 = 0) by (clear - Hsp1al; Z.div_mod_to_equations; lia).
assert (Hal1 : (sc_sp1 (spZ regs) - spZ regs) mod 16 = 0)
  by (rewrite <- Zminus_mod_idemp_l, Hsp1al16, <- Zminus_mod_idemp_r, Hal16; reflexivity).
assert (Hgp1 : getr (ms_regs ms1) 3 = w64 (as_gp B)) by (rewrite P3, (EE 3%nat 3%bv eq_refl), E3r; exact Hgp).
assert (Htp1 : getr (ms_regs ms1) 4 = w64 (as_tp B)) by (rewrite P4, (EE 4%nat 4%bv eq_refl), E4r; exact Htp).
assert (Hra1 : YK0s.ret_ok (getr (ms_regs ms1) 1)) by (rewrite P1; apply ret_ok_codeptr_v; [lia | reflexivity]).
assert (Hra41 : 4096 <= bv_unsigned (getr (ms_regs ms1) 1)) by (rewrite P1, unsigned_lit_small by lia; lia).
assert (H10c : getr (ms_regs ms1) 10 = w64 (rec_slot R)) by (rewrite P10, E22; reflexivity).
assert (H11c : getr (ms_regs ms1) 11 = w64 (F + 32)) by (rewrite P11, E21; reflexivity).
(* the read-only bytes and the recorder at the call *)
assert (HROD1 : arodata_okP SEGS RLO RHI B (rdW Wc (ms_mem ms1)))
  by exact (sc_aro B HB LAWS IMG ly S W mem md O SUP_CALL_STK (spZ regs) [(0, fpos)] lyc Sc Wc (ms_mem ms1) mdv1
    (EV_RECORD R) HAR HOin HJ HROD0).
assert (HRO1 : cmd_ro_ok (rdW Wc (ms_mem ms1)))
  by exact (cmd_ro_ok_of_aro SEGS B LAWS HB IMG lyc Sc Wc (ms_mem ms1) mdv1 HAR1 HROD1).
assert (HO1in : forall pn, In pn O1 -> In pn (ablocks B lyc Sc))
  by exact (sc_O_live B lyc Sc _ (rec_record R REC_CALL []) O1 HREP1).
assert (KEEPREC1 : forall a, A_G_REC <= a < A_G_REC + REC_SIZE \/ A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE \/
    inFP (ablocks_fp O1) a -> rdW Wc (ms_mem ms1) a = rdW Wc memc a).
{ intros a [Ha | [Ha | Ha]].
  - unfold A_G_REC, REC_SIZE in Ha. apply KEEP1; lia.
  - unfold A_REC_SPILL, SC_SIZE in Ha. apply KEEP1; lia.
  - destruct (inFP_ablocks_fp_inv O1 a Ha) as (p & n & Hpn & Hr).
    destruct (scl_blk_apart lyc Sc Wc memc mdc fpos p n a HARc Hfin (HO1in _ Hpn) Hr) as (K1 & K2 & _ & K3 & K4).
    rewrite EF in K1, K2. apply KEEP1; lia. }
assert (HREP1' : rec_repA B lyc Sc (rdW Wc (ms_mem ms1)) (rec_record R REC_CALL []) O1)
  by exact (rec_repA_kept B lyc Sc _ lyc Sc _ (rec_record R REC_CALL []) O1 HREP1 HO1in KEEPREC1).
(* b holds the printed id, its shadow bytes are 00, and the frame's bytes are present *)
pose proof (dec_length id Hid) as DL.
assert (HDEC1 : astr_atR (rdW Wc (ms_mem ms1)) (F + 32) (dec id)).
{ apply (astr_atR_kept_r (rdW Wc memc)); [|exact HDEC]. intros x Hx. apply KEEP1; lia. }
assert (ZB1 : forall i, 4 <= i < 6 -> rdW Wc (ms_mem ms1) (SB + F / 8 + i) = Some 0).
{ lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
  pose proof (st_ok_region_nth Ex ssx msx 0 _ HS eq_refl) as HRG1 end.
  cbn [ms_mem restrict] in HRG1.
  intros i Hi. assert (Hc : i = 4 \/ i = 5) by lia.
  destruct Hc as [-> | ->]; (apply aview_of_val_mem1; [|lia]);
  (eapply field_of_region with (w := 1%N) (e := SLit 0) (v := 0);
   [exact HRG1 | exact U23 | cbn [In]; tauto | reflexivity | cbn; lia | cbn; lia]). }
assert (HAFOBJ : afobj SEGS B lyc Sc Wc (ms_mem ms1) (F + 32) (Z.of_nat (length (dec id)) + 1)).
{ split; [|split].
  - exists 0, fpos. split; [exact Hfin|]. split; [lia|]. rewrite EF.
    split; [exact HF8z|]. split; [lia|]. change (fs_frame_bytes 0) with 64. lia.
  - clear - HF8z HF8d HF8b. Z.div_mod_to_equations. lia.
  - intros x Hx. exists 0. split; [|left; reflexivity].
    unfold shadow_of_addr. rewrite <- SB_SHADOW_OFF.
    assert (Hi : 4 <= x / 8 - F / 8 < 6) by (clear - Hx HF8z HF8d HF8b DL; Z.div_mod_to_equations; lia).
    replace (SB + x / 8) with (SB + F / 8 + (x / 8 - F / 8)) by lia. exact (ZB1 _ Hi). }
assert (HTAIL1 : forall x, Some (dec id) = Some x -> atail_vis SEGS Wc (ms_mem ms1) (F + 32 + Z.of_nat (length x))).
{ intros x Hx. injection Hx as <-. intros a Ha. apply (aview_some_of_apresent SEGS).
  apply (proj1 (HFpres1 a ltac:(clear - Ha DL HF4096; Z.div_mod_to_equations; lia))). }
assert (Hlen1 : Z.of_nat (length (dec id)) + 1 <= LMAX + 1) by (unfold LMAX; lia).
(* the budgets at the call *)
assert (HEV1 : st_nev Sc + EV_ARG_S <= EV_MAX).
{ clear - Hnevc HEV. unfold EV_SUP_CALL, EV_ARG_S, EV_ARG_LINE, EV_ANSWER, EV_HAND_BACK, EV_REC_CANONICAL,
    EV_XMALLOC in *. lia. }
assert (HLIVE1 : blocks_bytes Sc + LIVE_ARG_S (Some (dec id)) <= LIVE_MAX).
{ clear - HBB1 HLIVE. unfold LIVE_SUP_CALL, LIVE_ARG_LINE, LIVE_REC_CANONICAL, LIVE_ANSWER, LIVE_HAND_BACK,
    LIVE_XMALLOC in *. lia. }
assert (HXMS : 0 <= XM_ARG_S MT (Some (dec id)))
  by (unfold XM_ARG_S, XM_XMALLOC; apply (mo_malloc_nonneg MT MTL); unfold LIVE_XMALLOC; lia).
assert (HXML : 0 <= XM_ARG_LINE MT line)
  by (unfold XM_ARG_LINE, XM_REC_CANONICAL, XM_XMALLOC; apply (mo_malloc_nonneg MT MTL); unfold LIVE_XMALLOC; lia).
assert (HXMA : 0 <= XM_ANSWER MT t).
{ unfold XM_ANSWER, XM_HAND_BACK, XM_XMALLOC.
  pose proof (mo_free_nonneg MT MTL).
  pose proof (mo_malloc_nonneg MT MTL (LIVE_XMALLOC (Z.of_nat (length t) + 1)) ltac:(unfold LIVE_XMALLOC; lia)). lia. }
assert (HMO1 : mo_ok MT Sc (XM_ARG_S MT (Some (dec id)))).
{ apply (mok_station MT S Sc (XM_SUP_CALL MT R id line t) (XM_RECORD MT R) _ MTL HMOK HMLE1 HXMS).
  unfold XM_SUP_CALL. lia. }
(* the frame facts and the callee's frame chain at the call *)
assert (HFL1 : rdword (rdW Wc (ms_mem ms1)) (F + 56) = Some FL)
  by (apply (sc_rdword_ext (rdW Wc memc)); [intros x Hx; apply KEEP1; lia | exact HFLW]).
assert (HL1 : sc_live B ly S W regs mem md O fpos F FL lyc Sc Wc (ms_regs ms1) (ms_mem ms1) mdv1 (EV_RECORD R)).
{ apply (scl_live ly S W regs mem md ch O fpos F FL lyc Sc Wc regsc memc mdc (EV_RECORD R)
    lyc Sc Wc (ms_regs ms1) (ms_mem ms1) mdv1 (EV_RECORD R) HAFN HL HJ RK1); [|exact HFL1].
  intros a Ha. apply KEEP1; lia. }
destruct (sc_chain B LAWS ly S W regs mem md ch O fpos F FL lyc Sc Wc (ms_regs ms1) (ms_mem ms1) mdv1
  (EV_RECORD R) HAFN HOin HL1) as (ch1 & Hch1).
assert (Hch1' : achain lyc (rdW Wc (ms_mem ms1)) (spZ regs + (sc_sp1 (spZ regs) - spZ regs)) (s0Z (ms_regs ms1)) ch1)
  by (replace (spZ regs + (sc_sp1 (spZ regs) - spZ regs)) with (sc_sp1 (spZ regs)) by lia; exact Hch1).
(* 0x8b064: arg_s(c, b) *)
rewrite scl_sig_s.
eapply SRr_bind.
{ eapply (cl_callS_pg (fx := fx) (L := cmd_listing) (PI := PI) B LAWS Wc (ms_regs ms1) (ms_mem ms1)
    (Z_to_bv 64 (BASE + AF_arg_s)) SUP_CALL_STK (spZ regs) (SC_FP O) ly S W mem md [(0, fpos)] lyc Sc mdv1
    (EV_RECORD R) ARG_S_STK (scl_fp (rec_slot R) 0) EV_ARG_S (sc_sp1 (spZ regs) - spZ regs)
    (getr (ms_regs ms1) 1) ch1 _ HJ Hsp1c Hal1 ltac:(lia)
    ltac:(unfold ARG_S_STK, ESTACK, XMALLOC_STK, ASTACK; lia)
    ltac:(rewrite FFS; unfold ARG_S_STK, ESTACK, XMALLOC_STK, ASTACK; lia)
    Hgp1 Htp1 eq_refl Hra1 Hra41 Hch1').
  - intros HPREc.
    exact (TARG_S fx lyc Sc Wc (ms_regs ms1) (ms_mem ms1) mdv1 _ (rec_slot R) (F + 32) REC_CALL
      (@nil (list byte)) (Some (dec id)) R O1 HPREc HROD1 HRO1 H10c H11c eq_refl HREP1'
      (or_intror (ex_intro _ (dec id) (conj eq_refl (conj HDEC1 (conj Hlen1 HAFOBJ)))))
      HTAIL1 HEV1 HLIVE1 HMO1).
  - intros a Ha.
    destruct (scl_fp_slot O (rec_slot R) 0 a Hslot ltac:(unfold REC_ARGS_MAX; lia) Ha) as (G1 & G2 & G3 & _).
    left. split; [exact G1 | right; split; [exact G2 | exact G3]]. }
cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJo2 & HJi2 & HP2 & HQ2).
cbv zeta in HQ2.
(* arg_s recorded the printed id: the table arm is impossible (nargs = 0 < 6) *)
destruct HQ2 as (HBB2 & HMLE2 & [(Hbad & _) | (_ & p1 & Hp1 & Hperm1 & Hfresh1 & HREP2)]);
  [cbn [length Z.of_nat] in Hbad; unfold REC_ARGS_MAX in Hbad; lia|].
cbn [length app] in Hperm1, Hfresh1, HREP2. change (sarg (Some (dec id))) with (dec id) in Hperm1, Hfresh1, HREP2.
set (n1 := Z.of_nat (length (dec id)) + 1) in Hperm1, Hfresh1, HREP2.
(* back at 0x8b068: the frame, its shadow, the flag word and the saves are kept *)
pose proof (proj1 HJi2) as HAR2.
pose proof HJi2 as (_ & Hly2 & _ & _ & _ & Hfrs2 & _ & _ & F1i & F2i & _ & F4i & _).
assert (Hfin2 : In (0, fpos) (frames S2)) by (rewrite Hfrs2; exact Hfin).
destruct (al_layout _ _ LAWS lyc Sc Wc (ms_mem ms1) mdv1 ly2 HAR1 Hly2) as (Eab2 & Efa2 & _).
assert (EF2 : frame_addr ly2 0 fpos = F) by (rewrite (Efa2 0 fpos); exact EF).
assert (EFL2 : flag_addr ly2 0 fpos = FL)
  by (pose proof (Efa2 0 fpos) as Ee; unfold frame_addr, flag_addr in *; lia).
destruct (al_frames _ _ LAWS ly2 S2 W2 mem2 md2 0 fpos HAR2 Hfin2) as (_ & _ & HFpres2 & HFSpres2).
change (fs_frame_bytes 0) with 64 in HFpres2, HFSpres2. rewrite EF2 in HFpres2, HFSpres2.
unfold shadow_addr in HFSpres2. rewrite <- SB_SHADOW_OFF in HFSpres2. change (64 / 8) with 8 in HFSpres2.
assert (HNFP1 : forall a, inFP (scl_fp (rec_slot R) 0) a -> A_G_REC + OFF_CALLS <= a < A_REC_SPILL + SC_SIZE)
  by (intros a Hf; destruct (scl_fp_slot O (rec_slot R) 0 a Hslot ltac:(unfold REC_ARGS_MAX; lia) Hf) as (_ & _ & _ & _ & Hr & _); exact Hr).
assert (KEEPC1 : forall a, F <= a < F + 64 \/ SB + F / 8 <= a < SB + F / 8 + 8 \/
    (alloc_ceiling <= a < 2 ^ 64 /\ ~ (sc_sp1 (spZ regs) - ARG_S_STK <= a < sc_sp1 (spZ regs))) ->
  rdW W2 mem2 a = rdW Wc (ms_mem ms1) a).
{ assert (HNF : forall a, F <= a < F + 64 \/ SB + F / 8 <= a < SB + F / 8 + 8 \/ alloc_ceiling <= a ->
    ~ inFP (scl_fp (rec_slot R) 0) a).
  { intros a Ha Hf. pose proof (HNFP1 a Hf) as Hr.
    unfold A_G_REC, OFF_CALLS, A_REC_SPILL, SC_SIZE in Hr. lia. }
  intros a [Ha | [Ha | (Ha & Haw)]].
  - apply (F4i 0 fpos a Hfin); [|apply HNF; left; exact Ha].
    left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite EF. change (fs_frame_bytes 0) with 64. lia.
  - apply (F4i 0 fpos a Hfin); [|apply HNF; right; left; exact Ha].
    right. unfold in_zr. cbn [fst snd]. rewrite EF. unfold shadow_addr. rewrite <- SB_SHADOW_OFF.
    change (fs_frame_bytes 0 / 8) with 8. lia.
  - apply (F1i a Ha); [clear - Haw; lia | apply HNF; right; right; lia]. }
rewrite P1.
jafter_call_keep_pi HS 48%nat regs2 (mrestrict (w_H W2) mem2) HP2 [0; 1; 2; 3]%nat HS2.
match type of HS2 with ?T -> _ => assert (HRK : T); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict].
  repeat apply Forall_cons; try apply Forall_nil;
  (split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val];
   rewrite ?U23, ?U24, ?U8; intros a Ha;
   [ apply (mbyte_of_aview SEGS); apply KEEPC1;
     first [ left; lia | right; left; lia | right; right; split; lia ]
   | intros _; apply (apresent_writable SEGS);
     first [ apply (proj1 (HFpres2 a ltac:(lia)))
           | let Hp := fresh "Hp" in
             pose proof (proj1 (HFSpres2 (a - (SB + F / 8)) ltac:(lia))) as Hp;
             replace (SB + F / 8 + (a - (SB + F / 8))) with a in Hp by lia; exact Hp
           | lia ] ]). }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
hei_havoc HS. rebaseE HS AG HEv. clear HEv.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
  assert (V19 : ew Ev 19 = Z_to_bv 64 pl) by (rewrite (AG 19%nat ltac:(lia)); exact E19);
  assert (V22 : ew Ev 22 = Z_to_bv 64 (rec_slot R)) by (rewrite (AG 22%nat ltac:(lia)); exact E22);
  assert (V23 : bv_unsigned (ew Ev 23) = SB + F / 8) by (rewrite (AG 23%nat ltac:(lia)); exact U23);
  assert (V24 : bv_unsigned (ew Ev 24) = F) by (rewrite (AG 24%nat ltac:(lia)); exact U24);
  assert (V8 : bv_unsigned (ew Ev 8) = spZ regs) by (rewrite (AG 8%nat ltac:(lia)); exact U8);
  assert (V2 : bv_unsigned (ew Ev 2) = sc_sp1 (spZ regs)) by (rewrite (AG 2%nat ltac:(lia)); exact U2);
  assert (HAE2 : env_agree 32 (Ereg regsc (sc_mid_extra regs FL)) Ev)
    by (split; [intros n Hn; rewrite (AG n Hn); exact (proj1 HAE n Hn) | rewrite AD; exact (proj2 HAE)]);
  assert (Vgp : ew Ev 3 = getr regsc 3) by (rewrite (AG 3%nat ltac:(lia)); exact (EE 3%nat 3%bv eq_refl));
  assert (Vtp : ew Ev 4 = getr regsc 4) by (rewrite (AG 4%nat ltac:(lia)); exact (EE 4%nat 4%bv eq_refl))
end.
(* 0x8b068 .. 0x8b078: b's shadow f8, a0 := c, a1 := line, the call of arg_line *)
paj_run_shc RUNP RUNC HS HJo2.
{ scl_awr AG EF2 fpos. }
pmkst HS. collapse_md.
rename ms into ms2. rename mdv into mdv2.
(* the bytes outside run 2's write windows are those at the arg_s call's return *)
pose proof (kept_of_frame (segs := SEGS) E0 _ (w_H W2) mem2 (ms_mem ms2)
  (fun x => (SB + F / 8 + 4 <= x < SB + F / 8 + 6) \/ (F <= x < F + 24)) HFr0
  ltac:(intros b wlo whi a' Hin Hrr; vm_compute in Hin;
        repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr;
          rewrite ?V23, ?V24, ?V8, ?V2 in Hrr; cbv beta; lia|]); destruct Hin)) as KEEP2'.
assert (KEEP2 : forall a, 0 <= a < 2 ^ 64 -> ~ (SB + F / 8 + 4 <= a < SB + F / 8 + 6) -> ~ (F <= a < F + 24) ->
  rdW W2 (ms_mem ms2) a = rdW W2 mem2 a).
{ intros a Ha0 Ha1 Ha2. apply (KEEP2' a Ha0). cbv beta. intros [Hx|Hx]; [exact (Ha1 Hx) | exact (Ha2 Hx)]. }
clear KEEP2'.
assert (Hc1' : 6173392 <= rec_slot R) by (unfold A_G_REC, OFF_CALLS in Hc1; lia).
assert (Hc2' : rec_slot R + 56 <= 6174616) by (unfold A_REC_SPILL, SC_SIZE, CALL_SIZE in Hc2; lia).
(* the bytes at and above sp1, and the bytes of the caller's blocks, are the entry's *)
assert (KHI2 : forall a, sc_sp1 (spZ regs) <= a < 2 ^ 64 -> rdW W2 (ms_mem ms2) a = rdW Wc memc a).
{ intros a Ha.
  assert (HC : F <= a < F + 64 \/ SB + F / 8 <= a < SB + F / 8 + 8 \/
    (alloc_ceiling <= a < 2 ^ 64 /\ ~ (sc_sp1 (spZ regs) - ARG_S_STK <= a < sc_sp1 (spZ regs))))
    by (right; right; split; lia).
  rewrite (KEEP2 a ltac:(lia) ltac:(lia) ltac:(lia)), (KEEPC1 a HC). apply KEEP1; lia. }
assert (Hsub12 : forall pn, In pn (ablocks B lyc Sc) -> In pn (ablocks B ly2 S2))
  by (intros pn Hpn; exact (Permutation_in _ (Permutation_sym Hperm1) (or_intror Hpn))).
assert (KB2 : forall q m x, In (q, m) (ablocks B lyc Sc) -> q <= x < q + m ->
  rdW W2 (ms_mem ms2) x = rdW Wc memc x).
{ intros q m x Hq Hx.
  destruct (al_blocks _ _ LAWS lyc Sc Wc (ms_mem ms1) mdv1 q m HAR1 Hq) as (_ & _ & _ & _ & _ & _ & Hn0).
  pose proof (req_size_pos m (proj1 Hn0)) as (_ & Hrq).
  destruct (scl_blk_apart lyc Sc Wc (ms_mem ms1) mdv1 fpos q m x HAR1 Hfin Hq ltac:(lia)) as (K1 & K2 & K3 & K4 & K5).
  rewrite EF in K1, K2.
  rewrite (KEEP2 x ltac:(lia) ltac:(lia) ltac:(lia)).
  replace x with (q + (x - q)) by lia.
  rewrite (F2i q m (x - q) Hq (Hsub12 _ Hq) ltac:(lia)
    ltac:(intros Hf; pose proof (HNFP1 _ Hf) as Hr; unfold A_G_REC, OFF_CALLS, A_REC_SPILL, SC_SIZE in Hr; lia)).
  replace (q + (x - q)) with x by lia. apply KEEP1; lia. }
(* the line and the slot at the arg_line call *)
destruct HINB as (pb & kb & Hpbin & Hpb1 & Hpb2).
assert (HpbO : ~ In (pb, kb) O).
{ intros Hin. pose proof (proj1 (Forall_forall _ _) HAPO _ Hin) as Hap.
  unfold iv_apart in Hap. cbn [fst snd] in Hap. lia. }
assert (Hpbc : In (pb, kb) (ablocks B lyc Sc)) by exact (proj2 (proj2 HBLK1) _ Hpbin HpbO).
assert (HSTR2 : astr_atR (rdW W2 (ms_mem ms2)) pl line).
{ apply (astr_atR_kept_r (rdW Wc memc)); [|exact HSTRL].
  intros x Hx. apply (KB2 pb kb x Hpbc). lia. }
assert (HINB2 : in_blockA (ablocks B ly2 S2) pl (Z.of_nat (length line) + 1)).
{ exists pb, kb. split; [exact (Hsub12 _ Hpbc)|]. split; lia. }
destruct (rec_bridge_slot B ly2 S2 _ R REC_CALL [dec id] ((p1, n1) :: O1) HREP2) as (_ & HN2 & _ & _).
cbn [length Z.of_nat Pos.of_succ_nat] in HN2.
assert (HN2' : aval_mem (rdW W2 (ms_mem ms2)) (rec_slot R + CALL_OFF_NARGS) 4 1).
{ apply (aval_mem_kept_r (rdW W2 mem2)); [|exact HN2].
  intros x Hx. unfold CALL_OFF_NARGS in Hx. apply KEEP2; lia. }
(* the budgets at the arg_line call *)
pose proof HJo2 as (_ & _ & _ & _ & _ & _ & Hnev2 & _).
assert (HEV2 : st_nev S2 + EV_ARG_LINE <= EV_MAX).
{ clear - Hnev2 HEV. unfold EV_SUP_CALL, EV_ARG_S, EV_ARG_LINE, EV_ANSWER, EV_HAND_BACK, EV_REC_CANONICAL,
    EV_XMALLOC in *. lia. }
assert (HLIVE2 : blocks_bytes S2 + LIVE_ARG_LINE line <= LIVE_MAX).
{ clear - HBB1 HBB2 HLIVE. unfold LIVE_SUP_CALL, LIVE_ANSWER, LIVE_HAND_BACK, LIVE_XMALLOC in *. lia. }
assert (HMLE12 : mo_le MT S S2 (XM_RECORD MT R + XM_ARG_S MT (Some (dec id))))
  by exact (mle_station MT S Sc S2 _ _ MTL HMLE1 HMLE2).
assert (HMO2 : mo_ok MT S2 (XM_ARG_LINE MT line)).
{ apply (mok_station MT S S2 (XM_SUP_CALL MT R id line t) (XM_RECORD MT R + XM_ARG_S MT (Some (dec id))) _ MTL
    HMOK HMLE12 HXML). unfold XM_SUP_CALL. lia. }
(* the registers at the arg_line call *)
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11.
assert (RK2 : forall r : bv 5, In r [2; 3; 4; 8; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv ->
  getr (ms_regs ms2) r = getr regsc r).
{ intros r Hr.
  exact (regs_kept_of_st_ok SEGS E0 _ (restrict (w_H W2) ms2) regsc (sc_mid_extra regs FL)
    [2; 3; 4; 8; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv HS HAE2 ltac:(vm_compute; reflexivity) r Hr). }
assert (Hsp2c : spZ (ms_regs ms2) = spZ regs + (sc_sp1 (spZ regs) - spZ regs))
  by (unfold spZ at 1; rewrite Q2, V2; lia).
assert (Hgp2 : getr (ms_regs ms2) 3 = w64 (as_gp B)) by (rewrite Q3, Vgp, E3r; exact Hgp).
assert (Htp2 : getr (ms_regs ms2) 4 = w64 (as_tp B)) by (rewrite Q4, Vtp, E4r; exact Htp).
assert (Hra2 : YK0s.ret_ok (getr (ms_regs ms2) 1)) by (rewrite Q1; apply ret_ok_codeptr_v; [lia | reflexivity]).
assert (Hra42 : 4096 <= bv_unsigned (getr (ms_regs ms2) 1)) by (rewrite Q1, unsigned_lit_small by lia; lia).
assert (H10d : getr (ms_regs ms2) 10 = w64 (rec_slot R)) by (rewrite Q10, V22; reflexivity).
assert (H11d : getr (ms_regs ms2) 11 = w64 pl) by (rewrite Q11, V19; reflexivity).
assert (HROD2 : arodata_okP SEGS RLO RHI B (rdW W2 (ms_mem ms2)))
  by exact (sc_aro B HB LAWS IMG ly S W mem md O SUP_CALL_STK (spZ regs) [(0, fpos)] ly2 S2 W2 (ms_mem ms2) mdv2
    (EV_RECORD R + EV_ARG_S) HAR HOin HJo2 HROD0).
assert (KFR2 : forall a, F + 24 <= a < F + 64 -> rdW W2 (ms_mem ms2) a = rdW Wc memc a).
{ intros a Ha.
  assert (HC : F <= a < F + 64 \/ SB + F / 8 <= a < SB + F / 8 + 8 \/
    (alloc_ceiling <= a < 2 ^ 64 /\ ~ (sc_sp1 (spZ regs) - ARG_S_STK <= a < sc_sp1 (spZ regs))))
    by (left; lia).
  rewrite (KEEP2 a ltac:(lia) ltac:(lia) ltac:(lia)), (KEEPC1 a HC). apply KEEP1; lia. }
assert (HFL2 : rdword (rdW W2 (ms_mem ms2)) (F + 56) = Some FL)
  by (apply (sc_rdword_ext (rdW Wc memc)); [intros x Hx; apply KFR2; lia | exact HFLW]).
assert (HL2 : sc_live B ly S W regs mem md O fpos F FL ly2 S2 W2 (ms_regs ms2) (ms_mem ms2) mdv2
  (EV_RECORD R + EV_ARG_S)).
{ apply (scl_live ly S W regs mem md ch O fpos F FL lyc Sc Wc regsc memc mdc (EV_RECORD R)
    ly2 S2 W2 (ms_regs ms2) (ms_mem ms2) mdv2 (EV_RECORD R + EV_ARG_S) HAFN HL HJo2 RK2); [|exact HFL2].
  intros a Ha. apply KHI2; lia. }
destruct (sc_chain B LAWS ly S W regs mem md ch O fpos F FL ly2 S2 W2 (ms_regs ms2) (ms_mem ms2) mdv2
  (EV_RECORD R + EV_ARG_S) HAFN HOin HL2) as (ch2 & Hch2).
assert (Hch2' : achain ly2 (rdW W2 (ms_mem ms2)) (spZ regs + (sc_sp1 (spZ regs) - spZ regs)) (s0Z (ms_regs ms2)) ch2)
  by (replace (spZ regs + (sc_sp1 (spZ regs) - spZ regs)) with (sc_sp1 (spZ regs)) by lia; exact Hch2).
(* 0x8b078: arg_line(c, line) *)
rewrite scl_sig_line.
eapply SRr_bind.
{ eapply (cl_callS_pg (fx := fx) (L := cmd_listing) (PI := PI) B LAWS W2 (ms_regs ms2) (ms_mem ms2)
    (Z_to_bv 64 (BASE + AF_arg_line)) SUP_CALL_STK (spZ regs) (SC_FP O) ly S W mem md [(0, fpos)] ly2 S2 mdv2
    (EV_RECORD R + EV_ARG_S) ARG_LINE_STK (scl_fp (rec_slot R) 1) EV_ARG_LINE (sc_sp1 (spZ regs) - spZ regs)
    (getr (ms_regs ms2) 1) ch2 _ HJo2 Hsp2c Hal1 ltac:(lia)
    ltac:(unfold ARG_LINE_STK, ESTACK, REC_CANONICAL_STK, XMALLOC_STK, ASTACK; lia)
    ltac:(rewrite FFS; unfold ARG_LINE_STK, ESTACK, REC_CANONICAL_STK, XMALLOC_STK, ASTACK; lia)
    Hgp2 Htp2 eq_refl Hra2 Hra42 Hch2').
  - intros HPREc.
    exact (TARG_LINE fx ly2 S2 W2 (ms_regs ms2) (ms_mem ms2) mdv2 _ (rec_slot R) pl 1 line
      HPREc HROD2 H10d H11d Hpl Hslot HN2' ltac:(unfold REC_ARGS_MAX; lia) HINB2 HSTR2 HLEN HEV2 HLIVE2 HMO2).
  - intros a Ha.
    destruct (scl_fp_slot O (rec_slot R) 1 a Hslot ltac:(unfold REC_ARGS_MAX; lia) Ha) as (G1 & G2 & G3 & _).
    left. split; [exact G1 | right; split; [exact G2 | exact G3]]. }
cbv beta. intros W3 c3 _ (ly3 & S3 & regs3 & mem3 & md3 & -> & HJo3 & HJi3 & HP3 & HQ3).
cbv beta in HQ3.
(* arg_line recorded the canonical line: the full-table arm is impossible (nargs = 1 < 6) *)
destruct HQ3 as (HBB3 & HMLE3 & [(Hbad & _) | (_ & p2 & HQ3')]); [unfold REC_ARGS_MAX in Hbad; lia|].
cbv zeta in HQ3'. destruct HQ3' as (Hp2 & Hperm2 & Hfresh2 & HNA3 & HA13 & HSTRC).
pose proof (canon_length line) as CL.
assert (Hn1 : 1 <= n1) by (change n1 with (Z.of_nat (length (dec id)) + 1); lia).
assert (Hsub23 : forall pn, In pn (ablocks B ly2 S2) -> In pn (ablocks B ly3 S3))
  by (intros pn Hpn; exact (Permutation_in _ (Permutation_sym Hperm2) (or_intror Hpn))).
assert (HP2in3 : In (p2, Z.of_nat (length line) + 1) (ablocks B ly3 S3))
  by exact (Permutation_in _ (Permutation_sym Hperm2) (or_introl eq_refl)).
assert (HO1pos : forall pn, In pn O1 -> 0 < snd pn).
{ intros pn Hpn. pose proof HREP1 as (Q & HQ & HOQ).
  exact (proj2 (scl_rep_blocks _ _ _ _ _ _ HQ pn (proj1 (HOQ pn) Hpn))). }
assert (HO2in : forall pn, In pn ((p1, n1) :: O1) -> In pn (ablocks B ly2 S2))
  by exact (sc_O_live B ly2 S2 _ (rec_record R REC_CALL [dec id]) ((p1, n1) :: O1) HREP2).
(* the recorder at the state the arg_line call started from *)
assert (KEEPREC2 : forall a, A_G_REC <= a < A_G_REC + REC_SIZE \/ A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE \/
    inFP (ablocks_fp ((p1, n1) :: O1)) a -> rdW W2 (ms_mem ms2) a = rdW W2 mem2 a).
{ intros a [Ha | [Ha | Ha]].
  - unfold A_G_REC, REC_SIZE in Ha. apply KEEP2; lia.
  - unfold A_REC_SPILL, SC_SIZE in Ha. apply KEEP2; lia.
  - destruct (inFP_ablocks_fp_inv _ a Ha) as (q & m & Hqm & Hr).
    destruct (scl_blk_apart ly2 S2 W2 mem2 md2 fpos q m a HAR2 Hfin2 (HO2in _ Hqm) Hr) as (K1 & K2 & _ & K3 & K4).
    rewrite EF2 in K1, K2. apply KEEP2; lia. }
assert (HREP2' : rec_repA B ly2 S2 (rdW W2 (ms_mem ms2)) (rec_record R REC_CALL [dec id]) ((p1, n1) :: O1))
  by exact (rec_repA_kept B ly2 S2 _ ly2 S2 _ (rec_record R REC_CALL [dec id]) ((p1, n1) :: O1) HREP2 HO2in KEEPREC2).
(* back at 0x8b07c: the frame, its shadow, the flag word and the saves are kept across the arg_line call *)
pose proof (proj1 HJi3) as HAR3.
pose proof HJi3 as (_ & Hly3 & _ & _ & _ & Hfrs3 & _ & _ & F1j & F2j & F3j & F4j & _).
assert (Hfin3 : In (0, fpos) (frames S3)) by (rewrite Hfrs3; exact Hfin2).
pose proof (proj1 HJo2) as HAR2b.
destruct (al_layout _ _ LAWS ly2 S2 W2 (ms_mem ms2) mdv2 ly3 HAR2b Hly3) as (Eab3 & Efa3 & _).
assert (EF3 : frame_addr ly3 0 fpos = F) by (rewrite (Efa3 0 fpos); exact EF2).
assert (EFL3 : flag_addr ly3 0 fpos = FL)
  by (pose proof (Efa3 0 fpos) as Ee; unfold frame_addr, flag_addr in *; lia).
destruct (al_frames _ _ LAWS ly3 S3 W3 mem3 md3 0 fpos HAR3 Hfin3) as (_ & _ & HFpres3 & HFSpres3).
change (fs_frame_bytes 0) with 64 in HFpres3, HFSpres3. rewrite EF3 in HFpres3, HFSpres3.
unfold shadow_addr in HFSpres3. rewrite <- SB_SHADOW_OFF in HFSpres3. change (64 / 8) with 8 in HFSpres3.
assert (HNFP2 : forall a, inFP (scl_fp (rec_slot R) 1) a -> A_G_REC + OFF_CALLS <= a < A_REC_SPILL + SC_SIZE)
  by (intros a Hf; destruct (scl_fp_slot O (rec_slot R) 1 a Hslot ltac:(unfold REC_ARGS_MAX; lia) Hf) as (_ & _ & _ & _ & Hr & _); exact Hr).
assert (KEEPC2 : forall a, F <= a < F + 64 \/ SB + F / 8 <= a < SB + F / 8 + 8 \/
    (alloc_ceiling <= a < 2 ^ 64 /\ ~ (sc_sp1 (spZ regs) - ARG_LINE_STK <= a < sc_sp1 (spZ regs))) ->
  rdW W3 mem3 a = rdW W2 (ms_mem ms2) a).
{ assert (HNF : forall a, F <= a < F + 64 \/ SB + F / 8 <= a < SB + F / 8 + 8 \/ alloc_ceiling <= a ->
    ~ inFP (scl_fp (rec_slot R) 1) a).
  { intros a Ha Hf. pose proof (HNFP2 a Hf) as Hr.
    unfold A_G_REC, OFF_CALLS, A_REC_SPILL, SC_SIZE in Hr. lia. }
  intros a [Ha | [Ha | (Ha & Haw)]].
  - apply (F4j 0 fpos a Hfin2); [|apply HNF; left; exact Ha].
    left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite EF2. change (fs_frame_bytes 0) with 64. lia.
  - apply (F4j 0 fpos a Hfin2); [|apply HNF; right; left; exact Ha].
    right. unfold in_zr. cbn [fst snd]. rewrite EF2. unfold shadow_addr. rewrite <- SB_SHADOW_OFF.
    change (fs_frame_bytes 0 / 8) with 8. lia.
  - apply (F1j a Ha); [clear - Haw; lia | apply HNF; right; right; lia]. }
rewrite Q1.
jafter_call_keep_pi HS 64%nat regs3 (mrestrict (w_H W3) mem3) HP3 [0; 1; 2; 3]%nat HS2.
match type of HS2 with ?T -> _ => assert (HRK : T); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict].
  repeat apply Forall_cons; try apply Forall_nil;
  (split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val];
   rewrite ?V23, ?V24, ?V8; intros a Ha;
   [ apply (mbyte_of_aview SEGS); apply KEEPC2;
     first [ left; lia | right; left; lia | right; right; split; lia ]
   | intros _; apply (apresent_writable SEGS);
     first [ apply (proj1 (HFpres3 a ltac:(lia)))
           | let Hp := fresh "Hp" in
             pose proof (proj1 (HFSpres3 (a - (SB + F / 8)) ltac:(lia))) as Hp;
             replace (SB + F / 8 + (a - (SB + F / 8))) with a in Hp by lia; exact Hp
           | lia ] ]). }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
hei_havoc HS. rebaseE HS AG HEv. clear HEv.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
  assert (X22 : ew Ev 22 = Z_to_bv 64 (rec_slot R)) by (rewrite (AG 22%nat ltac:(lia)); exact E22);
  assert (X23 : bv_unsigned (ew Ev 23) = SB + F / 8) by (rewrite (AG 23%nat ltac:(lia)); exact U23);
  assert (X24 : bv_unsigned (ew Ev 24) = F) by (rewrite (AG 24%nat ltac:(lia)); exact U24);
  assert (X8 : bv_unsigned (ew Ev 8) = spZ regs) by (rewrite (AG 8%nat ltac:(lia)); exact U8);
  assert (X2 : bv_unsigned (ew Ev 2) = sc_sp1 (spZ regs)) by (rewrite (AG 2%nat ltac:(lia)); exact U2);
  assert (HAE3 : env_agree 32 (Ereg regsc (sc_mid_extra regs FL)) Ev)
    by (split; [intros n Hn; rewrite (AG n Hn); exact (proj1 HAE n Hn) | rewrite AD; exact (proj2 HAE)]);
  assert (Xgp : ew Ev 3 = getr regsc 3) by (rewrite (AG 3%nat ltac:(lia)); exact (EE 3%nat 3%bv eq_refl));
  assert (Xtp : ew Ev 4 = getr regsc 4) by (rewrite (AG 4%nat ltac:(lia)); exact (EE 4%nat 4%bv eq_refl))
end.
(* 0x8b07c .. 0x8b08c: a1 := "resp 0", a2 := 1, a0 := c, the call of answer *)
paj_run_shc RUNP RUNC HS HJo3.
{ scl_awr AG EF3 fpos. }
lazymatch goal with HFx : frame_of _ _ (mrestrict _ mem3) (mrestrict _ _) |- _ => rename HFx into HFR3 end.
pmkst HS. collapse_md.
rename ms into ms3. rename mdv into mdv3.
(* run 3 writes nothing *)
pose proof (kept_of_frame (segs := SEGS) E1 _ (w_H W3) mem3 (ms_mem ms3)
  (fun x => (SB + F / 8 + 4 <= x < SB + F / 8 + 6) \/ (F <= x < F + 24)) HFR3
  ltac:(intros b wlo whi a' Hin Hrr; vm_compute in Hin;
        repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr;
          rewrite ?X23, ?X24, ?X8, ?X2 in Hrr; cbv beta; lia|]); destruct Hin)) as KEEP3'.
assert (KEEP3 : forall a, 0 <= a < 2 ^ 64 -> ~ (SB + F / 8 + 4 <= a < SB + F / 8 + 6) -> ~ (F <= a < F + 24) ->
  rdW W3 (ms_mem ms3) a = rdW W3 mem3 a).
{ intros a Ha0 Ha1 Ha2. apply (KEEP3' a Ha0). cbv beta. intros [Hx|Hx]; [exact (Ha1 Hx) | exact (Ha2 Hx)]. }
clear KEEP3'.
(* the recorder after the append: the two slot fields are the only changed bytes of g_rec and record.spill *)
assert (KEEPG3 : forall a, A_G_REC <= a < A_G_REC + REC_SIZE \/ A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE ->
  ~ (rec_slot R + CALL_OFF_NARGS <= a < rec_slot R + CALL_OFF_NARGS + 4) ->
  ~ (rec_slot R + CALL_OFF_ARGS + 8 * Z.of_nat (length [dec id]) <= a <
     rec_slot R + CALL_OFF_ARGS + 8 * Z.of_nat (length [dec id]) + 8) ->
  rdW W3 (ms_mem ms3) a = rdW W2 (ms_mem ms2) a).
{ intros a Ha Hn1f Hn2f.
  cbn [length Z.of_nat Pos.of_succ_nat] in Hn2f. unfold CALL_OFF_NARGS, CALL_OFF_ARGS in Hn1f, Hn2f.
  assert (HPG : inFP cmd_PG a).
  { unfold cmd_PG. rewrite !inFP_cons. destruct Ha as [Ha | Ha];
    [left; unfold A_G_REC, REC_SIZE in *; lia | right; left; unfold A_REC_SPILL, SC_SIZE in *; lia]. }
  assert (HNF : ~ inFP (scl_fp (rec_slot R) 1) a).
  { intros Hf. unfold scl_fp in Hf. rewrite !inFP_cons in Hf. cbn [fst snd] in Hf.
    unfold CALL_OFF_NARGS, CALL_OFF_ARGS in Hf. destruct Hf as [Hx | [Hx | Hx]];
    [lia | lia | destruct (inFP_nil a Hx)]. }
  assert (HSYMS : asyms_ok B) by exact (am_syms _ _ _ _ (proj1 HAR)).
  destruct (prog_static_sep B a HSYMS ltac:(rewrite (ts_prog B HB); unfold TFIB_PROG_STATIC;
    destruct Ha as [Ha | Ha]; [apply Exists_cons_hd | apply Exists_cons_tl, Exists_cons_hd];
    unfold in_zr; cbn [fst snd]; unfold A_G_REC, REC_SIZE, A_REC_SPILL, SC_SIZE in *; lia))
    as (Hno & Hne & _).
  rewrite (KEEP3 a ltac:(unfold A_G_REC, REC_SIZE, A_REC_SPILL, SC_SIZE in *; lia)
    ltac:(unfold A_G_REC, REC_SIZE, A_REC_SPILL, SC_SIZE in *; lia)
    ltac:(unfold A_G_REC, REC_SIZE, A_REC_SPILL, SC_SIZE in *; lia)).
  apply (F3j a (cif_prog_img SEGS B IMG a HPG) Hno Hne).
  apply fp_spares_closed; [|exact HNF].
  apply sink_closed_pos. unfold scl_fp. repeat apply Forall_cons; try apply Forall_nil;
  cbn [fst]; unfold CALL_OFF_NARGS, CALL_OFF_ARGS; lia. }
assert (KEEPB3 : forall pn, In pn ((p1, n1) :: O1) ->
  In pn (ablocks B ly3 S3) /\ rd_agree (rdW W2 (ms_mem ms2)) (rdW W3 (ms_mem ms3)) (fst pn) (snd pn)).
{ intros pn Hpn. pose proof (HO2in _ Hpn) as Hin2. split; [exact (Hsub23 _ Hin2)|].
  intros i Hi. destruct pn as (q & m). cbn [fst snd] in *.
  destruct (al_blocks _ _ LAWS ly2 S2 W2 (ms_mem ms2) mdv2 q m HAR2b Hin2) as (_ & _ & _ & _ & _ & _ & Hn0).
  pose proof (req_size_pos m (proj1 Hn0)) as (_ & Hrq).
  destruct (scl_blk_apart ly2 S2 W2 (ms_mem ms2) mdv2 fpos q m (q + i) HAR2b Hfin2 Hin2 ltac:(lia))
    as (K1 & K2 & K3 & K4 & K5).
  rewrite EF2 in K1, K2.
  rewrite (KEEP3 (q + i) ltac:(lia) ltac:(lia) ltac:(lia)).
  apply (F2j q m i Hin2 (Hsub23 _ Hin2) ltac:(lia)).
  intros Hf. pose proof (HNFP2 _ Hf) as Hr. unfold A_G_REC, OFF_CALLS, A_REC_SPILL, SC_SIZE in Hr. lia. }
assert (HP2NEW : ~ In p2 (map fst ((p1, n1) :: O1))).
{ intros Hin. apply in_map_iff in Hin as (qm & Hq & Hin2).
  assert (Hin3 : In qm (ablocks B ly2 S2)) by exact (HO2in _ Hin2).
  assert (Hmpos : 0 < snd qm).
  { destruct Hin2 as [Heq | Hin2]; [rewrite <- Heq; cbn [snd]; lia | exact (HO1pos _ Hin2)]. }
  pose proof (proj1 (Forall_forall _ _) Hfresh2 _ Hin3) as Hap. unfold iv_apart in Hap. lia. }
assert (HAPG2 : iv_apart p2 (Z.of_nat (length line) + 1) A_G_REC REC_SIZE /\
  iv_apart p2 (Z.of_nat (length line) + 1) A_REC_SPILL SC_SIZE).
{ pose proof (blk_off_imgP B ly3 S3 W3 (ms_mem ms3) mdv3 p2 (Z.of_nat (length line) + 1)
    (proj1 HJo3) HP2in3) as Hoff.
  unfold off_img in Hoff. pose proof (req_size_pos (Z.of_nat (length line) + 1) ltac:(lia)) as (_ & Hrq).
  unfold iv_apart, A_G_REC, REC_SIZE, A_REC_SPILL, SC_SIZE. split; lia. }
assert (HNA3' : aval_mem (rdW W3 (ms_mem ms3)) (rec_slot R + CALL_OFF_NARGS) 4 (1 + 1)).
{ apply (aval_mem_kept_r (rdW W3 mem3)); [|exact HNA3].
  intros x Hx. unfold CALL_OFF_NARGS in Hx. apply KEEP3; lia. }
assert (HA13' : aval_mem (rdW W3 (ms_mem ms3)) (rec_slot R + CALL_OFF_ARGS + 8 * 1) 8 p2).
{ apply (aval_mem_kept_r (rdW W3 mem3)); [|exact HA13].
  intros x Hx. unfold CALL_OFF_ARGS in Hx. apply KEEP3; lia. }
assert (HSTRC' : astr_atR (rdW W3 (ms_mem ms3)) p2 (canon line)).
{ apply (astr_atR_kept_r (rdW W3 mem3)); [|exact HSTRC].
  intros x Hx.
  destruct (al_blocks _ _ LAWS ly3 S3 W3 mem3 md3 p2 (Z.of_nat (length line) + 1) HAR3 HP2in3)
    as (_ & _ & _ & _ & _ & _ & Hn0).
  destruct (scl_blk_apart ly3 S3 W3 mem3 md3 fpos p2 (Z.of_nat (length line) + 1) x HAR3 Hfin3 HP2in3
    ltac:(pose proof (req_size_pos (Z.of_nat (length line) + 1) ltac:(lia)) as (_ & Hrq); lia)) as (K1 & K2 & _ & K3 & K4).
  rewrite EF3 in K1, K2. apply KEEP3; lia. }
pose proof (rec_bridge_add B ly2 S2 ly3 S3 (rdW W2 (ms_mem ms2)) (rdW W3 (ms_mem ms3)) R REC_CALL [dec id]
  ((p1, n1) :: O1) (canon line) p2 (Z.of_nat (length line) + 1) HREP2' ltac:(cbn [length]; lia) KEEPG3 KEEPB3
  HP2in3 HP2NEW (proj1 HAPG2) (proj2 HAPG2) ltac:(lia) ltac:(unfold LMAX in *; lia) ltac:(unfold LMAX in *; lia)
  HNA3' HA13' HSTRC') as HREP3.
cbn [app] in HREP3.
(* the state at answer's entry *)
prreg HS (1%bv : bv 5) T1. prreg HS (2%bv : bv 5) T2. prreg HS (10%bv : bv 5) T10.
prreg HS (11%bv : bv 5) T11. prreg HS (12%bv : bv 5) T12. prreg HS (22%bv : bv 5) T22.
assert (RK3 : forall r : bv 5, In r [2; 3; 4; 8; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv ->
  getr (ms_regs ms3) r = getr regsc r).
{ intros r Hr.
  lazymatch type of HS with st_ok _ ?Ex _ _ =>
  exact (regs_kept_of_st_ok SEGS Ex _ (restrict (w_H W3) ms3) regsc (sc_mid_extra regs FL)
    [2; 3; 4; 8; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv HS HAE3 ltac:(vm_compute; reflexivity) r Hr) end. }
assert (KHI3 : forall a, sc_sp1 (spZ regs) <= a < 2 ^ 64 -> rdW W3 (ms_mem ms3) a = rdW Wc memc a).
{ intros a Ha.
  assert (HC : F <= a < F + 64 \/ SB + F / 8 <= a < SB + F / 8 + 8 \/
    (alloc_ceiling <= a < 2 ^ 64 /\ ~ (sc_sp1 (spZ regs) - ARG_LINE_STK <= a < sc_sp1 (spZ regs))))
    by (right; right; split; lia).
  rewrite (KEEP3 a ltac:(lia) ltac:(lia) ltac:(lia)), (KEEPC2 a HC). apply KHI2; lia. }
assert (HFL3 : rdword (rdW W3 (ms_mem ms3)) (F + 56) = Some FL).
{ apply (sc_rdword_ext (rdW W2 (ms_mem ms2))); [|exact HFL2].
  intros x Hx.
  assert (HC : F <= x < F + 64 \/ SB + F / 8 <= x < SB + F / 8 + 8 \/
    (alloc_ceiling <= x < 2 ^ 64 /\ ~ (sc_sp1 (spZ regs) - ARG_LINE_STK <= x < sc_sp1 (spZ regs))))
    by (left; lia).
  rewrite (KEEP3 x ltac:(lia) ltac:(lia) ltac:(lia)). exact (KEEPC2 x HC). }
assert (HL3 : sc_live B ly S W regs mem md O fpos F FL ly3 S3 W3 (ms_regs ms3) (ms_mem ms3) mdv3
  (EV_RECORD R + EV_ARG_S + EV_ARG_LINE)).
{ apply (scl_live ly S W regs mem md ch O fpos F FL lyc Sc Wc regsc memc mdc (EV_RECORD R)
    ly3 S3 W3 (ms_regs ms3) (ms_mem ms3) mdv3 (EV_RECORD R + EV_ARG_S + EV_ARG_LINE) HAFN HL HJo3 RK3); [|exact HFL3].
  intros a Ha. apply KHI3; lia. }
assert (HOBJ42 : VAL (A_OBJ 42) = 0x21d20)
  by (rewrite (VOBJS 42%nat ltac:(vm_compute; lia)); vm_compute; reflexivity).
assert (H22e : getr (ms_regs ms3) 22 = w64 (rec_slot R)) by (rewrite (RK3 22%bv ltac:(cbn [In]; tauto)); exact H22).
assert (HRA3 : getr (ms_regs ms3) 1 = w64 (BASE + AF_sup_call + SC_PC_R))
  by (rewrite T1; unfold w64; f_equal; unfold AF_sup_call, SC_PC_R; lia).
assert (H10e : getr (ms_regs ms3) 10 = w64 (rec_slot R)) by (rewrite T10, X22; reflexivity).
assert (H11e : getr (ms_regs ms3) 11 = w64 0x21d20).
{ rewrite T11. apply bv_eq.
  lazymatch goal with |- context [ew ?Ev 283%nat] =>
    let HEv := rnHEI Ev in rewrite (HEv 283%nat ltac:(unfold A_TEXT, A_LIM; lia)) end.
  change (VAL 283%nat) with (VAL (A_OBJ 42)). rewrite HOBJ42. unfold w64.
  rewrite unsigned_lit_small by lia. reflexivity. }
assert (H12e : getr (ms_regs ms3) 12 = w64 1) by (rewrite T12; reflexivity).
assert (HATL : sc_at_l B MT ly S W regs mem md id line R O fpos F FL ly3 S3 W3 (ms_regs ms3) (ms_mem ms3) mdv3).
{ split; [exact HL3|]. split; [exact H22e|]. split; [exact HRA3|]. split; [exact H10e|]. split; [exact H11e|].
  split; [exact H12e|].
  exists ((p2, Z.of_nat (length line) + 1) :: (p1, n1) :: O1).
  split; [unfold sc_args; exact HREP3|].
  split; [|split].
  - split; [|split].
    + intros pn [<- | [<- | Hpn]].
      * destruct (in_dec scl_pdec (p2, Z.of_nat (length line) + 1) O) as [Hx|Hx]; [left; exact Hx | right; intros Hin].
        pose proof (proj1 (Forall_forall _ _) Hfresh2 _ (Hsub12 _ (proj2 (proj2 HBLK1) _ Hin Hx))) as Hap.
        unfold iv_apart in Hap. cbn [fst snd] in Hap. lia.
      * destruct (in_dec scl_pdec (p1, n1) O) as [Hx|Hx]; [left; exact Hx | right; intros Hin].
        pose proof (proj1 (Forall_forall _ _) Hfresh1 _ (proj2 (proj2 HBLK1) _ Hin Hx)) as Hap.
        unfold iv_apart in Hap. cbn [fst snd] in Hap. lia.
      * exact (proj1 HBLK1 _ Hpn).
    + intros pn Hpn. apply (Permutation_in _ Hperm2) in Hpn.
      destruct Hpn as [<- | Hpn]; [right; left; reflexivity|].
      apply (Permutation_in _ Hperm1) in Hpn.
      destruct Hpn as [<- | Hpn]; [right; right; left; reflexivity|].
      destruct (proj1 (proj2 HBLK1) _ Hpn) as [Hc | Hc]; [left; exact Hc | right; right; right; exact Hc].
    + intros pn Hpn HnO. exact (Hsub23 _ (Hsub12 _ (proj2 (proj2 HBLK1) _ Hpn HnO))).
  - clear - HBB1 HBB2 HBB3. unfold LIVE_ARG_LINE, LIVE_REC_CANONICAL in *. lia.
  - exact (mle_station MT S S2 S3 _ _ MTL HMLE12 HMLE3). }
rewrite scl_sig_ans.
exact (SCL ly S W regs mem md ch id pl line R O fpos F FL ly3 S3 W3 (ms_regs ms3) (ms_mem ms3) mdv3 HFRM HPRE HATL).
Qed.
End e.
End f.
End w.
