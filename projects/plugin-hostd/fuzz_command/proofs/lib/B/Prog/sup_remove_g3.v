(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the check_arity step of segment K of LLVMFuzzerTestOneInput's ASan walk (plugin-hostd/fuzz_command, 0x86948 addi a0,sp,120 and 0x8694c jal check_arity, to the return point 0x86950): from the cut after check_reply to the cut after check_arity (lib/A/Prog/LLVMFuzzerTestOneInput_Kcut.v), through check_arity's statement, in the form of proofs/cgif/cgif_file_fuzzer/lib/A/ACh1.v (cl_FC_okX: a symbolic run to a program call, the callee's contract, the next cut statement at the return point) and A/ACh2.v:122-290 (a program call through cl_callS and back), with lib/A/Prog/check_refusal.v's call step. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/LLVMFuzzerTestOneInput_Karity.v, with its module paths and module names changed; 506 of its 545 lines of code are new or changed and 214 lines of the source are left out. *)
(* sup_remove's walk on the ASan+UBSan build of plugin-hostd/fuzz_command (fuzz_command.asan-ubsan,
   BASE + AF_sup_remove = 0x8b258), segment G3 (sup_remove_s1.v): from the snprintf wrapper's return 0x8b378 (SR_S)
   to answer's return 0x8b3a0 (SR_T), at the FP state the wrapper returned (sup_remove_g2.v applies sr_g3 there).

   0x8b378 .. 0x8b380: a0 := s5 (record's slot c), a1 := s4 (b = F + 32), `jal arg_s`. The state is seated from
     sr_cut's registers alone (no region: the run writes nothing, so the memory after it is the cut's).
   arg_s(c, b) (arg_s_c.v's targ_s_spec, an apost_base post at this FP state) through PaNoChain.v's cl_callS_wide:
     its footprint (c's nargs field and args[0]) is a program static of sup_remove's footprint (g_rec's call table or
     record.spill); b is the right disjunct of its string premise (dec id in the frame object b, whose shadow bytes 4
     and 5 are 00 at the cut), its word tail CmdRecRo.cmd_fobj_tail.
   0x8b384 .. 0x8b39c: shadow bytes 4 and 5 of the frame := f8 (s8), a1 := "resp 0" (A_OBJ 42 = 0x21d20), a2 := 1,
     a0 := s5, `jal answer`. The state is seated afresh with one region, the frame's shadow bytes 4 and 5 (base s6,
     the write window, no chunk), and run with the plain run lemmas (paj_run_shc).
   answer(c, "resp 0", 1) (answer_c.v's tanswer_spec, an apost_baseF post) through PaFx.v's cl_callS_wideF and
     srr_after_callF: at the FP state fx2 it returns, the cut at 0x8b3a0 (sr_cut with the events of record, arg_s
     and answer) and the statement's post there (sr_q_stmt, from the three posts) give sr_g4_stmt's premises.

   The frame chain at both calls: s0 = sp0 (class B), afn_pre's chain pushed at sp0 with the saved ra and s0
   (achain_push), as sc_chain of lib/B/Prog/sup_call_s0.v. The bytes from sp1 up
   (the saves) and the frame's flag word are kept by the callees' journals (their footprints lie below alloc_ceiling
   and outside the frame) and by the run (its window is two shadow bytes).

   Walk hypotheses: HB, LAWS, MTL, IMG, SIGP. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import String ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI04 YI09 YG0s YI00.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q YG0v YI0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdSyms CmdList CmdPa CmdPaLib PaLibG PaDenot PaLibF PaLibH.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaSB PaCallRun PaCall PaCallPg PaNoChain PaFx.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob CmdBase CmdRep CmdObj CmdRo.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs RtFormat.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import xmalloc_c hand_back_c record_c arg_s_c answer_c sup_remove_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import RecBridge CmdRecAns sup_remove_s1.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require CmdRecBase CmdRecRo.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- facts with no machine state ---- *)
Lemma srg_pair_dec : forall (x y : Z * Z), {x = y} + {x <> y}.
Proof. decide equality; apply Z.eq_dec. Qed.

(* arg_s's footprint for a call that holds no argument yet: c's nargs field and args[0] *)
Lemma srg_argsFP : forall c a,
  inFP (if Z.of_nat (length (@nil (list byte))) <? REC_ARGS_MAX
        then [(c + CALL_OFF_NARGS, c + CALL_OFF_NARGS + 4);
              (c + CALL_OFF_ARGS + 8 * Z.of_nat (length (@nil (list byte))),
               c + CALL_OFF_ARGS + 8 * Z.of_nat (length (@nil (list byte))) + 8)]
        else []) a -> c + 4 <= a < c + 16.
Proof.
intros c a Ha. change (Z.of_nat (length (@nil (list byte))) <? REC_ARGS_MAX) with true in Ha.
change (Z.of_nat (length (@nil (list byte)))) with 0 in Ha. cbv iota in Ha.
rewrite !inFP_cons in Ha. unfold CALL_OFF_NARGS, CALL_OFF_ARGS in Ha.
destruct Ha as [Ha | [Ha | Ha]]; [lia | lia | exact (False_ind _ (inFP_nil a Ha))].
Qed.

(* record()'s slot: a slot of g_rec's call table, or record.spill *)
Lemma srg_slot_rng : forall R,
  (A_G_REC + OFF_CALLS <= rec_slot R /\ rec_slot R + CALL_SIZE <= A_G_REC + OFF_ANSWER) \/ rec_slot R = A_REC_SPILL.
Proof.
intros R. unfold rec_slot. destruct (Nat.ltb_spec (length (r_calls R)) 16) as [Hl | Hl]; [left | right; reflexivity].
unfold A_G_REC, OFF_CALLS, CALL_SIZE, OFF_ANSWER. lia.
Qed.

(* the ten saved words read through a reader that agrees on their bytes *)
Lemma srg_saves_kept : forall (rd rd' : reader) sp0 (regs : bvmap 5 word), sr_saves rd sp0 regs ->
  (forall a, sp0 - 80 <= a < sp0 -> rd' a = rd a) -> sr_saves rd' sp0 regs.
Proof.
intros rd rd' sp0 regs H K.
assert (R : forall o, 8 <= o <= 80 -> rdword rd' (sp0 - o) = rdword rd (sp0 - o))
  by (intros o Ho; apply rdword_ext; intros k Hk; apply K; lia).
destruct H as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10).
unfold sr_saves. rewrite !R by lia.
repeat match goal with |- _ /\ _ => split end; assumption.
Qed.

(* frame addresses do not move along a layout_le *)
Lemma srg_ly_F : forall n ly ly', layout_le n ly ly' ->
  forall cid pos, frame_addr ly' cid pos = frame_addr ly cid pos /\ flag_addr ly' cid pos = flag_addr ly cid pos.
Proof.
intros n ly ly' Hl cid pos. pose proof Hl as (_ & _ & _ & _ & _ & EF & _).
unfold frame_addr, flag_addr. rewrite EF. split; reflexivity.
Qed.

(* the shadow word of an application frame F lies outside every application range *)
Lemma srg_app_shadow : forall {rc : YM05.RunCeil} F q len a, in_app F 64 -> F + 64 <= ASAN_CEIL -> F = 8 * (F / 8) ->
  in_app q len -> q <= a < q + len -> ~ (SB + F / 8 <= a < SB + F / 8 + 8).
Proof.
intros rc F q len a [HF0 HF] HFc HF8 [Hq0 Hq] Ha Hs.
pose proof ASAN_CEIL_range as [CR _].
unfold kLowShadowBeg, kHighMemBeg, SB in *.
destruct HF as [HF | [HF1 HF2]]; destruct Hq as [Hq | [Hq1 Hq2]]; lia.
Qed.

Definition srg_facts : facts := mkFacts [] [] [].
(* the frame's shadow bytes 4 and 5 (base s6), written at 0x8b384 and 0x8b388 *)
Definition srg_regsh : YP09.region := YP09.mkRegion (Some 22%nat) 4 6 4 6 [].

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation SIG s := (@pa_sigma _ cmd_listing PI s).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

(* a state seated from its registers, with the regions rs over them *)
Lemma srg_seat : forall (W : world SEGS) (regs : bvmap 5 word) mem k (rs : smem),
  regions_wf rs = true -> Forall (region_ok SEGS (Eimg (Ereg regs [])) (mrestrict (w_H W) mem)) rs ->
  pairwise_disjoint (Eimg (Ereg regs [])) rs ->
  st_ok_pi SEGS VAL (Eimg (Ereg regs [])) (mkSS k sr_atoms rs None srg_facts)
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + k)) mem (seg_rom SEGS))).
Proof.
intros W regs mem k rs Hwf Hok Hd. rewrite restrict_mkst_fx.
apply pa_entry_st_ok_full; [apply regs_ok_Eimg_Ereg | exact Hwf | exact Hok | exact Hd |].
split; [exact I | split; exact I].
Qed.

(* the same with the frame's shadow bytes 4 and 5 at b = s6 *)
Lemma srg_seat_sh : forall (W : world SEGS) (regs : bvmap 5 word) mem k b,
  bv_unsigned (getr regs 22) = b -> 0 <= b -> b + 6 <= 2 ^ 64 ->
  (forall o, 4 <= o < 6 -> apresent (w_H W) mem (b + o)) ->
  st_ok_pi SEGS VAL (Eimg (Ereg regs [])) (mkSS k sr_atoms [srg_regsh] None srg_facts)
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + k)) mem (seg_rom SEGS))).
Proof.
intros W regs mem k b Hb Hb0 Hb1 Hp. apply srg_seat.
- reflexivity.
- apply Forall_cons; [|apply Forall_nil]. unfold region_ok, srg_regsh.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite Eimg_low by (unfold A_TEXT; lia). rewrite (ew_Ereg_nat regs [] 22 22%bv eq_refl), Hb.
  split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
  intros o Ho. apply (apresent_writable SEGS). apply Hp. exact Ho.
- split; exact I.
Qed.

Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
(* the statement's Section hypotheses this segment uses (sup_remove_c.v:89-90, :93), word for word *)
Hypothesis TARG_S : forall fx0 : YK11.FPState, @targ_s_spec fx0 rc SK PI B MT.
Hypothesis TANSWER : forall fx0 : YK11.FPState, @tanswer_spec fx0 rc SK PI B MT.
Hypothesis VOBJS : cmd_val_objs.
(* the walk hypotheses, with cgif's names *)
Hypothesis HB : CmdBSyms B.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis MTL : ameter_laws MT.
Hypothesis IMG : CmdRecBase.cmd_img_facts SEGS B.
Hypothesis SIGP : cmd_sig_prog.
(* the segments this one ends in (sup_remove_s1.v) *)
Hypothesis G4 : forall fx0 : YK11.FPState, @sr_g4_stmt fx0 rc SK PI B MT.
Hypothesis QP : sr_q_stmt B MT.
Let RUNP := SRr_run_pi_AJ (PL := PL_cmd) (PI := PI) B LAWS.
Let RUNC := SRr_run_pi_AJ_call (PL := PL_cmd) (PI := PI) B LAWS.

(* a live block: its bounds and size (bsra_blk of the B sup_remove_all walk) *)
Lemma srg_blk : forall ly S (W : world SEGS) mem md p n, AR SEGS B ly S W mem md -> In (p, n) (ablocks B ly S) ->
  4096 <= p /\ p + req_size n <= alloc_ceiling /\ 0 <= n /\ 1 <= req_size n /\ in_app p (req_size n).
Proof.
intros ly S W mem md p n HAR Hin.
destruct (al_blocks _ _ LAWS ly S W mem md p n HAR Hin) as (_ & H1 & H2 & H4 & _ & _ & H3).
pose proof (req_size_pos n ltac:(lia)). split; [lia|]. split; [lia|]. split; [lia|]. split; [lia | exact H4].
Qed.

(* the recorder's blocks are live blocks *)
Lemma srg_rep_live : forall ly S rd R O pn, rec_repA B ly S rd R O -> In pn O -> In pn (ablocks B ly S).
Proof. intros ly S rd R O pn (Q & HQ & HO) Hin. exact (rca_rep_blocks _ _ _ _ _ _ pn HQ (proj1 (HO pn) Hin)). Qed.

(* a program function's call target is its entry *)
Lemma srg_sig : forall s af, In s cmd_prog_syms -> cmd_af s = af -> SIG s = BASE + af.
Proof. intros s af Hs Ha. rewrite (SIGP s Hs), Ha. reflexivity. Qed.

(* sup_remove's footprint lies below alloc_ceiling *)
Lemma srg_FP_low : forall ly S (W : world SEGS) mem md O, AR SEGS B ly S W mem md ->
  (forall pn, In pn O -> In pn (ablocks B ly S)) -> forall a, inFP (sr_FP O) a -> 0 < a < alloc_ceiling.
Proof.
intros ly S W mem md O HAR HO a Ha. pose proof asan_consts as (C1 & _).
unfold sr_FP in Ha. rewrite !inFP_cons in Ha.
destruct Ha as [Ha | [Ha | [Ha | [Ha | Ha]]]];
  [unfold A_G_REC, A_REC_SPILL, OFF_NCALLS, OFF_CALLS, OFF_ANSWER, OFF_STATE, SC_SIZE in Ha; lia ..|].
destruct (inFP_ablocks_fp_inv O a Ha) as (p & n & Hin & Hr).
destruct (srg_blk ly S W mem md p n HAR (HO _ Hin)) as (B1 & B2 & _). lia.
Qed.

(* the frame chain a program call at sp1 takes for s0 = sp0 (sup_call_s0.v's sc_chain): afn_pre's chain pushed at sp0
   with the ra and s0 the prologue saved there, or the empty chain when sp0 is within 16 bytes of the stack top *)
Lemma srg_chain : forall ly S (W : world SEGS) (regs : bvmap 5 word) mem md ch O own lyc Sc (Wc : world SEGS) memc mdc k,
  afn_pre SEGS B SUP_REMOVE_STK ly S W regs mem md ch ->
  (forall pn, In pn O -> In pn (ablocks B ly S)) ->
  ajournal SEGS B SUP_REMOVE_STK (spZ regs) (sr_FP O) ly S W mem md own lyc Sc Wc memc mdc k ->
  rdword (rdW Wc memc) (spZ regs - 8) = Some (raZ regs) ->
  rdword (rdW Wc memc) (spZ regs - 16) = Some (s0Z regs) ->
  exists ch1, achain lyc (rdW Wc memc) (sr_sp1 (spZ regs)) (spZ regs) ch1.
Proof.
intros ly S W regs mem md ch O own lyc Sc Wc memc mdc k HPRE HO HJ H8 H16.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof HJ as (_ & Hly & _ & _ & _ & _ & _ & _ & F1 & _).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _).
assert (WS : 112 <= SUP_REMOVE_STK) by (apply Z.leb_le; vm_compute; reflexivity).
assert (Hsp1 : sr_sp1 (spZ regs) <= spZ regs - 96) by (unfold sr_sp1; clear - Hal16; Z.div_mod_to_equations; lia).
assert (Hal8 : spZ regs mod 8 = 0) by (clear - Hal16; Z.div_mod_to_equations; lia).
destruct (Z_lt_le_dec (spZ regs) (ly_top ly - 16)) as [Hlt | Hge].
- exists ((spZ regs, raZ regs, s0Z regs) :: ch).
  apply (achain_ly_top ly lyc); [exact Etop|].
  apply (achain_push ly (rdW W mem) (rdW Wc memc) (spZ regs) (s0Z regs) (raZ regs) ch (sr_sp1 (spZ regs)) Hch);
  [lia | | exact H8 | exact H16 | exact Hra4 | lia | exact Hal8 | exact Hlt | lia].
  intros a Ha. apply F1; [lia | lia |]. intros Hf. pose proof (srg_FP_low ly S W mem md O HAR HO a Hf). lia.
- exists []. left. split; [right; left; rewrite Etop; lia | reflexivity].
Qed.

(* a callee's journal (at sp1, its footprint below alloc_ceiling) keeps every byte from sp1 up *)
Lemma srg_kept_hi : forall STK1 sp1 FP1 lyc Sc (Wc : world SEGS) memc mdc own ly2 S2 (W2 : world SEGS) mem2 md2 k1,
  ajournal SEGS B STK1 sp1 FP1 lyc Sc Wc memc mdc own ly2 S2 W2 mem2 md2 k1 ->
  (forall x, inFP FP1 x -> x < alloc_ceiling) -> alloc_ceiling <= sp1 ->
  forall a, sp1 <= a < 2 ^ 64 -> rdW W2 mem2 a = rdW Wc memc a.
Proof.
intros STK1 sp1 FP1 lyc Sc Wc memc mdc own ly2 S2 W2 mem2 md2 k1 HJ HF Hc a Ha.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & F1 & _).
apply F1; [lia | lia |]. intros Hf. pose proof (HF a Hf). lia.
Qed.

(* the same journal keeps the bytes of a live side-stack frame outside its footprint *)
Lemma srg_kept_frm : forall STK1 sp1 FP1 lyc Sc (Wc : world SEGS) memc mdc own ly2 S2 (W2 : world SEGS) mem2 md2 k1 cid pos,
  ajournal SEGS B STK1 sp1 FP1 lyc Sc Wc memc mdc own ly2 S2 W2 mem2 md2 k1 -> In (cid, pos) (frames Sc) ->
  forall a, frame_addr lyc cid pos <= a < frame_addr lyc cid pos + fs_frame_bytes cid -> ~ inFP FP1 a ->
  rdW W2 mem2 a = rdW Wc memc a.
Proof.
intros STK1 sp1 FP1 lyc Sc Wc memc mdc own ly2 S2 W2 mem2 md2 k1 cid pos HJ Hin a Ha Hf.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F4 & _).
apply (F4 cid pos a Hin); [left; unfold in_zr, frame_rng; cbn [fst snd]; lia | exact Hf].
Qed.

(* a callee-saved register r through aregs_preserved HP, then the cut's fact G *)
Ltac srg_r HP r G := etransitivity; [exact (HP r ltac:(unfold acallee_saved; lia)) | exact G].

Theorem sr_g3 : sr_g3_stmt B MT.
Proof.
unfold sr_g3_stmt.
intros ly S W regs mem md ch id R O lyc Sc Wc regsc memc mdc pos Fr O1 HPRE HFRM HCUT HRECD H21 HZ4 HZ5 HSTR.
pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HPRE as (HAFN & HFR7 & HROD & HROK & H10 & Hid & HREP & HEV & HLIVE & HMO).
pose proof HAFN as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof HCUT as (HJc & HFLAG & Hspc & G8 & G9 & G18 & G19 & G20 & G22 & G23 & G24 & G3 & G4r & G25 & G26 & G27 & HSAV).
pose proof HRECD as (HPERM & HFRl & HFrO & HREP1 & HO1 & HBB1 & HMLE1).
pose proof HJc as (HARc & Hlyc & _ & _ & _ & Hfrc & Hnevc & _ & _).
assert (WS : SUP_REMOVE_STK = ltac:(let v := eval vm_compute in SUP_REMOVE_STK in exact v)) by reflexivity.
assert (WA : ARG_S_STK = ltac:(let v := eval vm_compute in ARG_S_STK in exact v)) by reflexivity.
assert (WN : ANSWER_STK = ltac:(let v := eval vm_compute in ANSWER_STK in exact v)) by reflexivity.
(* the realigned sp1 *)
assert (Hsp1 : spZ regs - 112 <= sr_sp1 (spZ regs) <= spZ regs - 96)
  by (unfold sr_sp1; clear - Hal16; Z.div_mod_to_equations; lia).
assert (Ho16 : (sr_sp1 (spZ regs) - spZ regs) mod 16 = 0)
  by (unfold sr_sp1; clear - Hal16; Z.div_mod_to_equations; lia).
(* the frame F *)
assert (HinSc : In (0, pos) (frames Sc)) by (rewrite Hfrc; left; reflexivity).
destruct (frame_al64 SEGS B lyc Sc Wc memc mdc 0 pos HARc HinSc) as (HF64 & _ & _).
destruct (frames_bounds SEGS B LAWS lyc Sc Wc memc mdc 0 pos HARc HinSc) as (HF4096 & HFceil & HFapp).
remember (frame_addr lyc 0 pos) as F eqn:EF.
change (fs_frame_bytes 0) with 64 in HFceil, HFapp.
assert (HF8 : F = 8 * (F / 8)) by (clear - HF64; Z.div_mod_to_equations; lia).
(* the recorder's blocks *)
assert (HOlive : forall pn, In pn O -> In pn (ablocks B ly S)) by (intros pn Hp; exact (srg_rep_live _ _ _ _ _ pn HREP Hp)).
assert (HOF : Forall (fun pn => In pn (ablocks B ly S)) O) by (apply Forall_forall; exact HOlive).
assert (HO1c : forall pn, In pn O1 -> In pn (ablocks B lyc Sc)) by (intros pn Hp; exact (srg_rep_live _ _ _ _ _ pn HREP1 Hp)).
assert (HO1O : forall pn, In pn O1 -> In pn O) by (intros pn Hp; exact (proj1 (proj1 (HO1 pn) Hp))).
(* record's slot: a program static of sup_remove's footprint *)
pose proof (srg_slot_rng R) as HSL.
assert (Hcb : 0 <= rec_slot R < 2 ^ 64) by (destruct HSL as [HSL | HSL]; [unfold A_G_REC, OFF_CALLS, CALL_SIZE, OFF_ANSWER in HSL | rewrite HSL; unfold A_REC_SPILL]; lia).
assert (Hclo : rec_slot R + 16 <= A_REC_SPILL + 16) by (destruct HSL as [HSL | HSL]; [unfold A_G_REC, OFF_CALLS, CALL_SIZE, OFF_ANSWER, A_REC_SPILL in *; lia | lia]).
assert (HslotFP : forall a, rec_slot R + 4 <= a < rec_slot R + 16 -> inFP (sr_FP O) a /\ inFP cmd_PG a).
{ intros a Ha. destruct HSL as [HSL | HSL].
  - split.
    + unfold sr_FP. rewrite !inFP_cons. right; left. unfold A_G_REC, OFF_CALLS, OFF_ANSWER, CALL_SIZE in *. lia.
    + exists (A_G_REC, A_G_REC + 960). split; [left; reflexivity | cbn [fst snd]; unfold A_G_REC, OFF_CALLS, OFF_ANSWER, CALL_SIZE in *; lia].
  - rewrite HSL in Ha. split.
    + unfold sr_FP. rewrite !inFP_cons. right; right; right; left. unfold A_REC_SPILL, SC_SIZE in *. lia.
    + exists (A_REC_SPILL, A_REC_SPILL + 56). split; [right; left; reflexivity | cbn [fst snd]; lia]. }
(* the read-only bytes at the cut *)
assert (HRODc : arodata_okP SEGS RLO RHI B (rdW Wc memc))
  by exact (sr_aro_journal (PI := PI) B HB LAWS IMG _ _ O ly S W mem md _ lyc Sc Wc memc mdc _ HAR HOF HJc HROD).
assert (HROKc : cmd_ro_ok (rdW Wc memc)) by exact (CmdRecRo.cmd_ro_ok_of_aro SEGS B LAWS HB IMG lyc Sc Wc memc mdc HARc HRODc).
(* b = F + 32 holds dec id, in the frame's object b, with shadow bytes 4 and 5 = 00 *)
pose proof (dec_length id Hid) as Hdl.
assert (HOBJ : afobj SEGS B lyc Sc Wc memc (F + 32) (Z.of_nat (length (dec id)) + 1)).
{ split.
  - exists 0, pos. split; [exact HinSc|]. split; [lia|]. rewrite <- EF.
    split; [clear - HF64; Z.div_mod_to_equations; lia|]. change (fs_frame_bytes 0) with 64. lia.
  - split; [clear - HF64; Z.div_mod_to_equations; lia|].
    intros x Hx. exists 0. split; [|left; reflexivity]. unfold shadow_of_addr.
    assert (Hx8 : x / 8 = F / 8 + 4 \/ x / 8 = F / 8 + 5) by (clear - Hx HF64 Hdl; Z.div_mod_to_equations; lia).
    destruct Hx8 as [Hx8 | Hx8]; rewrite Hx8; change SHADOW_OFF with SB; rewrite Z.add_assoc; [exact HZ4 | exact HZ5]. }
assert (HSTRA : astr_argA B lyc Sc (rdW Wc memc) (in_roP SEGS RLO RHI) [] (F + 32) (Some (dec id)) \/
  (exists x, Some (dec id) = Some x /\ astr_atR (rdW Wc memc) (F + 32) x /\ Z.of_nat (length x) + 1 <= LMAX + 1 /\
   afobj SEGS B lyc Sc Wc memc (F + 32) (Z.of_nat (length x) + 1))).
{ right. exists (dec id). split; [reflexivity|]. split; [exact HSTR|]. split; [unfold LMAX; lia | exact HOBJ]. }
assert (HTAIL : forall x, Some (dec id) = Some x -> atail_vis SEGS Wc memc (F + 32 + Z.of_nat (length x))).
{ intros x Ex. injection Ex as <-. exact (CmdRecRo.cmd_fobj_tail SEGS B LAWS HB lyc Sc Wc memc mdc (F + 32) (dec id) HARc HOBJ HSTR). }
(* events, live bytes and the meter *)
assert (HEVa : 0 <= EV_ANSWER) by (unfold EV_ANSWER, EV_HAND_BACK, EV_XMALLOC; lia).
assert (HLVa : 0 <= LIVE_ANSWER (snd (sup_remove_m R id))) by (unfold LIVE_ANSWER, LIVE_HAND_BACK, LIVE_XMALLOC; lia).
assert (HXA : 0 <= XM_ANSWER MT (snd (sup_remove_m R id))).
{ unfold XM_ANSWER, XM_HAND_BACK, XM_XMALLOC, LIVE_XMALLOC. pose proof (mo_free_nonneg MT MTL).
  pose proof (mo_malloc_nonneg MT MTL (Z.max (Z.of_nat (length (snd (sup_remove_m R id))) + 1) 1) ltac:(lia)). lia. }
assert (HXS : 0 <= XM_ARG_S MT (Some (dec id))).
{ unfold XM_ARG_S, XM_XMALLOC, LIVE_XMALLOC. apply (mo_malloc_nonneg MT MTL). lia. }
unfold EV_SUP_REMOVE in HEV. unfold LIVE_SUP_REMOVE in HLIVE.
assert (HEVA : st_nev Sc + EV_ARG_S <= EV_MAX) by lia.
assert (HLIVEA : blocks_bytes Sc + LIVE_ARG_S (Some (dec id)) <= LIVE_MAX) by lia.
assert (HMOA : mo_ok MT Sc (XM_ARG_S MT (Some (dec id)))).
{ apply (mok_station MT S Sc (XM_SUP_REMOVE MT R id (snd (sup_remove_m R id))) (XM_RECORD MT R) _ MTL HMO HMLE1 HXS).
  unfold XM_SUP_REMOVE. lia. }
(* arg_s's frame chain at the call *)
destruct (srg_chain ly S W regs mem md ch O [(0, pos)] lyc Sc Wc memc mdc (EV_RECORD R) HAFN HOlive HJc
  (proj1 HSAV) (proj1 (proj2 HSAV))) as (chA & HchA).
(* ---- 0x8b378 .. 0x8b380: a0 := s5, a1 := s4, `jal arg_s` ---- *)
remember (Eimg (Ereg regsc [])) as E1 eqn:HE1.
assert (HEI : img_env VAL A_LIM E1) by (subst E1; apply Eimg_env).
assert (EE1 : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew E1 k = getr regsc r).
{ intros k r Hk. pose proof (bv_unsigned_in_range 5 r) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  subst E1. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hk. }
assert (HAE1 : env_agree 32 (Ereg regsc []) E1)
  by (subst E1; split; [intros n Hn; rewrite Eimg_low by (unfold A_TEXT; lia); reflexivity | reflexivity]).
assert (HS : st_ok_pi SEGS VAL E1 (mkSS (AF_sup_remove + SR_S) sr_atoms [] None srg_facts)
  (restrict (w_H Wc) (mkst regsc (Z_to_bv 64 (BASE + (AF_sup_remove + SR_S))) memc (seg_rom SEGS))))
  by (subst E1; apply srg_seat; [reflexivity | apply Forall_nil | exact I]).
clear HE1.
pose proof HJc as HJ.
paj_run_shc RUNP RUNC HS HJ.
{ apply awr_ok_nil. }
lazymatch goal with HFx : frame_of _ _ memc (ms_mem ?m) |- _ => rename HFx into HF1; rename m into msA end.
pose proof (frame_of_read_only E1 [] memc (ms_mem msA) eq_refl HF1) as EM1.
repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.
pmkst HS. rewrite EM1 in HJ |- *. collapse_md.
prreg HS (1%bv : bv 5) P1. prreg HS (10%bv : bv 5) P10. prreg HS (11%bv : bv 5) P11.
pose proof (aregs_preserved_of_st_ok SEGS _ E1 _ _ regsc [] HS HAE1 ltac:(vm_compute; reflexivity)) as HPR1.
cbn [ms_regs restrict] in HPR1.
lazymatch goal with |- SRr _ _ (mkCfg _ ?dA) _ => rename dA into mdA end.
(* the registers at arg_s's entry *)
assert (P10A : getr (ms_regs msA) 10 = w64 (rec_slot R)) by (rewrite P10, (EE1 21%nat 21%bv eq_refl); exact H21).
assert (P11A : getr (ms_regs msA) 11 = w64 (F + 32)) by (rewrite P11, (EE1 20%nat 20%bv eq_refl); exact G20).
assert (HPA2 : spZ (ms_regs msA) = sr_sp1 (spZ regs))
  by (rewrite <- Hspc; unfold spZ; f_equal; exact (HPR1 2 ltac:(unfold acallee_saved; lia))).
assert (HgpA : getr (ms_regs msA) 3 = w64 (as_gp B))
  by (etransitivity; [exact (HPR1 3 ltac:(unfold acallee_saved; lia)) | etransitivity; [exact G3 | exact Hgp]]).
assert (HtpA : getr (ms_regs msA) 4 = w64 (as_tp B))
  by (etransitivity; [exact (HPR1 4 ltac:(unfold acallee_saved; lia)) | etransitivity; [exact G4r | exact Htp]]).
assert (Hs0A : s0Z (ms_regs msA) = spZ regs)
  by (unfold s0Z, spZ; f_equal; etransitivity; [exact (HPR1 8 ltac:(unfold acallee_saved; lia)) | exact G8]).
assert (HraA : YK0s.ret_ok (getr (ms_regs msA) 1)) by (rewrite P1; apply ret_ok_codeptr_v; [lia | reflexivity]).
assert (Hra4A : 4096 <= bv_unsigned (getr (ms_regs msA) 1)) by (rewrite P1, unsigned_lit_small by lia; lia).
(* ---- arg_s(c, b) at 0x8b380 (arg_s_c.v, apost_base at this FP state) ---- *)
rewrite (srg_sig CS_arg_s AF_arg_s ltac:(unfold cmd_prog_syms; simpl; repeat (first [left; reflexivity | right]))
  ltac:(vm_compute; reflexivity)).
pose proof (TARG_S fx lyc Sc Wc (ms_regs msA) memc mdA chA (rec_slot R) (F + 32) REC_REMOVE [] (Some (dec id)) R O1) as HAS.
cbv zeta in HAS.
lazymatch type of HAS with
| context [apost_base _ _ _ ?FP _ _ _ _ _ _ _ ?Q] => remember FP as FPA eqn:EFPA in HAS; remember Q as QA eqn:EQA in HAS
end.
assert (FPAc : forall a, inFP FPA a -> rec_slot R + 4 <= a < rec_slot R + 16)
  by (intros a Ha; rewrite EFPA in Ha; exact (srg_argsFP _ _ Ha)).
assert (HFA : forall a, inFP FPA a ->
  awr_byte SEGS B SUP_REMOVE_STK (spZ regs) (sr_FP O) (ablocks B ly S) (ablocks B lyc Sc) (frames S) lyc [(0, pos)] a).
{ intros a Ha. destruct (HslotFP a (FPAc a Ha)) as [Hf Hpg].
  right; right; right; right; left. split; [exact Hf | exact (rca_prog (PI := PI) B HB IMG a Hpg)]. }
assert (FPAlow : forall x, inFP FPA x -> x < alloc_ceiling).
{ intros x Hx. pose proof (FPAc x Hx). unfold A_REC_SPILL in Hclo. lia. }
assert (HVISA : forall ly2 S2 W2 regs2 mem2 md2, QA ly2 S2 W2 regs2 mem2 md2 -> forall a, inFP FPA a ->
  spZ regs - SUP_REMOVE_STK <= a < spZ regs ->
  ~ (spZ regs + (sr_sp1 (spZ regs) - spZ regs) - ARG_S_STK <= a < spZ regs + (sr_sp1 (spZ regs) - spZ regs)) ->
  aview SEGS (w_H W2) mem2 a <> None).
{ intros ? ? ? ? ? ? _ a Ha Hw _. exfalso. pose proof (FPAlow a Ha). lia. }
eapply SRr_bind.
{ refine (cl_callS_wide (fx := fx) (PI := PI) B LAWS Wc (ms_regs msA) memc (Z_to_bv 64 (BASE + AF_arg_s)) SUP_REMOVE_STK
    (spZ regs) (sr_FP O) ly S W mem md [(0, pos)] lyc Sc mdA (EV_RECORD R) ARG_S_STK FPA EV_ARG_S
    (sr_sp1 (spZ regs) - spZ regs) (getr (ms_regs msA) 1) chA QA
    HJ ltac:(rewrite HPA2; lia) Ho16 ltac:(lia) ltac:(rewrite WA; lia) ltac:(rewrite WA, WS; lia) HgpA HtpA eq_refl HraA Hra4A
    ltac:(rewrite Hs0A; replace (spZ regs + (sr_sp1 (spZ regs) - spZ regs)) with (sr_sp1 (spZ regs)) by lia; exact HchA)
    (fun HP => HAS HP HRODc HROKc P10A P11A eq_refl HREP1 HSTRA HTAIL HEVA HLIVEA HMOA) HFA HVISA). }
cbv beta. intros W3 c3 Hwle3 (ly3 & S3 & regs3 & mem3 & md3 & -> & HJo3 & HJi3 & HPR3 & HK3).
rewrite EQA in HK3. cbv beta in HK3. cbn [sarg app] in HK3.
destruct HK3 as (HBB3 & HMLE3 & [(Hl6 & _) | (_ & p & Hp & HPERM3 & HAPART & HREP3)]);
  [exfalso; unfold REC_ARGS_MAX in Hl6; cbn in Hl6; lia|].
(* ---- back at 0x8b384 ---- *)
pose proof HJo3 as (HAR3 & _ & _ & _ & _ & _ & Hnev3 & _).
pose proof HJi3 as (_ & Hly3i & _ & _ & _ & Hfr3i & _).
assert (EF3 : frame_addr ly3 0 pos = F) by (rewrite EF; exact (proj1 (srg_ly_F _ _ _ Hly3i 0 pos))).
assert (HinS3 : In (0, pos) (frames S3)) by (rewrite Hfr3i; exact HinSc).
(* arg_s keeps the bytes from sp1 up and the frame *)
assert (KA3 : forall a, sr_sp1 (spZ regs) <= a < 2 ^ 64 -> rdW W3 mem3 a = rdW Wc memc a).
{ intros a Ha. apply (srg_kept_hi _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJi3 FPAlow); lia. }
assert (FA3 : forall a, F <= a < F + 64 -> rdW W3 mem3 a = rdW Wc memc a).
{ intros a Ha. apply (srg_kept_frm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 0 pos HJi3 HinSc);
    [rewrite <- EF; change (fs_frame_bytes 0) with 64; lia|].
  intros Hf. destruct (HslotFP a (FPAc a Hf)) as [_ Hpg].
  apply (frm_img SEGS B LAWS lyc Sc Wc memc mdc 0 pos a HARc HinSc); [rewrite <- EF; change (fs_frame_bytes 0) with 64; lia|].
  exact (CmdRecBase.cif_prog_img _ _ IMG a Hpg). }
(* the seat at 0x8b384: the frame's shadow bytes 4 and 5 at s6 *)
assert (G22v : bv_unsigned (getr regs3 22) = SB + F / 8).
{ transitivity (bv_unsigned (getr regsc 22)).
  - f_equal. etransitivity; [exact (HPR3 22 ltac:(unfold acallee_saved; lia)) | exact (HPR1 22 ltac:(unfold acallee_saved; lia))].
  - rewrite G22. unfold w64. apply unsigned_lit_small. unfold SB. lia. }
destruct (al_frames _ _ LAWS ly3 S3 W3 mem3 md3 0 pos HAR3 HinS3) as (_ & _ & _ & HFS3).
rewrite EF3 in HFS3. change (fs_frame_bytes 0 / 8) with 8 in HFS3.
assert (HSH3 : forall o, 4 <= o < 6 -> apresent (w_H W3) mem3 (SB + F / 8 + o)).
{ intros o Ho. pose proof (proj1 (HFS3 o ltac:(lia))) as Hpr. unfold shadow_addr in Hpr. rewrite <- SB_SHADOW_OFF in Hpr. exact Hpr. }
rewrite P1.
remember (Eimg (Ereg regs3 [])) as E2 eqn:HE2.
assert (HEI2 : img_env VAL A_LIM E2) by (subst E2; apply Eimg_env).
assert (EE2 : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew E2 k = getr regs3 r).
{ intros k r Hk. pose proof (bv_unsigned_in_range 5 r) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  subst E2. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hk. }
assert (HAE2 : env_agree 32 (Ereg regs3 []) E2)
  by (subst E2; split; [intros n Hn; rewrite Eimg_low by (unfold A_TEXT; lia); reflexivity | reflexivity]).
assert (U22 : bv_unsigned (ew E2 22) = SB + F / 8) by (rewrite (EE2 22%nat 22%bv eq_refl); exact G22v).
clear HS.
lazymatch goal with |- SRr _ _ (mkCfg (mkst _ (Z_to_bv 64 (_ + ?k)) _ _) _) _ =>
  assert (HS : st_ok_pi SEGS VAL E2 (mkSS k sr_atoms [srg_regsh] None srg_facts)
    (restrict (w_H W3) (mkst regs3 (Z_to_bv 64 (BASE + k)) mem3 (seg_rom SEGS))))
  by (subst E2; apply (srg_seat_sh W3 regs3 mem3 k (SB + F / 8)); [exact G22v | unfold SB; lia | unfold SB; lia | exact HSH3]) end.
clear HE2.
(* ---- 0x8b384 .. 0x8b39c: shadow 4, 5 := f8, a1 := "resp 0", a2 := 1, a0 := s5, `jal answer` ---- *)
paj_run_shc RUNP RUNC HS HJo3.
{ intros a (r & Hin & Hr). cbn [ss_mem In] in Hin. destruct Hin as [<- | []].
  cbn [srg_regsh YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr. rewrite U22 in Hr.
  right; right; right; left. exists 0, pos. split; [left; reflexivity|]. right.
  rewrite EF3. unfold in_zr, shadow_addr. cbn [fst snd]. change (fs_frame_bytes 0 / 8) with 8. unfold SHADOW_OFF, SB in *. lia. }
lazymatch goal with HFx : frame_of _ _ (mrestrict _ mem3) (mrestrict _ (ms_mem ?m)) |- _ => rename HFx into HFr2; rename m into msB end.
pmkst HS. collapse_md.
lazymatch goal with |- SRr _ _ (mkCfg _ ?dB) _ => rename dB into mdB end.
prreg HS (1%bv : bv 5) Q1. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11. prreg HS (12%bv : bv 5) Q12.
pose proof (aregs_preserved_of_st_ok SEGS _ E2 _ _ regs3 [] HS HAE2 ltac:(vm_compute; reflexivity)) as HPR4.
cbn [ms_regs restrict] in HPR4.
(* the run wrote only the two shadow bytes *)
assert (KB : forall a, 0 <= a < 2 ^ 64 -> ~ (SB + F / 8 + 4 <= a < SB + F / 8 + 6) -> rdW W3 (ms_mem msB) a = rdW W3 mem3 a).
{ intros a Ha Hn.
  apply (kept_of_frame (segs := SEGS) E2 _ (w_H W3) mem3 (ms_mem msB) (fun a => SB + F / 8 + 4 <= a < SB + F / 8 + 6) HFr2);
    [|exact Ha | exact Hn].
  intros b wlo whi a' Hin Hrr. vm_compute in Hin. destruct Hin as [Hq | []]. injection Hq as <- <- <-.
  cbn [base_val] in Hrr. rewrite U22 in Hrr. lia. }
assert (KB3 : forall a, sr_sp1 (spZ regs) <= a < 2 ^ 64 -> rdW W3 (ms_mem msB) a = rdW Wc memc a).
{ intros a Ha. rewrite KB by (unfold SB in *; lia). apply KA3. exact Ha. }
assert (FB : forall a, F <= a < F + 64 -> rdW W3 (ms_mem msB) a = rdW W3 mem3 a).
{ intros a Ha. apply KB; [lia|]. intros Hc. apply (srg_app_shadow F F 64 a HFapp HFceil HF8 HFapp Ha). lia. }
(* ---- answer(c, "resp 0", 1) at 0x8b39c (answer_c.v, apost_baseF) ---- *)
pose proof HJo3 as (HAR4 & _).
assert (HROD4 : arodata_okP SEGS RLO RHI B (rdW W3 (ms_mem msB)))
  by exact (sr_aro_journal (PI := PI) B HB LAWS IMG _ _ O ly S W mem md _ ly3 S3 W3 (ms_mem msB) mdB _ HAR HOF HJo3 HROD).
assert (HROK4 : cmd_ro_ok (rdW W3 (ms_mem msB)))
  by exact (CmdRecRo.cmd_ro_ok_of_aro SEGS B LAWS HB IMG ly3 S3 W3 (ms_mem msB) mdB HAR4 HROD4).
assert (HPO3 : forall pn, In pn ((p, Z.of_nat (length (dec id)) + 1) :: O1) -> In pn (ablocks B ly3 S3))
  by (intros pn Hpn; exact (srg_rep_live _ _ _ _ _ pn HREP3 Hpn)).
assert (HREP4 : rec_repA B ly3 S3 (rdW W3 (ms_mem msB)) (rec_record R REC_REMOVE [dec id])
  ((p, Z.of_nat (length (dec id)) + 1) :: O1)).
{ apply (rec_repA_kept B ly3 S3 (rdW W3 mem3) ly3 S3 _ _ _ HREP3 HPO3).
  intros a Ha. destruct Ha as [Ha | [Ha | Ha]].
  - apply KB; [unfold A_G_REC, REC_SIZE in Ha; lia | unfold A_G_REC, REC_SIZE, SB in *; lia].
  - apply KB; [unfold A_REC_SPILL, SC_SIZE in Ha; lia | unfold A_REC_SPILL, SC_SIZE, SB in *; lia].
  - destruct (inFP_ablocks_fp_inv _ a Ha) as (q & k & Hin & Hr).
    destruct (srg_blk ly3 S3 W3 mem3 md3 q k HAR3 (HPO3 _ Hin)) as (B1 & B2 & _ & _ & Bapp).
    apply KB; [lia|]. intros Hc. apply (srg_app_shadow F q (req_size k) a HFapp HFceil HF8 Bapp Hr). lia. }
pose proof HREP4 as (Q4 & HQ4 & HQ4O).
destruct (rca_answer_cell _ _ _ _ HQ4) as (old & Hold & Hold').
assert (OLD : old = 0 \/ exists pn0, In pn0 ((p, Z.of_nat (length (dec id)) + 1) :: O1) /\ old = fst pn0).
{ destruct Hold' as [(_ & E0) | (pn0 & Ea & E0)]; [left; exact E0|]. right. exists pn0. split; [|exact E0].
  apply HQ4O. apply rca_in_answer. rewrite Ea. cbn [oblk]. left. reflexivity. }
assert (Hob : 0 <= old < 2 ^ 64).
{ destruct OLD as [-> | ([q k] & Hq & ->)]; [lia|]. cbn [fst].
  destruct (srg_blk ly3 S3 W3 (ms_mem msB) mdB q k HAR4 (HPO3 _ Hq)) as (B1 & B2 & _ & B4 & _). lia. }
pose proof (rca_shape_arg (PI := PI) B HB ly3 S3 W3 (ms_mem msB) mdB ((p, Z.of_nat (length (dec id)) + 1) :: O1) HAR4 HROK4
  (CmdRecRo.cmd_ro_in_img SEGS B LAWS HB IMG)) as HARG.
pose proof (rec_slot_entry R REC_REMOVE [dec id]) as HSLOT.
(* the registers at answer's entry *)
pose proof (aregs_preserved_trans _ _ _ (aregs_preserved_trans _ _ _ HPR1 HPR3) HPR4) as HPRB.
assert (P10B : getr (ms_regs msB) 10 = w64 (rec_slot R)).
{ rewrite Q10, (EE2 21%nat 21%bv eq_refl). etransitivity; [exact (HPR3 21 ltac:(unfold acallee_saved; lia))|].
  etransitivity; [exact (HPR1 21 ltac:(unfold acallee_saved; lia)) | exact H21]. }
assert (V42 : VAL (A_OBJ 42) = 0x21d20) by (rewrite (VOBJS 42%nat ltac:(vm_compute; lia)); reflexivity).
assert (P11B : getr (ms_regs msB) 11 = w64 0x21d20).
{ rewrite Q11. apply bv_eq. change 283%nat with (A_OBJ 42).
  rewrite (HEI2 (A_OBJ 42) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)), V42.
  unfold w64. rewrite unsigned_lit_small by lia. reflexivity. }
assert (PCHG : true = negb (bv_unsigned (getr (ms_regs msB) 12) =? 0)) by (rewrite Q12; vm_compute; reflexivity).
assert (HPA4 : spZ (ms_regs msB) = sr_sp1 (spZ regs))
  by (rewrite <- Hspc; unfold spZ; f_equal; exact (HPRB 2 ltac:(unfold acallee_saved; lia))).
assert (HgpB : getr (ms_regs msB) 3 = w64 (as_gp B))
  by (etransitivity; [exact (HPRB 3 ltac:(unfold acallee_saved; lia)) | etransitivity; [exact G3 | exact Hgp]]).
assert (HtpB : getr (ms_regs msB) 4 = w64 (as_tp B))
  by (etransitivity; [exact (HPRB 4 ltac:(unfold acallee_saved; lia)) | etransitivity; [exact G4r | exact Htp]]).
assert (Hs0B : s0Z (ms_regs msB) = spZ regs)
  by (unfold s0Z, spZ; f_equal; etransitivity; [exact (HPRB 8 ltac:(unfold acallee_saved; lia)) | exact G8]).
assert (HraB : YK0s.ret_ok (getr (ms_regs msB) 1)) by (rewrite Q1; apply ret_ok_codeptr_v; [lia | reflexivity]).
assert (Hra4B : 4096 <= bv_unsigned (getr (ms_regs msB) 1)) by (rewrite Q1, unsigned_lit_small by lia; lia).
(* frames, events, live bytes, meter *)
assert (PF8 : Z.of_nat (length (frames S3)) <= 8) by (rewrite Hfr3i, Hfrc; cbn [app length]; lia).
assert (PEV : st_nev S3 + EV_ANSWER <= EV_MAX) by lia.
assert (PLIVE : blocks_bytes S3 + LIVE_ANSWER (snd (sup_remove_m R id)) <= LIVE_MAX) by lia.
assert (PMO : mo_ok MT S3 (XM_ANSWER MT (snd (sup_remove_m R id)))).
{ apply (mok_station MT S S3 (XM_SUP_REMOVE MT R id (snd (sup_remove_m R id))) (XM_RECORD MT R + XM_ARG_S MT (Some (dec id)))
    _ MTL HMO (mle_station MT S Sc S3 _ _ MTL HMLE1 HMLE3) HXA).
  unfold XM_SUP_REMOVE. lia. }
(* answer's frame chain at the call *)
assert (HSAV4 : sr_saves (rdW W3 (ms_mem msB)) (spZ regs) regs)
  by (apply (srg_saves_kept _ _ _ _ HSAV); intros a Ha; apply KB3; lia).
destruct (srg_chain ly S W regs mem md ch O [(0, pos)] ly3 S3 W3 (ms_mem msB) mdB (EV_RECORD R + EV_ARG_S) HAFN HOlive HJo3
  (proj1 HSAV4) (proj1 (proj2 HSAV4))) as (chB & HchB).
rewrite (srg_sig CS_answer AF_answer ltac:(unfold cmd_prog_syms; simpl; repeat (first [left; reflexivity | right]))
  ltac:(vm_compute; reflexivity)).
pose proof (TANSWER fx ly3 S3 W3 (ms_regs msB) (ms_mem msB) mdB chB (rec_slot R) 0x21d20 old (REC_REMOVE, [dec id])
  REC_MOD_HOST_SHAPE true (rec_record R REC_REMOVE [dec id]) ((p, Z.of_nat (length (dec id)) + 1) :: O1)) as HANS.
cbv zeta in HANS.
assert (Et : snd (rec_answer (rec_record R REC_REMOVE [dec id]) (REC_REMOVE, [dec id]) REC_MOD_HOST_SHAPE true) =
  snd (sup_remove_m R id)) by reflexivity.
rewrite Et in HANS.
lazymatch type of HANS with
| context [apost_baseF _ _ _ ?FP _ _ _ _ _ _ _ ?Q] => remember FP as FPa eqn:EFPa in HANS; remember Q as Qa eqn:EQa in HANS
end.
assert (FPa_cases : forall a, inFP FPa a ->
  (A_G_REC + OFF_ANSWER <= a < A_G_REC + OFF_ANSWER + 8) \/ (A_G_REC + OFF_STATE <= a < A_G_REC + OFF_STATE + 8) \/
  exists q k, In (q, k) ((p, Z.of_nat (length (dec id)) + 1) :: O1) /\ q <= a < q + req_size k).
{ intros a Ha. rewrite EFPa in Ha. rewrite !inFP_cons in Ha.
  destruct Ha as [Ha | [Ha | Ha]]; [left; exact Ha | right; left; exact Ha |]. right; right.
  destruct (inFP_ablocks_fp_inv _ a Ha) as (q & k & Hin & Hr). exists q, k. split; [exact (rca_filter_in _ _ _ Hin) | exact Hr]. }
assert (FPalow : forall x, inFP FPa x -> x < alloc_ceiling).
{ intros x Hx. destruct (FPa_cases x Hx) as [Hx' | [Hx' | (q & k & Hin & Hr)]];
    [unfold A_G_REC, OFF_ANSWER in Hx'; lia | unfold A_G_REC, OFF_STATE in Hx'; lia |].
  destruct (srg_blk ly3 S3 W3 (ms_mem msB) mdB q k HAR4 (HPO3 _ Hin)) as (B1 & B2 & _). lia. }
assert (HFB : forall a, inFP FPa a ->
  awr_byte SEGS B SUP_REMOVE_STK (spZ regs) (sr_FP O) (ablocks B ly S) (ablocks B ly3 S3) (frames S) ly3 [(0, pos)] a).
{ intros a Ha. destruct (FPa_cases a Ha) as [Hx | [Hx | (q & k & Hin & Hr)]].
  - right; right; right; right; left. split.
    + unfold sr_FP. rewrite !inFP_cons. right; left. unfold A_G_REC, OFF_CALLS, OFF_ANSWER in *. lia.
    + apply (rca_prog (PI := PI) B HB IMG). exists (A_G_REC, A_G_REC + 960). split; [left; reflexivity | cbn [fst snd]; unfold A_G_REC, OFF_ANSWER in *; lia].
  - right; right; right; right; left. split.
    + unfold sr_FP. rewrite !inFP_cons. right; right; left. exact Hx.
    + apply (rca_prog (PI := PI) B HB IMG). exists (A_G_REC, A_G_REC + 960). split; [left; reflexivity | cbn [fst snd]; unfold A_G_REC, OFF_STATE in *; lia].
  - assert (Hq3 : In (q, k) (ablocks B ly3 S3)) by exact (HPO3 _ Hin).
    destruct Hin as [Eq | Hin].
    + injection Eq as Eq1 Eq2. subst q k.
      destruct (in_dec srg_pair_dec (p, Z.of_nat (length (dec id)) + 1) (ablocks B ly S)) as [Hin0 | Hn0].
      * right; left. split; [|exists p, (Z.of_nat (length (dec id)) + 1); split; [exact Hq3 | exact Hr]].
        apply (Permutation_in _ HPERM) in Hin0. apply in_app_or in Hin0 as [Hc | Hf].
        -- exfalso. pose proof (proj1 (Forall_forall _ _) HAPART _ Hc) as Hap. unfold iv_apart in Hap. cbn [fst snd] in Hap. lia.
        -- unfold sr_FP. rewrite !inFP_cons. right; right; right; right.
           replace a with (p + (a - p)) by lia.
           apply (inFP_ablocks_fp O p (Z.of_nat (length (dec id)) + 1) (a - p)); [exact (HFrO _ Hf) | lia].
      * right; right; left. exists p, (Z.of_nat (length (dec id)) + 1). split; [exact Hq3|]. split; [exact Hn0 | exact Hr].
    + right; left. split; [|exists q, k; split; [exact Hq3 | exact Hr]].
      unfold sr_FP. rewrite !inFP_cons. right; right; right; right.
      replace a with (q + (a - q)) by lia. apply (inFP_ablocks_fp O q k (a - q)); [exact (HO1O _ Hin) | lia]. }
assert (HVISB : forall ly2 S2 W2 regs2 mem2 md2, Qa ly2 S2 W2 regs2 mem2 md2 -> forall a, inFP FPa a ->
  spZ regs - SUP_REMOVE_STK <= a < spZ regs ->
  ~ (spZ regs + (sr_sp1 (spZ regs) - spZ regs) - ANSWER_STK <= a < spZ regs + (sr_sp1 (spZ regs) - spZ regs)) ->
  aview SEGS (w_H W2) mem2 a <> None).
{ intros ? ? ? ? ? ? _ a Ha Hw _. exfalso. pose proof (FPalow a Ha). lia. }
eapply (srr_after_callF (fx := fx) SEGS).
{ refine (cl_callS_wideF (fx := fx) (PI := PI) B LAWS W3 (ms_regs msB) (ms_mem msB) (Z_to_bv 64 (BASE + AF_answer))
    SUP_REMOVE_STK (spZ regs) (sr_FP O) ly S W mem md [(0, pos)] ly3 S3 mdB (EV_RECORD R + EV_ARG_S) ANSWER_STK FPa EV_ANSWER
    (sr_sp1 (spZ regs) - spZ regs) (getr (ms_regs msB) 1) chB Qa
    HJo3 ltac:(rewrite HPA4; lia) Ho16 ltac:(lia) ltac:(rewrite WN; lia) ltac:(rewrite WN, WS; lia) HgpB HtpB eq_refl HraB Hra4B
    ltac:(rewrite Hs0B; replace (spZ regs + (sr_sp1 (spZ regs) - spZ regs)) with (sr_sp1 (spZ regs)) by lia; exact HchB)
    (fun HP => HANS HP HFRM PF8 HROD4 HROK4 P10B Hcb P11B ltac:(lia) PCHG HREP4 Hold Hob (fun _ => HARG) (fun _ _ => HSLOT)
      PEV PLIVE PMO)
    HFB HVISB). }
intros fx2 ly5 S5 W5 regs5 mem5 md5 Hwle5 Hfx2 (HJo5 & HJi5 & HPR5 & HK5).
rewrite EQa in HK5. cbv beta in HK5.
destruct HK5 as (p1 & p2 & O' & K10 & K4096 & Kne & Kfr & KBL & KREP & KO & KSTR & KBB & KMLE).
(* ---- at 0x8b3a0, at the FP state fx2 answer returned ---- *)
pose proof HJo5 as (HAR5 & Hly5 & _).
assert (EF5 : frame_addr ly5 0 pos = F /\ flag_addr ly5 0 pos = flag_addr lyc 0 pos).
{ destruct (srg_ly_F _ _ _ Hly5 0 pos) as [A1 A2]. destruct (srg_ly_F _ _ _ Hlyc 0 pos) as [B1 B2].
  rewrite EF. split; congruence. }
destruct EF5 as [EF5 EG5].
assert (K5 : forall a, sr_sp1 (spZ regs) <= a < 2 ^ 64 -> rdW W5 mem5 a = rdW W3 (ms_mem msB) a).
{ intros a Ha. apply (srg_kept_hi _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJi5 FPalow); lia. }
assert (F5 : forall a, F <= a < F + 64 -> rdW W5 mem5 a = rdW W3 (ms_mem msB) a).
{ intros a Ha. apply (srg_kept_frm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 0 pos HJi5 HinS3);
    [rewrite EF3; change (fs_frame_bytes 0) with 64; lia|].
  intros Hf. destruct (FPa_cases a Hf) as [Hx | [Hx | (q & k & Hin & Hr)]].
  - apply (frm_img SEGS B LAWS ly3 S3 W3 (ms_mem msB) mdB 0 pos a HAR4 HinS3); [rewrite EF3; change (fs_frame_bytes 0) with 64; lia|].
    apply (CmdRecBase.cif_prog_img _ _ IMG). exists (A_G_REC, A_G_REC + 960).
    split; [left; reflexivity | cbn [fst snd]; unfold A_G_REC, OFF_ANSWER in *; lia].
  - apply (frm_img SEGS B LAWS ly3 S3 W3 (ms_mem msB) mdB 0 pos a HAR4 HinS3); [rewrite EF3; change (fs_frame_bytes 0) with 64; lia|].
    apply (CmdRecBase.cif_prog_img _ _ IMG). exists (A_G_REC, A_G_REC + 960).
    split; [left; reflexivity | cbn [fst snd]; unfold A_G_REC, OFF_STATE in *; lia].
  - pose proof (sep_block_frame SEGS B LAWS ly3 S3 W3 (ms_mem msB) mdB q k 0 pos HAR4 (HPO3 _ Hin) HinS3) as Hd.
    rewrite EF3 in Hd. unfold zdisjoint in Hd. cbn [fst snd] in Hd. change (fs_frame_bytes 0) with 64 in Hd. lia. }
assert (HFLAG5 : rdword (rdW W5 mem5) (F + 56) = Some (flag_addr ly5 0 pos)).
{ rewrite EG5, <- HFLAG. apply rdword_ext. intros k Hk.
  rewrite F5 by lia. rewrite FB by lia. apply FA3. lia. }
assert (HSAV5 : sr_saves (rdW W5 mem5) (spZ regs) regs).
{ apply (srg_saves_kept _ _ _ _ HSAV). intros a Ha. rewrite K5 by lia. apply KB3. lia. }
pose proof (aregs_preserved_trans _ _ _ HPRB HPR5) as HPRT.
assert (R2 : spZ regs5 = sr_sp1 (spZ regs))
  by (rewrite <- Hspc; unfold spZ; f_equal; exact (HPRT 2 ltac:(unfold acallee_saved; lia))).
assert (HCUT5 : sr_cut B ly S W regs mem md O ly5 S5 W5 regs5 mem5 md5 pos (EV_SUP_REMOVE R)).
{ unfold sr_cut. rewrite EF5.
  split; [exact HJo5|]. split; [exact HFLAG5|]. split; [exact R2|].
  split; [srg_r HPRT 8 G8|]. split; [srg_r HPRT 9 G9|]. split; [srg_r HPRT 18 G18|]. split; [srg_r HPRT 19 G19|].
  split; [srg_r HPRT 20 G20|]. split; [srg_r HPRT 22 G22|]. split; [srg_r HPRT 23 G23|]. split; [srg_r HPRT 24 G24|].
  split; [srg_r HPRT 3 G3|]. split; [srg_r HPRT 4 G4r|]. split; [srg_r HPRT 25 G25|]. split; [srg_r HPRT 26 G26|].
  split; [srg_r HPRT 27 G27|]. exact HSAV5. }
(* the statement's post at 0x8b3a0, from record's, arg_s's and answer's posts (sr_q_stmt) *)
pose proof (QP ly S W regs mem md ch id R O lyc Sc Wc memc mdc Fr O1 ly3 S3 p W3 (ms_mem msB) mdB old
  ly5 S5 W5 regs5 mem5 md5 p1 p2 O') as HQ.
cbv zeta in HQ.
assert (HPOST : sr_post B MT ly S W R O id ly5 S5 W5 regs5 mem5 md5)
  by exact (HQ HPRE HARc HRECD Hp HPERM3 HAPART HBB3 HMLE3 HAR4 HREP4 Hold Hob HAR5 K10 K4096 Kne Kfr KBL KREP KO KSTR KBB KMLE).
rewrite Q1.
exact (G4 fx2 ly S W regs mem md ch id R O ly5 S5 W5 regs5 mem5 md5 pos HPRE HCUT5 HPOST).
Qed.
End e.
End f.
End d.
