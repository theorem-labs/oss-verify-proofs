(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: ported from this harness's lib/A/Prog/check_reply_s7.v (the ASan walk, a working branch 91059853ab1) to the ASan+UBSan build fuzz_command.asan-ubsan (lib/B, entry 0x86e64): B's addresses ("resp 0" at 0x21120), and B's reload of g_rec.reply with its inline check (0x870f8-0x87100) before the second syntax_reply_matches call, where A kept the reply in s3. *)
(* Modified by Theorem Labs, 2026-10: onto a working branch 917ca7ac6b1: astr_argA's read-only arm there names no reader (CmdChk's cmd_addr_b / cmd_hull_b, the end in CmdRo's cmd_ro_ends), so cr7_argA_eq carries that arm unchanged; "resp 0" (cr_lit0_arg, check_reply_t.v) gives the three checks by computation. *)
(* Modified by Theorem Labs, 2026-10: the shape join of check_reply's walk (fuzz_command.asan-ubsan, 0x870e4 .. 0x87114),
   ported from proofs/cgif/cgif_file_fuzzer/lib/A/ACh1.v..ACh8.v, AChc.v and ACke.v (cgif_close's segments and
   their program calls, cl_callS then a fresh seed at the return) at origin/ossv/recipes c8557374ad2e.

   From CR_JOIN (a0 = the shape string q) the code re-checks the shadow of g_rec.reply, loads the reply into a1 and
   calls syntax_reply_matches(q, reply) (0x870f0). A match goes to the epilogue CR_EPI; otherwise it re-checks the
   shadow of g_rec.reply, reloads it (0x870f8-0x87100; A kept it in s3) and calls
   syntax_reply_matches("resp 0" @ 0x21120, reply) (0x8710c), and a second miss would abort, which reply_okA's
   second conjunct refutes (0 <= code: one of the two shapes matches). Each run starts from the mid-walk seed
   (check_reply_sd.v cr_seed) with the frame header read-only, so the run changes no byte the walk reads. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI04 YI00.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YC5d YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs RtString RtFormat RtAPI.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv CommandModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import check_reply_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaTable PaSym PaRun PaShadow PaStep CmdSyms
  CmdList CmdAddr CmdPa PaJournal CmdPaLib PaLibG PaLibH PaLibF PaDenot PaSB PaCall CmdBase CmdRep CmdObj CmdRo CmdZsh
  PaNoChain CmdRecBase CmdRecImg.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import sup_reply_code_c check_reply_answer_c
  rec_code_declared_c rec_shape_of_c syntax_reply_matches_c check_reply_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import check_reply_k check_reply_m check_reply_sd
  check_reply_t.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

(* the seed's state with the frame header read-only (window 0 0): a run from it writes no byte *)
Definition cr_frh0 : YP09.region := YP09.mkRegion (Some 36%nat) 0 32 0 0 [].
Definition ss7 (pc : Z) : sstate := mkSS pc sr_mid [cr_stkm; cr_grecm; cr_frh0; cr_frt; cr_frs false] None cr_facts_mid.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

(* readers that agree on [0, 2^64) agree everywhere (a byte address is taken mod 2^64) *)
Lemma cr7_aview_all : forall (H : word -> bool) (m m' : word -> option byte),
(forall a, 0 <= a < 2 ^ 64 -> aview SEGS H m' a = aview SEGS H m a) -> forall a, aview SEGS H m' a = aview SEGS H m a.
Proof.
intros H m m' K a.
assert (E : forall mm, aview SEGS H mm a = aview SEGS H mm (a mod 2 ^ 64)).
{ intros mm. unfold aview, mbyte. replace (Z_to_bv 64 (a mod 2 ^ 64)) with (Z_to_bv 64 a); [reflexivity|].
  apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  rewrite Z.mod_mod by lia. reflexivity. }
rewrite !E. apply K. apply Z.mod_pos_bound. lia.
Qed.
(* astr_argA over two readers that agree everywhere (only the string's bytes are read through the reader: the
   block arm and the read-only arm's checks cmd_addr_b, cmd_hull_b and cmd_ro_ends do not name it) *)
Lemma cr7_argA_eq : forall B ly S (rd rd' : reader) ro O p x,
(forall a, rd' a = rd a) -> astr_argA B ly S rd ro O p (Some x) -> astr_argA B ly S rd' ro O p (Some x).
Proof.
intros B ly S rd rd' ro O p x K HA. unfold astr_argA in HA |- *. cbv zeta in HA |- *.
destruct HA as (H1 & H2 & H3 & H4).
split; [exact H1|]. split; [apply (astr_atR_agree rd); [intros y _; apply K | exact H2]|]. exact (conj H3 H4).
Qed.

Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
Context {RO : ro_below_ofl SEGS RLO RHI}.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis HB : CmdBSyms B.
Hypothesis SRM : forall fx0 : YK11.FPState, @tsyntax_reply_matches_spec fx0 rc SK PI B MT.
Hypothesis SIGP : cmd_sig_prog.
Hypothesis RELRO_IMG : forall a, RLO <= a < RHI -> in_img SEGS a.
Hypothesis IMG : cmd_img_facts SEGS B.
Hypothesis CMD_RO_AT : forall ly S W mem md, AR SEGS B ly S W mem md ->
  arodata_okP SEGS RLO RHI B (aview SEGS (w_H W) mem) -> cmd_ro_ok (aview SEGS (w_H W) mem).
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.

(* the transfer facts this segment reads (check_reply_t.v), at a mid-walk state *)
Lemma cr7_state : forall v lyc Sc Wc memc mdc pos,
cr_cx B RLO RHI v -> cr_mid B v lyc Sc Wc memc mdc pos ->
arodata_okP SEGS RLO RHI B (rdW Wc memc) /\ cmd_ro_ok (rdW Wc memc) /\ cmd_got_ok (rdW Wc memc) /\
aguard_ok SEGS Wc memc 0xa6bf8 0x604158 /\ rdW Wc memc A_FLAG_REPLACE_STR = Some 1 /\
(exists ev, rd32 (rdW Wc memc) (as_errno B) ev) /\ rt_rom_view SEGS B Wc memc /\
cmd_ro_in (in_roP SEGS RLO RHI) /\ cmd_val_objs.
Proof. intros. eapply cr_state_facts; eassumption. Qed.
Lemma cr7_reply : forall v lyc Sc Wc memc mdc pos,
cr_cx B RLO RHI v -> cr_mid B v lyc Sc Wc memc mdc pos ->
exists m, In (c_p v, m) (ablocks B lyc Sc) /\ c_nr v + 1 <= m /\ astr_atR (rdW Wc memc) (c_p v) (c_xr v) /\
atail_vis SEGS Wc memc (c_p v + c_nr v) /\ in_blockA (ablocks B lyc Sc) (c_p v) (c_nr v + 1) /\
(forall i, 0 <= i < c_nr v -> exists b, rdW Wc memc (c_p v + i) = Some b /\ b <> 0).
Proof. intros. eapply cr_reply_facts; eassumption. Qed.
Lemma cr7_lit0 : forall v lyc Sc Wc memc mdc pos, cr_cx B RLO RHI v -> cr_mid B v lyc Sc Wc memc mdc pos ->
astr_argA B lyc Sc (rdW Wc memc) (in_roP SEGS RLO RHI) [] 0x21120 (Some REC_MOD_HOST_SHAPE).
Proof. intros. eapply cr_lit0_arg; eassumption. Qed.

(* the reply block's numbers the seed asks, from the entry's recorder state *)
Lemma cr7_nums : forall v, cr_cx B RLO RHI v ->
4096 <= c_p v /\ c_p v mod 16 = 0 /\ c_p v + c_nr v + 1 <= 140737479966720 /\ c_nr v + 1 <= 8194.
Proof.
intros v CX.
pose proof CX as (HPRE & _ & _ & _ & _ & _ & _ & _ & _ & HREC & _ & Hry & _ & Hrep & _).
pose proof HPRE as (HAR & _).
destruct HREC as (Q & (_ & _ & _ & _ & _ & Hrepl & _) & _).
unfold areply_at in Hrepl. rewrite Hry in Hrepl. destruct (l_reply Q) as [[rp rn]|]; [|destruct Hrepl].
destruct Hrepl as (Vrp & _ & _ & _ & Hrin & Hrsz & _ & Hrlen). cbn [fst snd] in *.
rewrite length_app in Hrsz, Hrlen. cbn [length] in Hrsz, Hrlen. rewrite Nat2Z.inj_add in Hrsz, Hrlen.
change (Z.of_nat 1) with 1 in Hrsz, Hrlen. unfold LMAX in Hrsz, Hrlen.
destruct (al_blocks _ _ LAWS _ _ _ _ _ rp rn HAR Hrin) as (Hr16 & Hr4096 & Hrceil & _).
pose proof (req_size_pos0 rn ltac:(lia)) as [Hrq0 Hrq].
pose proof HPRE as (_ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HSTK : CHECK_REPLY_STK = 12464) by reflexivity.
assert (Erp : c_p v = rp).
{ unfold c_p. rewrite (aval_mem_mod64 _ _ _ _ Hrep Vrp). apply Z.mod_small. lia. }
unfold c_nr. rewrite Erp. lia.
Qed.

(* the seed at any listing offset, with the frame header read-only *)
Lemma cr7_seed : forall v lyc Sc Wc regs1 memc mdc pos pc,
cr_cx B RLO RHI v -> cr_mid B v lyc Sc Wc memc mdc pos -> cr_regs_at B v lyc pos regs1 ->
st_ok_pi SEGS VAL (crM regs1 v lyc pos) (ss7 pc)
(restrict (w_H Wc) (mkst regs1 (Z_to_bv 64 (BASE + pc)) memc (seg_rom SEGS))).
Proof.
intros v lyc Sc Wc regs1 memc mdc pos pc CX MID RA.
destruct (cr7_nums v CX) as (N1 & N2 & N3 & N4).
pose proof (cr_seed B RLO RHI LAWS v lyc Sc Wc regs1 memc mdc pos pc false CX MID RA N1 N2 N3 N4) as HS.
pose proof (st_ok_pi_region_nth _ _ _ 2 cr_frh HS eq_refl) as Hr.
exact (ast_ok_pi_set_region _ _ _ 2 cr_frh cr_frh0 HS eq_refl eq_refl ltac:(vm_compute; reflexivity)
  (region_ok_rewindow SEGS _ _ cr_frh 0 0 Hr ltac:(intros o Ho; lia))).
Qed.

(* the mid-walk invariant across a run that changes no byte *)
Lemma cr7_mid_run : forall v lyc Sc Wc memc mdc mem' mdc' pos,
cr_mid B v lyc Sc Wc memc mdc pos ->
ajournal SEGS B CHECK_REPLY_STK (c_sp v) [] (c_ly v) (c_S v) (c_W v) (c_mem v) (c_md v) [(1, pos)] lyc Sc Wc mem' mdc' 0 ->
(forall a, aview SEGS (w_H Wc) mem' a = aview SEGS (w_H Wc) memc a) ->
cr_mid B v lyc Sc Wc mem' mdc' pos.
Proof.
intros v lyc Sc Wc memc mdc mem' mdc' pos MID HJ' K. unfold cr_mid in MID |- *. cbv zeta in MID |- *.
destruct MID as (HJ & HP & VFL & VSH & VSV & VREP & VSZ).
assert (MV : forall a n x, val_mem SEGS (mrestrict (w_H Wc) memc) a n x -> val_mem SEGS (mrestrict (w_H Wc) mem') a n x)
by (intros a n x; apply val_mem_moved; intros k _; apply K).
split; [exact HJ'|]. split; [exact HP|]. split; [apply MV, VFL|]. split; [intros i Hi; apply MV, VSH, Hi|].
split; [intros j r Hj; apply MV, (VSV j r Hj)|]. split; apply MV; assumption.
Qed.

(* the mid-walk invariant after a program call whose journal has the footprint [] and a window below sp0 - 96 *)
Lemma cr7_mid_call : forall v lyc Sc Wc memc mdc pos STK1 sp1 ly2 S2 W2 mem2 md2 k1,
cr_cx B RLO RHI v -> cr_mid B v lyc Sc Wc memc mdc pos ->
ajournal SEGS B CHECK_REPLY_STK (c_sp v) [] (c_ly v) (c_S v) (c_W v) (c_mem v) (c_md v) [(1, pos)] ly2 S2 W2 mem2 md2 0 ->
ajournal SEGS B STK1 sp1 [] lyc Sc Wc memc mdc [] ly2 S2 W2 mem2 md2 k1 ->
sp1 <= c_sp v - 96 ->
Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) ->
cr_mid B v ly2 S2 W2 mem2 md2 pos.
Proof.
intros v lyc Sc Wc memc mdc pos STK1 sp1 ly2 S2 W2 mem2 md2 k1 CX MID HJ2 HJc Hsp1 HP.
unfold cr_mid in MID |- *. cbv zeta in MID |- *.
destruct MID as (HJ & HPerm & VFL & VSH & VSV & VREP & VSZ).
pose proof CX as (HPRE & _). pose proof HPRE as (_ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof HJ as (_ & _ & _ & _ & _ & Hfrs & _).
pose proof HJc as (_ & Hly & _ & _ & _ & _ & _ & _ & G1 & _ & Gimg & Gfr & _).
pose proof Hly as (_ & _ & _ & _ & _ & HlyF & _).
assert (Hfin : In (1, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
assert (EF : frame_addr ly2 1 pos = frame_addr lyc 1 pos) by (unfold frame_addr; rewrite HlyF; reflexivity).
assert (EFL : flag_addr ly2 1 pos = flag_addr lyc 1 pos) by (unfold flag_addr; rewrite HlyF; reflexivity).
rewrite EF, EFL.
assert (HSTK : CHECK_REPLY_STK = 12464) by reflexivity.
unfold c_sp in *. rewrite HSTK in Hslo.
assert (KF : forall a, frame_addr lyc 1 pos <= a < frame_addr lyc 1 pos + 128 ->
  aview SEGS (w_H W2) mem2 a = aview SEGS (w_H Wc) memc a).
{ intros a Ha. apply (Gfr 1 pos a Hfin); [left; unfold in_zr, frame_rng; cbn [fst snd]; change (fs_frame_bytes 1) with 128; lia
  | apply inFP_nil]. }
assert (KS : forall a, shadow_addr (frame_addr lyc 1 pos) <= a < shadow_addr (frame_addr lyc 1 pos) + 16 ->
  aview SEGS (w_H W2) mem2 a = aview SEGS (w_H Wc) memc a).
{ intros a Ha. apply (Gfr 1 pos a Hfin); [right; unfold in_zr; cbn [fst snd]; change (fs_frame_bytes 1 / 8) with 16; lia
  | apply inFP_nil]. }
assert (KI : forall a, A_G_REC <= a < A_G_REC + 960 -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H Wc) memc a).
{ intros a Ha. destruct (cmd_prog_unowned SEGS B LAWS HB IMG a) as (I1 & I2 & I3).
  - exists (A_G_REC, A_G_REC + 960). split; [left; reflexivity | cbn [fst snd]; lia].
  - apply (Gimg a I1 I2 I3). apply fp_spares_closed; [intros (r & Hr & _); destruct Hr | apply inFP_nil]. }
split; [exact HJ2|]. split; [eapply Permutation_trans; [exact HP | exact HPerm]|].
split.
{ eapply (val_mem_moved SEGS (w_H Wc) (w_H W2) memc mem2); [|exact VFL]. intros k Hk. apply KF.
  change (Z.of_nat 8) with 8 in Hk. lia. }
split.
{ intros i Hi. eapply (val_mem_moved SEGS (w_H Wc) (w_H W2) memc mem2); [|exact (VSH i Hi)]. intros k Hk.
  change (Z.of_nat 1) with 1 in Hk. apply KS. unfold shadow_addr. lia. }
split.
{ intros j r Hj. eapply (val_mem_moved SEGS (w_H Wc) (w_H W2) memc mem2); [|exact (VSV j r Hj)].
  assert (Hj12 : (j < length cr_saved_regs)%nat) by (apply nth_error_Some; rewrite Hj; discriminate).
  cbn [length cr_saved_regs] in Hj12. intros k Hk. change (Z.of_nat 8) with 8 in Hk.
  apply (G1 _); [unfold alloc_ceiling in *; lia | lia | apply inFP_nil]. }
split; (eapply (val_mem_moved SEGS (w_H Wc) (w_H W2) memc mem2); [|eassumption]); intros k Hk; apply KI;
change (Z.of_nat 8) with 8 in Hk; unfold A_G_REC, OFF_REPLY, OFF_REPLY_SIZE in *; lia.
Qed.

(* two conjuncts of the entry bundle, by position *)
Lemma cr7_ev : forall v, cr_cx B RLO RHI v -> st_nev (c_S v) + EV_CHECK_REPLY <= EV_MAX.
Proof. intros v CX. unfold cr_cx in CX. do 28 (apply proj2 in CX). exact (proj1 CX). Qed.
Lemma cr7_rok : forall v, cr_cx B RLO RHI v -> reply_okA (c_n v) (c_w0 v) (c_xr v).
Proof. intros v CX. unfold cr_cx in CX. do 25 (apply proj2 in CX). exact (proj1 CX). Qed.

(* the frame chain at the call site: either the entry's s0 is at the top of the stack window, or the prologue's
   record (ra at sp0 - 8, the caller's s0 at sp0 - 16) extends the entry's chain *)
Lemma cr7_achain : forall v lyc Sc Wc memc mdc pos,
cr_cx B RLO RHI v -> cr_mid B v lyc Sc Wc memc mdc pos ->
exists ch1, achain lyc (rdW Wc memc) (sp1_of (c_sp v)) (c_sp v) ch1.
Proof.
intros v lyc Sc Wc memc mdc pos CX MID.
pose proof CX as (HPRE & _). pose proof MID as (HJ & _ & _ & _ & VSV & _).
pose proof HPRE as (HAR0 & Hra0 & Hra4 & Hgp & Htp & Hstk & Hpres0 & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof HJ as (_ & Hly & _ & _ & _ & _ & _ & _ & G1 & _).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HSTK : CHECK_REPLY_STK = 12464) by reflexivity.
unfold c_sp in *. set (sp0 := spZ (c_regs v)) in *.
assert (Hsp1 : sp1_of sp0 + 128 <= sp0 /\ sp0 - 160 <= sp1_of sp0)
by (unfold sp1_of; pose proof (Z.mod_pos_bound (sp0 - 128) 32 ltac:(lia)); lia).
destruct (Z_lt_ge_dec sp0 (ly_top lyc - 16)) as [Hcase | Hcase]; cycle 1.
- exists []. left. split; [right; left; lia | reflexivity].
- exists ((sp0, raZ (c_regs v), s0Z (c_regs v)) :: c_ch v).
  assert (Hra64 : 0 <= raZ (c_regs v) < 2 ^ 64)
  by (unfold raZ; pose proof (bv_unsigned_in_range 64 (getr (c_regs v) 1)) as H64;
      change (bv_modulus 64) with (2 ^ 64) in H64; lia).
  assert (Hs064 : 0 <= s0Z (c_regs v) < 2 ^ 64)
  by (unfold s0Z; pose proof (bv_unsigned_in_range 64 (getr (c_regs v) 8)) as H64;
      change (bv_modulus 64) with (2 ^ 64) in H64; lia).
  eapply (achain_push lyc (rdW (c_W v) (c_mem v)) (rdW Wc memc) sp0 (s0Z (c_regs v)) (raZ (c_regs v)) (c_ch v) (sp1_of sp0)).
  + apply (achain_ly_top (c_ly v) lyc); [rewrite Etop; reflexivity | exact Hch].
  + rewrite Etop. lia.
  + intros a Ha. apply G1; [lia | lia | apply inFP_nil].
  + apply (rdword_of_val_mem SEGS); [|exact Hra64].
    replace (sp0 - 8) with (sp0 - 8 - 8 * Z.of_nat 0) by lia. unfold raZ.
    replace (getr (c_regs v) 1) with (getr (c_regs v) (Z_to_bv 5 1)) by (f_equal; apply bv_eq; reflexivity).
    exact (VSV 0%nat 1 eq_refl).
  + apply (rdword_of_val_mem SEGS); [|exact Hs064].
    replace (sp0 - 16) with (sp0 - 8 - 8 * Z.of_nat 1) by lia. unfold s0Z.
    replace (getr (c_regs v) 8) with (getr (c_regs v) (Z_to_bv 5 8)) by (f_equal; apply bv_eq; reflexivity).
    exact (VSV 1%nat 8 eq_refl).
  + exact Hra4.
  + lia.
  + pose proof (Z.div_mod sp0 16 ltac:(lia)). pose proof (Z.div_mod sp0 8 ltac:(lia)).
    pose proof (Z.mod_pos_bound sp0 8 ltac:(lia)). lia.
  + lia.
  + lia.
Qed.

(* one syntax_reply_matches call from a mid-walk state, and the state at its return *)
Lemma cr7_srm_call : forall v lyc Sc Wc regsc memc mdc pos q sh ret,
cr_cx B RLO RHI v -> cr_mid B v lyc Sc Wc memc mdc pos -> cr_regs_at B v lyc pos regsc -> cr_ls v lyc Sc ->
getr regsc 10 = w64 q -> 0 <= q < 2 ^ 64 -> getr regsc 11 = w64 (c_p v) -> getr regsc 1 = w64 (BASE + ret) ->
0 <= ret < 2 ^ 40 -> ret mod 2 = 0 ->
astr_argA B lyc Sc (rdW Wc memc) (in_roP SEGS RLO RHI) [] q (Some sh) ->
(forall ly2 S2 W2 regs2 mem2 md2,
   cr_mid B v ly2 S2 W2 mem2 md2 pos -> cr_regs_at B v ly2 pos regs2 -> cr_ls v ly2 S2 -> aregs_preserved regsc regs2 ->
   getr regs2 10 = w64 (if reply_matches sh (c_xr v) then 1 else 0) ->
   SRr SEGS W2 (mkCfg (mkst regs2 (w64 (BASE + ret)) mem2 (seg_rom SEGS)) md2) (CR_POST B v)) ->
SRr SEGS Wc (mkCfg (mkst regsc (w64 (BASE + AF_syntax_reply_matches)) memc (seg_rom SEGS)) mdc) (CR_POST B v).
Proof.
intros v lyc Sc Wc regsc memc mdc pos q sh ret CX MID RA LS Q10 Hq64 Q11 Q1 Hret Hret2 ARG CONT.
destruct (cr7_state v lyc Sc Wc memc mdc pos CX MID) as (HROD & HROK & HGOT & HGRD & HFL & HEVc & HRV & HROI & HVAL).
destruct (cr7_reply v lyc Sc Wc memc mdc pos CX MID) as (m & Hin & Hm & Hstr & Htail & Hblk & _).
destruct (cr7_achain v lyc Sc Wc memc mdc pos CX MID) as (ch1 & HCH).
pose proof CX as (HPRE & _).
pose proof (cr7_ev v CX) as HEV.
assert (Hlensh : Z.of_nat (length sh) < 2 ^ 31)
by (destruct ARG as (_ & _ & Hl & _); unfold LMAX in Hl; lia).
pose proof MID as (HJ & HPerm & VFL & VSH & VSV & VREP & VSZ).
pose proof HPRE as (HAR0 & Hra0 & Hra4 & Hgp & Htp & Hstk & Hpres0 & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof RA as (R2 & R3 & R4 & R8 & R9 & R18 & R23 & R22 & R24 & R25 & R20 & R26 & R27).
pose proof HJ as (HARc & Hly & _ & _ & _ & _ & Hnevc & _).
pose proof Hly as (_ & _ & _ & _ & _ & HlyF & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof pa_base_lo as HBLO. pose proof pa_B_ok as HBASE.
assert (HSTK : CHECK_REPLY_STK = 12464) by reflexivity.
unfold c_sp in *. set (sp0 := spZ (c_regs v)) in *.
assert (Hsp1 : sp1_of sp0 = sp0 - 128 - sp0 mod 32 /\ (sp0 mod 32 = 0 \/ sp0 mod 32 = 16)).
{ unfold sp1_of. replace ((sp0 - 128) mod 32) with (sp0 mod 32)
    by (rewrite Zminus_mod; change (128 mod 32) with 0; rewrite Z.sub_0_r, Z.mod_mod by lia; reflexivity).
  split; [reflexivity|]. pose proof (Z.mod_pos_bound sp0 32 ltac:(lia)).
  pose proof (Z.div_mod sp0 32 ltac:(lia)). pose proof (Z.div_mod sp0 16 ltac:(lia)). lia. }
destruct Hsp1 as [Hsp1e Hsp1m].
assert (Hspc : spZ regsc = sp0 + (sp1_of sp0 - sp0))
by (unfold spZ at 1; rewrite R2; unfold w64; rewrite unsigned_lit_small by lia; lia).
assert (Hmod : (sp1_of sp0 - sp0) mod 16 = 0).
{ rewrite Hsp1e. destruct Hsp1m as [H0 | H0]; rewrite H0.
  - replace (sp0 - 128 - 0 - sp0) with ((-8) * 16) by lia. apply Z_mod_mult.
  - replace (sp0 - 128 - 16 - sp0) with ((-9) * 16) by lia. apply Z_mod_mult. }
eapply SRr_bind.
{ eapply (cl_callS B LAWS Wc regsc memc (w64 (BASE + AF_syntax_reply_matches)) CHECK_REPLY_STK sp0 []
    (c_ly v) (c_S v) (c_W v) (c_mem v) (c_md v) [(1, pos)] lyc Sc mdc 0 SYNTAX_REPLY_MATCHES_STK []
    EV_SYNTAX_REPLY_MATCHES (sp1_of sp0 - sp0) (w64 (BASE + ret)) ch1
    (fun ly2 S2 W2 regs2 mem2 md2 =>
       getr regs2 10 = w64 (if reply_matches sh (c_xr v) then 1 else 0) /\
       Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) /\ ly2 = lyc /\ S2 = Sc) HJ Hspc Hmod);
  [ lia | unfold SYNTAX_REPLY_MATCHES_STK, ESTACK; lia | rewrite HSTK; unfold SYNTAX_REPLY_MATCHES_STK, ESTACK; lia
  | exact R3 | exact R4 | exact Q1 | apply ret_ok_codeptr_v; [lia | exact Hret2] | unfold w64; rewrite unsigned_lit_small by lia; lia
  | replace (sp0 + (sp1_of sp0 - sp0)) with (sp1_of sp0) by lia;
    unfold s0Z; rewrite R8; unfold w64; rewrite unsigned_lit_small by lia; exact HCH
  | intros HPRE1 | intros a Ha; exfalso; exact (inFP_nil a Ha) ].
  eapply SRr_mono.
  - exact (SRM fx lyc Sc Wc regsc memc mdc q (c_p v) sh (c_xr v) ltac:(eapply afn_pre_na_of; exact HPRE1) HROD Q10 Hq64 Q11
      ltac:(unfold c_p; apply Z.mod_pos_bound; lia) ARG Hlensh Hblk Hstr Htail HROK HVAL
      ltac:(unfold EV_SYNTAX_REPLY_MATCHES, EV_CHECK_REPLY in *; lia)).
  - cbv beta. unfold apost_base. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ1 & HP & HK).
    exists ly2, S2, regs2, mem2, md2. rewrite Q1.
    split; [reflexivity|]. split; [exact HJ1|]. split; [exact HP | exact HK]. }
cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HJc & HP2 & HR10 & HPerm2 & Ely2 & ES2).
assert (EF : frame_addr ly2 1 pos = frame_addr lyc 1 pos).
{ pose proof HJc as (_ & Hly2 & _). pose proof Hly2 as (_ & _ & _ & _ & _ & HF2 & _).
  unfold frame_addr. rewrite HF2. reflexivity. }
assert (MID2 : cr_mid B v ly2 S2 W2 mem2 md2 pos).
{ eapply (cr7_mid_call v lyc Sc Wc memc mdc pos SYNTAX_REPLY_MATCHES_STK (sp0 + (sp1_of sp0 - sp0)));
  [exact CX | exact MID | exact HJ2 | exact HJc
  | unfold c_sp; fold sp0; pose proof (Z.mod_pos_bound sp0 32 ltac:(lia)); lia | exact HPerm2]. }
assert (HPz : forall (r : bv 5) (z : Z), Z_to_bv 5 z = r -> acallee_saved z -> getr regs2 r = getr regsc r)
by (intros r z <- Hc; exact (HP2 z Hc)).
assert (RA2 : cr_regs_at B v ly2 pos regs2).
{ unfold cr_regs_at in RA |- *. rewrite EF.
  repeat split;
  lazymatch goal with |- getr regs2 ?r = _ =>
    let z := eval vm_compute in (bv_unsigned r) in
    rewrite (HPz r z ltac:(apply bv_eq; vm_compute; reflexivity) ltac:(unfold acallee_saved; lia)) end;
  assumption. }
exact (CONT ly2 S2 W2 regs2 mem2 md2 MID2 RA2 ltac:(rewrite Ely2, ES2; exact LS) HP2 HR10).
Qed.

(* the shadow entry of g_rec.reply that the inline checks of this segment need *)
Lemma cr7_shok : forall v lyc Sc Wc regs1 memc mdc pos,
cr_mid B v lyc Sc Wc memc mdc pos ->
sh_ok SEGS crBx crSH_mid (crM regs1 v lyc pos) (mrestrict (w_H Wc) memc).
Proof.
intros v lyc Sc Wc regs1 memc mdc pos MID.
pose proof MID as (HJ & _). pose proof (proj1 HJ) as HARc.
pose proof (crM_extra_nth regs1 v lyc pos 0 ltac:(lia)) as E32. pose proof (crM_extra_nth regs1 v lyc pos 1 ltac:(lia)) as E33.
cbn [Nat.add nth crM_extra map app] in E32, E33.
unfold sh_ok, crSH_mid. constructor; [|constructor].
apply (shent_ok_of_range SEGS (w_H Wc) memc (crM regs1 v lyc pos) crBx 33 (A_G_REC + 928) 16 A_G_REC 928 944).
- apply (cmd_addressable_in SEGS B LAWS HB lyc Sc Wc memc mdc (0xad560, 0x5e3680 - 0xad560)); [exact HARc | | reflexivity
  | reflexivity | cbn [fst]; unfold A_G_REC; lia | cbn [fst snd]; unfold A_G_REC; lia].
  unfold Tfib_zero_shadow. repeat (first [left; reflexivity | right]).
- unfold crBx. rewrite (U_atom _ 32 SBc E32) by (unfold SBc; lia). reflexivity.
- rewrite (U_atom _ 33 0x5e32c0 E33) by lia. reflexivity.
- lia.
- lia.
- intros x Hx. unfold A_G_REC, SHADOW_OFF in *. cbn [Z.min Z.max] in Hx. lia.
Qed.

(* every region of the seed's state is read-only, so a run from it writes nothing (awr_ok) *)
Ltac cr7_awr :=
first [ (try unfold ss7; cbn [ss_mem]; repeat (apply awr_ok_cons_ro; [cbn; lia|]); apply awr_ok_nil)
      | (lazymatch goal with |- awr_ok ?a1 ?a2 ?a3 ?rs ?a5 ?a6 ?a7 ?a8 ?a9 ?a10 ?a11 ?a12 =>
           let rs' := eval vm_compute in rs in change (awr_ok a1 a2 a3 rs' a5 a6 a7 a8 a9 a10 a11 a12) end;
         repeat (apply awr_ok_cons_ro; [cbn; lia|]); apply awr_ok_nil) ].
(* the registers cr_regs_at names, read off a state a run from the seed reached: the run left them as they were *)
Ltac cr7_regs_at HSx EErx E32x E33x E36x E38x :=
unfold cr_regs_at;
split; [ let Q := fresh in prreg HSx (2%bv : bv 5) Q; rewrite Q, (EErx 2%nat 2%bv eq_refl); assumption |];
split; [ let Q := fresh in prreg HSx (3%bv : bv 5) Q; rewrite Q, (EErx 3%nat 3%bv eq_refl); assumption |];
split; [ let Q := fresh in prreg HSx (4%bv : bv 5) Q; rewrite Q, (EErx 4%nat 4%bv eq_refl); assumption |];
split; [ let Q := fresh in prreg HSx (8%bv : bv 5) Q; rewrite Q, (EErx 8%nat 8%bv eq_refl); assumption |];
split; [ let Q := fresh in prreg HSx (9%bv : bv 5) Q; rewrite Q, (EErx 2%nat 2%bv eq_refl); assumption |];
split; [ let Q := fresh in prreg HSx (18%bv : bv 5) Q; rewrite Q, E36x; reflexivity |];
split; [ let Q := fresh in prreg HSx (23%bv : bv 5) Q; rewrite Q, E36x; reflexivity |];
split; [ let Q := fresh in prreg HSx (22%bv : bv 5) Q; rewrite Q, E38x; rewrite <- SBc_SHADOW_OFF; reflexivity |];
split; [ let Q := fresh in prreg HSx (24%bv : bv 5) Q; rewrite Q, E32x; rewrite <- SBc_SHADOW_OFF; reflexivity |];
split; [ let Q := fresh in prreg HSx (25%bv : bv 5) Q; rewrite Q, E33x; reflexivity |];
split; [ let Q := fresh in prreg HSx (20%bv : bv 5) Q; rewrite Q, E33x, unsigned_lit_small by lia; reflexivity |];
split; [ first [ rewrite (st_ok_pi_restrict_reg _ _ _ _ (26%bv : bv 5) HSx)
               | rewrite (st_ok_restrict_reg SEGS _ _ _ _ (26%bv : bv 5) HSx) ];
         apply denot_s10; [exact E33x | exact E32x]
       | let Q := fresh in prreg HSx (27%bv : bv 5) Q; rewrite Q, (EErx 27%nat 27%bv eq_refl); assumption ].

(* the shape matched: the branch at 0x870f4 goes to the epilogue *)
Lemma cr7_arm_epi1 : CR_EPI_stmt B RLO RHI -> forall v lyc Sc Wc regsc memc mdc pos b,
cr_cx B RLO RHI v -> cr_mid B v lyc Sc Wc memc mdc pos -> cr_regs_at B v lyc pos regsc -> cr_ls v lyc Sc ->
getr regsc 10 = w64 b -> 0 <= b < 2 ^ 64 -> b <> 0 ->
SRr SEGS Wc (mkCfg (mkst regsc (w64 (BASE + CR_RET_SRM1)) memc (seg_rom SEGS)) mdc) (CR_POST B v).
Proof.
intros EPI v lyc Sc Wc regsc memc mdc pos b CX MID RA LS H10 Hb Hb0.
pose proof (cr7_seed v lyc Sc Wc regsc memc mdc pos CR_RET_SRM1 CX MID RA) as HS.
pose proof (cr7_shok v lyc Sc Wc regsc memc mdc pos MID) as SHOK.
set (E := crM regsc v lyc pos) in HS, SHOK.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold crM; apply Eimg_env).
assert (EEr : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew E k = getr regsc r)
by (subst E; intros k r Hk; apply crM_reg; exact Hk).
assert (EX : forall j, (j < 23)%nat -> ew E (32 + j) = nth j (crM_extra v lyc pos) (Z_to_bv 64 0))
by (subst E; intros j Hj; apply crM_extra_nth; exact Hj).
pose proof (EX 0%nat ltac:(lia)) as E32. pose proof (EX 1%nat ltac:(lia)) as E33.
pose proof (EX 4%nat ltac:(lia)) as E36. pose proof (EX 6%nat ltac:(lia)) as E38.
cbn [Nat.add nth crM_extra map app] in E32, E33, E36, E38.
assert (E10 : ew E 10 = Z_to_bv 64 b) by (rewrite (EEr 10%nat 10%bv eq_refl); exact H10).
pose proof MID as (HJ & _).
pose proof RA as (R2 & R3 & R4 & R8 & R9 & R18 & R23 & R22 & R24 & R25 & R20 & R26 & R27).
psrr_branch_tok RUN paj_branch HS SHOK crSpan.
- paj_run_to_tok RUNTO HS HJ SHOK crSpan CR_EPI.
  { cr7_awr. }
  set (mdw := with_vm_backing (m_vm_lazy mdc) mat mdc) in *; clearbody mdw.
  lazymatch type of HFr with frame_of ?Ex ?rs _ _ =>
    pose proof (kept_of_frame (segs:=SEGS) Ex rs _ _ _ (fun _ => False) HFr
      ltac:(intros bb wlo whi a Hinw Hrr; vm_compute in Hinw;
            repeat (destruct Hinw as [Hq | Hinw]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; lia|]);
            destruct Hinw)) as UN0 end.
  pose proof (cr7_aview_all (w_H Wc) memc (ms_mem ms) ltac:(intros a Ha; apply UN0; [exact Ha | intros []])) as UNA.
  pose proof (cr7_mid_run v lyc Sc Wc memc mdc (ms_mem ms) mdw pos MID HJ UNA) as MID1.
  assert (RA1 : cr_regs_at B v lyc pos (ms_regs ms)) by cr7_regs_at HS EEr E32 E33 E36 E38.
  pmkst HS.
  exact (EPI v lyc Sc Wc (ms_regs ms) (ms_mem ms) mdw pos CX MID1 RA1 LS).
- exfalso. rewrite branch_ne_U in Hc. rewrite (U_atom E 10 b E10) in Hc by lia.
  replace (U E (SLit 0)) with 0 in Hc by reflexivity.
  apply Bool.negb_false_iff, Z.eqb_eq in Hc. lia.
Qed.

(* the second shape matched: the branch at 0x87110 does not go to the abort *)
Lemma cr7_arm_epi2 : CR_EPI_stmt B RLO RHI -> forall v lyc Sc Wc regsc memc mdc pos b,
cr_cx B RLO RHI v -> cr_mid B v lyc Sc Wc memc mdc pos -> cr_regs_at B v lyc pos regsc -> cr_ls v lyc Sc ->
getr regsc 10 = w64 b -> 0 <= b < 2 ^ 64 -> b <> 0 ->
SRr SEGS Wc (mkCfg (mkst regsc (w64 (BASE + CR_RET_SRM2)) memc (seg_rom SEGS)) mdc) (CR_POST B v).
Proof.
intros EPI v lyc Sc Wc regsc memc mdc pos b CX MID RA LS H10 Hb Hb0.
pose proof (cr7_seed v lyc Sc Wc regsc memc mdc pos CR_RET_SRM2 CX MID RA) as HS.
pose proof (cr7_shok v lyc Sc Wc regsc memc mdc pos MID) as SHOK.
set (E := crM regsc v lyc pos) in HS, SHOK.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold crM; apply Eimg_env).
assert (EEr : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew E k = getr regsc r)
by (subst E; intros k r Hk; apply crM_reg; exact Hk).
assert (EX : forall j, (j < 23)%nat -> ew E (32 + j) = nth j (crM_extra v lyc pos) (Z_to_bv 64 0))
by (subst E; intros j Hj; apply crM_extra_nth; exact Hj).
pose proof (EX 0%nat ltac:(lia)) as E32. pose proof (EX 1%nat ltac:(lia)) as E33.
pose proof (EX 4%nat ltac:(lia)) as E36. pose proof (EX 6%nat ltac:(lia)) as E38.
cbn [Nat.add nth crM_extra map app] in E32, E33, E36, E38.
assert (E10 : ew E 10 = Z_to_bv 64 b) by (rewrite (EEr 10%nat 10%bv eq_refl); exact H10).
pose proof MID as (HJ & _).
pose proof RA as (R2 & R3 & R4 & R8 & R9 & R18 & R23 & R22 & R24 & R25 & R20 & R26 & R27).
psrr_branch_tok RUN paj_branch HS SHOK crSpan.
- exfalso. rewrite branch_eq_U in Hc. rewrite (U_atom E 10 b E10) in Hc by lia.
  replace (U E (SLit 0)) with 0 in Hc by reflexivity. apply Z.eqb_eq in Hc. lia.
- paj_run_to_tok RUNTO HS HJ SHOK crSpan CR_EPI.
  { cr7_awr. }
  set (mdw := with_vm_backing (m_vm_lazy mdc) mat mdc) in *; clearbody mdw.
  lazymatch type of HFr with frame_of ?Ex ?rs _ _ =>
    pose proof (kept_of_frame (segs:=SEGS) Ex rs _ _ _ (fun _ => False) HFr
      ltac:(intros bb wlo whi a Hinw Hrr; vm_compute in Hinw;
            repeat (destruct Hinw as [Hq | Hinw]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; lia|]);
            destruct Hinw)) as UN0 end.
  pose proof (cr7_aview_all (w_H Wc) memc (ms_mem ms) ltac:(intros a Ha; apply UN0; [exact Ha | intros []])) as UNA.
  pose proof (cr7_mid_run v lyc Sc Wc memc mdc (ms_mem ms) mdw pos MID HJ UNA) as MID1.
  assert (RA1 : cr_regs_at B v lyc pos (ms_regs ms)) by cr7_regs_at HS EEr E32 E33 E36 E38.
  pmkst HS.
  exact (EPI v lyc Sc Wc (ms_regs ms) (ms_mem ms) mdw pos CX MID1 RA1 LS).
Qed.

(* the first shape did not match: the reply re-checked and reloaded (0x870f8-0x87100), mod-host's "resp 0" goes to
   syntax_reply_matches a second time *)
Lemma cr7_arm2 : CR_EPI_stmt B RLO RHI -> forall v lyc Sc Wc regsc memc mdc pos,
cr_cx B RLO RHI v -> cr_mid B v lyc Sc Wc memc mdc pos -> cr_regs_at B v lyc pos regsc -> cr_ls v lyc Sc ->
getr regsc 10 = w64 0 ->
reply_matches REC_MOD_HOST_SHAPE (c_xr v) = true ->
SRr SEGS Wc (mkCfg (mkst regsc (w64 (BASE + CR_RET_SRM1)) memc (seg_rom SEGS)) mdc) (CR_POST B v).
Proof.
intros EPI v lyc Sc Wc regsc memc mdc pos CX MID RA LS H10 HM.
pose proof (cr7_seed v lyc Sc Wc regsc memc mdc pos CR_RET_SRM1 CX MID RA) as HS.
pose proof (cr7_shok v lyc Sc Wc regsc memc mdc pos MID) as SHOK.
destruct (cr7_state v lyc Sc Wc memc mdc pos CX MID) as (_ & _ & _ & _ & _ & _ & _ & _ & HVAL).
set (E := crM regsc v lyc pos) in HS, SHOK.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold crM; apply Eimg_env).
assert (EEr : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew E k = getr regsc r)
by (subst E; intros k r Hk; apply crM_reg; exact Hk).
assert (EX : forall j, (j < 23)%nat -> ew E (32 + j) = nth j (crM_extra v lyc pos) (Z_to_bv 64 0))
by (subst E; intros j Hj; apply crM_extra_nth; exact Hj).
pose proof (EX 0%nat ltac:(lia)) as E32. pose proof (EX 1%nat ltac:(lia)) as E33.
pose proof (EX 2%nat ltac:(lia)) as E34. pose proof (EX 4%nat ltac:(lia)) as E36.
pose proof (EX 6%nat ltac:(lia)) as E38.
cbn [Nat.add nth crM_extra map app] in E32, E33, E34, E36, E38.
assert (E10 : ew E 10 = Z_to_bv 64 0) by (rewrite (EEr 10%nat 10%bv eq_refl); exact H10).
pose proof MID as (HJ & _).
pose proof RA as (R2 & R3 & R4 & R8 & R9 & R18 & R23 & R22 & R24 & R25 & R20 & R26 & R27).
psrr_branch_tok RUN paj_branch HS SHOK crSpan.
- exfalso. rewrite branch_ne_U in Hc. rewrite (U_atom E 10 0 E10) in Hc by lia.
  replace (U E (SLit 0)) with 0 in Hc by reflexivity. cbn in Hc. discriminate Hc.
- paj_run_tok RUN HS HJ SHOK crSpan.
  { cr7_awr. }
  set (mdw := with_vm_backing (m_vm_lazy mdc) mat mdc) in *; clearbody mdw.
  lazymatch type of HFr with frame_of ?Ex ?rs _ _ =>
    pose proof (kept_of_frame (segs:=SEGS) Ex rs _ _ _ (fun _ => False) HFr
      ltac:(intros bb wlo whi a Hinw Hrr; vm_compute in Hinw;
            repeat (destruct Hinw as [Hq | Hinw]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; lia|]);
            destruct Hinw)) as UN0 end.
  pose proof (cr7_aview_all (w_H Wc) memc (ms_mem ms) ltac:(intros a Ha; apply UN0; [exact Ha | intros []])) as UNA.
  pose proof (cr7_mid_run v lyc Sc Wc memc mdc (ms_mem ms) mdw pos MID HJ UNA) as MID1.
  assert (RA1 : cr_regs_at B v lyc pos (ms_regs ms)) by cr7_regs_at HS EEr E32 E33 E36 E38.
  assert (A10 : getr (ms_regs ms) 10 = w64 0x21120).
  { let Q := fresh in prreg HS (10%bv : bv 5) Q; rewrite Q.
    assert (Hv : bv_unsigned (ew E (A_OBJ 13)) = VAL (A_OBJ 13)) by (apply HEI; unfold A_OBJ, A_TEXT, A_LIM; lia).
    rewrite (HVAL 13%nat ltac:(vm_compute; lia)) in Hv. cbn [nth cmd_objs] in Hv.
    unfold w64. rewrite <- Hv, Z_to_bv_bv_unsigned. reflexivity. }
  assert (A11 : getr (ms_regs ms) 11 = w64 (c_p v))
  by (let Q := fresh in prreg HS (11%bv : bv 5) Q; rewrite Q, E34; reflexivity).
  assert (A1 : getr (ms_regs ms) 1 = w64 (BASE + CR_RET_SRM2))
  by (let Q := fresh in prreg HS (1%bv : bv 5) Q; rewrite Q; reflexivity).
  assert (ARG2 : astr_argA B lyc Sc (rdW Wc (ms_mem ms)) (in_roP SEGS RLO RHI) [] 0x21120 (Some REC_MOD_HOST_SHAPE))
  by (apply (cr7_argA_eq B lyc Sc (rdW Wc memc)); [exact UNA | exact (cr7_lit0 v lyc Sc Wc memc mdc pos CX MID)]).
  pmkst HS.
  rewrite (SIGP CS_syntax_reply_matches ltac:(unfold cmd_prog_syms; repeat (first [left; reflexivity | right]))).
  change (cmd_af CS_syntax_reply_matches) with AF_syntax_reply_matches.
  apply (cr7_srm_call v lyc Sc Wc (ms_regs ms) (ms_mem ms) mdw pos 0x21120 REC_MOD_HOST_SHAPE CR_RET_SRM2
    CX MID1 RA1 LS A10 ltac:(lia) A11 A1 ltac:(unfold CR_RET_SRM2; lia) ltac:(reflexivity) ARG2).
  intros ly3 S3 W3 regs3 mem3 md3 MID3 RA3 LS3 HP3 HR10.
  rewrite HM in HR10.
  exact (cr7_arm_epi2 EPI v ly3 S3 W3 regs3 mem3 md3 pos 1 CX MID3 RA3 LS3 HR10 ltac:(lia) ltac:(lia)).
Qed.


Theorem cr_s7 : CR_EPI_stmt B RLO RHI -> CR_JOIN_stmt B RLO RHI.
Proof.
intros EPI v lyc Sc Wc regs1 memc mdc pos q CX MID RA Hcode H10 Hq64 ARG LS.
unfold cr_at.
pose proof (cr7_seed v lyc Sc Wc regs1 memc mdc pos CR_JOIN CX MID RA) as HS.
pose proof (cr7_shok v lyc Sc Wc regs1 memc mdc pos MID) as SHOK.
set (E := crM regs1 v lyc pos) in HS, SHOK.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold crM; apply Eimg_env).
assert (EEr : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew E k = getr regs1 r)
by (subst E; intros k r Hk; apply crM_reg; exact Hk).
assert (EX : forall j, (j < 23)%nat -> ew E (32 + j) = nth j (crM_extra v lyc pos) (Z_to_bv 64 0))
by (subst E; intros j Hj; apply crM_extra_nth; exact Hj).
pose proof (EX 0%nat ltac:(lia)) as E32. pose proof (EX 1%nat ltac:(lia)) as E33.
pose proof (EX 2%nat ltac:(lia)) as E34. pose proof (EX 4%nat ltac:(lia)) as E36.
pose proof (EX 6%nat ltac:(lia)) as E38.
cbn [Nat.add nth crM_extra map app] in E32, E33, E34, E36, E38.
pose proof MID as (HJ & _).
pose proof RA as (R2 & R3 & R4 & R8 & R9 & R18 & R23 & R22 & R24 & R25 & R20 & R26 & R27).
paj_run_tok RUN HS HJ SHOK crSpan.
{ cr7_awr. }
set (mdv := with_vm_backing (m_vm_lazy mdc) mat mdc) in *; clearbody mdv.
lazymatch type of HFr with frame_of ?Ex ?rs _ _ =>
  pose proof (kept_of_frame (segs:=SEGS) Ex rs _ _ _ (fun _ => False) HFr
    ltac:(intros bb wlo whi a Hinw Hrr; vm_compute in Hinw;
          repeat (destruct Hinw as [Hq | Hinw]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; lia|]);
          destruct Hinw)) as UN0 end.
pose proof (cr7_aview_all (w_H Wc) memc (ms_mem ms) ltac:(intros a Ha; apply UN0; [exact Ha | intros []])) as UNA.
pose proof (cr7_mid_run v lyc Sc Wc memc mdc (ms_mem ms) mdv pos MID HJ UNA) as MID1.
assert (RA1 : cr_regs_at B v lyc pos (ms_regs ms)) by cr7_regs_at HS EEr E32 E33 E36 E38.
assert (A10 : getr (ms_regs ms) 10 = w64 q)
by (let Q := fresh in prreg HS (10%bv : bv 5) Q; rewrite Q, (EEr 10%nat 10%bv eq_refl); exact H10).
assert (A11 : getr (ms_regs ms) 11 = w64 (c_p v))
by (let Q := fresh in prreg HS (11%bv : bv 5) Q; rewrite Q, E34; reflexivity).
assert (A1 : getr (ms_regs ms) 1 = w64 (BASE + CR_RET_SRM1))
by (let Q := fresh in prreg HS (1%bv : bv 5) Q; rewrite Q; reflexivity).
assert (ARG1 : astr_argA B lyc Sc (rdW Wc (ms_mem ms)) (in_roP SEGS RLO RHI) [] q (Some (shape_strA (c_n v) (c_w0 v))))
by (apply (cr7_argA_eq B lyc Sc (rdW Wc memc)); [exact UNA | exact ARG]).
pmkst HS.
rewrite (SIGP CS_syntax_reply_matches ltac:(unfold cmd_prog_syms; repeat (first [left; reflexivity | right]))).
change (cmd_af CS_syntax_reply_matches) with AF_syntax_reply_matches.
apply (cr7_srm_call v lyc Sc Wc (ms_regs ms) (ms_mem ms) mdv pos q (shape_strA (c_n v) (c_w0 v)) CR_RET_SRM1
  CX MID1 RA1 LS A10 Hq64 A11 A1 ltac:(unfold CR_RET_SRM1; lia) ltac:(reflexivity) ARG1).
intros ly2 S2 W2 regs2 mem2 md2 MID2 RA2 LS2 HP2 HR10.
destruct (reply_matches (shape_strA (c_n v) (c_w0 v)) (c_xr v)) eqn:HRM.
- exact (cr7_arm_epi1 EPI v ly2 S2 W2 regs2 mem2 md2 pos 1 CX MID2 RA2 LS2 HR10 ltac:(lia) ltac:(lia)).
- apply (cr7_arm2 EPI v ly2 S2 W2 regs2 mem2 md2 pos CX MID2 RA2 LS2 HR10).
  destruct (cr7_rok v CX) as (_ & HR2). destruct (HR2 Hcode) as [Hbad | Hgood]; [rewrite HRM in Hbad; discriminate | exact Hgood].
Qed.


End e.
End f.
End d.
