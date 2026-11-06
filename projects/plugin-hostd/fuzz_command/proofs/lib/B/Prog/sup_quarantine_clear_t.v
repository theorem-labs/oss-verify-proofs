(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the ASan+UBSan walk of sup_quarantine_clear (plugin-hostd/fuzz_command,
   fuzz_command.asan-ubsan), its tail: the walk's statement and the segment from the return of rec_shape_of
   (0x8bde8) through the tail jump into answer (0x8be04) to the statement's post. In the form of
   lib/A/Prog/sup_quarantine_clear_s3.v (the A walk, a working branch f2402580166: sqc_SX's
   rec_shape_of return, run E and answer tail), re-derived on B's code. *)

(* sup_quarantine_clear on B, 0x8bde8 .. 0x8be04 (8 instructions, no branch, no ASan check, no UBSan trap):
   li a2,1; mv a1,a0; mv a0,s1; ld ra,24(sp); ld s0,16(sp); ld s1,8(sp); addi sp,sp,32; j answer.
   answer runs at the entry stack pointer and returns to the entry's ra. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import String ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI00 YI04 YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YI16 YM05 YC5d YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdSyms CmdAddr CmdList CmdPa CmdPaLib.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaCall PaCallRun PaLibF PaLibG PaLibH PaSB PaDenot PaNoChain.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob CmdBase CmdRep CmdObj CmdRo CmdZsh CmdChk.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
xmalloc_c rec_calls_free_c record_c arg_s_c rec_shape_of_c mix_call_c hand_back_c answer_c sup_quarantine_clear_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require CmdRecBase CmdRecRest CmdRecRo CmdRecImg RecBLemmas.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import sup_quarantine_clear_aux.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Definition SQB_STK : Z := SUP_QUARANTINE_CLEAR_STK.
Lemma SQB_STK_val : SQB_STK = 16592.
Proof. reflexivity. Qed.
Definition sqcb_Bspan : Z * Z := (SB, SB + 2 ^ 44 - 1).

Lemma sqcb_in_filter : forall (old : Z) (l : list (Z * Z)) pn,
In pn (filter (fun pn => fst pn =? old) l) -> In pn l /\ fst pn = old.
Proof.
intros old l pn. induction l as [|a l IH]; intros H; [cbn in H; contradiction|].
cbn in H. destruct (decide _) as [Hd | Hd] in H.
- destruct H as [<- | H].
  + split; [left; reflexivity|]. revert Hd. destruct (fst a =? old) eqn:E; intros Hd; [apply Z.eqb_eq; exact E | destruct Hd].
  + destruct (IH H) as [H1 H2]. split; [right; exact H1 | exact H2].
- destruct (IH H) as [H1 H2]. split; [right; exact H1 | exact H2].
Qed.

(* after a symbolic run the model term grows (a Theorem Labs lane, 2026-10-28): name it *)
Ltac sqcb_md :=
lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?m |} _ =>
  let mdv := fresh "mdv" in set (mdv := m) in *; clearbody mdv end.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation SIG s := (@pa_sigma _ cmd_listing PI s).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
(* the statement's callee answer (sup_quarantine_clear_c.v, at every FP state), the object bridge, and the walk
   hypotheses (a Theorem Labs lane's RULING-STMT.md section 1): the record HB, the image facts IMG of a Theorem Labs lane's lib/B/Prog/CmdRecBase.v,
   from which a Theorem Labs lane's CmdRecRest / CmdRecRo give the read-only and program-static facts below *)
Context {TANSWER : forall fx0 : YK11.FPState, @tanswer_spec fx0 rc SK PI B MT}.
Context {VOBJS : cmd_val_objs}.
Context {HB : CmdBSyms B}.
Context {IMG : CmdRecBase.cmd_img_facts SEGS B}.
Context {MTL : ameter_laws MT}.
Context {cmd_sig_prog_PB : cmd_sig_prog}.
Let LAWS : AR_laws SEGS B := AR_laws_ok SEGS B.
Let RUN := paj_run B LAWS.
Let cmd_prog_img := @CmdRecRest.cmd_prog_img rc SK SEGS B LAWS HB IMG.
Let cmd_ro_prog_apart := @CmdRecRest.cmd_ro_prog_apart rc SK SEGS B LAWS HB IMG.
Let ROB := @CmdRecRo.ROB rc SK SEGS B LAWS HB IMG.
Let cmd_ro_ok_of_aro := @CmdRecRo.cmd_ro_ok_of_aro rc SK SEGS B LAWS HB IMG.

(* the statement's premises (sup_quarantine_clear_c.v:79-104) *)
Definition sqcb_pre ly S W (regs : bvmap 5 word) mem md ch (pw : Z) (which : option (list byte)) (R : rstate)
  (O : list (Z * Z)) : Prop :=
afn_pre SEGS B SQB_STK ly S W regs mem md ch /\
Z.land (Z.shiftr (bv_unsigned (@fp_csr fx)) 5) 7 = 0 /\
arodata_okP SEGS RLO RHI B (rdW W mem) /\
cmd_ro_ok (rdW W mem) /\
getr regs 10 = w64 pw /\ 0 <= pw < 2 ^ 64 /\
(exists x, which = Some x /\
 in_blockA (ablocks B ly S) pw (Z.of_nat (length x) + 1) /\ astr_atR (rdW W mem) pw x /\
 Z.of_nat (length x) + 1 <= LMAX + 1 /\
 Forall (fun qk => iv_apart pw (Z.of_nat (length x) + 1) (fst qk) (snd qk)) O) /\
rec_repA B ly S (rdW W mem) R O /\
Z.of_nat (length (frames S)) <= 8 /\
st_nev S + EV_SUP_QUARANTINE_CLEAR R <= EV_MAX /\ blocks_bytes S + LIVE_SUP_QUARANTINE_CLEAR R which <= LIVE_MAX /\
mo_ok MT S (XM_SUP_QUARANTINE_CLEAR MT R which).

(* the statement's post (sup_quarantine_clear_c.v:104-128) *)
Definition sqcb_Q (ly : alayout) (S : astate) (R : rstate) (O : list (Z * Z)) (which : option (list byte))
: alayout -> astate -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop :=
fun ly' S' W' regs' mem' md' => exists (R' : rstate) (t : list byte) (q : Z) (O' : list (Z * Z)),
 sup_quarantine_clear_m R which = (R', t) /\
 getr regs' 10 = w64 q /\ 4096 <= q < 2 ^ 64 /\
 rec_repA B ly' S' (rdW W' mem') R' O' /\
 (forall pn, In pn O' -> In pn O \/ ~ In pn (ablocks B ly S)) /\
 In (q, Z.of_nat (length t) + 1) (ablocks B ly' S') /\
 (forall pn, In pn (ablocks B ly S) -> ~ In pn O -> pn <> (q, Z.of_nat (length t) + 1)) /\
 ~ In q (map fst O') /\
 astr_atR (rdW W' mem') q t /\
 (forall pn, In pn (ablocks B ly S) -> ~ In pn O ->
    In pn (ablocks B ly' S') /\ iv_apart (fst pn) (snd pn) q (Z.of_nat (length t) + 1)) /\
 (forall pn, In pn (ablocks B ly' S') ->
    (In pn (ablocks B ly S) /\ ~ In pn O) \/ In pn O' \/ pn = (q, Z.of_nat (length t) + 1)) /\
 blocks_bytes S' <= blocks_bytes S + LIVE_SUP_QUARANTINE_CLEAR R which /\
 mo_le MT S S' (XM_SUP_QUARANTINE_CLEAR MT R which).

(* the walk at the return of rec_shape_of (0x8bde8): the journal from the entry, the frame, the registers the tail
   reads, the reply shape, the recorder after record(11) and arg_s, and the blocks and meter so far *)
Definition sqcb_S3_spec : Prop :=
forall ly S W regs mem md ch pw which R O x (L1 F O1 : list (Z * Z)) p ly3 S3 W3 (regs3 : bvmap 5 word) mem3 md3 k3 q,
sqcb_pre ly S W regs mem md ch pw which R O -> which = Some x ->
ajournal SEGS B SQB_STK (spZ regs) (sqcb_FP O) ly S W mem md [] ly3 S3 W3 mem3 md3 k3 ->
k3 = EV_RECORD R + EV_ARG_S ->
sqcb_frame_at (mrestrict (w_H W3) mem3) (spZ regs - SQB_FRAME) regs ->
getr regs3 2 = w64 (spZ regs - SQB_FRAME) -> getr regs3 3 = w64 (as_gp B) -> getr regs3 4 = w64 (as_tp B) ->
getr regs3 9 = w64 (rec_slot R) -> getr regs3 10 = w64 q -> 0 <= q < 2 ^ 64 ->
(forall r, 18 <= r <= 27 -> getr regs3 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) ->
(forall O', astr_argA B ly3 S3 (rdW W3 mem3) (in_roP SEGS RLO RHI) O' q (Some (shape_of sqcb_verb))) ->
rec_repA B ly3 S3 (rdW W3 mem3) (rec_record R SQB_FN [x]) ((p, Z.of_nat (length x) + 1) :: O1) ->
Permutation (ablocks B ly S) (L1 ++ F) -> (forall pn, In pn F -> In pn O) ->
(forall pn, In pn O1 <-> In pn O /\ ~ In pn F) ->
Permutation (ablocks B ly3 S3) ((p, Z.of_nat (length x) + 1) :: L1) ->
Forall (fun qk => iv_apart p (Z.of_nat (length x) + 1) (fst qk) (snd qk)) L1 ->
mo_le MT S S3 (XM_RECORD MT R + XM_ARG_S MT which) ->
blocks_bytes S3 <= blocks_bytes S + LIVE_ARG_S which ->
SRr SEGS W3 (mkCfg (mkst regs3 (Z_to_bv 64 (BASE + SQB_RETS)) mem3 (seg_rom SEGS)) md3)
(apost_baseF SEGS B SQB_STK (sqcb_FP O) regs ly S W mem md (EV_SUP_QUARANTINE_CLEAR R) (sqcb_Q ly S R O which)).

Lemma sqcb_S3 : sqcb_S3_spec.
Proof.
intros ly S W regs mem md ch pw which R O x L1 F O1 p ly3 S3 W3 regs3 mem3 md3 k3 q
  PRE Hwh HJ Hk HFRM G2 G3 G4 G9 G10 Hq64 G18 HSH HREP3 HPERM HFO HO1 HPERM3 HFR3 MLE3 HBB3.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof PRE as (HPRE & Hfrm0 & HROD & HRO & H10 & Hpw & HARG & HREP & HFR8 & HEV & HLIVE & HMOK).
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQTi).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
assert (HST : SQB_STK = 16592) by reflexivity.
set (sp0 := spZ regs) in *.
set (n := Z.of_nat (length x) + 1) in *.
assert (HOin : forall pn, In pn O -> In pn (ablocks B ly S)) by exact (sqcb_rec_repA_in B ly S _ R O HREP).
assert (Hn16 : (length (r_calls R) <= 16)%nat).
{ destruct HREP as (Q0 & (_ & _ & _ & (Gl & _) & _) & _). exact Gl. }
destruct (sqcb_slot_bounds R Hn16) as (Hcs & Hcb).
set (c := rec_slot R) in *.
pose proof (proj1 HJ) as HAR3.
assert (Hsp0 : 2 ^ 46 + 32 <= sp0 <= 2 ^ 47) by (rewrite HST in Hslo; lia).
assert (G2u : bv_unsigned (getr regs3 2) = sp0 - SQB_FRAME)
  by (rewrite G2; unfold w64; apply unsigned_lit_small; unfold SQB_FRAME; lia).
assert (HS : st_ok_pi SEGS VAL (sqcb_E regs3 regs) (sqcb_ssF SQB_RETS sr_atoms)
  (restrict (w_H W3) (mkst regs3 (Z_to_bv 64 (BASE + SQB_RETS)) mem3 (seg_rom SEGS)))).
{ apply sqcb_seed.
  - rewrite G2u. unfold SQB_FRAME. lia.
  - rewrite G2u. unfold SQB_FRAME. replace (sp0 - 32) with (sp0 + (-2) * 16) by lia. rewrite Z_mod_plus_full. exact Hal16.
  - unfold sqcb_E. apply regs_ok_Eimg_Ereg.
  - rewrite G2u. exact HFRM. }
assert (EE : forall kk (rr : bv 5), Z.of_nat kk = bv_unsigned rr -> ew (sqcb_E regs3 regs) kk = getr regs3 rr)
  by (intros kk rr Hkk; exact (sqcb_E_reg regs3 regs kk rr Hkk)).
assert (EX : forall k, (32 <= k < 35)%nat -> ew (sqcb_E regs3 regs) k = nth (k - 32) (sqcb_extra regs) (Z_to_bv 64 0))
  by (intros k0 Hk0; exact (sqcb_E_extra_at regs3 regs k0 Hk0)).
assert (HEI : img_env VAL A_LIM (sqcb_E regs3 regs)) by exact (sqcb_E_img regs3 regs).
set (E := sqcb_E regs3 regs) in *.
assert (SHOK : sh_ok SEGS (SLit 0) [] E (mrestrict (w_H W3) mem3)) by (unfold sh_ok; constructor).
(* 0x8bde8 .. 0x8be04: a2 := 1, a1 := the shape, a0 := the slot, the frame's registers back, sp += 32, j answer *)
paj_run_tok RUN HS HJ SHOK sqcb_Bspan.
{ lazymatch goal with |- awr_ok ?sg ?Bv ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?f0 ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok sg Bv Ex rs' stk spx fp b0 bc f0 lyx own) end.
  apply awr_ok_cons_ro; [cbn [YP09.r_whi YP09.r_wlo]; lia|]. apply awr_ok_nil. }
pmkst HS. sqcb_md.
prreg HS (1%bv : bv 5) T1. prreg HS (2%bv : bv 5) T2. prreg HS (3%bv : bv 5) T3. prreg HS (4%bv : bv 5) T4.
prreg HS (8%bv : bv 5) T8. prreg HS (9%bv : bv 5) T9. prreg HS (10%bv : bv 5) T10. prreg HS (11%bv : bv 5) T11.
prreg HS (12%bv : bv 5) T12.
lazymatch goal with HFx : frame_of E _ (mrestrict _ _) (mrestrict _ _) |- _ => rename HFx into HFRE end.
pose proof (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun _ => False) HFRE
  ltac:(intros b wlo whi a Hin Hrr; vm_compute in Hin;
        repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; lia|]); destruct Hin)) as KE.
pose proof (proj1 HJ) as HART.
(* the registers at the jump to answer: the entry's callee-saved registers, sp and ra, a0 = c, a1 = q, a2 = 1 *)
assert (A1 : getr (ms_regs ms) 1 = getr regs 1).
{ rewrite T1. rewrite (EX 32%nat ltac:(lia)). reflexivity. }
assert (X2 : getr (ms_regs ms) 2%bv = getr regs 2%bv).
{ rewrite T2. rewrite (EE 2%nat 2%bv eq_refl), G2. unfold w64.
  rewrite unsigned_lit_small by (unfold SQB_FRAME; lia). unfold SQB_FRAME. replace (sp0 - 32 + 32) with sp0 by lia.
  unfold sp0, spZ. apply Z_to_bv_bv_unsigned. }
assert (X3 : getr (ms_regs ms) 3%bv = getr regs 3%bv) by (rewrite T3, (EE 3%nat 3%bv eq_refl), G3, Hgp; reflexivity).
assert (X4 : getr (ms_regs ms) 4%bv = getr regs 4%bv) by (rewrite T4, (EE 4%nat 4%bv eq_refl), G4, Htp; reflexivity).
assert (X8 : getr (ms_regs ms) 8%bv = getr regs 8%bv) by (rewrite T8, (EX 33%nat ltac:(lia)); reflexivity).
assert (X9 : getr (ms_regs ms) 9%bv = getr regs 9%bv) by (rewrite T9, (EX 34%nat ltac:(lia)); reflexivity).
assert (Y10 : getr (ms_regs ms) 10 = w64 c) by (rewrite T10, (EE 9%nat 9%bv eq_refl); exact G9).
assert (Y11 : getr (ms_regs ms) 11 = w64 q) by (rewrite T11, (EE 10%nat 10%bv eq_refl); exact G10).
assert (X18_27 : forall r, 18 <= r <= 27 -> getr (ms_regs ms) (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)).
{ intros r Hr. rewrite <- (G18 r Hr).
  assert (H10r : r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
  repeat (destruct H10r as [-> | H10r]); [..| subst r];
  rewrite (st_ok_restrict_reg SEGS (w_H W3) E _ _ _ HS); cbn [ms_regs];
  lazymatch goal with |- sv_denot _ (sr_get ?a ?rr2) = _ => let v := eval vm_compute in (sr_get a rr2) in change (sr_get a rr2) with v end;
  cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned;
  lazymatch goal with |- ew _ ?m = getr _ (Z_to_bv 5 ?rr) => exact (EE m (Z_to_bv 5 rr) eq_refl) end. }
assert (HPA : aregs_preserved regs (ms_regs ms)).
{ apply sqcb_pres. intros nr Hnr. cbn [In] in Hnr.
  destruct Hnr as [<- | [<- | [<- | [<- | [<- | Hnr]]]]]; [exact X2 | exact X3 | exact X4 | exact X8 | exact X9 |].
  apply X18_27. repeat (destruct Hnr as [<- | Hnr]; [lia|]). destruct Hnr. }
(* ---- the memory at the jump: the run wrote nothing ---- *)
assert (HRK : forall a, 0 <= a < 2 ^ 64 -> rdW W3 (ms_mem ms) a = rdW W3 mem3 a)
  by (intros a Ha; exact (KE a Ha (fun H => H))).
assert (HO23 : forall pn, In pn ((p, n) :: O1) -> In pn (ablocks B ly3 S3))
  by exact (sqcb_rec_repA_in B _ _ _ _ _ HREP3).
assert (HREPT : rec_repA B ly3 S3 (rdW W3 (ms_mem ms)) (rec_record R SQB_FN [x]) ((p, n) :: O1)).
{ apply (sqcb_rec_repA_ext B ly3 S3 (rdW W3 mem3) ly3 S3 _ _ _ HREP3 HO23).
  intros a [Ha | [Ha | (pn & Hpn & Ha)]]; apply HRK;
  [unfold A_G_REC, REC_SIZE in Ha; lia | unfold A_REC_SPILL, SC_SIZE in Ha; lia |].
  destruct pn as [b m]. cbn [fst snd] in Ha.
  destruct (sqcb_blk_bounds B ly3 S3 W3 mem3 md3 b m HAR3 (HO23 _ Hpn)) as (Hb & Hbc & _ & Hmr & _). lia. }
assert (HSHT : forall O', astr_argA B ly3 S3 (rdW W3 (ms_mem ms)) (in_roP SEGS RLO RHI) O' q (Some (shape_of sqcb_verb))).
{ intros O'. apply (sqcb_argA_kept B _ _ (rdW W3 mem3)); [exact (HSH O')|]. intros i Hi. apply HRK.
  pose proof (HSH []) as Hq. cbn [astr_argA] in Hq. destruct Hq as (_ & _ & _ & [(Hblk & _) | (Hro & _)]).
  - destruct Hblk as (b & m & Hin & Hb1 & Hb2).
    destruct (sqcb_blk_bounds B ly3 S3 W3 mem3 md3 b m HAR3 Hin) as (Hb & Hbc & _ & Hmr & _). lia.
  - destruct (Hro i Hi) as (Hr & _). pose proof (pa_img_range _ (proj1 (cmd_ro_prog_apart _ Hr))). lia. }
(* the old answer: g_rec.answer, the start of one of the recorder's blocks or 0 *)
pose proof HREPT as (QT & HQTa & HOQT).
destruct (sqcb_old_at _ _ _ _ HQTa) as [HOLD HOLDin].
set (old := sqcb_old QT) in *.
assert (HOLDO2 : forall pn, In pn (ablocks B ly3 S3) -> fst pn = old -> In pn ((p, n) :: O1)).
{ intros pn Hpn Hf. unfold old, sqcb_old in Hf. destruct (l_answer QT) as [an|] eqn:Ean.
  - pose proof (HOLDin an eq_refl) as Han. pose proof (proj2 (HOQT an) Han) as HanO.
    rewrite (sqcb_same_start B ly3 S3 W3 mem3 md3 pn an HAR3 Hpn (HO23 _ HanO) Hf). exact HanO.
  - destruct pn as [b m]. destruct (sqcb_blk_bounds B ly3 S3 W3 mem3 md3 b m HAR3 Hpn) as (Hb & _). cbn [fst] in Hf. lia. }
assert (Hold64 : 0 <= old < 2 ^ 64).
{ unfold old, sqcb_old. destruct (l_answer QT) as [an|] eqn:Ean; [|lia].
  pose proof (HO23 _ (proj2 (HOQT an) (HOLDin an eq_refl))) as Han3. destruct an as [a1 a2].
  destruct (sqcb_blk_bounds B ly3 S3 W3 mem3 md3 a1 a2 HAR3 Han3) as (Hb0 & Hb1 & _ & _ & Hr1). cbn [fst]. lia. }
(* the blocks: the copy (p, n) is fresh, every other block of the walk's own is one of O1 *)
assert (HpL1 : ~ In (p, n) L1).
{ intros Hin. rewrite Forall_forall in HFR3. pose proof (HFR3 _ Hin) as Hap. cbn [fst snd] in Hap.
  unfold iv_apart, n in Hap. lia. }
assert (HL0 : forall pn, In pn (ablocks B ly S) -> In pn L1 \/ In pn F)
  by (intros pn Hpn; apply in_app_or; exact (Permutation_in _ HPERM Hpn)).
assert (HL13 : forall pn, In pn L1 -> In pn (ablocks B ly3 S3))
  by (intros pn Hpn; apply (Permutation_in _ (Permutation_sym HPERM3)); right; exact Hpn).
assert (HL10 : forall pn, In pn L1 -> In pn (ablocks B ly S))
  by (intros pn Hpn; apply (Permutation_in _ (Permutation_sym HPERM)); apply in_or_app; left; exact Hpn).
assert (HF0 : forall pn, In pn F -> In pn (ablocks B ly S))
  by (intros pn Hpn; apply (Permutation_in _ (Permutation_sym HPERM)); apply in_or_app; right; exact Hpn).
assert (HL1F : forall pn, In pn L1 -> ~ In pn F)
  by (intros pn H1 H2; exact (sqcb_dup_false B ly S W mem md L1 F pn HAR HPERM H1 H2)).
assert (HO2O : forall pn, In pn ((p, n) :: O1) -> In pn (ablocks B ly S) -> In pn O).
{ intros pn [<- | Hpn] H0.
  - destruct (HL0 _ H0) as [H | H]; [exfalso; exact (HpL1 H) | exact (HFO _ H)].
  - exact (proj1 (proj1 (HO1 pn) Hpn)). }
assert (HL1O : forall pn, In pn L1 -> In pn O -> In pn ((p, n) :: O1)).
{ intros pn H1 HO. right. apply HO1. split; [exact HO | exact (HL1F _ H1)]. }
(* the model's step *)
assert (HM : sup_quarantine_clear_m R which = rec_answer (rec_record R SQB_FN [x]) (SQB_FN, [x]) (shape_of sqcb_verb) true)
  by (rewrite Hwh; exact (sqcb_m R (Some x))).
(* ---- the tail jump into answer (0x8be04): answer runs at the entry's sp and returns to the entry's ra ---- *)
assert (SPA : spZ (ms_regs ms) = sp0) by (unfold spZ at 1; rewrite X2; reflexivity).
assert (HAS : ANSWER_STK = 16592) by reflexivity.
assert (HFPlow : forall a, inFP (sqcb_FP O) a -> a < alloc_ceiling)
  by (intros a Ha; exact (sqcb_FP_low B ly S W mem md O a HAR HOin Ha)).
assert (HchA : achain ly3 (rdW W3 (ms_mem ms)) (spZ (ms_regs ms)) (s0Z (ms_regs ms)) ch).
{ rewrite SPA. unfold s0Z at 1. rewrite X8. exact (sqcb_achain_kept B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ HFPlow Hch). }
assert (HPREA : afn_pre SEGS B ANSWER_STK ly3 S3 W3 (ms_regs ms) (ms_mem ms) mdv ch).
{ apply (afn_pre_at SEGS B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (ms_regs ms) ANSWER_STK 0 ch HJ).
  - rewrite SPA. lia.
  - reflexivity.
  - lia.
  - rewrite HAS. lia.
  - rewrite HAS, HST. lia.
  - rewrite A1. exact Hra.
  - unfold raZ. rewrite A1. exact Hra4.
  - rewrite X3. exact Hgp.
  - rewrite X4. exact Htp.
  - exact HchA. }
pose proof HJ as (_ & _ & _ & _ & _ & HfrJ & HnevJ & _).
assert (HRAJ : arodata_okP SEGS RLO RHI B (rdW W3 (ms_mem ms)))
  by exact (sqcb_aro B (ROB := ROB) cmd_ro_prog_apart _ ly S W mem md O ly3 S3 W3 (ms_mem ms) mdv [] _ sp0 HAR HOin HJ HROD).
set (t := snd (rec_answer (rec_record R SQB_FN [x]) (SQB_FN, [x]) (shape_of sqcb_verb) true)) in *.
assert (HXA : 0 <= XM_ANSWER MT t).
{ unfold XM_ANSWER, XM_HAND_BACK, XM_XMALLOC, LIVE_XMALLOC. pose proof (mo_free_nonneg MT MTL).
  pose proof (mo_malloc_nonneg MT MTL (Z.max (Z.of_nat (length t) + 1) 1) ltac:(lia)). lia. }
assert (HLA : 0 <= LIVE_ANSWER t) by (unfold LIVE_ANSWER, LIVE_HAND_BACK, LIVE_XMALLOC; lia).
assert (HMt : snd (sup_quarantine_clear_m R which) = t) by (rewrite HM; reflexivity).
rewrite (cmd_sig_prog_PB CS_answer ltac:(vm_compute; tauto)).
change (pa_val A_TEXT + cmd_af CS_answer) with (BASE + AF_answer).
eapply SRr_mono.
{ apply (TANSWER fx ly3 S3 W3 (ms_regs ms) (ms_mem ms) mdv ch c q old (SQB_FN, [x])
    (shape_of sqcb_verb) true (rec_record R SQB_FN [x]) ((p, n) :: O1) HPREA Hfrm0).
  - rewrite HfrJ. cbn [app]. exact HFR8.
  - exact HRAJ.
  - exact (cmd_ro_ok_of_aro _ _ _ _ _ HART HRAJ).
  - exact Y10.
  - clear - Hcb. unfold A_G_REC, OFF_CALLS, A_REC_SPILL in Hcb. lia.
  - exact Y11.
  - exact Hq64.
  - rewrite T12. reflexivity.
  - exact HREPT.
  - exact HOLD.
  - exact Hold64.
  - intros _. split; [exact (HSHT _)|]. unfold fits. vm_compute. congruence.
  - intros _ _. exact (sqcb_answer_slot R x).
  - rewrite Hk in HnevJ. unfold EV_SUP_QUARANTINE_CLEAR in HEV. lia.
  - fold t. unfold LIVE_SUP_QUARANTINE_CLEAR in HLIVE. rewrite HMt in HLIVE. lia.
  - fold t. apply (mok_station MT S S3 _ _ _ MTL HMOK MLE3 HXA).
    unfold XM_SUP_QUARANTINE_CLEAR. rewrite HMt. lia. }
cbv beta. intros W4 c4 _ (fx4 & ly4 & S4 & regs4 & mem4 & md4 & -> & HFP4 & HCSR4 & HJ4 & HP4 & HQ4).
cbv zeta in HQ4.
destruct HQ4 as (p1 & p2 & O' & Hp2 & Hp2a & Hp12 & Hfr12 & Hbl & HrepF & HO' & Hstr & HBB4 & Hmle).
set (nT := Z.of_nat (length t) + 1) in *.
pose proof (proj1 HJ4) as HAR4.
(* a block of the entry that the tail's copies could reuse is one of O *)
assert (HfreshO : forall z, (z = p1 \/ z = p2) -> In (z, nT) (ablocks B ly S) -> In (z, nT) O).
{ intros z Hz H0. destruct (HL0 _ H0) as [H1 | H1]; [|exact (HFO _ H1)].
  destruct (Z.eq_dec z old) as [Ho | Ho].
  - apply (HO2O _ (HOLDO2 _ (HL13 _ H1) Ho) H0).
  - exfalso. destruct (Hfr12 (z, nT) (HL13 _ H1) Ho) as [N1 N2].
    destruct Hz as [-> | ->]; [exact (N1 eq_refl) | exact (N2 eq_refl)]. }
(* a block of the entry the recorder does not own is still live and not the old answer *)
assert (HnotO : forall pn, In pn (ablocks B ly S) -> ~ In pn O -> In pn L1 /\ fst pn <> old).
{ intros pn Hpn HnO. destruct (HL0 _ Hpn) as [H1 | H1]; [|exfalso; exact (HnO (HFO _ H1))].
  split; [exact H1|]. intros Hf. pose proof (HOLDO2 _ (HL13 _ H1) Hf) as H2.
  exact (HnO (HO2O _ H2 Hpn)). }
unfold apost_baseF. exists fx4, ly4, S4, regs4, mem4, md4.
split; [rewrite A1; reflexivity|].
split; [exact HFP4|]. split; [exact HCSR4|].
split.
{ assert (HJF : ajournal SEGS B SQB_STK sp0 (sqcb_FP O) ly S W mem md ([] ++ []) ly4 S4 W4 mem4 md4 (k3 + EV_ANSWER)).
  { eapply (ajournal_sub_wide SEGS B LAWS pa_segs_low); [exact HJ | exact HJ4 | rewrite SPA, HAS, HST; lia | rewrite SPA; lia | |].
    - intros a (r & Hr & Hra'). destruct Hr as [<- | [<- | Hr]]; cbn [fst snd] in Hra'.
      + apply (sqcb_awr_prog B HB cmd_prog_img); [apply sqcb_PG_grec | unfold sqcb_FP; apply inFP_cons; left];
        unfold OFF_ANSWER, REC_SIZE in *; lia.
      + apply (sqcb_awr_prog B HB cmd_prog_img); [apply sqcb_PG_grec | unfold sqcb_FP; apply inFP_cons; left];
        unfold OFF_STATE, REC_SIZE in *; lia.
      + unfold ablocks_fp in Hr. apply in_map_iff in Hr as ([b m] & <- & Hin).
        apply sqcb_in_filter in Hin. destruct Hin as [Hin Hf]. cbn [fst snd] in *.
        destruct (in_dec RecBLemmas.recb_pair_dec (b, m) (ablocks B ly S)) as [H0 | H0].
        * right; left. split.
          -- unfold sqcb_FP. apply inFP_cons. right. apply inFP_cons. right.
             replace a with (b + (a - b)) by lia. apply (inFP_ablocks_fp O b m (a - b)); [exact (HO2O _ Hin H0) | lia].
          -- exists b, m. split; [exact (HO23 _ Hin) | lia].
        * right; right; left. exists b, m. split; [exact (HO23 _ Hin) | split; [exact H0 | lia]].
    - intros a _ Ha Hn. exfalso. apply Hn. rewrite SPA, HAS. rewrite HST in Ha. exact Ha. }
  cbn [app] in HJF. apply (ajournal_mono_k SEGS B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJF).
  unfold EV_SUP_QUARANTINE_CLEAR. rewrite Hk. lia. }
split; [exact (aregs_preserved_trans _ _ _ HPA HP4)|].
exists (fst (rec_answer (rec_record R SQB_FN [x]) (SQB_FN, [x]) (shape_of sqcb_verb) true)), t, p2, O'.
split; [rewrite HM; apply surjective_pairing|].
split; [exact Hp2|]. split; [exact Hp2a|]. split; [exact HrepF|].
split.
{ intros pn Hpn. destruct (in_dec RecBLemmas.recb_pair_dec pn (ablocks B ly S)) as [H0 | H0]; [left | right; exact H0].
  apply HO' in Hpn as [[Hpn1 _] | ->].
  - exact (HO2O _ Hpn1 H0).
  - exact (HfreshO p1 (or_introl eq_refl) H0). }
split; [apply Hbl; right; right; reflexivity|].
split.
{ intros pn Hpn HnO Heq. destruct (HnotO pn Hpn HnO) as [H1 Hf].
  exact (proj2 (Hfr12 pn (HL13 _ H1) Hf) Heq). }
split.
{ intros Hin. apply in_map_iff in Hin as (pn & Hf & Hpn).
  pose proof (sqcb_rec_repA_in B _ _ _ _ _ HrepF pn Hpn) as Hpn4.
  pose proof (proj2 (Hbl (p2, nT)) (or_intror (or_intror eq_refl))) as Hq4.
  pose proof (sqcb_same_start B ly4 S4 W4 mem4 md4 pn (p2, nT) HAR4 Hpn4 Hq4 Hf) as ->.
  apply HO' in Hpn as [[Hpn1 Hfo] | Heq];
  [exact (proj2 (Hfr12 _ (HO23 _ Hpn1) Hfo) eq_refl) | injection Heq as Heq; exact (Hp12 (eq_sym Heq))]. }
split; [exact Hstr|].
split.
{ intros pn Hpn HnO. destruct (HnotO pn Hpn HnO) as [H1 Hf].
  assert (H4 : In pn (ablocks B ly4 S4)) by (apply Hbl; left; split; [exact (HL13 _ H1) | exact Hf]).
  split; [exact H4|].
  pose proof (proj2 (Hbl (p2, nT)) (or_intror (or_intror eq_refl))) as Hq4.
  destruct pn as [b m]. cbn [fst snd].
  assert (Hne : (b, m) <> (p2, nT)) by exact (proj2 (Hfr12 (b, m) (HL13 _ H1) Hf)).
  destruct (sqcb_blk_bounds B ly4 S4 W4 mem4 md4 b m HAR4 H4) as (_ & _ & Hm0 & Hmr & _).
  destruct (sqcb_blk_bounds B ly4 S4 W4 mem4 md4 p2 nT HAR4 Hq4) as (_ & _ & Hn0 & Hnr & _).
  unfold iv_apart. destruct (sqcb_blk_apart B ly4 S4 W4 mem4 md4 b m p2 nT HAR4 H4 Hq4 Hne); lia. }
split.
{ intros pn Hpn. apply Hbl in Hpn as [[H3 Hf] | [-> | ->]].
  - apply (Permutation_in _ HPERM3) in H3. destruct H3 as [<- | H3].
    + right; left. apply HO'. left. split; [left; reflexivity | exact Hf].
    + destruct (in_dec RecBLemmas.recb_pair_dec pn ((p, n) :: O1)) as [H2 | H2n].
      * right; left. apply HO'. left. split; [exact H2 | exact Hf].
      * left. split; [exact (HL10 _ H3)|]. intros HinO. exact (H2n (HL1O _ H3 HinO)).
  - right; left. apply HO'. right. reflexivity.
  - right; right. reflexivity. }
split.
{ fold t in HBB4. unfold LIVE_SUP_QUARANTINE_CLEAR. rewrite HMt. lia. }
fold t in Hmle.
apply (mle_weaken MT S S4 _ _ MTL (mle_station MT S S3 S4 _ _ MTL MLE3 Hmle)).
unfold XM_SUP_QUARANTINE_CLEAR. rewrite HMt. lia.
Qed.

End e.
End f.
End d.

Print Assumptions sqcb_S3.
