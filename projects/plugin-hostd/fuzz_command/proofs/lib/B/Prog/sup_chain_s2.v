(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the entry segment of sup_chain's image-B walk (plugin-hostd/fuzz_command,
   fuzz_command.asan-ubsan, a Theorem Labs lane's lib/B/Prog/sup_chain_c.v `tsup_chain_spec`, statement f490061c104): from the entry
   0x8c1c4 (BASE + AF_sup_chain) to the first arrival at the loop head 0x8c3d0 (BASE + SCB_LOOP), against the
   interface lib/B/Prog/sup_chain_d.v (scb_lctx, scb_inv 0). B code (capstone over the pin's .symtab, listing
   CmdList.v:6004+):
     run 1  0x8c1c4 .. 0x8c23c  the 192-byte frame, s0 := entry sp, sp := s1 := (sp - 192) & -32, the member array
                                and the shadow base to s1 + 48 / s1 + 56, the use-after-return flag (1: the record's
                                const cell), a0 := 96, jal __asan_stack_malloc_1
     run 2  0x8c240 .. 0x8c2f4  the frame F non-null (bnez taken), its words on the stack, the header (magic,
                                descriptor 0x1dfad, pc 0x8c1c4), the 12 shadow stores, a0 := 17, jal record
     run 3  0x8c2f8 .. 0x8c30c  s4 := the slot, a0 := 12n + 1, jal xmalloc
     run 4  0x8c310 .. 0x8c334  s6 := the text, unpoison F + 64, snprintf(F + 64, 16, "%d", id)
     run 5  0x8c338 .. 0x8c340  arg_s(slot, F + 64)
     run 6  0x8c344 .. 0x8c364  unpoison F + 32, poison F + 64, snprintf(F + 32, 16, "%d", n)
     run 7  0x8c368 .. 0x8c374  the slot to s1 + 8, arg_s(slot, F + 32)
     run 8  0x8c378 .. 0x8c3cc  poison F + 32, SB + F / 8 to s1 + 24, the store1 check of list[0] (shadow 0: xmalloc's
                                fresh block), list[0] := 0, n >= 1, the loop's registers, " %d" to s1 + 40
   The two snprintf calls return at an FP state the walk continues at (fx1, then fx2): the symbolic state is moved
   to it (PaFx.st_ok_pi_restrict_xfx) and the run lemmas are taken there. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import String ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI04 YI00 YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YM05 YG05 YG0q YI16.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdSyms CmdList CmdAddr CmdPa CmdPaLib PaCall PaCallRun PaDenot PaLibF PaLibG PaLibH PaSB.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs RtFormat.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require RtPFCmd RtPFShared RtPFSx RtPFPf.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob CmdBase CmdRep CmdObj CmdRo CmdZsh CmdChk.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaNoChain PaFx RecBLemmas.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import record_c xmalloc_c arg_s_c hand_back_c rec_shape_of_c answer_c sup_chain_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdRecBase CmdRecRo CmdRecRest CmdRecCells CmdRecImg.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdSnText.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import sup_chain_aux sup_chain_d.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* ---------- Ltacs (B answer_code's preg / norm_ssp / nwin_tac, a working branch db9a922ed3f) ---------- *)
Ltac preg HS r Hr :=
lazymatch type of HS with
| st_ok_pi ?segs ?val ?E ?ss (restrict ?H ?ms) =>
pose proof (st_ok_pi_restrict_reg H E ss ms r HS) as Hr;
let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
cbn [ms_regs restrict mkst] in Hr
| st_ok ?segs ?E ?ss (restrict ?H ?ms) =>
pose proof (st_ok_restrict_reg segs H E ss ms r HS) as Hr;
let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
cbn [ms_regs restrict mkst] in Hr
end.
Ltac norm_ssp HS :=
lazymatch type of HS with
| st_ok_pi _ _ _ ?ss3 _ => let v := eval vm_compute in ss3 in change ss3 with v in HS
| st_ok _ _ ?ss3 _ => let v := eval vm_compute in ss3 in change ss3 with v in HS
end.

(* the write windows of the walk's regions, one region at a time: the frame's shadow (1041) and header (1028) are
   this call's frame (own), the stack regions (2: entry sp, 34: s1) lie in its window, a region without a write
   window is read-only; `extra` handles any other region *)
Ltac scs_awr_step fpos sp0 sp1 FS Vs Vf V2 V34 EFA extra :=
lazymatch goal with
| |- awr_ok _ _ _ [] _ _ _ _ _ _ _ _ => apply (awr_ok_nil _ _)
| |- awr_ok _ _ _ (?r :: _) _ _ _ _ _ _ _ _ =>
  let wro := eval vm_compute in (YP09.r_whi r <=? YP09.r_wlo r) in
  let nbase := eval vm_compute in (YP09.r_base r) in
  lazymatch wro with
  | true => apply (awr_ok_cons_ro _ _); [cbn; lia|]
  | false =>
    lazymatch nbase with
    | Some 1041%nat =>
      eapply (YCbq.awr_ok_cons_gen _ _) with (k := 1041%nat); [reflexivity | exact Vs |
      intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha; right; right; right; left; exists 1, fpos; split; [left; reflexivity|];
      right; unfold in_zr, shadow_addr; cbn [fst snd]; rewrite EFA, <- SB_SHADOW_OFF; change (fs_frame_bytes 1 / 8) with 16; lia |]
    | Some 1028%nat =>
      eapply (YCbq.awr_ok_cons_gen _ _) with (k := 1028%nat); [reflexivity | exact Vf |
      intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha; right; right; right; left; exists 1, fpos; split; [left; reflexivity|];
      left; unfold in_zr; cbn [fst snd]; rewrite EFA; change (fs_frame_bytes 1) with 128; lia |]
    | Some 34%nat =>
      eapply (awr_ok_cons_stack_off _ _) with (n := 34%nat) (d := sp1 - sp0);
      [reflexivity | rewrite V34; lia | cbn; rewrite FS; lia | cbn; lia |]
    | Some 2%nat =>
      eapply (awr_ok_cons_stack_off _ _) with (n := 2%nat) (d := 0);
      [reflexivity | rewrite V2; lia | cbn; rewrite FS; lia | cbn; lia |]
    | _ => extra
    end
  end
end.
Ltac scs_awr fpos sp0 sp1 FS Vs Vf V2 V34 EFA extra :=
lazymatch goal with |- awr_ok ?sg ?Bb ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr ?lyx ?own =>
  let rs' := eval vm_compute in rs in change (awr_ok sg Bb Ex rs' stk spx fp b0 bc fr lyx own) end;
repeat (scs_awr_step fpos sp0 sp1 FS Vs Vf V2 V34 EFA extra).
(* PaLibH's jafter_call_keep_hi with the FP state named (PASS4-REFIT.md A.6: with a second FP state in the context
   the after-call lemma's implicit FP argument must be given) *)
Ltac scs_keep_hi fxv HS k regs2 mem2 HP idxs HS2 :=
lazymatch type of HS with
| st_ok_pi ?segs ?val ?E ?ss ?ms =>
let HEI := lazymatch goal with HEI : img_env _ _ E |- _ => HEI | _ => fail "scs_keep_hi: no img_env hypothesis for" E end in
let rs := eval vm_compute in (pick (ss_mem ss) idxs) in
let retk := eval vm_compute in (match sr_get (ss_regs ss) 1 with SOff _ z => z | _ => 0 end) in
pose proof (st_ok_pi_after_call_hi (fx := fxv) k E (abs_ss val ss) ms regs2 mem2 rs retk HEI ltac:(lia) HS eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
ltac:(vm_compute; reflexivity) ltac:(submem_tac) ltac:(vm_compute; reflexivity) HP) as HS2;
let ss2 := eval vm_compute in (ss_after_call ss rs k retk) in
change (ss_after_call (abs_ss val ss) rs k retk) with ss2 in HS2
| st_ok ?segs ?E ?ss ?ms =>
let HEI := lazymatch goal with HEI : img_env _ _ E |- _ => HEI | _ => fail "scs_keep_hi: no img_env hypothesis for" E end in
let rs := eval vm_compute in (pick (ss_mem ss) idxs) in
let retk := eval vm_compute in (match sr_get (ss_regs ss) 1 with SOff _ z => z | _ => 0 end) in
pose proof (st_ok_pi_after_call_hi (fx := fxv) k E ss ms regs2 mem2 rs retk HEI ltac:(lia) HS eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
ltac:(vm_compute; reflexivity) ltac:(submem_tac) ltac:(vm_compute; reflexivity) HP) as HS2;
let ss2 := eval vm_compute in (ss_after_call ss rs k retk) in
change (ss_after_call ss rs k retk) with ss2 in HS2
end.

(* ---------- the representation's readers (B sup_reset's srb_*, a working branch c79a9f2daf7) ---------- *)
Lemma scs_aval_keep : forall rd rd' a n v, aval_mem rd a n v ->
  (forall x, a <= x < a + Z.of_nat n -> rd' x = rd x) -> aval_mem rd' a n v.
Proof. intros rd rd' a n v H K k Hk. rewrite K by lia. exact (H k Hk). Qed.
Lemma scs_bytes_keep : forall rd rd' a l, abytes_atR rd a l ->
  (forall x, a <= x < a + Z.of_nat (length l) -> rd' x = rd x) -> abytes_atR rd' a l.
Proof. intros rd rd' a l H K i Hi. rewrite K by lia. exact (H i Hi). Qed.
Lemma scs_str_keep : forall rd rd' p s, astr_atR rd p s ->
  (forall x, p <= x < p + Z.of_nat (length s) + 1 -> rd' x = rd x) -> astr_atR rd' p s.
Proof.
  intros rd rd' p s [H1 H2] K. split; [|exact H2].
  apply (scs_bytes_keep rd); [exact H1|]. intros x Hx. apply K. rewrite length_app in Hx. cbn [length] in Hx. lia.
Qed.
Lemma scs_call_keep : forall bl bl' rd rd' a c P, acall_at bl rd a c P ->
  (forall x, a <= x < a + CALL_SIZE -> rd' x = rd x) ->
  (forall pn, In pn P -> In pn bl' /\ forall x, fst pn <= x < fst pn + snd pn -> rd' x = rd x) ->
  acall_at bl' rd' a c P.
Proof.
  intros bl bl' rd rd' a c P (H1 & H2 & H3 & H4 & H5 & H6 & H7) KA KP.
  unfold acall_at, CALL_SIZE, CALL_OFF_FN, CALL_OFF_NARGS, CALL_OFF_ARGS in *.
  refine (conj H1 (conj H2 (conj H3 (conj _ (conj _ (conj H6 _)))))).
  - apply (scs_aval_keep rd); [exact H4|]. intros x Hx. apply KA. lia.
  - apply (scs_aval_keep rd); [exact H5|]. intros x Hx. apply KA. lia.
  - intros k s pn Es Ep. destruct (H7 k s pn Es Ep) as (G1 & G2 & G3 & G4 & G5).
    assert (Hk : (k < length (snd c))%nat) by (apply nth_error_Some; rewrite Es; discriminate).
    destruct (KP pn ltac:(eapply nth_error_In; exact Ep)) as [Kin Kx].
    refine (conj _ (conj G2 (conj Kin (conj G4 _)))).
    + apply (scs_aval_keep rd); [exact G1|]. intros x Hx. apply KA. lia.
    + apply (scs_str_keep rd); [exact G5|]. intros x Hx. apply Kx. lia.
Qed.
Lemma scs_answer_keep : forall bl bl' rd rd' gr t q, aanswer_at bl rd gr t q ->
  (forall x, gr + OFF_ANSWER <= x < gr + OFF_ANSWER + 8 -> rd' x = rd x) ->
  (forall pn, In pn (oblk q) -> In pn bl' /\ forall x, fst pn <= x < fst pn + snd pn -> rd' x = rd x) ->
  aanswer_at bl' rd' gr t q.
Proof.
  intros bl bl' rd rd' gr t q H KA KP.
  destruct t as [x|]; destruct q as [pn|]; cbn [aanswer_at] in H |- *; try contradiction.
  - destruct H as (N1 & N2 & N3 & N4 & N5 & N6).
    destruct (KP pn ltac:(cbn; left; reflexivity)) as [Kin Kx].
    refine (conj _ (conj N2 (conj Kin (conj N4 (conj _ N6))))).
    + apply (scs_aval_keep rd); [exact N1|]. intros y Hy. apply KA. lia.
    + apply (scs_str_keep rd); [exact N5|]. intros y Hy. apply Kx. lia.
  - apply (scs_aval_keep rd); [exact H|]. intros y Hy. apply KA. lia.
Qed.
Lemma scs_reply_keep : forall bl bl' rd rd' gr y q, areply_at bl rd gr y q ->
  (forall x, gr + OFF_REPLY <= x < gr + OFF_REPLY + 16 -> rd' x = rd x) ->
  (forall pn, In pn (oblk q) -> In pn bl' /\ forall x, fst pn <= x < fst pn + snd pn -> rd' x = rd x) ->
  areply_at bl' rd' gr y q.
Proof.
  intros bl bl' rd rd' gr y q H KA KP.
  destruct y as [x|]; destruct q as [pn|]; cbn [areply_at] in H |- *; try contradiction;
    unfold OFF_REPLY, OFF_REPLY_SIZE in *.
  - destruct H as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8).
    destruct (KP pn ltac:(cbn; left; reflexivity)) as [Kin Kx].
    refine (conj _ (conj _ (conj P3 (conj P4 (conj Kin (conj P6 (conj _ P8))))))).
    + apply (scs_aval_keep rd); [exact P1|]. intros z Hz. apply KA. lia.
    + apply (scs_aval_keep rd); [exact P2|]. intros z Hz. apply KA. lia.
    + apply (scs_bytes_keep rd); [exact P7|]. intros z Hz. apply Kx. lia.
  - destruct H as [P1 P2]. split.
    + apply (scs_aval_keep rd); [exact P1|]. intros z Hz. apply KA. lia.
    + apply (scs_aval_keep rd); [exact P2|]. intros z Hz. apply KA. lia.
Qed.
Lemma scs_scalars_keep : forall rd rd' gr R, ag1_scalars rd gr R ->
  (forall x, gr <= x < gr + 8 \/ gr + 920 <= x < gr + 924 \/ gr + 944 <= x < gr + 960 -> rd' x = rd x) ->
  ag1_scalars rd' gr R.
Proof.
  intros rd rd' gr R (X1 & X2 & X3 & X4 & X5 & X6) K.
  unfold ag1_scalars, OFF_REFUSE, OFF_CODE, OFF_NREPLIES, OFF_STATE, OFF_HOST in *.
  refine (conj _ (conj _ (conj _ (conj _ (conj _ X6))))).
  all: apply (scs_aval_keep rd); [eassumption|]; intros z Hz; apply K; lia.
Qed.
Lemma scs_in_calls : forall Q i P pn, nth_error (l_calls Q) i = Some P -> In pn P -> In pn (lay_blocks Q).
Proof.
  intros Q i P pn E H. unfold lay_blocks. apply in_or_app. left. apply in_concat. exists P.
  split; [eapply nth_error_In; exact E | exact H].
Qed.
Lemma scs_in_spill : forall Q pn, In pn (l_spill Q) -> In pn (lay_blocks Q).
Proof. intros Q pn H. unfold lay_blocks. apply in_or_app. right. apply in_or_app. left. exact H. Qed.
Lemma scs_in_answer : forall Q pn, In pn (oblk (l_answer Q)) -> In pn (lay_blocks Q).
Proof.
  intros Q pn H. unfold lay_blocks. apply in_or_app. right. apply in_or_app. right. apply in_or_app. left. exact H.
Qed.
Lemma scs_in_reply : forall Q pn, In pn (oblk (l_reply Q)) -> In pn (lay_blocks Q).
Proof.
  intros Q pn H. unfold lay_blocks. apply in_or_app. right. apply in_or_app. right. apply in_or_app. right. exact H.
Qed.
Lemma scs_arep_at_ext : forall bl bl' rd rd' gr sc R Q,
  arep_at bl rd gr sc R Q ->
  (forall pn, In pn (lay_blocks Q) -> In pn bl') ->
  (forall a, (gr <= a < gr + REC_SIZE) \/ (sc <= a < sc + SC_SIZE) \/
             (exists pn, In pn (lay_blocks Q) /\ fst pn <= a < fst pn + snd pn) -> rd' a = rd a) ->
  arep_at bl' rd' gr sc R Q.
Proof.
  intros bl bl' rd rd' gr sc R Q (G1 & G2 & G3 & (C1 & C2 & C3 & C4 & C5 & C6) & HA & HP & HX & HW) KL K.
  assert (KQ : forall pn, In pn (lay_blocks Q) -> In pn bl' /\
             forall x, fst pn <= x < fst pn + snd pn -> rd' x = rd x).
  { intros pn Hpn. split; [exact (KL pn Hpn)|]. intros x Hx. apply K. right. right. exists pn.
    split; [exact Hpn | exact Hx]. }
  assert (KR : forall x, gr <= x < gr + REC_SIZE -> rd' x = rd x) by (intros x Hx; apply K; left; exact Hx).
  assert (KS : forall x, sc <= x < sc + SC_SIZE -> rd' x = rd x) by (intros x Hx; apply K; right; left; exact Hx).
  unfold REC_SIZE, SC_SIZE in KR, KS.
  refine (conj G1 (conj G2 (conj G3 (conj _ (conj _ (conj _ (conj _ HW))))))).
  - refine (conj C1 (conj C2 (conj _ (conj _ (conj _ C6))))).
    + apply (scs_aval_keep rd); [exact C3|]. intros x Hx. apply KR. unfold OFF_NCALLS in Hx. lia.
    + intros i c P Ec EP. destruct (C4 i c P Ec EP) as [Hc HL]. split; [|exact HL].
      assert (Hi : (i < length (r_calls R))%nat) by (apply nth_error_Some; rewrite Ec; discriminate).
      apply (scs_call_keep bl _ rd); [exact Hc | |].
      * intros x Hx. apply KR. unfold OFF_CALLS, CALL_SIZE in *. lia.
      * intros pn Hpn. apply KQ. exact (scs_in_calls Q i P pn EP Hpn).
    + apply (scs_call_keep bl _ rd); [exact C5 | |].
      * intros x Hx. apply KS. unfold CALL_SIZE in Hx. lia.
      * intros pn Hpn. apply KQ. apply scs_in_spill. exact Hpn.
  - apply (scs_answer_keep bl _ rd); [exact HA | |].
    + intros x Hx. apply KR. unfold OFF_ANSWER in Hx. lia.
    + intros pn Hpn. apply KQ. apply scs_in_answer. exact Hpn.
  - apply (scs_reply_keep bl _ rd); [exact HP | |].
    + intros x Hx. apply KR. unfold OFF_REPLY in Hx. lia.
    + intros pn Hpn. apply KQ. apply scs_in_reply. exact Hpn.
  - apply (scs_scalars_keep rd); [exact HX|]. intros x Hx. apply KR. lia.
Qed.
Lemma scs_call_in : forall bl rd a c P pn, acall_at bl rd a c P -> In pn P -> In pn bl.
Proof.
  intros bl rd a c P pn (_ & _ & Hl & _ & _ & _ & Hk) Hin.
  destruct (In_nth_error P pn Hin) as [k Ek].
  assert (Hk' : (k < length (snd c))%nat) by (rewrite <- Hl; apply nth_error_Some; rewrite Ek; discriminate).
  destruct (nth_error (snd c) k) as [s|] eqn:Es; [|apply nth_error_None in Es; lia].
  destruct (Hk k s pn Es Ek) as (_ & _ & G3 & _). exact G3.
Qed.
Lemma scs_lay_in : forall bl rd gr sc R Q pn, arep_at bl rd gr sc R Q -> In pn (lay_blocks Q) -> In pn bl.
Proof.
  intros bl rd gr sc R Q pn (_ & _ & _ & (C1 & C2 & C3 & C4 & C5 & C6) & HA & HP & _ & _) Hin.
  unfold lay_blocks in Hin. apply in_app_or in Hin as [Hin|Hin].
  - apply in_concat in Hin as (P & HP' & Hpn).
    destruct (In_nth_error _ _ HP') as [i Ei].
    assert (Hi : (i < length (r_calls R))%nat) by (rewrite <- C2; apply nth_error_Some; rewrite Ei; discriminate).
    destruct (nth_error (r_calls R) i) as [c|] eqn:Ec; [|apply nth_error_None in Ec; lia].
    destruct (C4 i c P Ec Ei) as [Hc _]. exact (scs_call_in _ _ _ _ _ _ Hc Hpn).
  - apply in_app_or in Hin as [Hin|Hin]; [exact (scs_call_in _ _ _ _ _ _ C5 Hin)|].
    apply in_app_or in Hin as [Hin|Hin].
    + revert HA Hin. destruct (r_answer R) as [x|]; destruct (l_answer Q) as [qn|];
        cbn [aanswer_at oblk In]; intros HA Hin; try contradiction.
      destruct Hin as [<-|[]]. destruct HA as (_ & _ & N3 & _). exact N3.
    + revert HP Hin. destruct (r_reply R) as [x|]; destruct (l_reply Q) as [qn|];
        cbn [areply_at oblk In]; intros HP Hin; try contradiction.
      destruct Hin as [<-|[]]. destruct HP as (_ & _ & _ & _ & P5 & _). exact P5.
Qed.
(* the slot record() returns (record_c.v rec_slot): an entry of g_rec's table, or record.spill *)
Lemma scs_slot_bounds : forall R, (length (r_calls R) <= 16)%nat ->
  (A_G_REC + OFF_CALLS <= rec_slot R /\ rec_slot R + CALL_SIZE <= A_G_REC + REC_SIZE) \/ rec_slot R = A_REC_SPILL.
Proof.
  intros R H. unfold rec_slot. destruct (Nat.ltb_spec (length (r_calls R)) 16) as [L|L]; [left | right; reflexivity].
  unfold A_G_REC, OFF_CALLS, CALL_SIZE, REC_SIZE. lia.
Qed.
Lemma scs_inFP_cases : forall O a, inFP (SCB_FP O) a ->
Exists (in_zr a) TFIB_PROG_STATIC \/ exists b n, In (b, n) O /\ b <= a < b + req_size n.
Proof.
intros O a (r & Hr & Ha). unfold SCB_FP in Hr. destruct Hr as [<- | [<- | Hr]]; cbn [fst snd] in Ha.
- left. apply recb_grec_in. exact Ha.
- left. apply recb_spill_in. exact Ha.
- right. unfold ablocks_fp in Hr. apply in_map_iff in Hr as ([b n] & <- & Hin). cbn [fst snd] in Ha.
  exists b, n. split; [exact Hin | exact Ha].
Qed.
(* a one-byte val_mem of 0 from the view (PaDenot's val_mem_zero8, at one byte) *)
Lemma scs_val_mem_zero1 : forall segs H (m : word -> option byte) a,
aview segs H m a = Some 0 -> val_mem segs (mrestrict H m) a 1 0.
Proof.
intros segs H m a Hz j Hj. assert (j = 0%nat) by lia. subst j. rewrite Z.add_0_r.
destruct (aview_byte segs H m a 0 Hz) as (b & Hb & Hv & _).
rewrite Hb. f_equal. apply bv_eq. rewrite Z_to_bv_unsigned. unfold YO0f.le_byte, bv_wrap.
repeat (rewrite Z.shiftr_0_l || rewrite Z.mod_0_l by ((first [lazymatch goal with |- _ <> @nil _ => discriminate end | vm_compute; discriminate]))). lia.
Qed.
(* the loop's registers as the symbolic run leaves them (0x8c3a8 .. 0x8c3c0) *)
Lemma scs_den_not : forall E k v, ew E k = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
sv_denot E (SAlu ALU_XOR (SOff k 0) (SLit (-1))) = Z_to_bv 64 (2 ^ 64 - 1 - v).
Proof.
intros E k v Hk Hv.
rewrite <- (Z_to_bv_bv_unsigned 64 (sv_denot E (SAlu ALU_XOR (SOff k 0) (SLit (-1))))). f_equal.
change (U E (SAlu ALU_XOR (SOff k 0) (SLit (-1))) = 2 ^ 64 - 1 - v).
rewrite U_SAlu, U_SOff, U_SLit, Hk. rewrite unsigned_lit_small by lia. cbn [zalu_raw].
replace (zcanon (v + 0)) with v by (rewrite zcanon_small; lia).
replace (zcanon (-1)) with (2 ^ 64 - 1) by reflexivity.
rewrite (scb_xor_m1 v Hv). rewrite zcanon_small; lia.
Qed.
Lemma scs_den_s4 : forall E k v, ew E k = Z_to_bv 64 v -> 0 < v < 2 ^ 64 ->
sv_denot E (SAlu ALU_SLTU (SLit 0) (SOff k 0)) = Z_to_bv 64 1.
Proof.
intros E k v Hk Hv.
rewrite <- (Z_to_bv_bv_unsigned 64 (sv_denot E (SAlu ALU_SLTU (SLit 0) (SOff k 0)))). f_equal.
change (U E (SAlu ALU_SLTU (SLit 0) (SOff k 0)) = 1).
rewrite U_SAlu, U_SOff, U_SLit, Hk. rewrite unsigned_lit_small by lia. cbn [zalu_raw].
replace (zcanon (v + 0)) with v by (rewrite zcanon_small; lia).
replace (zcanon 0) with 0 by reflexivity.
replace (0 <? v) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
Qed.
Lemma scs_den_s9 : forall E k v, ew E k = Z_to_bv 64 v -> 0 < v < 2 ^ 64 -> v mod 4 = 0 ->
sv_denot E (SAlu ALU_AND (SAlu ALU_SLTU (SAlu ALU_AND (SOff k 0) (SLit 3)) (SLit 1)) (SAlu ALU_SLTU (SLit 0) (SOff k 0))) =
Z_to_bv 64 1.
Proof.
intros E k v Hk Hv H4.
rewrite <- (Z_to_bv_bv_unsigned 64 (sv_denot E
  (SAlu ALU_AND (SAlu ALU_SLTU (SAlu ALU_AND (SOff k 0) (SLit 3)) (SLit 1)) (SAlu ALU_SLTU (SLit 0) (SOff k 0))))). f_equal.
change (U E (SAlu ALU_AND (SAlu ALU_SLTU (SAlu ALU_AND (SOff k 0) (SLit 3)) (SLit 1)) (SAlu ALU_SLTU (SLit 0) (SOff k 0))) = 1).
rewrite !U_SAlu, !U_SOff, !U_SLit, Hk. rewrite unsigned_lit_small by lia. cbn [zalu_raw].
replace (zcanon (v + 0)) with v by (rewrite zcanon_small; lia).
replace (zcanon 3) with (Z.ones 2) by reflexivity. rewrite Z.land_ones by lia. change (2 ^ 2) with 4. rewrite H4.
replace (zcanon 0) with 0 by reflexivity.
replace (0 <? v) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
Qed.
(* the frame's 16 shadow bytes, read off its symbolic region *)
Lemma scs_byte_lit : forall v, (bv_unsigned (Z_to_bv 64 v) mod 256) = v mod 256.
Proof.
intros v. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
rewrite (Z.mod_eq v (2 ^ 64)) by lia.
replace (v - 2 ^ 64 * (v / 2 ^ 64)) with (v + (- (2 ^ 56) * (v / 2 ^ 64)) * 256) by lia.
rewrite Z.mod_add by lia. reflexivity.
Qed.

(* the class-1 frame's shadow with the zero bytes __asan_stack_malloc_1 leaves (bytes 12 .. 15 stay zero) *)
Definition scs_zchunk (i : Z) : YP09.chunk := YP09.mkChunk i (CVal 1 (SLit 0)).
Definition scs_fr_shd : YP09.region :=
YP09.mkRegion (Some 1041%nat) 0 16 0 16 (map scs_zchunk [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15]).
Lemma scs_zchunks_ok : forall segs E H (m : word -> option byte) b,
(forall i, 0 <= i < 16 -> aview segs H m (b + i) = Some 0) ->
Forall (YP09.chunk_ok segs E (mrestrict H m) b) (map scs_zchunk [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15]).
Proof.
intros segs E H m b Hz. apply Forall_forall. intros c Hc. apply in_map_iff in Hc as (i & <- & Hi).
assert (Hi' : 0 <= i < 16) by (cbn [In] in Hi; lia).
apply (chunk_ok_val segs E _ b i 1 (SLit 0) 0); [reflexivity | lia | lia |].
apply scs_val_mem_zero1. exact (Hz i Hi').
Qed.
(* the stack words the walk stores after the frame is seated: s1 + 8 .. s1 + 48 and s1 + 80 *)
Definition scs_rw1 : YP09.region := YP09.mkRegion (Some 34%nat) 8 48 8 48 [].
Definition scs_rw2 : YP09.region := YP09.mkRegion (Some 34%nat) 80 88 80 88 [].
(* the text block's first byte (xmalloc's block, atom 1062), which the store list[0] := 0 writes *)
Definition scs_txt : YP09.region := YP09.mkRegion (Some 1062%nat) 0 1 0 1 [].
(* the shadow byte of list[0] (atom 1138 = SB + lst / 8), read-only, 0 *)
Definition scs_lsh : YP09.region := YP09.mkRegion (Some 1138%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SLit 0))].

(* a buffer of at most 16 bytes at an 8-aligned d whose two shadow bytes are 0 is addressable *)
Lemma scs_rng_of_zs : forall (rd : Z -> option Z) d n, 0 <= d -> d mod 8 = 0 -> 0 <= n <= 16 ->
(forall i, 0 <= i < 2 -> rd (SB + d / 8 + i) = Some 0) -> range_addressable rd SHADOW_OFF d n.
Proof.
intros rd d n Hd Hd8 Hn Hz x Hx. exists 0. split; [|left; reflexivity]. unfold shadow_of_addr. rewrite <- SB_SHADOW_OFF.
pose proof (Z.div_mod x 8 ltac:(lia)). pose proof (Z.mod_pos_bound x 8 ltac:(lia)). pose proof (Z.div_mod d 8 ltac:(lia)).
replace (SB + x / 8) with (SB + d / 8 + (x / 8 - d / 8)) by lia. apply Hz. lia.
Qed.
(* 0x8c2fc .. 0x8c308 as the symbolic run simplifies it: a0 := n * 12 + 1 *)
Lemma scs_den_xm : forall E k n, ew E k = Z_to_bv 64 n -> 0 <= n <= 62 ->
sv_denot E (SAlu ALU_ADD (SMd M_MUL (SOff k 0) (SLit 12)) (SLit 1)) = Z_to_bv 64 (12 * n + 1).
Proof.
intros E k n Hk Hn.
rewrite <- (Z_to_bv_bv_unsigned 64 (sv_denot E (SAlu ALU_ADD (SMd M_MUL (SOff k 0) (SLit 12)) (SLit 1)))). f_equal.
change (U E (SAlu ALU_ADD (SMd M_MUL (SOff k 0) (SLit 12)) (SLit 1)) = 12 * n + 1).
rewrite U_SAlu, U_SMd, U_SOff, !U_SLit, Hk. rewrite unsigned_lit_small by lia. cbn [zalu_raw zmd_raw].
replace (zcanon (n + 0)) with n by (rewrite zcanon_small; lia).
replace (zcanon 12) with 12 by reflexivity. replace (zcanon 1) with 1 by reflexivity.
replace (zcanon (n * 12)) with (n * 12) by (rewrite zcanon_small; lia).
rewrite zcanon_small by lia. lia.
Qed.
(* ---------- the inlined arg_i's snprintf(d, 16, "%d", v) into a buffer of this call's class-1 frame ---------- *)
(* the read-only ranges the snprintf chain reads lie in the image *)
Lemma scs_cr_img : forall r, In r RtPFCmd.CMD_SNP_CR -> 0x10000 <= fst r /\ 0 <= snd r /\ fst r + snd r <= 0x606000.
Proof.
intros r Hr. pose proof RtPFCmd.cmd_snp_cr_img as H. rewrite forallb_forall in H. specialize (H r Hr).
unfold RtPFCmd.in_cmd_img, RtPFCmd.CMD_IMG_LO, RtPFCmd.CMD_IMG_HI in H.
apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1, H2, H3. lia.
Qed.
Lemma scs_img_apart : forall lo n K sp d w, 0x10000 <= lo -> lo + n <= 0x606000 -> 0x606000 <= sp - K ->
(d + w <= 0x10000 \/ 0x606000 <= d) -> Forall (zdisjoint (lo, n)) (RtPFShared.snp_out K sp d w).
Proof. intros lo n K sp d w H1 H2 H3 H4. apply RtPFSx.Forall_snp. unfold zdisjoint. cbn [fst snd]. split; lia. Qed.
(* the printed number as the recorder's bytes *)
Lemma scs_dec_bytes : forall v, -2 ^ 31 <= v < 2 ^ 31 -> PF.pf_bytes (PF.pf_dec v ++ [0]) = dec v ++ [Z_to_bv 8 0].
Proof.
intros v Hv. unfold PF.pf_bytes. rewrite map_app. fold (PF.pf_bytes (PF.pf_dec v)). rewrite (snt_pf_dec v Hv). reflexivity.
Qed.
Lemma scs_dec_len : forall v, -2 ^ 31 <= v < 2 ^ 31 -> length (PF.pf_dec v) = length (dec v).
Proof.
intros v Hv. rewrite <- (snt_pf_dec v Hv). unfold PF.pf_bytes. rewrite length_map. reflexivity.
Qed.
Lemma scs_sn_eqs : forall v, -2 ^ 31 <= v < 2 ^ 31 ->
RtPFShared.sn_len (16 - 1) (PF.pf_dec v) = Z.of_nat (length (PF.pf_dec v)) + 1 /\
RtPFShared.sn_bytes (16 - 1) (PF.pf_dec v) = PF.pf_dec v ++ [0].
Proof.
intros v Hv. pose proof (scb_pf_dec_len v Hv) as HL. unfold RtPFShared.sn_len, RtPFShared.sn_bytes.
change (Z.to_nat (16 - 1)) with 15%nat. rewrite firstn_all2 by lia. rewrite length_app. cbn [length]. split; [lia | reflexivity].
Qed.
Section sn. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation SIG c := (@pa_sigma _ cmd_listing PI c).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Lemma scs_snp : forall B (LAWS : AR_laws SEGS B) (HB : CmdBSyms B) (IMG : @cmd_img_facts SK SEGS B)
  (ASN : asnprintf_realizes SEGS B (SIG CS___interceptor_trampoline_snprintf) 0xa6bf8 0x604158)
  ly S W regs mem md (d v pos : Z),
  ecall_pre SEGS B ly S W regs mem md ->
  ly_stk_lo ly + RtPFCmd.CMD_SNP_K <= spZ regs ->
  (forall a, spZ regs - RtPFCmd.CMD_SNP_K <= a < spZ regs -> apresent (w_H W) mem a) ->
  alloc_ceiling + RtPFCmd.CMD_SNP_K <= spZ regs -> spZ regs <= 2 ^ 47 ->
  getr regs 10 = w64 d -> getr regs 11 = w64 16 -> getr regs 12 = w64 0x21f40 -> getr regs 13 = w64 v ->
  -2 ^ 31 <= v < 2 ^ 31 ->
  arodata_okP SEGS CMD_RLO CMD_RHI B (rdW W mem) -> cmd_ro_ok (rdW W mem) ->
  In (1, pos) (frames S) -> frame_addr ly 1 pos <= d -> d + 24 <= frame_addr ly 1 pos + 128 -> d mod 8 = 0 ->
  (forall i, 0 <= i < 2 -> rdW W mem (SB + d / 8 + i) = Some 0) ->
  frm0 fx ->
  SRr SEGS W (cfg_at SEGS (SIG CS___interceptor_trampoline_snprintf) regs mem md)
   (art_postF SEGS B RtPFCmd.CMD_SNP_K ly S W regs mem md
     (fun a => d <= a < d + RtPFShared.sn_len (16 - 1) (PF.pf_dec v))
     (fun regs' mem' => getr regs' 10 = w64 (Z.of_nat (length (PF.pf_dec v))) /\
       forall i, 0 <= i < RtPFShared.sn_len (16 - 1) (PF.pf_dec v) ->
       rdW W mem' (d + i) = Some (nth (Z.to_nat i) (RtPFShared.sn_bytes (16 - 1) (PF.pf_dec v)) 0))).
Proof.
intros B LAWS HB IMG ASN ly S W regs mem md d v pos HPRE Hlo Hscr Hceil H47 R10 R11 R12 R13 Hv HRO HROk Hfin Hd1 Hd2 Hd8 Hsh Hfrm.
pose proof HPRE as (HAR & _ & Hal & Hslo & Hshi & _ & _ & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HK : RtPFCmd.CMD_SNP_K = 8192) by reflexivity.
pose proof (scb_pf_dec_len v Hv) as HTl.
destruct (scs_sn_eqs v Hv) as [Ew _].
destruct (al_frames _ _ LAWS _ _ _ _ _ 1 pos HAR Hfin) as (HFal & HFapp & HFpres & HFSpres).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 1 pos HAR Hfin) as (HF4096 & HFceil & _).
pose proof (frm_off_imgP _ _ _ _ _ _ _ _ HAR Hfin) as HFoff. unfold off_img in HFoff.
change (fs_frame_bytes 1) with 128 in *.
destruct (cmd_rec_cells (SK := SK) SEGS B LAWS HB IMG ly S W mem md HAR) as (_ & (Hgot & cval & Hcan) & _).
pose proof (scb_lit_21f40_at _ HROk) as HL.
apply (srr_art_postF_of_pf SEGS B RtPFCmd.CMD_SNP_K ly S W regs mem md _ d (RtPFShared.sn_len (16 - 1) (PF.pf_dec v))
  (RtPFShared.sn_bytes (16 - 1) (PF.pf_dec v)) (Z.of_nat (length (PF.pf_dec v))) Hscr).
apply (ASN ly S W regs mem md d 16 0x21f40 [] (map (argZ regs) [3; 4; 5; 6; 7] ++ []) (PF.pf_dec v) cval);
  rewrite ?Ew.
- exact HPRE.
- exact Hlo.
- exact Hscr.
- exact R10.
- exact R11.
- exact R12.
- exact (cmd_consts_view_snp (SK := SK) SEGS B LAWS HB IMG CMD_RLO CMD_RHI W mem HRO).
- apply Forall_forall. intros r Hr. destruct (scs_cr_img r Hr) as (Q1 & Q2 & Q3). lia.
- apply Forall_forall. intros r Hr. destruct (scs_cr_img r Hr) as (Q1 & Q2 & Q3).
  destruct r as [lo n]. cbn [fst snd] in *. apply scs_img_apart; lia.
- exact Hgot.
- exact Hcan.
- lia.
- lia.
- lia.
- lia.
- apply scs_img_apart; lia.
- apply scs_img_apart; lia.
- split; [reflexivity | intros i Hi; cbn [length] in Hi; lia].
- cbn [length Z.of_nat]. lia.
- apply RtPFSx.Forall_snp. unfold zdisjoint. cbn [fst snd length Z.of_nat]. split; lia.
- apply (RtPFCmd.FR_cmd_intro _ _ _ _ _ scb_fmt0 [PF.Pd] [PF.AInt v]).
  + split; [lia|]. split.
    { intros i Hi. change (Z.of_nat (length scb_fmt0)) with 2 in Hi. assert (Hk : (Z.to_nat i < 3)%nat) by lia.
      pose proof (HL (Z.to_nat i) ltac:(change (length RO_lit_21f40) with 3%nat; exact Hk)) as Hb.
      rewrite Z2Nat.id in Hb by lia. rewrite Hb. f_equal.
      destruct (Z.to_nat i) as [|[|[|k]]]; [vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | lia]. }
    split; [apply scs_img_apart; cbn [length Z.of_nat scb_fmt0]; lia|].
    split; [left; unfold kLowMemEnd; cbn [length Z.of_nat scb_fmt0]; lia|].
    split; [exact (scb_rng_21f40 B HB ly S W mem md HAR) | exact (scb_hull_21f40 B HB ly S W mem md HAR)].
  + exact scb_fmt0_parse.
  + cbn [map RtPFCmd.arg_of RtPFShared.pf_args_asan RtPFShared.pf_arg_asan app]. split; [|exact I]. split; [exact Hv|].
    unfold argZ. replace (Z_to_bv 5 (10 + 3)) with (13%bv : bv 5) by (apply bv_eq; reflexivity). rewrite R13.
    unfold w64. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
    rewrite (Z.mod_eq v (2 ^ 64)) by lia.
    replace (v - 2 ^ 64 * (v / 2 ^ 64)) with (v + (- (2 ^ 32) * (v / 2 ^ 64)) * 2 ^ 32) by lia.
    rewrite Z.mod_add by lia. reflexivity.
  + exact (snt_text_d v).
  + cbn. exact I.
  + vm_compute; reflexivity.
- lia.
- exact (scb_snprintf_len v Hv).
- lia.
- lia.
- apply RtPFSx.pairwise_snp. unfold zdisjoint. cbn [fst snd]. lia.
- intros a Ha. destruct (HFpres a ltac:(lia)) as [Hp Hno].
  split; [apply (apresent_writable SEGS); exact Hp|]. split; [exact Hno|].
  assert (Hes : ESTACK = 4096) by reflexivity. rewrite Hes. lia.
- apply (amem_range_sub_app (frame_addr ly 1 pos) 128); [exact HFapp | exact HFceil | lia | lia | lia].
- intros x Hx. exists 0. split; [|left; reflexivity]. unfold shadow_of_addr. rewrite <- SB_SHADOW_OFF.
  pose proof (Z.div_mod x 8 ltac:(lia)). pose proof (Z.mod_pos_bound x 8 ltac:(lia)).
  pose proof (Z.div_mod d 8 ltac:(lia)).
  replace (SB + x / 8) with (SB + d / 8 + (x / 8 - d / 8)) by lia. apply Hsh. lia.
- apply (shadow_hull_vis_of_frame SEGS B LAWS ly S W mem md 1 pos d _ HAR Hfin); [lia | change (fs_frame_bytes 1) with 128; lia | lia].
- unfold zdisjoint, RtPFCmd.CMD_IMG_LO, RtPFCmd.CMD_IMG_HI. cbn [fst snd]. lia.
- exact Hfrm.
Qed.
End sn.

(* a side-stack frame's size is a multiple of 64 *)
Lemma scs_fsb8 : forall c, 0 <= c -> fs_frame_bytes c = 8 * (8 * 2 ^ c).
Proof. intros c Hc. unfold fs_frame_bytes. rewrite Z.shiftl_mul_pow2 by lia. lia. Qed.
(* the member array's bytes (sup_chain_s3.v's scl_concat_len) *)
Lemma scs_ids_len : forall l : list Z, length (concat (map le32 l)) = (4 * length l)%nat.
Proof.
induction l as [|x l IH]; [reflexivity|].
cbn [map concat]. rewrite length_app, IH.
assert (L4 : length (le32 x) = 4%nat) by (unfold le32, le4; apply length_Z_to_le_bytes).
rewrite L4. cbn [length]. lia.
Qed.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation SIG c := (@pa_sigma _ cmd_listing PI c).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.

Lemma scs_region_kept_hi : forall E H (m m2 : word -> option byte) n b lo hi wlo whi cs,
bv_unsigned (ew E n) = b ->
(forall a, b + lo <= a < b + hi -> aview SEGS H m2 a = aview SEGS H m a) ->
(forall a, b + wlo <= a < b + whi -> apresent H m2 a) ->
region_kept SEGS E (mrestrict H m) (mrestrict H m2) (YP09.mkRegion (Some n) lo hi wlo whi cs).
Proof.
intros E H m m2 n b lo hi wlo whi cs Hn Hav Hp.
split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Hn; intros a Ha.
- apply (mbyte_of_aview SEGS). apply Hav. exact Ha.
- intros _. apply (apresent_writable SEGS). apply Hp. exact Ha.
Qed.

(* a one-byte chunk of a symbolic region is the view's byte (its value's low byte) *)
Lemma scs_byte_of_region : forall E (W' : world SEGS) m n b lo hi wlo whi cs od e,
region_ok SEGS E (mrestrict (w_H W') m) (YP09.mkRegion (Some n) lo hi wlo whi cs) -> bv_unsigned (ew E n) = b ->
In (YP09.mkChunk od (CVal 1 e)) cs -> rdW W' m (b + od) = Some (bv_unsigned (sv_denot E e) mod 256).
Proof.
intros E W' m n b lo hi wlo whi cs od e HR Hb Hin.
pose proof (field_of_region_any E _ n b cs lo hi wlo whi od 1 e HR Hb Hin ltac:(lia)) as V.
change (2 ^ (8 * Z.of_N 1)) with 256 in V. change (N.to_nat 1) with 1%nat in V.
apply (aview_of_val_mem1 SEGS (w_H W') m _ _ V). apply Z.mod_pos_bound. lia.
Qed.
(* two zero bytes of the frame's shadow region *)
Lemma scs_zs2 : forall E (W' : world SEGS) m b cs i0 i1,
region_ok SEGS E (mrestrict (w_H W') m) (YP09.mkRegion (Some 1041%nat) 0 16 0 16 cs) -> bv_unsigned (ew E 1041) = b ->
In (YP09.mkChunk i0 (CVal 1 (SLit 0))) cs -> In (YP09.mkChunk i1 (CVal 1 (SLit 0))) cs -> i1 = i0 + 1 ->
forall i, 0 <= i < 2 -> rdW W' m (b + i0 + i) = Some 0.
Proof.
intros E W' m b cs i0 i1 HR Hb H0 H1 Hi1 i Hi. assert (Hi2 : i = 0 \/ i = 1) by lia.
destruct Hi2 as [-> | ->].
- rewrite Z.add_0_r. rewrite (scs_byte_of_region E W' m 1041 b _ _ _ _ _ i0 (SLit 0) HR Hb H0).
  cbn [sv_denot]. rewrite unsigned_lit_small by lia. reflexivity.
- replace (b + i0 + 1) with (b + i1) by lia. rewrite (scs_byte_of_region E W' m 1041 b _ _ _ _ _ i1 (SLit 0) HR Hb H1).
  cbn [sv_denot]. rewrite unsigned_lit_small by lia. reflexivity.
Qed.
(* an 8-byte chunk of a symbolic region with a known value is a word of the view *)
Lemma scs_word_of_region : forall E (W' : world SEGS) m n b lo hi wlo whi cs od e v,
region_ok SEGS E (mrestrict (w_H W') m) (YP09.mkRegion (Some n) lo hi wlo whi cs) -> bv_unsigned (ew E n) = b ->
In (YP09.mkChunk od (CVal 8 e)) cs -> sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
val_mem SEGS (mrestrict (w_H W') m) (b + od) 8 v.
Proof.
intros E W' m n b lo hi wlo whi cs od e v HR Hb Hin He Hv.
exact (field_of_region E _ n b cs lo hi wlo whi od 8 e v HR Hb Hin He Hv ltac:(lia)).
Qed.
(* the 13 saved registers at entry sp - 8 - 8j, read off the entry sp's symbolic region *)
Lemma scs_frame_at : forall Ex (W' : world SEGS) m sp0 (rg : bvmap 5 word) cs lo hi wlo whi,
region_ok SEGS Ex (mrestrict (w_H W') m) (YP09.mkRegion (Some 2%nat) lo hi wlo whi cs) -> bv_unsigned (ew Ex 2) = sp0 ->
(forall j r, nth_error scb_saved j = Some r -> In (YP09.mkChunk (-8 - 8 * Z.of_nat j) (CVal 8 (SOff (Z.to_nat r) 0))) cs) ->
(forall r, In r scb_saved -> ew Ex (Z.to_nat r) = getr rg (Z_to_bv 5 r)) ->
scb_frame_at (mrestrict (w_H W') m) sp0 rg.
Proof.
intros Ex W' m sp0 rg cs lo hi wlo whi HR Hb Hcs Hreg j r Hj.
pose proof (nth_error_In _ _ Hj) as Hin.
replace (sp0 - 8 - 8 * Z.of_nat j) with (sp0 + (-8 - 8 * Z.of_nat j)) by lia.
apply (scs_word_of_region Ex W' m 2 sp0 lo hi wlo whi cs _ (SOff (Z.to_nat r) 0) _ HR Hb (Hcs j r Hj)).
- rewrite scb_denot_off0, (Hreg r Hin). symmetry. apply Z_to_bv_bv_unsigned.
- apply bv_unsigned_in_range.
Qed.
(* the frame's 16 shadow bytes (scb_shadow0), read off its symbolic region *)
Lemma scs_fshadow_of : forall E (W' : world SEGS) m b lo hi wlo whi cs,
region_ok SEGS E (mrestrict (w_H W') m) (YP09.mkRegion (Some 1041%nat) lo hi wlo whi cs) -> bv_unsigned (ew E 1041) = b ->
(forall i, 0 <= i < 16 -> exists v, In (YP09.mkChunk i (CVal 1 (SLit v))) cs /\ v mod 256 = nth (Z.to_nat i) scb_shadow0 0) ->
forall i, 0 <= i < 16 -> rdW W' m (b + i) = Some (nth (Z.to_nat i) scb_shadow0 0).
Proof.
intros E W' m b lo hi wlo whi cs HR Hb Hc i Hi. destruct (Hc i Hi) as (v & Hin & Hv).
rewrite (scs_byte_of_region E W' m 1041 b lo hi wlo whi cs i (SLit v) HR Hb Hin). cbn [sv_denot].
rewrite scs_byte_lit, Hv. reflexivity.
Qed.
(* the bytes of a printed text, read off the view, as a byte list *)
Lemma scs_abytes_of_view : forall (W' : world SEGS) m d (l : list Z),
(forall i, 0 <= i < Z.of_nat (length l) -> rdW W' m (d + i) = Some (nth (Z.to_nat i) l 0)) ->
abytes_atR (rdW W' m) d (PF.pf_bytes l).
Proof.
intros W' m d l H k Hk. unfold PF.pf_bytes in Hk |- *. rewrite length_map in Hk.
pose proof (H (Z.of_nat k) ltac:(lia)) as Hv. rewrite Nat2Z.id in Hv. rewrite Hv. f_equal.
destruct (aview_byte SEGS (w_H W') m (d + Z.of_nat k) _ Hv) as (b & _ & _ & Hr).
rewrite (map_nth (Z_to_bv 8) l 0 k). rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
rewrite Z.mod_small by lia. reflexivity.
Qed.
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
(* the statement's Section hypotheses (sup_chain_c.v:109-119) this segment uses *)
Hypothesis TRECORD : forall fx0 : YK11.FPState, @trecord_spec fx0 rc SK PI B MT.
Hypothesis TXMALLOC : forall fx0 : YK11.FPState, @txmalloc_spec fx0 rc SK PI B MT.
Hypothesis TARG_S : forall fx0 : YK11.FPState, @targ_s_spec fx0 rc SK PI B MT.
Hypothesis ASTACK_MALLOC1 : forall fx0 : YK11.FPState, @astack_malloc_realizes fx0 rc SEGS B 1.
Hypothesis ASNPRINTF : forall fx0 : YK11.FPState, @asnprintf_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_snprintf) 0xa6bf8 0x604158.
Hypothesis VOBJS : cmd_val_objs.
(* the walk's (a Theorem Labs lane convention 09:2xZ, the brief sch-walk-brief.md) *)
Hypothesis HB : CmdBSyms B.
Hypothesis MTL : ameter_laws MT.
Hypothesis MTLF : ameter_fs_laws MT.
Hypothesis cmd_palibf : forall B0, CmdBSyms B0 -> PALibF B0.
Hypothesis cmd_sig_prog_PB : cmd_sig_prog.
Hypothesis cmd_palib : forall B0, CmdBSyms B0 -> PALib B0.
Hypothesis cmd_img_facts_tfib : forall B0, CmdBSyms B0 -> @cmd_img_facts SK SEGS B0.
Let TL : PALib B := cmd_palib B HB.
Let TLF : PALibF B := cmd_palibf B HB.
Let LAWS : AR_laws SEGS B := AR_laws_ok SEGS B.
Let IMG : @cmd_img_facts SK SEGS B := cmd_img_facts_tfib B HB.
Let RUNP := SRr_run_pi_AJ (L := cmd_listing) (PL := PL_cmd) (PI := PI) B LAWS.
Let RUNC := SRr_run_pi_AJ_call (L := cmd_listing) (PL := PL_cmd) (PI := PI) B LAWS.
Let ML : model_laws (as_universe B) := model_laws_ok (as_universe B) (YF0m.ts_universe B HB).

(* the statement's premises (sup_chain_c.v:121-157) *)
Variables (ly : alayout) (S : astate) (W : world SEGS) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
  (ch : list (Z * Z * Z)) (id pids : Z) (ids : list Z) (R : rstate) (O : list (Z * Z)).
Hypothesis HPRE : afn_pre SEGS B SUP_CHAIN_STK ly S W regs mem md ch.
Hypothesis HRM0 : scb_frm0 fx.
Hypothesis HRO : arodata_okP SEGS RLO RHI B (rdW W mem).
Hypothesis HROk : cmd_ro_ok (rdW W mem).
Hypothesis H10 : getr regs 10 = w64 id.
Hypothesis HID : -2 ^ 31 <= id < 2 ^ 31.
Hypothesis H11 : getr regs 11 = w64 pids.
Hypothesis HPR : 0 <= pids < 2 ^ 64.
Hypothesis H12 : getr regs 12 = w64 (Z.of_nat (length ids)).
Hypothesis HIDS : (1 <= length ids <= 62)%nat.
Hypothesis HIDR : Forall (fun v => -2 ^ 31 <= v < 2 ^ 31) ids.
Hypothesis HPNZ : pids <> 0.
Hypothesis HP4 : pids mod 4 = 0.
Hypothesis HARR : afobj SEGS B ly S W mem pids (4 * Z.of_nat (length ids)) \/
 (in_blockA (ablocks B ly S) pids (4 * Z.of_nat (length ids)) /\
  Forall (fun qk => iv_apart pids (4 * Z.of_nat (length ids)) (fst qk) (snd qk)) O).
Hypothesis HBYTES : abytes_atR (rdW W mem) pids (concat (map le32 ids)).
Hypothesis HREP : rec_repA B ly S (rdW W mem) R O.
Hypothesis HFR7 : Z.of_nat (length (frames S)) <= 7.
Hypothesis HNEV : st_nev S + EV_SUP_CHAIN R <= EV_MAX.
Hypothesis HLIVE : blocks_bytes S + LIVE_SUP_CHAIN R id ids <= LIVE_MAX.
Hypothesis HMOK : mo_ok MT S (XM_SUP_CHAIN MT R id ids).

(* ---------- the record facts by exact (a Theorem Labs lane's CmdRecRo / CmdRecRest over IMG) ---------- *)
Let scs_prog_img : forall a, Exists (in_zr a) TFIB_PROG_STATIC -> in_img SEGS a :=
  CmdRecRest.cmd_prog_img (SK := SK) SEGS B LAWS HB IMG.
Let scs_ro_ok_of_aro : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md ->
  arodata_okP SEGS RLO RHI B (rdW W mem) -> cmd_ro_ok (rdW W mem) :=
  CmdRecRo.cmd_ro_ok_of_aro (SK := SK) SEGS B LAWS HB IMG.

(* ---------- the allocator's blocks and the recorder's bytes ---------- *)
Lemma scs_O_in : forall ly1 S1 rd R1 O1, rec_repA B ly1 S1 rd R1 O1 -> forall pn, In pn O1 -> In pn (ablocks B ly1 S1).
Proof. intros ly1 S1 rd R1 O1 (Q & HQ & HOQ) pn Hpn. exact (scs_lay_in _ _ _ _ _ _ pn HQ (proj1 (HOQ pn) Hpn)). Qed.
Lemma scs_blk_bounds : forall ly1 S1 (W1 : world SEGS) mem1 md1 b m, AR SEGS B ly1 S1 W1 mem1 md1 ->
In (b, m) (ablocks B ly1 S1) -> 4096 <= b /\ b + req_size m <= alloc_ceiling /\ 0 <= m /\ m <= req_size m /\ 1 <= req_size m.
Proof.
intros ly1 S1 W1 mem1 md1 b m HAR1 Hin.
destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR1 Hin) as (_ & H4096 & Hceil & _ & _ & _ & Hm).
pose proof (req_size_pos m ltac:(lia)) as [Hq1 Hq2]. lia.
Qed.
(* RecBLemmas' kit lemmas over the allocator's blocks and the program statics, bound once *)
Let scs_blk_noimg := recb_heap_noimg_m B.
Let scs_prog_unowned := recb_prog_unowned_m B HB scs_prog_img.
(* the bytes rec_repA reads: g_rec, record.spill and the recorder's blocks *)
Definition scs_RX (O1 : list (Z * Z)) (a : Z) : Prop :=
(A_G_REC <= a < A_G_REC + REC_SIZE) \/ (A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE) \/
(exists pn, In pn O1 /\ fst pn <= a < fst pn + snd pn).
Lemma scs_rec_repA_ext : forall ly1 S1 rd ly' S' rd' R1 O1,
  rec_repA B ly1 S1 rd R1 O1 ->
  (forall pn, In pn O1 -> In pn (ablocks B ly' S')) ->
  (forall a, scs_RX O1 a -> rd' a = rd a) ->
  rec_repA B ly' S' rd' R1 O1.
Proof.
  intros ly1 S1 rd ly' S' rd' R1 O1 (Q & HR & HO) KB K. exists Q. split; [|exact HO].
  apply (scs_arep_at_ext (ablocks B ly1 S1) _ rd _ _ _ _ _ HR).
  - intros pn Hpn. apply KB. apply HO. exact Hpn.
  - intros a [Ha|[Ha|(pn & Hpn & Ha)]]; apply K;
      [left; exact Ha | right; left; exact Ha | right; right; exists pn; split; [apply HO; exact Hpn | exact Ha]].
Qed.
(* where a recorder byte lies: below alloc_ceiling, apart from the class-1 frame and its shadow; an unowned image byte or
   a byte of one of the recorder's live blocks *)
Lemma scs_RX_loc : forall ly1 S1 (W1 : world SEGS) mem1 md1 O1 pos a, AR SEGS B ly1 S1 W1 mem1 md1 ->
(forall pn, In pn O1 -> In pn (ablocks B ly1 S1)) -> In (1, pos) (frames S1) -> scs_RX O1 a ->
0 <= a < alloc_ceiling /\ ~ (frame_addr ly1 1 pos <= a < frame_addr ly1 1 pos + 128) /\
~ (SB + frame_addr ly1 1 pos / 8 <= a < SB + frame_addr ly1 1 pos / 8 + 16) /\
((in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4)) \/
 (exists p m, In (p, m) O1 /\ p <= a < p + req_size m)).
Proof.
intros ly1 S1 W1 mem1 md1 O1 pos a HAR1 HO Hfin Ha. pose proof asan_consts as (C1 & _).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 1 pos HAR1 Hfin) as (HF4096 & HFceil & _).
pose proof (frm_off_imgP _ _ _ _ _ _ _ _ HAR1 Hfin) as HFoff. unfold off_img in HFoff.
change (fs_frame_bytes 1) with 128 in *.
destruct Ha as [Ha | [Ha | ([p m] & Hpm & Ha)]].
- assert (HP : Exists (in_zr a) TFIB_PROG_STATIC) by exact (recb_grec_in a Ha).
  unfold A_G_REC, REC_SIZE in Ha. unfold SB.
  split; [lia|]. split; [lia|]. split; [lia|]. left. exact (scs_prog_unowned a HP).
- assert (HP : Exists (in_zr a) TFIB_PROG_STATIC) by exact (recb_spill_in a Ha).
  unfold A_REC_SPILL, SC_SIZE in Ha. unfold SB.
  split; [lia|]. split; [lia|]. split; [lia|]. left. exact (scs_prog_unowned a HP).
- cbn [fst snd] in Ha. pose proof (HO _ Hpm) as Hin.
  destruct (scs_blk_bounds _ _ _ _ _ p m HAR1 Hin) as (Hp & Hpc & Hm0 & Hmr & _).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ p m HAR1 Hin) as (_ & _ & _ & Hpapp & _).
  pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ p m 1 pos HAR1 Hin Hfin) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. change (fs_frame_bytes 1) with 128 in Hd.
  split; [lia|]. split; [lia|]. split.
  + intros Hs. apply (fshadow_not_app (frame_addr ly1 1 pos) 16 p (req_size m) a); [lia | lia | exact Hpapp | unfold SB in Hs; lia | lia].
  + right. exists p, m. split; [exact Hpm | lia].
Qed.
(* the footprint lies below alloc_ceiling *)
Lemma scs_FP_low : forall a, inFP (SCB_FP O) a -> 0 <= a < alloc_ceiling.
Proof.
intros a Ha. pose proof asan_consts as (C1 & _). pose proof HPRE as (HAR & _).
destruct (scs_inFP_cases O a Ha) as [HP | (b & n & Hin & Hb)].
- pose proof (pa_img_range a (scs_prog_img a HP)). lia.
- destruct (scs_blk_bounds ly S W mem md b n HAR (scs_O_in _ _ _ _ _ HREP _ Hin)) as (H4 & Hc & _). lia.
Qed.
(* arodata_okP along the walk's journal (cmd_rodata_kept: the footprint is statics and the recorder's blocks) *)
Lemma scs_aro : forall lyc Sc (Wc : world SEGS) memc mdc own k,
ajournal SEGS B SUP_CHAIN_STK (spZ regs) (SCB_FP O) ly S W mem md own lyc Sc Wc memc mdc k ->
arodata_okP SEGS RLO RHI B (rdW Wc memc).
Proof.
intros lyc Sc Wc memc mdc own k HJ. pose proof HPRE as (HAR & _).
apply (CmdRecRest.cmd_rodata_kept (SK := SK) SEGS B LAWS HB IMG ly S W mem md lyc Sc Wc memc mdc SUP_CHAIN_STK (spZ regs) (SCB_FP O) own k HAR HJ); [|exact HRO].
intros a Ha. destruct (scs_inFP_cases O a Ha) as [HP | (b & n & Hin & Hb)]; [left; exact HP|].
right. exists b, n. split; [apply in_or_app; left; exact (scs_O_in _ _ _ _ _ HREP _ Hin) | exact Hb].
Qed.
(* the frame chain at a program callee: s0 is the entry sp (class B), above afn_pre's chain, with the ra and entry s0
   words the prologue stored at sp0 - 8 and sp0 - 16 (PASS4-REFIT.md section B) *)
Lemma scs_chain : forall lyc Sc (Wc : world SEGS) memc mdc own k sp',
  ajournal SEGS B SUP_CHAIN_STK (spZ regs) (SCB_FP O) ly S W mem md own lyc Sc Wc memc mdc k ->
  rdword (rdW Wc memc) (spZ regs - 8) = Some (raZ regs) ->
  rdword (rdW Wc memc) (spZ regs - 16) = Some (s0Z regs) ->
  sp' + 16 <= spZ regs ->
  exists ch', achain lyc (rdW Wc memc) sp' (spZ regs) ch'.
Proof.
intros lyc Sc Wc memc mdc own k sp' HJ Hra8 Hs16 Hsp.
pose proof HPRE as (HAR & _ & Hra4 & _ & _ & Hstk & _ & Hch & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & _ & H47 & _ & Htop & Htop2).
pose proof HJ as (_ & Hly & _).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _).
pose proof asan_consts as (C1 & _).
assert (HNFP : forall a, spZ regs <= a < 2 ^ 64 -> ~ inFP (SCB_FP O) a).
{ intros a Ha Hf. pose proof (scs_FP_low a Hf). lia. }
assert (H8 : spZ regs mod 8 = 0).
{ pose proof (Z.div_mod (spZ regs) 16 ltac:(lia)) as D. rewrite Hal16 in D. rewrite D.
  replace (16 * (spZ regs / 16) + 0) with ((2 * (spZ regs / 16)) * 8) by lia. apply Z_mod_mult. }
destruct (Z_lt_le_dec (spZ regs) (ly_top ly - 16)) as [Hlt | Hge].
- exists ((spZ regs, raZ regs, s0Z regs) :: ch). apply (achain_ly_top ly lyc); [exact Etop|].
  eapply (achain_push ly (rdW W mem) (rdW Wc memc) (spZ regs) (s0Z regs) (raZ regs) ch);
  [exact Hch | lia | | exact Hra8 | exact Hs16 | exact Hra4 | lia | exact H8 | exact Hlt | lia].
  intros a Ha. exact (aview_above_of_journal B _ _ _ ly S W mem md _ _ _ _ _ _ _ HJ a Ha (HNFP a Ha)).
- exists []. left. split; [right; left; rewrite Etop; lia | reflexivity].
Qed.
(* a byte of a live block: below alloc_ceiling, off the image, apart from the class-1 frame and its shadow *)
Lemma scs_blk_loc : forall ly1 S1 (W1 : world SEGS) mem1 md1 pos p m a, AR SEGS B ly1 S1 W1 mem1 md1 ->
In (p, m) (ablocks B ly1 S1) -> In (1, pos) (frames S1) -> p <= a < p + req_size m ->
4096 <= a < alloc_ceiling /\ ~ in_img SEGS a /\ ~ (frame_addr ly1 1 pos <= a < frame_addr ly1 1 pos + 128) /\
~ (SB + frame_addr ly1 1 pos / 8 <= a < SB + frame_addr ly1 1 pos / 8 + 16).
Proof.
intros ly1 S1 W1 mem1 md1 pos p m a HAR1 Hin Hfin Ha. pose proof asan_consts as (C1 & _).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 1 pos HAR1 Hfin) as (HF4096 & HFceil & _).
change (fs_frame_bytes 1) with 128 in *.
destruct (scs_blk_bounds _ _ _ _ _ p m HAR1 Hin) as (Hp & Hpc & Hm0 & Hmr & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ p m HAR1 Hin) as (_ & _ & _ & Hpapp & _).
pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ p m 1 pos HAR1 Hin Hfin) as Hd.
unfold zdisjoint in Hd. cbn [fst snd] in Hd. change (fs_frame_bytes 1) with 128 in Hd.
split; [lia|]. split; [exact (scs_blk_noimg _ _ _ _ _ p m a HAR1 Hin Ha)|]. split; [lia|].
intros Hs. apply (fshadow_not_app (frame_addr ly1 1 pos) 16 p (req_size m) a); [lia | lia | exact Hpapp | unfold SB in Hs; lia | lia].
Qed.
(* the class-1 frame at a later state of the walk: still this call's, at the same address *)
Lemma scs_frame_later : forall pos ly' S' (W' : world SEGS) mem' md' k',
ajournal SEGS B SUP_CHAIN_STK (spZ regs) (SCB_FP O) ly S W mem md [(1, pos)] ly' S' W' mem' md' k' ->
In (1, pos) (frames S') /\ frame_addr ly' 1 pos = frame_addr ly 1 pos /\ flag_addr ly' 1 pos = flag_addr ly 1 pos.
Proof.
intros pos ly' S' W' mem' md' k' HJ. pose proof HJ as (_ & Hly & _ & _ & _ & Hfrs & _).
pose proof Hly as (_ & _ & _ & _ & _ & EF & _).
split; [rewrite Hfrs; left; reflexivity|]. unfold frame_addr, flag_addr. rewrite EF. split; reflexivity.
Qed.
(* the member array across the segment (HARR, HBYTES): its bytes and its shadow at the loop head, below
   alloc_ceiling and apart from the text block: a block of the entry that record() did not free (it is none of the
   recorder's blocks), or an object of a caller's side-stack frame *)
Lemma scs_arr_final : forall pos lyL SL (WL : world SEGS) memL mdL k lst Frec bl1,
  ajournal SEGS B SUP_CHAIN_STK (spZ regs) (SCB_FP O) ly S W mem md [(1, pos)] lyL SL WL memL mdL k ->
  Permutation (ablocks B ly S) (bl1 ++ Frec) -> (forall pn, In pn Frec -> In pn O) ->
  (forall pn, In pn bl1 -> In pn (ablocks B lyL SL)) ->
  Forall (fun qk => iv_apart lst (12 * Z.of_nat (length ids) + 1) (fst qk) (snd qk)) bl1 ->
  In (lst, 12 * Z.of_nat (length ids) + 1) (ablocks B lyL SL) ->
  abytes_atR (rdW WL memL) pids (concat (map le32 ids)) /\
  range_addressable (rdW WL memL) SHADOW_OFF pids (4 * Z.of_nat (length ids)) /\
  iv_apart pids (4 * Z.of_nat (length ids)) lst (12 * Z.of_nat (length ids) + 1) /\
  pids + 4 * Z.of_nat (length ids) <= alloc_ceiling.
Proof.
intros pos lyL SL WL memL mdL k lst Frec bl1 HJ HPm HFr HbL Hap HlL.
pose proof HPRE as (HAR & _).
pose proof HJ as (HARL & Hly & _ & _ & _ & Hfrs & _ & _ & _ & F2 & _ & F4 & _).
pose proof Hly as (_ & _ & _ & _ & _ & EF & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HL : Z.of_nat (length (concat (map le32 ids))) = 4 * Z.of_nat (length ids)) by (rewrite scs_ids_len; lia).
pose proof (req_size_pos (12 * Z.of_nat (length ids) + 1) ltac:(lia)) as RQl.
destruct HARR as [((cid & fp0 & Hin & Hc0 & Hal & Hlo & Hhi) & H8 & HRA) | ((p & m & Hin & Hp1 & Hp2) & HAO)].
- (* an object of a side-stack frame of the entry *)
  destruct (frames_bounds SEGS B LAWS _ _ _ _ _ cid fp0 HAR Hin) as (HF4096 & HFceil & _).
  pose proof (frm_off_imgP _ _ _ _ _ _ _ _ HAR Hin) as HFoff. unfold off_img in HFoff.
  pose proof (scs_fsb8 cid Hc0) as Efs.
  set (G := frame_addr ly cid fp0) in *.
  assert (Efs8 : fs_frame_bytes cid / 8 = 8 * 2 ^ cid)
    by (rewrite Efs; replace (8 * (8 * 2 ^ cid)) with ((8 * 2 ^ cid) * 8) by ring; apply Z.div_mul; lia).
  assert (HP2 : 0 < 2 ^ cid) by (apply Z.pow_pos_nonneg; lia).
  assert (HnFP : forall a, G <= a < G + fs_frame_bytes cid -> ~ inFP (SCB_FP O) a).
  { intros a Ha Hf. destruct (scs_inFP_cases O a Hf) as [HP | (b & m & HbO & Hb)].
    - pose proof (pa_img_range a (scs_prog_img a HP)). lia.
    - pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ b m cid fp0 HAR (scs_O_in _ _ _ _ _ HREP _ HbO) Hin) as Hd.
      unfold zdisjoint in Hd. cbn [fst snd] in Hd. fold G in Hd. lia. }
  assert (HnFPs : forall a, SHADOW_OFF + G / 8 <= a < SHADOW_OFF + G / 8 + fs_frame_bytes cid / 8 -> ~ inFP (SCB_FP O) a).
  { intros a Ha Hf. rewrite <- SB_SHADOW_OFF in Ha. destruct (scs_inFP_cases O a Hf) as [HP | (b & m & HbO & Hb)].
    - pose proof (pa_img_range a (scs_prog_img a HP)). unfold SB in Ha. pose proof (Z.div_pos G 8 ltac:(lia) ltac:(lia)). lia.
    - destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR (scs_O_in _ _ _ _ _ HREP _ HbO)) as (_ & _ & _ & Hbapp & _).
      apply (fshadow_not_app G (fs_frame_bytes cid / 8) b (req_size m) a); [lia | rewrite Efs8; lia | exact Hbapp | unfold SB in Ha; lia | lia]. }
  assert (HinL : In (cid, fp0) (frames SL)) by (rewrite Hfrs; right; exact Hin).
  assert (EFc : frame_addr lyL cid fp0 = G) by (unfold G, frame_addr; rewrite EF; reflexivity).
  pose proof (Z.div_mod G 8 ltac:(lia)) as DG.
  split; [|split; [|split]].
  + intros i Hi. rewrite <- (HBYTES i Hi).
    apply (F4 cid fp0 (pids + Z.of_nat i) Hin); [left; unfold in_zr, frame_rng; cbn [fst snd]; fold G; lia | apply HnFP; lia].
  + apply (range_addressable_agree (rdW W mem)); [|exact HRA]. intros x Hx.
    pose proof (Z.div_mod x 8 ltac:(lia)). pose proof (Z.mod_pos_bound x 8 ltac:(lia)).
    assert (Hs1 : G / 8 <= x / 8) by (apply Z.div_le_mono; lia).
    assert (Hs2 : x / 8 < G / 8 + 8 * 2 ^ cid) by (apply Z.div_lt_upper_bound; lia).
    apply (F4 cid fp0 _ Hin).
    * right. unfold in_zr, shadow_of_addr, shadow_addr. cbn [fst snd]. fold G. rewrite Efs8. lia.
    * apply HnFPs. unfold shadow_of_addr. rewrite Efs8. lia.
  + pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ lst _ cid fp0 HARL HlL HinL) as Hd.
    unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite EFc in Hd. unfold iv_apart. lia.
  + lia.
- (* a block of the entry, none of the recorder's *)
  assert (HnO : ~ In (p, m) O).
  { intros HO. pose proof (proj1 (Forall_forall _ _) HAO _ HO) as Hd. cbn [fst snd] in Hd. unfold iv_apart in Hd. lia. }
  assert (Hin1 : In (p, m) bl1).
  { pose proof (Permutation_in _ HPm Hin) as H'. apply in_app_or in H' as [H1 | H2]; [exact H1 | exfalso; exact (HnO (HFr _ H2))]. }
  pose proof (HbL _ Hin1) as HinL.
  destruct (scs_blk_bounds ly S W mem md p m HAR Hin) as (Hp4 & Hpc & Hm0 & Hmr & Hr1).
  assert (HnFP : forall a, p <= a < p + req_size m -> ~ inFP (SCB_FP O) a).
  { intros a Ha Hf. destruct (scs_inFP_cases O a Hf) as [HP | (b & m' & HbO & Hb)].
    - exact (scs_blk_noimg ly S W mem md p m a HAR Hin Ha (scs_prog_img a HP)).
    - assert (Hne : (b, m') <> (p, m)) by (intros E'; rewrite E' in HbO; exact (HnO HbO)).
      pose proof (sep_blocks SEGS B LAWS ly S W mem md b m' p m HAR (scs_O_in _ _ _ _ _ HREP _ HbO) Hin Hne) as Hd.
      unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia. }
  split; [|split; [|split]].
  + intros i Hi. rewrite <- (HBYTES i Hi).
    replace (pids + Z.of_nat i) with (p + (pids + Z.of_nat i - p)) by lia.
    apply (F2 p m _ Hin HinL); [lia | apply HnFP; lia].
  + destruct (al_shadow _ _ LAWS lyL SL WL memL mdL p m HARL HinL) as [HBS _].
    apply (block_shadow_range _ _ p (req_size m)); [exact HBS | lia | lia].
  + pose proof (proj1 (Forall_forall _ _) Hap _ Hin1) as Hd. cbn [fst snd] in Hd. unfold iv_apart in *. lia.
  + lia.
Qed.
(* the bytes record() and arg_s may write: g_rec / record.spill and the recorder's blocks *)
Lemma scs_awr_static : forall STK sp bl0 blc fr0 lyx own a, Exists (in_zr a) TFIB_PROG_STATIC -> inFP (SCB_FP O) a ->
awr_byte SEGS B STK sp (SCB_FP O) bl0 blc fr0 lyx own a.
Proof.
intros STK sp bl0 blc fr0 lyx own a HP HF.
right; right; right; right; left. split; [exact HF|]. split; [rewrite (ts_prog B HB); exact HP | exact (scs_prog_img a HP)].
Qed.
Lemma scs_awr_grec : forall STK sp bl0 blc fr0 lyx own a, A_G_REC <= a < A_G_REC + REC_SIZE ->
awr_byte SEGS B STK sp (SCB_FP O) bl0 blc fr0 lyx own a.
Proof.
intros STK sp bl0 blc fr0 lyx own a Ha. apply scs_awr_static; [exact (recb_grec_in a Ha)|].
exists (A_G_REC, A_G_REC + REC_SIZE). split; [left; reflexivity | cbn [fst snd]; exact Ha].
Qed.
Lemma scs_awr_spill : forall STK sp bl0 blc fr0 lyx own a, A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE ->
awr_byte SEGS B STK sp (SCB_FP O) bl0 blc fr0 lyx own a.
Proof.
intros STK sp bl0 blc fr0 lyx own a Ha. apply scs_awr_static; [exact (recb_spill_in a Ha)|].
exists (A_REC_SPILL, A_REC_SPILL + SC_SIZE). split; [right; left; reflexivity | cbn [fst snd]; exact Ha].
Qed.
Lemma scs_awr_slot : forall STK sp bl0 blc fr0 lyx own R1 a, (length (r_calls R1) <= 16)%nat ->
rec_slot R1 <= a < rec_slot R1 + CALL_SIZE -> awr_byte SEGS B STK sp (SCB_FP O) bl0 blc fr0 lyx own a.
Proof.
intros STK sp bl0 blc fr0 lyx own R1 a HL Ha. destruct (scs_slot_bounds R1 HL) as [Hs | Hs].
- apply scs_awr_grec. unfold A_G_REC, OFF_CALLS, CALL_SIZE, REC_SIZE in *. lia.
- apply scs_awr_spill. rewrite Hs in Ha. unfold SC_SIZE, CALL_SIZE in *. lia.
Qed.
Lemma scs_awr_blk : forall STK sp bl0 blc fr0 lyx own b n a, In (b, n) O -> In (b, n) blc ->
b <= a < b + req_size n -> awr_byte SEGS B STK sp (SCB_FP O) bl0 blc fr0 lyx own a.
Proof.
intros STK sp bl0 blc fr0 lyx own b n a HO Hc Ha. right; left. split.
- unfold SCB_FP. apply inFP_cons. right. apply inFP_cons. right.
  replace a with (b + (a - b)) by lia. apply (inFP_ablocks_fp O b n (a - b)); [exact HO | lia].
- exists b, n. split; [exact Hc | exact Ha].
Qed.
(* arg_s's footprint (arg_s_c.v:118-121) with at most one argument recorded: the slot's bytes *)
Lemma scs_argfp_slot : forall R1 (A : list (list byte)) a, (length A <= 1)%nat ->
inFP (if Z.of_nat (length A) <? REC_ARGS_MAX
      then [(rec_slot R1 + CALL_OFF_NARGS, rec_slot R1 + CALL_OFF_NARGS + 4);
            (rec_slot R1 + CALL_OFF_ARGS + 8 * Z.of_nat (length A), rec_slot R1 + CALL_OFF_ARGS + 8 * Z.of_nat (length A) + 8)]
      else []) a ->
rec_slot R1 <= a < rec_slot R1 + CALL_SIZE.
Proof.
intros R1 A a HA Ha. destruct (Z.of_nat (length A) <? REC_ARGS_MAX); [|exfalso; exact (inFP_nil a Ha)].
apply inFP_cons in Ha as [Ha | Ha]; [cbn [fst snd] in Ha; unfold CALL_OFF_NARGS, CALL_SIZE in *; lia|].
apply inFP_cons in Ha as [Ha | Ha]; [cbn [fst snd] in Ha; unfold CALL_OFF_ARGS, CALL_SIZE in *; lia | exfalso; exact (inFP_nil a Ha)].
Qed.
(* the slot's bytes are recorder bytes *)
Lemma scs_slot_RX : forall R1 O1 a, (length (r_calls R1) <= 16)%nat ->
rec_slot R1 <= a < rec_slot R1 + CALL_SIZE -> scs_RX O1 a.
Proof.
intros R1 O1 a HL Ha. destruct (scs_slot_bounds R1 HL) as [Hs | Hs].
- left. unfold A_G_REC, OFF_CALLS, CALL_SIZE, REC_SIZE in *. lia.
- right; left. rewrite Hs in Ha. unfold SC_SIZE, CALL_SIZE in *. lia.
Qed.
(* the number of calls the recorder holds *)
Lemma scs_ncalls : forall ly1 S1 rd R1 O1, rec_repA B ly1 S1 rd R1 O1 -> (length (r_calls R1) <= 16)%nat.
Proof. intros ly1 S1 rd R1 O1 (Q0 & HQ0 & _). destruct HQ0 as (_ & _ & _ & (HC1 & _) & _). exact HC1. Qed.
(* record()'s footprint: recorder bytes *)
Lemma scs_rec_fp : forall R1 O1 a, (length (r_calls R1) <= 16)%nat ->
inFP ((A_G_REC + OFF_NCALLS, A_G_REC + OFF_NCALLS + 4) :: (rec_slot R1, rec_slot R1 + 8) ::
  (if Nat.ltb (length (r_calls R1)) 16 then [] else ablocks_fp O1)) a ->
scs_RX O1 a \/ (exists p m, In (p, m) O1 /\ p <= a < p + req_size m).
Proof.
intros R1 O1 a HL Ha. apply inFP_cons in Ha as [Ha | Ha].
{ left. left. unfold OFF_NCALLS, A_G_REC, REC_SIZE in *. lia. }
apply inFP_cons in Ha as [Ha | Ha].
{ left. apply (scs_slot_RX R1 O1 a HL). unfold CALL_SIZE. lia. }
destruct (Nat.ltb (length (r_calls R1)) 16); [exfalso; exact (inFP_nil a Ha)|].
right. exact (inFP_ablocks_fp_inv O1 a Ha).
Qed.


Lemma scb_head : forall (Q : world SEGS -> config -> Prop),
  (forall (fx' : YK11.FPState) (WL : world SEGS) regsL memL mdL lyL SL fpos lst bl1 Frec O1 p1 p2,
     scb_frm0 fx' -> scb_fxok (@fp_regs fx) (@fp_csr fx) fx' ->
     scb_lctx B MT ly S W regs mem md id pids ids R O lyL SL WL memL mdL fpos lst bl1 Frec O1 p1 p2 ->
     scb_inv B ly S W regs mem md pids ids R O lyL SL WL memL fpos lst 0 regsL memL mdL ->
     SRr SEGS WL (@cfg_at fx' SEGS (BASE + SCB_LOOP) regsL memL mdL) Q) ->
  SRr SEGS W (cfg_at SEGS (BASE + AF_sup_chain) regs mem md) Q.
Proof.
intros Q K.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof (pa_base_lo (PL := PL_cmd)) as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
assert (FS : SUP_CHAIN_STK = 16800) by (vm_compute; reflexivity).
assert (Hes : ESTACK = 4096) by reflexivity. assert (Has : ASTACK = 16384) by reflexivity.
assert (HspA : alloc_ceiling + 16800 <= spZ regs) by (pose proof Hslo as X; rewrite FS in X; lia).
assert (HspT : spZ regs <= 2 ^ 47) by lia.
pose proof (scb_entry B TL TLF SUP_CHAIN_STK W ly S regs mem md ch ltac:(rewrite FS; lia) HPRE) as HS.
pose proof (ajournal_init SEGS B SUP_CHAIN_STK (SCB_FP O) ly S W regs mem md ch HPRE) as HJ.
set (sp1 := 32 * ((spZ regs - 192) / 32)) in HS.
destruct (scb_sp1_facts (spZ regs) Hal16 ltac:(lia)) as (Hsp1 & Hsp1a & Hsp1b). fold sp1 in Hsp1, Hsp1a, Hsp1b.
remember (Eimg (Ereg regs (scb_extra B sp1))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regs (scb_extra B sp1)) E) by (rewrite HE; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r) by (intros n r Hn; rewrite HE; apply ew_Eimg_Ereg_nat; exact Hn).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (rewrite HE, Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E34 : ew E 34 = Z_to_bv 64 sp1) by (rewrite HE, Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
clear HE.
assert (Esp : ew E 2 = Z_to_bv 64 (spZ regs)) by (rewrite (EE 2%nat 2%bv eq_refl); unfold spZ; symmetry; apply Z_to_bv_bv_unsigned).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite Esp; apply unsigned_lit_small; lia).
assert (U34 : bv_unsigned (ew E 34) = sp1) by (rewrite E34; apply unsigned_lit_small; lia).
unfold cfg_at. change (w64 (BASE + AF_sup_chain)) with (Z_to_bv 64 (BASE + AF_sup_chain)).
(* run 1: the prologue, the use-after-return flag (1, the record's const cell) and the call of __asan_stack_malloc_1 *)
paj_run_shc RUNP RUNC HS HJ.
{ unfold ss_scb0, scb_regions0, got_regionP, bcell_regionP, uar_got_regionP, uar_cell_regionP. cbn [ss_mem].
eapply (awr_ok_cons_stack_off SEGS B) with (n := 2%nat) (d := 0); [reflexivity | rewrite Usp; lia | cbn; rewrite FS; lia | cbn; lia |].
eapply (awr_ok_cons_stack_off SEGS B) with (n := 2%nat) (d := 0); [reflexivity | rewrite Usp; lia | cbn; rewrite FS; lia | cbn; lia |].
eapply (awr_ok_cons_stack_off SEGS B) with (n := 34%nat) (d := sp1 - spZ regs); [reflexivity | rewrite U34; lia | cbn; rewrite FS; lia | cbn; lia |].
repeat (apply (awr_ok_cons_ro SEGS B); [cbn; lia|]). apply (awr_ok_nil SEGS B). }
rename ms into ms1, mat into mat1, HF into HF1, HFr into HFr1, HG into HG1.
preg HS (2%bv : bv 5) R2. preg HS (9%bv : bv 5) R9.
rewrite (scb_denot_and32 E 2 (spZ regs) Esp ltac:(lia)) in R2. fold sp1 in R2.
rewrite scb_denot_add0, (scb_denot_and32 E 2 (spZ regs) Esp ltac:(lia)) in R9. fold sp1 in R9.
lazymatch type of HS with st_ok_pi _ _ _ ?ssx ?msx =>
pose proof (ast_ok_pi_set_reg_fp E ssx msx (2%bv : bv 5) (SOff 34 0) HS eq_refl
  ltac:(rewrite scb_denot_off0, E34; cbn [ms_regs restrict]; rewrite R2; reflexivity)) as HS3 end.
clear HS. rename HS3 into HS.
lazymatch type of HS with st_ok_pi _ _ _ ?ssx ?msx =>
pose proof (ast_ok_pi_set_reg_fp E ssx msx (9%bv : bv 5) (SOff 34 0) HS eq_refl
  ltac:(rewrite scb_denot_off0, E34; cbn [ms_regs restrict]; rewrite R9; reflexivity)) as HS3 end.
clear HS. rename HS3 into HS. norm_ssp HS.
clear R2 R9.
paj_run_shc RUNP RUNC HS HJ.
{ cbn [ss_mem].
eapply (awr_ok_cons_stack_off SEGS B) with (n := 2%nat) (d := 0); [reflexivity | rewrite Usp; lia | cbn; rewrite FS; lia | cbn; lia |].
eapply (awr_ok_cons_stack_off SEGS B) with (n := 2%nat) (d := 0); [reflexivity | rewrite Usp; lia | cbn; rewrite FS; lia | cbn; lia |].
eapply (awr_ok_cons_stack_off SEGS B) with (n := 34%nat) (d := sp1 - spZ regs); [reflexivity | rewrite U34; lia | cbn; rewrite FS; lia | cbn; lia |].
repeat (apply (awr_ok_cons_ro SEGS B); [cbn; lia|]). apply (awr_ok_nil SEGS B). }
rename ms into ms1b, mat into mat1b, HF into HF1b, HFr into HFr1b, HG into HG1b.
(* run 1 wrote the stack only *)
assert (K01 : forall a, 0 <= a < alloc_ceiling -> rdW W (ms_mem ms1b) a = rdW W mem a).
{ intros a Ha.
  rewrite (kept_of_frame (segs := SEGS) E _ (w_H W) (ms_mem ms1) (ms_mem ms1b) (fun a => alloc_ceiling <= a < 2 ^ 64) HFr1b); [| | lia | lia].
  2:{ intros b wlo whi a' Hin Hrr. vm_compute in Hin.
      repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?Usp, ?U34 in Hrr; lia|]).
      destruct Hin. }
  apply (kept_of_frame (segs := SEGS) E _ (w_H W) mem (ms_mem ms1) (fun a => alloc_ceiling <= a < 2 ^ 64) HFr1); [|lia|lia].
  intros b wlo whi a' Hin Hrr. vm_compute in Hin.
  repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?Usp, ?U34 in Hrr; lia|]).
  destruct Hin. }
clear HF1 HFr1 HG1 HF1b HFr1b HG1b.
pmkst HS.
preg HS (2%bv : bv 5) R2. preg HS (1%bv : bv 5) R1. preg HS (3%bv : bv 5) R3. preg HS (4%bv : bv 5) R4.
lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?m |} _ => set (md1 := m) in *; clearbody md1 end.
pose proof (palf_sm B TLF 1 ltac:(cbn; tauto)) as SM1. change (cs_stack_malloc 1) with CS___asan_stack_malloc_1 in SM1.
rewrite SM1.
rewrite scb_denot_off0, E34 in R2.
cbn [sv_denot] in R1. rewrite (img_env_codeptr E HEI 23824) in R1.
rewrite scb_denot_off0, (EE 3%nat 3%bv eq_refl) in R3. rewrite scb_denot_off0, (EE 4%nat 4%bv eq_refl) in R4.
assert (Qsp : spZ (ms_regs ms1b) = spZ regs + (sp1 - spZ regs)) by (unfold spZ at 1; rewrite R2, unsigned_lit_small by lia; lia).
(* the call of __asan_stack_malloc_1 (0x8c23c): the class-1 frame *)
eapply SRr_bind.
{ eapply (aj_stack_malloc_atS SEGS B LAWS pa_segs_low (pal_env B TL) ML (cmd_stack_malloc_progress B) 1 (ASTACK_MALLOC1 fx) ltac:(lia) W (ms_regs ms1b) (ms_mem ms1b)
  SUP_CHAIN_STK (spZ regs) (SCB_FP O) ly S W mem md [] ly S _ 0 (sp1 - spZ regs) (Z_to_bv 64 (BASE + 23824)) HJ);
  [ exact Qsp | exact Hsp1b | lia | rewrite FS, Hes; lia | rewrite R3; exact Hgp | rewrite R4; exact Htp
  | exact R1 | apply ret_ok_codeptr_v; [lia | reflexivity]
  | pose proof (count_cid_le_length 1 (frames S)); change (fs_frames 1) with 8192; lia ]. }
cbv beta. intros W2 c2 _ (-> & S2 & regs2 & mem2 & md2 & fpos & -> & HJ2 & HP2 & Ha0 & Eab & Hfrs2 & Hnin & Hnev2 & Hbb2 & Hz & Hflag & HK & HJS & (fS2 & ES2)).
pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJ2pres & _).
pose proof HK as (HK1 & HK2 & HK3 & HK4 & _ & _).
jafter_call_keep_hi HS 1024%nat regs2 (mrestrict (w_H W) mem2) HP2 [1;2]%nat HS2.
match type of HS2 with ?tq -> _ => assert (HRK : tq); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict mkst]. repeat apply Forall_cons; try apply Forall_nil.
- eapply scs_region_kept_hi; [exact Usp | intros a Ha; apply HK1; lia | intros a Ha; apply HJ2pres; rewrite FS; lia].
- eapply scs_region_kept_hi; [exact U34 | intros a Ha; apply HK1; lia | intros a Ha; apply HJ2pres; rewrite FS; lia]. }
rewrite <- restrict_mkst_fx in HS2. clear HS. rename HS2 into HS.
clear R1 R2 R3 R4 Qsp.
remember (havoc E 1024 (map (getr regs2) CLOB)) as E1 eqn:HE1 in HS.
assert (HAE1 : env_agree 32 (Ereg regs (scb_extra B sp1)) E1) by (rewrite HE1; apply env_agree_havoc_ge; [lia | exact HAE]).
assert (HEI1 : img_env VAL A_LIM E1) by (rewrite HE1; apply img_env_havoc_hi; [exact HEI | unfold A_LIM; lia]).
assert (OLD1 : forall n, (n < 1024)%nat -> ew E1 n = ew E n) by (intros n Hn; rewrite HE1; apply ew_havoc_old; exact Hn).
set (F := frame_addr ly 1 fpos) in *. set (FL := flag_addr ly 1 fpos) in *.
assert (E1028 : ew E1 1028 = Z_to_bv 64 F).
{ rewrite HE1. change 1028%nat with (1024 + 4)%nat. rewrite (ew_havoc_new E 1024 _ 4 (Z_to_bv 64 0)) by (cbv; lia).
  unfold CLOB. cbn [map nth]. exact Ha0. }
clear HE1.
pose proof (proj1 HJ2) as HAR2.
assert (Hfin : In (1, fpos) (frames S2)) by (rewrite Hfrs2; left; reflexivity).
destruct (al_frames _ _ LAWS _ _ _ _ _ 1 fpos HAR2 Hfin) as (HFal & HFapp & HFpres & HFSpres). fold F in HFal, HFapp, HFpres, HFSpres.
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 1 fpos HAR2 Hfin) as (HF4096 & HFceil & _). fold F in HF4096, HFceil.
pose proof (frm_off_imgP _ _ _ _ _ _ _ _ HAR2 Hfin) as HFoff. fold F in HFoff. unfold off_img in HFoff.
destruct (frame_al64 SEGS B _ _ _ _ _ 1 fpos HAR2 Hfin) as (HF64 & _ & _). fold F in HF64.
change (fs_frame_bytes 1) with 128 in *. change (128 / 8) with 16 in *.
replace (F + 128 - 8) with (F + 120) in Hflag by lia.
assert (HFq : F = 64 * (F / 64)) by (pose proof (Z.div_mod F 64 ltac:(lia)); lia).
assert (HF8m : F mod 8 = 0) by (rewrite HFq, Z.mul_comm; replace 64 with (8 * 8) by reflexivity; rewrite Z.mul_assoc; apply Z_mod_mult).
assert (HFin : in_app F 128) by exact HFapp.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFin.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssv ?msv =>
pose proof (st_ok_pi_havoc_hi 1040 Ev ssv msv [Z_to_bv 64 FL; Z_to_bv 64 (SB + F / 8)] HS ltac:(vm_compute; reflexivity)) as HS3 end.
clear HS. rename HS3 into HS.
remember (havoc E1 1040 [Z_to_bv 64 FL; Z_to_bv 64 (SB + F / 8)]) as E2 eqn:HE2 in HS.
assert (HAE2 : env_agree 32 (Ereg regs (scb_extra B sp1)) E2) by (rewrite HE2; apply env_agree_havoc_ge; [lia | exact HAE1]).
assert (HEI2 : img_env VAL A_LIM E2) by (rewrite HE2; apply img_env_havoc_hi; [exact HEI1 | unfold A_LIM; lia]).
assert (OLD2 : forall n, (n < 1024)%nat -> ew E2 n = ew E n) by (intros n Hn; rewrite HE2, ew_havoc_old by lia; apply OLD1; exact Hn).
assert (E1040 : ew E2 1040 = Z_to_bv 64 FL) by (rewrite HE2; exact (ew_havoc_new E1 1040 [Z_to_bv 64 FL; Z_to_bv 64 (SB + F / 8)] 0 (Z_to_bv 64 0) ltac:(cbn; lia))).
assert (E1041 : ew E2 1041 = Z_to_bv 64 (SB + F / 8)) by (rewrite HE2; exact (ew_havoc_new E1 1040 [Z_to_bv 64 FL; Z_to_bv 64 (SB + F / 8)] 1 (Z_to_bv 64 0) ltac:(cbn; lia))).
assert (E2028 : ew E2 1028 = Z_to_bv 64 F) by (rewrite HE2, ew_havoc_old by lia; exact E1028).
clear HE2.
assert (E2_32 : ew E2 32 = Z_to_bv 64 SB) by (rewrite OLD2 by lia; exact E32).
assert (V2 : bv_unsigned (ew E2 2) = spZ regs) by (rewrite OLD2 by lia; exact Usp).
assert (V34 : bv_unsigned (ew E2 34) = sp1) by (rewrite OLD2 by lia; exact U34).
assert (V1028 : bv_unsigned (ew E2 1028) = F) by (rewrite E2028; apply unsigned_lit_small; lia).
destruct (proj1 asan_consts) as [AC1 AC2].
assert (HFL : 4096 <= FL < alloc_ceiling).
{ destruct (al_flag _ _ LAWS _ _ _ _ _ 1 fpos HAR2 Hfin) as (_ & _ & (HFL1 & _) & HFL2). fold FL in HFL1, HFL2. lia. }
assert (V1040 : bv_unsigned (ew E2 1040) = FL) by (rewrite E1040; apply unsigned_lit_small; lia).
assert (HF8 : 512 <= F / 8 < 2 ^ 44) by (split; [apply Z.div_le_lower_bound | apply Z.div_lt_upper_bound]; lia).
assert (V1041 : bv_unsigned (ew E2 1041) = SB + F / 8) by (rewrite E1041; apply unsigned_lit_small; unfold SB; lia).
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssv ?msv =>
pose proof (st_ok_pi_add_fact Ev ssv msv 1028 (HPTR 5) HS
ltac:(unfold afact_ok, HPTR; cbn [af_lo af_hi af_al2]; rewrite V1028; change (2 ^ 5) with 32; lia)) as HS3 end.
clear HS. rename HS3 into HS.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssv ?msv =>
pose proof (st_ok_pi_add_alias Ev _ msv scb_shx_F (SOff 1041 0) HS (shadow_decl_ok Ev 1028 32 1041 F SB E2028 ltac:(lia) E2_32 E1041)) as HS3 end.
clear HS. rename HS3 into HS. norm_ssp HS.
(* the stack words below the shadow base and the frame's address (s1 + 8 .. s1 + 48, s1 + 80) *)
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssv ?msv =>
pose proof (st_ok_pi_add_region Ev ssv msv scs_rw1 HS eq_refl
ltac:(unfold region_ok, scs_rw1; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
  rewrite V34; split; [lia|]; split; [lia|]; split; [|apply Forall_nil];
  intros o Ho; apply (apresent_writable SEGS); apply HJ2pres; rewrite FS; lia)
ltac:(cbn [all_disjoint ss_mem]; unfold extent_disjoint, scs_rw1; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
  rewrite V2, V34; repeat split; lia)) as HS3 end.
clear HS. rename HS3 into HS. norm_ssp HS.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssv ?msv =>
pose proof (st_ok_pi_add_region Ev ssv msv scs_rw2 HS eq_refl
ltac:(unfold region_ok, scs_rw2; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
  rewrite V34; split; [lia|]; split; [lia|]; split; [|apply Forall_nil];
  intros o Ho; apply (apresent_writable SEGS); apply HJ2pres; rewrite FS; lia)
ltac:(cbn [all_disjoint ss_mem]; unfold extent_disjoint, scs_rw2, scs_rw1; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
  rewrite V2, V34; repeat split; lia)) as HS3 end.
clear HS. rename HS3 into HS. norm_ssp HS.
(* the frame's header, flag word and shadow (answer_code's fr_hdr / fr_flg / fr_shd) *)
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssv ?msv =>
pose proof (st_ok_pi_add_region Ev ssv msv scb_fr_hdr HS eq_refl
ltac:(unfold region_ok, scb_fr_hdr; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
  rewrite V1028; split; [lia|]; split; [lia|]; split; [|apply Forall_nil];
  intros o Ho; apply (apresent_writable SEGS); apply (proj1 (HFpres (F + o) ltac:(lia))))
ltac:(cbn [all_disjoint ss_mem]; unfold extent_disjoint, scb_fr_hdr, scs_rw1, scs_rw2; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
  rewrite V1028, V2, V34; repeat split; lia)) as HS3 end.
clear HS. rename HS3 into HS. norm_ssp HS.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssv ?msv =>
pose proof (st_ok_pi_add_region Ev ssv msv scb_fr_flg HS eq_refl
ltac:(unfold region_ok, scb_fr_flg; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
  rewrite V1028; split; [lia|]; split; [lia|]; split; [intros o Ho; lia|];
  apply Forall_cons; [|apply Forall_nil];
  apply (chunk_ok_val SEGS Ev _ F 120 8 (SOff 1040 0) FL); [rewrite scb_denot_off0; exact E1040 | lia | lia |];
  exact (val_mem_of_rdword SEGS _ _ _ _ Hflag))
ltac:(cbn [all_disjoint ss_mem]; unfold extent_disjoint, scb_fr_flg, scb_fr_hdr, scs_rw1, scs_rw2; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
  rewrite V1028, V2, V34; repeat split; lia)) as HS3 end.
clear HS. rename HS3 into HS. norm_ssp HS.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssv ?msv =>
pose proof (st_ok_pi_add_region Ev ssv msv scs_fr_shd HS eq_refl
ltac:(unfold region_ok, scs_fr_shd; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
  rewrite V1041; split; [unfold SB; lia|]; split; [unfold SB; lia|]; split;
  [ intros o Ho; apply (apresent_writable SEGS);
    replace (SB + F / 8 + o) with (shadow_addr F + o) by (unfold shadow_addr; rewrite <- SB_SHADOW_OFF; lia);
    apply (proj1 (HFSpres o ltac:(lia)))
  | apply scs_zchunks_ok; intros i Hi;
    pose proof (Hz i Hi) as Hzi; unfold shadow_of_addr in Hzi; rewrite <- SB_SHADOW_OFF in Hzi; exact Hzi ])
ltac:(cbn [all_disjoint ss_mem]; unfold extent_disjoint, scs_fr_shd, scb_fr_flg, scb_fr_hdr, scs_rw1, scs_rw2; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
  rewrite V1041, V1028, V2, V34; unfold SB; pose proof (Z.div_mod F 8 ltac:(lia)); pose proof (Z.mod_pos_bound F 8 ltac:(lia));
  repeat split; lia)) as HS3 end.
clear HS. rename HS3 into HS. norm_ssp HS.
assert (EFA : frame_addr ly 1 fpos = F) by reflexivity.
(* run 2: the frame's words, header and shadow, a0 := 17, jal record *)
paj_run_shc RUNP RUNC HS HJ2.
{ scs_awr fpos (spZ regs) sp1 FS V1041 V1028 V2 V34 EFA ltac:(fail "scs_awr: unknown region"). }
rename ms into ms3, mat into mat3, HF into HF3, HFr into HFr3, HG into HG3.
pmkst HS.
lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?m |} _ => set (md3 := m) in *; clearbody md3 end.
(* run 2 wrote the stack, the frame's header and its shadow *)
assert (K23 : forall a, 0 <= a < 2 ^ 64 -> ~ (alloc_ceiling <= a < 2 ^ 64) -> ~ (F <= a < F + 128) ->
  ~ (SB + F / 8 <= a < SB + F / 8 + 16) -> rdW W (ms_mem ms3) a = rdW W mem2 a).
{ intros a Ha H1 H2 H3.
  apply (kept_of_frame (segs := SEGS) E2 _ (w_H W) mem2 (ms_mem ms3)
    (fun a => (alloc_ceiling <= a < 2 ^ 64) \/ (F <= a < F + 128) \/ (SB + F / 8 <= a < SB + F / 8 + 16)) HFr3); [| lia | tauto].
  intros b wlo whi a' Hin Hrr. vm_compute in Hin.
  repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?V2, ?V34, ?V1028, ?V1041 in Hrr; lia|]).
  destruct Hin. }
clear HF3 HFr3 HG3.
assert (HOin : forall pn, In pn O -> In pn (ablocks B ly S)) by exact (scs_O_in _ _ _ _ _ HREP).
assert (HOin2 : forall pn, In pn O -> In pn (ablocks B ly S2)) by (intros pn Hpn; rewrite Eab; exact (HOin pn Hpn)).
assert (KR3 : forall a, scs_RX O a -> rdW W (ms_mem ms3) a = rdW W mem a).
{ intros a Ha. destruct (scs_RX_loc ly S2 W mem2 md2 O fpos a HAR2 HOin2 Hfin Ha) as (Hlo & HnF & HnS & Hcase).
  fold F in HnF, HnS.
  rewrite (K23 a ltac:(lia) ltac:(lia) HnF HnS).
  destruct Hcase as [(Hi & Ho & He) | (p & m & Hpm & Hpa)].
  - rewrite (HK3 a Hi Ho He). exact (K01 a Hlo).
  - replace a with (p + (a - p)) by lia.
    rewrite (HK2 p m (a - p) (HOin _ Hpm) ltac:(lia) (fun H => H)). replace (p + (a - p)) with a by lia. exact (K01 a Hlo). }
(* the call of record(17) (0x8c2f4) *)
preg HS (1%bv : bv 5) R1. preg HS (2%bv : bv 5) R2. preg HS (3%bv : bv 5) R3. preg HS (4%bv : bv 5) R4.
preg HS (8%bv : bv 5) R8. preg HS (10%bv : bv 5) R10.
cbn [sv_denot] in R1. rewrite (img_env_codeptr E2 HEI2 24008) in R1.
rewrite scb_denot_off0, OLD2, E34 in R2 by lia.
rewrite scb_denot_off0, OLD2, (EE 3%nat 3%bv eq_refl) in R3 by lia.
rewrite scb_denot_off0, OLD2, (EE 4%nat 4%bv eq_refl) in R4 by lia.
rewrite scb_denot_off0, OLD2, Esp in R8 by lia.
cbn [sv_denot] in R10.
pose proof (st_ok_region_nth E2 _ _ 5 _ HS eq_refl) as HR5. cbn [ms_mem restrict mkst] in HR5.
assert (SVra : rdword (rdW W (ms_mem ms3)) (spZ regs - 8) = Some (raZ regs)).
{ apply (rdword_of_val_mem SEGS); [|unfold raZ; apply bv_unsigned_in_range].
  replace (spZ regs - 8) with (spZ regs + -8) by lia.
  refine (field_of_region E2 _ 2 (spZ regs) _ (-104) 0 (-104) 0 (-8) 8%N (SOff 1 0) (raZ regs) HR5 V2 _ _ _ _);
  [cbn [In]; tauto | rewrite scb_denot_off0, OLD2, (EE 1%nat 1%bv eq_refl) by lia; unfold raZ; symmetry; apply Z_to_bv_bv_unsigned
  | unfold raZ; apply bv_unsigned_in_range | lia]. }
assert (SVs0 : rdword (rdW W (ms_mem ms3)) (spZ regs - 16) = Some (s0Z regs)).
{ apply (rdword_of_val_mem SEGS); [|unfold s0Z; apply bv_unsigned_in_range].
  replace (spZ regs - 16) with (spZ regs + -16) by lia.
  refine (field_of_region E2 _ 2 (spZ regs) _ (-104) 0 (-104) 0 (-16) 8%N (SOff 8 0) (s0Z regs) HR5 V2 _ _ _ _);
  [cbn [In]; tauto | rewrite scb_denot_off0, OLD2, (EE 8%nat 8%bv eq_refl) by lia; unfold s0Z; symmetry; apply Z_to_bv_bv_unsigned
  | unfold s0Z; apply bv_unsigned_in_range | lia]. }
clear HR5.
assert (Qsp3 : spZ (ms_regs ms3) = spZ regs + (sp1 - spZ regs)) by (unfold spZ at 1; rewrite R2, unsigned_lit_small by lia; lia).
assert (Hs03 : s0Z (ms_regs ms3) = spZ regs) by (unfold s0Z; rewrite R8, unsigned_lit_small by lia; reflexivity).
destruct (scs_chain ly S2 W (ms_mem ms3) md3 [(1, fpos)] 0 (spZ regs + (sp1 - spZ regs)) HJ2 SVra SVs0 ltac:(lia)) as (ch3 & HCH3).
assert (HCH3' : achain ly (rdW W (ms_mem ms3)) (spZ regs + (sp1 - spZ regs)) (s0Z (ms_regs ms3)) ch3) by (rewrite Hs03; exact HCH3).
clear HCH3. rename HCH3' into HCH3.
assert (G1r : YK0s.ret_ok (getr (ms_regs ms3) 1)) by (rewrite R1; apply ret_ok_codeptr_v; [lia | reflexivity]).
assert (G1a : 4096 <= bv_unsigned (getr (ms_regs ms3) 1)) by (rewrite R1, unsigned_lit_small; lia).
assert (G3 : getr (ms_regs ms3) 3 = w64 (as_gp B)) by (rewrite R3; exact Hgp).
assert (G4 : getr (ms_regs ms3) 4 = w64 (as_tp B)) by (rewrite R4; exact Htp).
assert (HRS : RECORD_STK = 16560) by (vm_compute; reflexivity).
assert (XR0 : 0 <= XM_RECORD MT R).
{ unfold XM_RECORD, rec_spill_frees. pose proof (mo_free_nonneg MT MTL). destruct (Nat.ltb _ _); lia. }
assert (XM0 : forall n, 0 <= n -> 0 <= XM_XMALLOC MT n).
{ intros n Hn. unfold XM_XMALLOC. apply (mo_malloc_nonneg MT MTL). unfold LIVE_XMALLOC. lia. }
assert (XA0 : forall v, 0 <= XM_ARG_S MT v).
{ intros v. unfold XM_ARG_S. apply XM0. lia. }
assert (XN0 : forall t, 0 <= XM_ANSWER MT t).
{ intros t. unfold XM_ANSWER, XM_HAND_BACK, XM_XMALLOC. pose proof (mo_free_nonneg MT MTL).
  pose proof (mo_malloc_nonneg MT MTL (LIVE_XMALLOC (Z.of_nat (length t) + 1)) ltac:(unfold LIVE_XMALLOC; lia)). lia. }
pose proof (mo_free_nonneg MT MTL) as XF0.
rewrite (proj1 (scb_sigs cmd_sig_prog_PB)).
eapply SRr_bind.
{ eapply (cl_callS_wide B LAWS W (ms_regs ms3) (ms_mem ms3) _ SUP_CHAIN_STK (spZ regs) (SCB_FP O) ly S W mem md [(1, fpos)] ly S2 _ 0
    RECORD_STK _ (EV_RECORD R) (sp1 - spZ regs) (getr (ms_regs ms3) 1) ch3 _ HJ2 Qsp3 Hsp1b ltac:(lia)
    ltac:(rewrite HRS; lia) ltac:(rewrite HRS, FS; lia) G3 G4 eq_refl G1r G1a HCH3).
  - intros HPRE1. pose proof (TRECORD fx ly S2 W (ms_regs ms3) (ms_mem ms3) _ ch3 17 R O HPRE1) as T.
    unfold apost_base in T. apply T.
    + exact (scs_aro _ _ _ _ _ _ _ HJ2).
    + exact R10.
    + unfold REC_FN_COUNT. lia.
    + apply (scs_rec_repA_ext ly S (rdW W mem) ly S2 _ R O HREP HOin2). exact KR3.
    + rewrite Hnev2. unfold EV_SUP_CHAIN, EV_ARG_S, EV_ANSWER, EV_HAND_BACK, EV_XMALLOC in HNEV. lia.
    + rewrite ES2. apply (mo_ok_set_fs MT MTLF). apply (mo_ok_le MT MTL S _ (XM_SUP_CHAIN MT R id ids) HMOK).
      unfold XM_SUP_CHAIN. pose proof (XM0 (12 * Z.of_nat (length ids) + 1) ltac:(lia)).
      pose proof (XA0 (Some (dec id))). pose proof (XA0 (Some (dec (Z.of_nat (length ids))))). pose proof (XA0 (Some (dec_list ids))).
      pose proof (XN0 (snd (sup_chain_m R id ids))). lia.
  - intros a Ha. destruct (scs_rec_fp R O a (scs_ncalls _ _ _ _ _ HREP) Ha) as [HRX | (p & m & Hpm & Hpa)].
    + destruct HRX as [Hg | [Hsl | ([p m] & Hpm & Hpa)]].
      * apply scs_awr_grec. exact Hg.
      * apply scs_awr_spill. exact Hsl.
      * cbn [fst snd] in Hpa. apply (scs_awr_blk _ _ _ _ _ _ _ p m a Hpm (HOin2 _ Hpm)).
        destruct (scs_blk_bounds _ _ _ _ _ p m HAR2 (HOin2 _ Hpm)) as (_ & _ & _ & Hmr & _). lia.
    + exact (scs_awr_blk _ _ _ _ _ _ _ p m a Hpm (HOin2 _ Hpm) Hpa).
  - intros ly' S' W' regs' mem' md' _ a Ha Hw _. exfalso.
    destruct (scs_rec_fp R O a (scs_ncalls _ _ _ _ _ HREP) Ha) as [HRX | (p & m & Hpm & Hpa)].
    + destruct (scs_RX_loc ly S2 W mem2 md2 O fpos a HAR2 HOin2 Hfin HRX) as (Hlo & _). rewrite FS in Hw. lia.
    + destruct (scs_blk_loc ly S2 W mem2 md2 fpos p m a HAR2 (HOin2 _ Hpm) Hfin Hpa) as (Hlo & _). rewrite FS in Hw. lia. }
cbv beta. intros W4 c4 Hwle4 (ly4 & S4 & regs4 & mem4 & md4 & -> & HJ4 & HJc4 & HPv4 & HKr4).
destruct HKr4 as (Frec & O1 & R10r & HPermF & HFlen & HFO & HREP1 & HO1 & HBB1 & MLE1).
rewrite R1.
(* record()'s footprint lies below alloc_ceiling, apart from the frame and its shadow *)
assert (FP1loc : forall a, inFP ((A_G_REC + OFF_NCALLS, A_G_REC + OFF_NCALLS + 4) :: (rec_slot R, rec_slot R + 8) ::
    (if Nat.ltb (length (r_calls R)) 16 then [] else ablocks_fp O)) a ->
  0 <= a < alloc_ceiling /\ ~ (F <= a < F + 128) /\ ~ (SB + F / 8 <= a < SB + F / 8 + 16)).
{ intros a Ha. destruct (scs_rec_fp R O a (scs_ncalls _ _ _ _ _ HREP) Ha) as [HRX | (p & m & Hpm & Hpa)].
  - destruct (scs_RX_loc ly S2 W mem2 md2 O fpos a HAR2 HOin2 Hfin HRX) as (Hlo & HnF & HnS & _). fold F in HnF, HnS. lia.
  - destruct (scs_blk_loc ly S2 W mem2 md2 fpos p m a HAR2 (HOin2 _ Hpm) Hfin Hpa) as (Hlo & _ & HnF & HnS). fold F in HnF, HnS. lia. }
pose proof (proj1 HJ4) as HAR4.
destruct (scs_frame_later fpos ly4 S4 W4 mem4 md4 _ HJ4) as (Hfin4 & EFA4 & EFL4). fold F in EFA4. fold FL in EFL4.
destruct (al_frames _ _ LAWS _ _ _ _ _ 1 fpos HAR4 Hfin4) as (_ & _ & HFpres4 & HFSpres4). rewrite EFA4 in HFpres4, HFSpres4.
change (fs_frame_bytes 1) with 128 in HFpres4, HFSpres4. change (128 / 8) with 16 in HFSpres4.
pose proof HJ4 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJ4pres & _).
jafter_call_keep_hi HS 1042%nat regs4 (mrestrict (w_H W4) mem4) HPv4 [0;1;3;4;5;6]%nat HS4.
match type of HS4 with ?tq -> _ => assert (HRK : tq); [|specialize (HS4 HRK); clear HRK] end.
{ cbn [ms_mem restrict mkst]. repeat apply Forall_cons; try apply Forall_nil.
  - eapply (region_kept_fshadow_sub (segs := SEGS) B E2 _ _ _ ly S2 W (ms_mem ms3) _ ly4 S4 W4 mem4 md4 _ 1041 (SB + F / 8) _ _ _ _ _ 1 fpos HJc4 V1041 Hfin);
    [ unfold shadow_addr; fold F; rewrite <- SB_SHADOW_OFF; lia
    | unfold shadow_addr; fold F; rewrite <- SB_SHADOW_OFF; change (fs_frame_bytes 1 / 8) with 16; lia
    | intros a Ha HFa; destruct (FP1loc a HFa) as (_ & _ & HnS); lia
    | intros a Ha; replace a with (shadow_addr F + (a - (SB + F / 8))) by (unfold shadow_addr; rewrite <- SB_SHADOW_OFF; lia);
      apply (proj1 (HFSpres4 (a - (SB + F / 8)) ltac:(lia))) ].
  - eapply (region_kept_frame_sub (segs := SEGS) B E2 _ _ _ ly S2 W (ms_mem ms3) _ ly4 S4 W4 mem4 md4 _ 1028 F _ _ _ _ _ 1 fpos HJc4 V1028 Hfin);
    [ fold F; lia | fold F; change (fs_frame_bytes 1) with 128; lia
    | intros a Ha HFa; destruct (FP1loc a HFa) as (_ & HnF & _); lia
    | intros a Ha; lia ].
  - eapply (region_kept_stack_sub SEGS B); [exact HJc4 | exact HJ4 | exact V34 | cbn; lia | cbn; rewrite FS; lia | cbn; lia | cbn; lia | cbn; lia |].
    intros a Ha HFa. destruct (FP1loc a HFa) as (Hlo & _). lia.
  - eapply (region_kept_stack_sub SEGS B); [exact HJc4 | exact HJ4 | exact V34 | cbn; lia | cbn; rewrite FS; lia | cbn; lia | cbn; lia | cbn; lia |].
    intros a Ha HFa. destruct (FP1loc a HFa) as (Hlo & _). lia.
  - eapply (region_kept_stack_sub SEGS B); [exact HJc4 | exact HJ4 | exact V2 | cbn; lia | cbn; rewrite FS; lia | cbn; lia | cbn; lia | cbn; lia |].
    intros a Ha HFa. destruct (FP1loc a HFa) as (Hlo & _). lia.
  - eapply (region_kept_stack_sub SEGS B); [exact HJc4 | exact HJ4 | exact V34 | cbn; lia | cbn; rewrite FS; lia | cbn; lia | cbn; lia | cbn; lia |].
    intros a Ha HFa. destruct (FP1loc a HFa) as (Hlo & _). lia. }
rewrite <- restrict_mkst_fx in HS4. clear HS. rename HS4 into HS.
remember (havoc E2 1042 (map (getr regs4) CLOB)) as E3 eqn:HE3 in HS.
assert (HEI3 : img_env VAL A_LIM E3) by (rewrite HE3; apply img_env_havoc_hi; [exact HEI2 | unfold A_LIM; lia]).
assert (OLD3 : forall n, (n < 1042)%nat -> ew E3 n = ew E2 n) by (intros n Hn; rewrite HE3; apply ew_havoc_old; exact Hn).
assert (E1046 : ew E3 1046 = getr regs4 10) by (rewrite HE3; reflexivity).
clear HE3.
assert (X2 : bv_unsigned (ew E3 2) = spZ regs) by (rewrite OLD3 by lia; exact V2).
assert (X34 : bv_unsigned (ew E3 34) = sp1) by (rewrite OLD3 by lia; exact V34).
assert (X1028 : bv_unsigned (ew E3 1028) = F) by (rewrite OLD3 by lia; exact V1028).
assert (X1041 : bv_unsigned (ew E3 1041) = SB + F / 8) by (rewrite OLD3 by lia; exact V1041).
clear R1 R2 R3 R4 R8 R10 SVra SVs0 HCH3 G1r G1a G3 G4 Qsp3 Hs03.
(* run 3: s4 := the slot, a0 := 12 n + 1, jal xmalloc *)
paj_run_shc RUNP RUNC HS HJ4.
{ scs_awr fpos (spZ regs) sp1 FS X1041 X1028 X2 X34 EFA4 ltac:(fail "scs_awr: unknown region"). }
rename ms into ms5, mat into mat5, HF into HF5, HFr into HFr5, HG into HG5.
assert (K45 : forall a, 0 <= a < 2 ^ 64 -> ~ (alloc_ceiling <= a < 2 ^ 64) -> ~ (F <= a < F + 128) ->
  ~ (SB + F / 8 <= a < SB + F / 8 + 16) -> rdW W4 (ms_mem ms5) a = rdW W4 mem4 a).
{ intros a Ha H1 H2 H3.
  apply (kept_of_frame (segs := SEGS) E3 _ (w_H W4) mem4 (ms_mem ms5)
    (fun a => (alloc_ceiling <= a < 2 ^ 64) \/ (F <= a < F + 128) \/ (SB + F / 8 <= a < SB + F / 8 + 16)) HFr5); [| lia | tauto].
  intros b wlo whi a' Hin Hrr. vm_compute in Hin.
  repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?X2, ?X34, ?X1028, ?X1041 in Hrr; lia|]).
  destruct Hin. }
clear HF5 HFr5 HG5.
pmkst HS.
lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?m |} _ => set (md5 := m) in *; clearbody md5 end.
preg HS (1%bv : bv 5) R1. preg HS (2%bv : bv 5) R2. preg HS (8%bv : bv 5) R8. preg HS (10%bv : bv 5) R10. preg HS (20%bv : bv 5) R20.
assert (AG3 : forall n, (n < 1024)%nat -> ew E3 n = ew E n) by (intros n Hn; rewrite OLD3, OLD2 by lia; reflexivity).
cbn [sv_denot] in R1. rewrite (img_env_codeptr E3 HEI3 24032) in R1.
rewrite scb_denot_off0, AG3, E34 in R2 by lia.
rewrite scb_denot_off0, AG3, Esp in R8 by lia.
rewrite (scs_den_xm E3 12 (Z.of_nat (length ids)) ltac:(rewrite AG3 by lia; rewrite (EE 12%nat 12%bv eq_refl); exact H12) ltac:(lia)) in R10.
preg HS (3%bv : bv 5) R3. preg HS (4%bv : bv 5) R4.
rewrite scb_denot_off0, AG3, (EE 3%nat 3%bv eq_refl) in R3 by lia.
rewrite scb_denot_off0, AG3, (EE 4%nat 4%bv eq_refl) in R4 by lia.
pose proof (st_ok_region_nth E3 _ _ 4 _ HS eq_refl) as HR. cbn [ms_mem restrict mkst] in HR.
assert (SVra : rdword (rdW W4 (ms_mem ms5)) (spZ regs - 8) = Some (raZ regs)).
{ apply (rdword_of_val_mem SEGS); [|unfold raZ; apply bv_unsigned_in_range].
  replace (spZ regs - 8) with (spZ regs + -8) by lia.
  refine (field_of_region E3 _ 2 (spZ regs) _ (-104) 0 (-104) 0 (-8) 8%N (SOff 1 0) (raZ regs) HR X2 _ _ _ _);
  [cbn [In]; tauto | rewrite scb_denot_off0, AG3, (EE 1%nat 1%bv eq_refl) by lia; unfold raZ; symmetry; apply Z_to_bv_bv_unsigned
  | unfold raZ; apply bv_unsigned_in_range | lia]. }
assert (SVs0 : rdword (rdW W4 (ms_mem ms5)) (spZ regs - 16) = Some (s0Z regs)).
{ apply (rdword_of_val_mem SEGS); [|unfold s0Z; apply bv_unsigned_in_range].
  replace (spZ regs - 16) with (spZ regs + -16) by lia.
  refine (field_of_region E3 _ 2 (spZ regs) _ (-104) 0 (-104) 0 (-16) 8%N (SOff 8 0) (s0Z regs) HR X2 _ _ _ _);
  [cbn [In]; tauto | rewrite scb_denot_off0, AG3, (EE 8%nat 8%bv eq_refl) by lia; unfold s0Z; symmetry; apply Z_to_bv_bv_unsigned
  | unfold s0Z; apply bv_unsigned_in_range | lia]. }
clear HR.
assert (Qsp5 : spZ (ms_regs ms5) = spZ regs + (sp1 - spZ regs)) by (unfold spZ at 1; rewrite R2, unsigned_lit_small by lia; lia).
assert (Hs05 : s0Z (ms_regs ms5) = spZ regs) by (unfold s0Z; rewrite R8, unsigned_lit_small by lia; reflexivity).
destruct (scs_chain ly4 S4 W4 (ms_mem ms5) md5 [(1, fpos)] (0 + EV_RECORD R) (spZ regs + (sp1 - spZ regs)) HJ4 SVra SVs0 ltac:(lia)) as (ch5 & HCH).
assert (HCH5 : achain ly4 (rdW W4 (ms_mem ms5)) (spZ regs + (sp1 - spZ regs)) (s0Z (ms_regs ms5)) ch5) by (rewrite Hs05; exact HCH).
clear HCH SVra SVs0.
assert (G1r : YK0s.ret_ok (getr (ms_regs ms5) 1)) by (rewrite R1; apply ret_ok_codeptr_v; [lia | reflexivity]).
assert (G1a : 4096 <= bv_unsigned (getr (ms_regs ms5) 1)) by (rewrite R1, unsigned_lit_small; lia).
assert (G3 : getr (ms_regs ms5) 3 = w64 (as_gp B)) by (rewrite R3; exact Hgp).
assert (G4 : getr (ms_regs ms5) 4 = w64 (as_tp B)) by (rewrite R4; exact Htp).
assert (HXS : XMALLOC_STK = 16400) by (vm_compute; reflexivity).
assert (MLS4 : mo_le MT S S4 (XM_RECORD MT R)) by (apply (mo_le_set_fs_l MT MTLF S S4 fS2); rewrite <- ES2; exact MLE1).
assert (LA0 : forall v, 0 <= LIVE_ARG_S v) by (intros v; unfold LIVE_ARG_S, LIVE_XMALLOC; lia).
assert (LN0 : forall t, 0 <= LIVE_ANSWER t) by (intros t; unfold LIVE_ANSWER, LIVE_HAND_BACK, LIVE_XMALLOC; lia).
pose proof HJ4 as (_ & _ & _ & _ & _ & _ & Hnev4 & _).
rewrite (proj1 (proj2 (scb_sigs cmd_sig_prog_PB))).
(* the call of xmalloc(12 n + 1) (0x8c30c) *)
eapply SRr_bind.
{ eapply (cl_callS_wide B LAWS W4 (ms_regs ms5) (ms_mem ms5) _ SUP_CHAIN_STK (spZ regs) (SCB_FP O) ly S W mem md [(1, fpos)] ly4 S4 _ (0 + EV_RECORD R)
    XMALLOC_STK [] EV_XMALLOC (sp1 - spZ regs) (getr (ms_regs ms5) 1) ch5 _ HJ4 Qsp5 Hsp1b ltac:(lia)
    ltac:(rewrite HXS; lia) ltac:(rewrite HXS, FS; lia) G3 G4 eq_refl G1r G1a HCH5).
  - intros HPRE1. pose proof (TXMALLOC fx ly4 S4 W4 (ms_regs ms5) (ms_mem ms5) _ ch5 (12 * Z.of_nat (length ids) + 1) HPRE1) as T.
    unfold apost_base in T. apply T.
    + exact R10.
    + unfold MALLOC_MAX. lia.
    + unfold EV_SUP_CHAIN, EV_ARG_S, EV_ANSWER, EV_HAND_BACK, EV_XMALLOC in *. lia.
    + unfold LIVE_SUP_CHAIN in HLIVE. pose proof (LA0 (Some (dec id))). pose proof (LA0 (Some (dec (Z.of_nat (length ids))))).
      pose proof (LA0 (Some (dec_list ids))). pose proof (LN0 (snd (sup_chain_m R id ids))). lia.
    + apply (mok_station MT S S4 (XM_SUP_CHAIN MT R id ids) (XM_RECORD MT R) _ MTL HMOK MLS4); [apply XM0; lia|].
      unfold XM_SUP_CHAIN. pose proof (XA0 (Some (dec id))). pose proof (XA0 (Some (dec (Z.of_nat (length ids))))).
      pose proof (XA0 (Some (dec_list ids))). pose proof (XN0 (snd (sup_chain_m R id ids))). lia.
  - intros a Ha. exfalso. exact (inFP_nil a Ha).
  - intros ly' S' W' regs' mem' md' _ a Ha. exfalso. exact (inFP_nil a Ha). }
cbv beta. intros W6 c6 Hwle6 (ly6 & S6 & regs6 & mem6 & md6 & -> & HJ6 & HJc6 & HPv6 & HKx6).
destruct HKx6 as (lst & R10x & Hlst & HpermX & HfreshX & HinbX & HBBX & MLEX).
rewrite R1.
pose proof (proj1 HJ6) as HAR6.
destruct (scs_frame_later fpos ly6 S6 W6 mem6 md6 _ HJ6) as (Hfin6 & EFA6 & EFL6). fold F in EFA6. fold FL in EFL6.
destruct (al_frames _ _ LAWS _ _ _ _ _ 1 fpos HAR6 Hfin6) as (_ & _ & HFpres6 & HFSpres6). rewrite EFA6 in HFpres6, HFSpres6.
change (fs_frame_bytes 1) with 128 in HFpres6, HFSpres6. change (128 / 8) with 16 in HFSpres6.
jafter_call_keep_hi HS 1058%nat regs6 (mrestrict (w_H W6) mem6) HPv6 [0;1;2;3;4;5]%nat HS6.
match type of HS6 with ?tq -> _ => assert (HRK : tq); [|specialize (HS6 HRK); clear HRK] end.
{ cbn [ms_mem restrict mkst]. repeat apply Forall_cons; try apply Forall_nil.
  - eapply (region_kept_fshadow_sub (segs := SEGS) B E3 _ _ _ ly4 S4 W4 (ms_mem ms5) _ ly6 S6 W6 mem6 md6 _ 1041 (SB + F / 8) _ _ _ _ _ 1 fpos HJc6 X1041 Hfin4);
    [ unfold shadow_addr; rewrite EFA4; rewrite <- SB_SHADOW_OFF; lia
    | unfold shadow_addr; rewrite EFA4; rewrite <- SB_SHADOW_OFF; change (fs_frame_bytes 1 / 8) with 16; lia
    | intros a _ HFa; exact (inFP_nil a HFa)
    | intros a Ha; replace a with (shadow_addr F + (a - (SB + F / 8))) by (unfold shadow_addr; rewrite <- SB_SHADOW_OFF; lia);
      apply (proj1 (HFSpres6 (a - (SB + F / 8)) ltac:(lia))) ].
  - eapply (region_kept_frame_sub (segs := SEGS) B E3 _ _ _ ly4 S4 W4 (ms_mem ms5) _ ly6 S6 W6 mem6 md6 _ 1028 F _ _ _ _ _ 1 fpos HJc6 X1028 Hfin4);
    [ rewrite EFA4; lia | rewrite EFA4; change (fs_frame_bytes 1) with 128; lia
    | intros a _ HFa; exact (inFP_nil a HFa)
    | intros a Ha; lia ].
  - eapply (region_kept_stack_sub SEGS B); [exact HJc6 | exact HJ6 | exact X34 | cbn; lia | cbn; rewrite FS; lia | cbn; lia | cbn; lia | cbn; lia |].
    intros a _ HFa. exact (inFP_nil a HFa).
  - eapply (region_kept_stack_sub SEGS B); [exact HJc6 | exact HJ6 | exact X34 | cbn; lia | cbn; rewrite FS; lia | cbn; lia | cbn; lia | cbn; lia |].
    intros a _ HFa. exact (inFP_nil a HFa).
  - eapply (region_kept_stack_sub SEGS B); [exact HJc6 | exact HJ6 | exact X2 | cbn; lia | cbn; rewrite FS; lia | cbn; lia | cbn; lia | cbn; lia |].
    intros a _ HFa. exact (inFP_nil a HFa).
  - eapply (region_kept_stack_sub SEGS B); [exact HJc6 | exact HJ6 | exact X34 | cbn; lia | cbn; rewrite FS; lia | cbn; lia | cbn; lia | cbn; lia |].
    intros a _ HFa. exact (inFP_nil a HFa). }
rewrite <- restrict_mkst_fx in HS6. clear HS. rename HS6 into HS.
remember (havoc E3 1058 (map (getr regs6) CLOB)) as E4 eqn:HE4 in HS.
assert (HEI4 : img_env VAL A_LIM E4) by (rewrite HE4; apply img_env_havoc_hi; [exact HEI3 | unfold A_LIM; lia]).
assert (OLD4 : forall n, (n < 1058)%nat -> ew E4 n = ew E3 n) by (intros n Hn; rewrite HE4; apply ew_havoc_old; exact Hn).
assert (E1062 : ew E4 1062 = getr regs6 10) by (rewrite HE4; reflexivity).
clear HE4.
assert (AG4 : forall n, (n < 1024)%nat -> ew E4 n = ew E n) by (intros n Hn; rewrite OLD4 by lia; exact (AG3 n Hn)).
assert (Y2 : bv_unsigned (ew E4 2) = spZ regs) by (rewrite OLD4 by lia; exact X2).
assert (Y34 : bv_unsigned (ew E4 34) = sp1) by (rewrite OLD4 by lia; exact X34).
assert (Y1028 : bv_unsigned (ew E4 1028) = F) by (rewrite OLD4 by lia; exact X1028).
assert (Y1041 : bv_unsigned (ew E4 1041) = SB + F / 8) by (rewrite OLD4 by lia; exact X1041).
clear R1 R2 R3 R4 R8 R10 R20 HCH5 G1r G1a G3 G4 Qsp5 Hs05.
(* run 4: s6 := the text, unpoison F + 64 (shadow bytes 8, 9), snprintf(F + 64, 16, "%d", id) *)
paj_run_shc RUNP RUNC HS HJ6.
{ scs_awr fpos (spZ regs) sp1 FS Y1041 Y1028 Y2 Y34 EFA6 ltac:(fail "scs_awr: unknown region"). }
rename ms into ms7, mat into mat7, HF into HF7, HFr into HFr7, HG into HG7.
assert (K67 : forall a, 0 <= a < 2 ^ 64 -> ~ (alloc_ceiling <= a < 2 ^ 64) -> ~ (F <= a < F + 128) ->
  ~ (SB + F / 8 <= a < SB + F / 8 + 16) -> rdW W6 (ms_mem ms7) a = rdW W6 mem6 a).
{ intros a Ha H1 H2 H3.
  apply (kept_of_frame (segs := SEGS) E4 _ (w_H W6) mem6 (ms_mem ms7)
    (fun a => (alloc_ceiling <= a < 2 ^ 64) \/ (F <= a < F + 128) \/ (SB + F / 8 <= a < SB + F / 8 + 16)) HFr7); [| lia | tauto].
  intros b wlo whi a' Hin Hrr. vm_compute in Hin.
  repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?Y2, ?Y34, ?Y1028, ?Y1041 in Hrr; lia|]).
  destruct Hin. }
clear HF7 HFr7 HG7.
pmkst HS.
lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?m |} _ => set (md7 := m) in *; clearbody md7 end.
preg HS (1%bv : bv 5) R1. preg HS (2%bv : bv 5) R2. preg HS (10%bv : bv 5) R10. preg HS (11%bv : bv 5) R11.
preg HS (12%bv : bv 5) R12. preg HS (13%bv : bv 5) R13.
preg HS (3%bv : bv 5) R3. preg HS (4%bv : bv 5) R4.
cbn [sv_denot] in R1. rewrite (img_env_codeptr E4 HEI4 24072) in R1.
rewrite scb_denot_off0, AG4, E34 in R2 by lia.
cbn [sv_denot] in R10. rewrite Y1028 in R10.
cbn [sv_denot] in R11.
destruct (scb_vals VOBJS) as (_ & _ & _ & V51 & _ & _ & V79 & _).
rewrite scb_denot_off0, (img_env_atomP E4 292 HEI4 ltac:(unfold A_TEXT, A_LIM; lia)) in R12.
change (VAL 292) with (VAL (A_OBJ 51)) in R12. rewrite V51 in R12.
rewrite scb_denot_off0, AG4, (EE 10%nat 10%bv eq_refl), H10 in R13 by lia.
rewrite scb_denot_off0, AG4, (EE 3%nat 3%bv eq_refl) in R3 by lia.
rewrite scb_denot_off0, AG4, (EE 4%nat 4%bv eq_refl) in R4 by lia.
assert (Qsp7 : spZ (ms_regs ms7) = spZ regs + (sp1 - spZ regs)) by (unfold spZ at 1; rewrite R2, unsigned_lit_small by lia; lia).
assert (G1r : YK0s.ret_ok (getr (ms_regs ms7) 1)) by (rewrite R1; apply ret_ok_codeptr_v; [lia | reflexivity]).
assert (F64 : (F + 64) / 8 = F / 8 + 8) by (replace (F + 64) with (8 * 8 + F) by lia; rewrite Z.div_add_l by lia; lia).
pose proof (st_ok_region_nth E4 _ _ 0 _ HS eq_refl) as HR0. cbn [ms_mem restrict mkst] in HR0.
assert (ZS8 : forall i, 0 <= i < 2 -> rdW W6 (ms_mem ms7) (SB + (F + 64) / 8 + i) = Some 0).
{ intros i Hi. rewrite F64. assert (Hi2 : i = 0 \/ i = 1) by lia.
  destruct Hi2 as [-> | ->].
  - replace (SB + (F / 8 + 8) + 0) with (SB + F / 8 + 8) by lia.
    rewrite (scs_byte_of_region E4 W6 _ 1041 (SB + F / 8) _ _ _ _ _ 8 (SLit 0) HR0 Y1041 ltac:(cbn [In]; tauto)).
    cbn [sv_denot]. rewrite unsigned_lit_small by lia. reflexivity.
  - replace (SB + (F / 8 + 8) + 1) with (SB + F / 8 + 9) by lia.
    rewrite (scs_byte_of_region E4 W6 _ 1041 (SB + F / 8) _ _ _ _ _ 9 (SLit 0) HR0 Y1041 ltac:(cbn [In]; tauto)).
    cbn [sv_denot]. rewrite unsigned_lit_small by lia. reflexivity. }
clear HR0.
pose proof HJ6 as (_ & Hly6 & _ & _ & _ & _ & Hnev6 & _ & _ & _ & _ & _ & _ & HJ6pres & _).
pose proof Hly6 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Eslo6 & _).
pose proof (proj1 HJ6) as HAR6'.
assert (HROD7 : arodata_okP SEGS RLO RHI B (rdW W6 (ms_mem ms7))) by exact (scs_aro _ _ _ _ _ _ _ HJ6).
pose proof (scs_ro_ok_of_aro _ _ _ _ _ HAR6' HROD7) as HROk7.
destruct (scs_sn_eqs id HID) as [Ew1 Eb1].
pose proof (scb_pf_dec_len id HID) as Hdl1.
(* the call of the snprintf wrapper (0x8c334): snprintf(F + 64, 16, "%d", id), at the entry's FP state *)
eapply SRr_bind.
{ eapply (aj_art_own_atF SEGS B LAWS pa_segs_low RtPFCmd.CMD_SNP_K
    (fun a => F + 64 <= a < F + 64 + RtPFShared.sn_len (16 - 1) (PF.pf_dec id)) _ W6 (ms_regs ms7) (ms_mem ms7)
    SUP_CHAIN_STK (spZ regs) (SCB_FP O) ly S W mem md [(1, fpos)] ly6 S6 md7 _ (sp1 - spZ regs) (getr (ms_regs ms7) 1) _
    HJ6 Qsp7 Hsp1b ltac:(lia) ltac:(unfold RtPFCmd.CMD_SNP_K; lia) ltac:(rewrite FS; unfold RtPFCmd.CMD_SNP_K; lia) eq_refl).
  - intros a Ha. rewrite Ew1 in Ha. right; right; right; left. exists 1, fpos. split; [left; reflexivity|].
    left. unfold in_zr; cbn [fst snd]. rewrite EFA6. change (fs_frame_bytes 1) with 128. lia.
  - apply (scs_snp B LAWS HB IMG (ASNPRINTF fx) ly6 S6 W6 (ms_regs ms7) (ms_mem ms7) md7 (F + 64) id fpos).
    + exact (ecall_pre_at SEGS B SUP_CHAIN_STK (spZ regs) (SCB_FP O) ly S W mem md [(1, fpos)] ly6 S6 W6 (ms_mem ms7) md7 _
        (ms_regs ms7) (sp1 - spZ regs) HJ6 Qsp7 Hsp1b ltac:(lia) ltac:(rewrite FS, Hes; lia) G1r
        ltac:(rewrite R3; exact Hgp) ltac:(rewrite R4; exact Htp)).
    + rewrite Qsp7, Eslo6. unfold RtPFCmd.CMD_SNP_K. lia.
    + intros a Ha. rewrite Qsp7 in Ha. apply HJ6pres. unfold RtPFCmd.CMD_SNP_K in Ha. lia.
    + rewrite Qsp7. unfold RtPFCmd.CMD_SNP_K. lia.
    + rewrite Qsp7. lia.
    + exact R10.
    + exact R11.
    + exact R12.
    + exact R13.
    + exact HID.
    + exact HROD7.
    + exact HROk7.
    + exact Hfin6.
    + rewrite EFA6. lia.
    + rewrite EFA6. lia.
    + rewrite Zplus_mod, HF8m. reflexivity.
    + exact ZS8.
    + exact HRM0. }
cbv beta. intros W8 c8 _ (-> & fx1 & regs8 & mem8 & md8 & Hfx1 & -> & HJ8 & HPv8 & (R10s & Hby8) & Hkeep8).
rewrite R1.
pose proof (Z.div_mod F 8 ltac:(lia)) as DF8.
pose proof (proj1 HJ8) as HAR8.
destruct (al_frames _ _ LAWS _ _ _ _ _ 1 fpos HAR8 Hfin6) as (_ & _ & HFpres8 & HFSpres8). rewrite EFA6 in HFpres8, HFSpres8.
change (fs_frame_bytes 1) with 128 in HFpres8, HFSpres8. change (128 / 8) with 16 in HFSpres8.
pose proof HJ8 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJ8pres & _).
assert (HKP8 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp1 - 8192 <= a < sp1) -> ~ (F + 64 <= a < F + 80) ->
  rdW W6 mem8 a = rdW W6 (ms_mem ms7) a).
{ intros a Ha H1 H2. apply Hkeep8; [exact Ha | unfold RtPFCmd.CMD_SNP_K; lia | rewrite Ew1; lia]. }
scs_keep_hi fx HS 1074%nat regs8 (mrestrict (w_H W6) mem8) HPv8 [0;1;2;3;4;5]%nat HS8.
match type of HS8 with ?tq -> _ => assert (HRK : tq); [|specialize (HS8 HRK); clear HRK] end.
{ cbn [ms_mem restrict mkst]. repeat apply Forall_cons; try apply Forall_nil.
  - eapply scs_region_kept_hi; [exact Y1041 | intros a Ha; apply HKP8; unfold SB in *; lia |].
    intros a Ha. replace a with (shadow_addr F + (a - (SB + F / 8))) by (unfold shadow_addr; rewrite <- SB_SHADOW_OFF; lia).
    apply (proj1 (HFSpres8 (a - (SB + F / 8)) ltac:(lia))).
  - eapply scs_region_kept_hi; [exact Y1028 | intros a Ha; apply HKP8; lia | intros a Ha; lia].
  - eapply scs_region_kept_hi; [exact Y34 | intros a Ha; apply HKP8; lia | intros a Ha; apply HJ8pres; rewrite FS; lia].
  - eapply scs_region_kept_hi; [exact Y34 | intros a Ha; apply HKP8; lia | intros a Ha; apply HJ8pres; rewrite FS; lia].
  - eapply scs_region_kept_hi; [exact Y2 | intros a Ha; apply HKP8; lia | intros a Ha; apply HJ8pres; rewrite FS; lia].
  - eapply scs_region_kept_hi; [exact Y34 | intros a Ha; apply HKP8; lia | intros a Ha; apply HJ8pres; rewrite FS; lia]. }
rewrite <- (restrict_mkst_fx (fx := fx)) in HS8. clear HS.
(* from here on the walk runs at the FP state fx1 the snprintf wrapper returned *)
pose proof (st_ok_pi_restrict_xfx fx fx1 _ _ _ _ _ _ _ _ _ HS8) as HS. clear HS8.
pose proof (SRr_run_pi_AJ (fx := fx1) (L := cmd_listing) (PL := PL_cmd) (PI := PI) B LAWS) as RUNP1.
pose proof (SRr_run_pi_AJ_call (fx := fx1) (L := cmd_listing) (PL := PL_cmd) (PI := PI) B LAWS) as RUNC1.
remember (havoc E4 1074 (map (getr regs8) CLOB)) as E5 eqn:HE5 in HS.
assert (HEI5 : img_env VAL A_LIM E5) by (rewrite HE5; apply img_env_havoc_hi; [exact HEI4 | unfold A_LIM; lia]).
assert (OLD5 : forall n, (n < 1074)%nat -> ew E5 n = ew E4 n) by (intros n Hn; rewrite HE5; apply ew_havoc_old; exact Hn).
clear HE5.
assert (AG5 : forall n, (n < 1024)%nat -> ew E5 n = ew E n) by (intros n Hn; rewrite OLD5 by lia; exact (AG4 n Hn)).
assert (Z2 : bv_unsigned (ew E5 2) = spZ regs) by (rewrite OLD5 by lia; exact Y2).
assert (Z34 : bv_unsigned (ew E5 34) = sp1) by (rewrite OLD5 by lia; exact Y34).
assert (Z1028 : bv_unsigned (ew E5 1028) = F) by (rewrite OLD5 by lia; exact Y1028).
assert (Z1041 : bv_unsigned (ew E5 1041) = SB + F / 8) by (rewrite OLD5 by lia; exact Y1041).
assert (Z1046 : ew E5 1046 = w64 (rec_slot R)) by (rewrite OLD5, OLD4, E1046 by lia; exact R10r).
clear R1 R2 R3 R4 R10 R11 R12 R13 G1r Qsp7 ZS8.
(* run 5: a0 := the slot, a1 := F + 64, jal arg_s *)
paj_run_shc RUNP1 RUNC1 HS HJ8.
{ scs_awr fpos (spZ regs) sp1 FS Z1041 Z1028 Z2 Z34 EFA6 ltac:(fail "scs_awr: unknown region"). }
rename ms into ms9, mat into mat9, HF into HF9, HFr into HFr9, HG into HG9.
assert (K89 : forall a, 0 <= a < 2 ^ 64 -> ~ (alloc_ceiling <= a < 2 ^ 64) ->
  ~ (SB + F / 8 <= a < SB + F / 8 + 16) -> rdW W6 (ms_mem ms9) a = rdW W6 mem8 a).
{ intros a Ha H1 H3.
  apply (kept_of_frame (segs := SEGS) E5 _ (w_H W6) mem8 (ms_mem ms9)
    (fun a => (alloc_ceiling <= a < 2 ^ 64) \/ (SB + F / 8 <= a < SB + F / 8 + 16)) HFr9); [| lia | tauto].
  intros b wlo whi a' Hin Hrr. vm_compute in Hin.
  repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?Z2, ?Z34, ?Z1028, ?Z1041 in Hrr; lia|]).
  destruct Hin. }
clear HF9 HFr9 HG9.
pmkst HS.
lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?m |} _ => set (md9 := m) in *; clearbody md9 end.
preg HS (1%bv : bv 5) R1. preg HS (2%bv : bv 5) R2. preg HS (3%bv : bv 5) R3. preg HS (4%bv : bv 5) R4.
preg HS (8%bv : bv 5) R8. preg HS (10%bv : bv 5) R10. preg HS (11%bv : bv 5) R11.
cbn [sv_denot] in R1. rewrite (img_env_codeptr E5 HEI5 24084) in R1.
rewrite scb_denot_off0, AG5, E34 in R2 by lia.
rewrite scb_denot_off0, AG5, (EE 3%nat 3%bv eq_refl) in R3 by lia.
rewrite scb_denot_off0, AG5, (EE 4%nat 4%bv eq_refl) in R4 by lia.
rewrite scb_denot_off0, AG5, Esp in R8 by lia.
rewrite scb_denot_off0, Z1046 in R10.
cbn [sv_denot] in R11. rewrite Z1028 in R11.
pose proof (st_ok_region_nth E5 _ _ 4 _ HS eq_refl) as HR. cbn [ms_mem restrict mkst] in HR.
assert (SVra : rdword (rdW W6 (ms_mem ms9)) (spZ regs - 8) = Some (raZ regs)).
{ apply (rdword_of_val_mem SEGS); [|unfold raZ; apply bv_unsigned_in_range].
  replace (spZ regs - 8) with (spZ regs + -8) by lia.
  refine (field_of_region E5 _ 2 (spZ regs) _ (-104) 0 (-104) 0 (-8) 8%N (SOff 1 0) (raZ regs) HR Z2 _ _ _ _);
  [cbn [In]; tauto | rewrite scb_denot_off0, AG5, (EE 1%nat 1%bv eq_refl) by lia; unfold raZ; symmetry; apply Z_to_bv_bv_unsigned
  | unfold raZ; apply bv_unsigned_in_range | lia]. }
assert (SVs0 : rdword (rdW W6 (ms_mem ms9)) (spZ regs - 16) = Some (s0Z regs)).
{ apply (rdword_of_val_mem SEGS); [|unfold s0Z; apply bv_unsigned_in_range].
  replace (spZ regs - 16) with (spZ regs + -16) by lia.
  refine (field_of_region E5 _ 2 (spZ regs) _ (-104) 0 (-104) 0 (-16) 8%N (SOff 8 0) (s0Z regs) HR Z2 _ _ _ _);
  [cbn [In]; tauto | rewrite scb_denot_off0, AG5, (EE 8%nat 8%bv eq_refl) by lia; unfold s0Z; symmetry; apply Z_to_bv_bv_unsigned
  | unfold s0Z; apply bv_unsigned_in_range | lia]. }
clear HR.
pose proof (st_ok_region_nth E5 _ _ 0 _ HS eq_refl) as HR0. cbn [ms_mem restrict mkst] in HR0.
assert (ZS9 : forall i, 0 <= i < 2 -> rdW W6 (ms_mem ms9) (SB + (F + 64) / 8 + i) = Some 0).
{ intros i Hi. rewrite F64, Z.add_assoc.
  exact (scs_zs2 E5 W6 (ms_mem ms9) (SB + F / 8) _ 8 9 HR0 Z1041 ltac:(cbn [In]; tauto) ltac:(cbn [In]; tauto) eq_refl i Hi). }
clear HR0.
assert (Qsp9 : spZ (ms_regs ms9) = spZ regs + (sp1 - spZ regs)) by (unfold spZ at 1; rewrite R2, unsigned_lit_small by lia; lia).
assert (Hs09 : s0Z (ms_regs ms9) = spZ regs) by (unfold s0Z; rewrite R8, unsigned_lit_small by lia; reflexivity).
destruct (scs_chain ly6 S6 W6 (ms_mem ms9) md9 [(1, fpos)] _ (spZ regs + (sp1 - spZ regs)) HJ8 SVra SVs0 ltac:(lia)) as (ch9 & HCH).
assert (HCH9 : achain ly6 (rdW W6 (ms_mem ms9)) (spZ regs + (sp1 - spZ regs)) (s0Z (ms_regs ms9)) ch9) by (rewrite Hs09; exact HCH).
clear HCH SVra SVs0.
assert (G1r : YK0s.ret_ok (getr (ms_regs ms9) 1)) by (rewrite R1; apply ret_ok_codeptr_v; [lia | reflexivity]).
assert (G1a : 4096 <= bv_unsigned (getr (ms_regs ms9) 1)) by (rewrite R1, unsigned_lit_small; lia).
assert (G3 : getr (ms_regs ms9) 3 = w64 (as_gp B)) by (rewrite R3; exact Hgp).
assert (G4 : getr (ms_regs ms9) 4 = w64 (as_tp B)) by (rewrite R4; exact Htp).
pose proof (proj1 HJ8) as HAR9.
destruct (al_frames _ _ LAWS _ _ _ _ _ 1 fpos HAR9 Hfin6) as (_ & _ & HFpres9 & _). rewrite EFA6 in HFpres9.
change (fs_frame_bytes 1) with 128 in HFpres9.
pose proof HJ8 as (_ & _ & _ & _ & _ & _ & Hnev9 & _).
assert (HROD9 : arodata_okP SEGS RLO RHI B (rdW W6 (ms_mem ms9))) by exact (scs_aro _ _ _ _ _ _ _ HJ8).
pose proof (scs_ro_ok_of_aro _ _ _ _ _ HAR9 HROD9) as HROk9.
(* the recorder's bytes from record()'s return to this call *)
assert (HO1in4 : forall pn, In pn O1 -> In pn (ablocks B ly4 S4)) by exact (scs_O_in _ _ _ _ _ HREP1).
assert (H46 : forall pn, In pn (ablocks B ly4 S4) -> In pn (ablocks B ly6 S6))
  by (intros pn Hpn; apply (Permutation_in _ (Permutation_sym HpermX)); right; exact Hpn).
pose proof HJc6 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & XF2 & XF3 & _).
assert (KRA9 : forall a, scs_RX O1 a -> rdW W6 (ms_mem ms9) a = rdW W4 mem4 a).
{ intros a Ha. destruct (scs_RX_loc ly4 S4 W4 mem4 md4 O1 fpos a HAR4 HO1in4 Hfin4 Ha) as (Hlo & HnF & HnS & Hcase).
  rewrite EFA4 in HnF, HnS.
  rewrite (K89 a ltac:(lia) ltac:(lia) HnS).
  rewrite (HKP8 a ltac:(lia) ltac:(lia) ltac:(lia)).
  rewrite (K67 a ltac:(lia) ltac:(lia) HnF HnS).
  destruct Hcase as [(Hi & Ho & He) | (p & m & Hpm & Hpa)].
  - rewrite (XF3 a Hi Ho He (fp_spares_closed [] a (sink_closed_pos [] (Forall_nil _)) (inFP_nil a))).
    exact (K45 a ltac:(lia) ltac:(lia) HnF HnS).
  - replace a with (p + (a - p)) by lia.
    rewrite (XF2 p m (a - p) (HO1in4 _ Hpm) (H46 _ (HO1in4 _ Hpm)) ltac:(lia) (inFP_nil _)).
    replace (p + (a - p)) with a by lia. exact (K45 a ltac:(lia) ltac:(lia) HnF HnS). }
assert (HREPA9 : rec_repA B ly6 S6 (rdW W6 (ms_mem ms9)) (rec_record R 17 []) O1)
  by exact (scs_rec_repA_ext ly4 S4 (rdW W4 mem4) ly6 S6 _ _ O1 HREP1 (fun pn Hpn => H46 _ (HO1in4 _ Hpn)) KRA9).
(* the printed id in the frame at F + 64 *)
rewrite Ew1, Eb1 in Hby8.
pose proof (dec_length id HID) as Hdl1'. rewrite <- (scs_dec_len id HID) in Hdl1'.
assert (HBy9 : forall i, 0 <= i < Z.of_nat (length (PF.pf_dec id ++ [0])) ->
  rdW W6 (ms_mem ms9) (F + 64 + i) = Some (nth (Z.to_nat i) (PF.pf_dec id ++ [0]) 0)).
{ intros i Hi. rewrite length_app in Hi. cbn [length] in Hi.
  rewrite (K89 (F + 64 + i) ltac:(lia) ltac:(lia) ltac:(unfold SB in *; lia)). apply Hby8. lia. }
assert (HSTR9 : astr_atR (rdW W6 (ms_mem ms9)) (F + 64) (dec id)).
{ split; [|exact (dec_no0 id)]. rewrite <- (scs_dec_bytes id HID). exact (scs_abytes_of_view W6 (ms_mem ms9) (F + 64) _ HBy9). }
assert (HAFO9 : afobj SEGS B ly6 S6 W6 (ms_mem ms9) (F + 64) (Z.of_nat (length (dec id)) + 1)).
{ rewrite <- (scs_dec_len id HID). split.
  - exists 1, fpos. split; [exact Hfin6|]. split; [lia|]. rewrite EFA6. split; [exact HF8m|]. split; [lia|].
    change (fs_frame_bytes 1) with 128. lia.
  - split; [rewrite Zplus_mod, HF8m; reflexivity|]. apply scs_rng_of_zs; [lia | rewrite Zplus_mod, HF8m; reflexivity | lia | exact ZS9]. }
assert (HTL9 : atail_vis SEGS W6 (ms_mem ms9) (F + 64 + Z.of_nat (length (dec id)))).
{ rewrite <- (scs_dec_len id HID). intros a Ha. apply (aview_some_of_apresent SEGS). apply (proj1 (HFpres9 a ltac:(
    pose proof (Z.div_mod (F + 64 + Z.of_nat (length (PF.pf_dec id))) 8 ltac:(lia));
    pose proof (Z.mod_pos_bound (F + 64 + Z.of_nat (length (PF.pf_dec id))) 8 ltac:(lia)); lia))). }
assert (HAS : ARG_S_STK = 16464) by (vm_compute; reflexivity).
assert (MLS6 : mo_le MT S S6 (XM_RECORD MT R + XM_XMALLOC MT (12 * Z.of_nat (length ids) + 1)))
  by exact (mo_le_trans MT MTL S S4 S6 _ _ MLS4 MLEX).
pose proof (scs_ncalls _ _ _ _ _ HREP) as HC1.
rewrite (proj1 (proj2 (proj2 (scb_sigs cmd_sig_prog_PB)))).
(* the call of arg_s(slot, F + 64) (0x8c340), at fx1 *)
eapply SRr_bind.
{ eapply (cl_callS_wide (fx := fx1) B LAWS W6 (ms_regs ms9) (ms_mem ms9) _ SUP_CHAIN_STK (spZ regs) (SCB_FP O) ly S W mem md [(1, fpos)] ly6 S6 _ _
    ARG_S_STK _ EV_ARG_S (sp1 - spZ regs) (getr (ms_regs ms9) 1) ch9 _ HJ8 Qsp9 Hsp1b ltac:(lia)
    ltac:(rewrite HAS; lia) ltac:(rewrite HAS, FS; lia) G3 G4 eq_refl G1r G1a HCH9).
  - intros HPRE1. pose proof (TARG_S fx1 ly6 S6 W6 (ms_regs ms9) (ms_mem ms9) _ ch9 (rec_slot R) (F + 64) 17 [] (Some (dec id)) R O1 HPRE1) as T.
    cbv zeta in T. unfold apost_base in T. apply T.
    + exact HROD9.
    + exact HROk9.
    + exact R10.
    + exact R11.
    + reflexivity.
    + exact HREPA9.
    + right. exists (dec id). split; [reflexivity|]. split; [exact HSTR9|].
      split; [pose proof (dec_length id HID); unfold LMAX; lia | exact HAFO9].
    + intros x Hx. injection Hx as <-. exact HTL9.
    + unfold EV_SUP_CHAIN, EV_ARG_S, EV_ANSWER, EV_HAND_BACK, EV_XMALLOC in *. lia.
    + unfold LIVE_SUP_CHAIN in HLIVE. pose proof (LA0 (Some (dec (Z.of_nat (length ids))))).
      pose proof (LA0 (Some (dec_list ids))). pose proof (LN0 (snd (sup_chain_m R id ids))). lia.
    + apply (mok_station MT S S6 (XM_SUP_CHAIN MT R id ids) _ _ MTL HMOK MLS6 (XA0 _)).
      unfold XM_SUP_CHAIN. pose proof (XA0 (Some (dec (Z.of_nat (length ids))))).
      pose proof (XA0 (Some (dec_list ids))). pose proof (XN0 (snd (sup_chain_m R id ids))). lia.
  - intros a Ha. unfold REC_ARGS_MAX in Ha. cbn [length Z.of_nat Z.ltb Z.compare] in Ha.
    apply inFP_cons in Ha as [Ha | Ha].
    { apply (scs_awr_slot _ _ _ _ _ _ _ R a HC1). unfold CALL_OFF_NARGS, CALL_SIZE in *. lia. }
    apply inFP_cons in Ha as [Ha | Ha]; [|exfalso; exact (inFP_nil a Ha)].
    apply (scs_awr_slot _ _ _ _ _ _ _ R a HC1). unfold CALL_OFF_ARGS, CALL_SIZE in *. lia.
  - intros ly' S' W' regs' mem' md' _ a Ha Hw _. exfalso.
    unfold REC_ARGS_MAX in Ha. cbn [length Z.of_nat Z.ltb Z.compare] in Ha.
    assert (Hsl : rec_slot R <= a < rec_slot R + CALL_SIZE).
    { apply inFP_cons in Ha as [Ha | Ha]; [unfold CALL_OFF_NARGS, CALL_SIZE in *; lia|].
      apply inFP_cons in Ha as [Ha | Ha]; [unfold CALL_OFF_ARGS, CALL_SIZE in *; lia | exact (False_ind _ (inFP_nil a Ha))]. }
    destruct (scs_slot_bounds R HC1) as [Hs | Hs]; [unfold A_G_REC, OFF_CALLS, CALL_SIZE, REC_SIZE in *; rewrite FS in Hw; lia|].
    rewrite Hs in Hsl. unfold A_REC_SPILL, CALL_SIZE in Hsl. rewrite FS in Hw. lia. }
cbv beta. intros W10 c10 Hwle10 (ly10 & S10 & regs10 & mem10 & md10 & -> & HJ10 & HJc10 & HPv10 & HKa10).
destruct HKa10 as (HBB10 & MLE10 & [(Hc6 & _) | (_ & p1 & Hp1 & Hperm10 & Hfresh10 & HREP10)]).
{ exfalso. unfold REC_ARGS_MAX in Hc6. cbn [length Z.of_nat] in Hc6. lia. }
cbn [app sarg] in Hperm10, Hfresh10, HREP10.
rewrite R1.
(* arg_s's footprint (the slot) lies below alloc_ceiling, apart from the frame and its shadow *)
assert (FPA : forall (A : list (list byte)) a, (length A <= 1)%nat ->
  inFP (if Z.of_nat (length A) <? REC_ARGS_MAX
        then [(rec_slot R + CALL_OFF_NARGS, rec_slot R + CALL_OFF_NARGS + 4);
              (rec_slot R + CALL_OFF_ARGS + 8 * Z.of_nat (length A), rec_slot R + CALL_OFF_ARGS + 8 * Z.of_nat (length A) + 8)]
        else []) a ->
  0 <= a < alloc_ceiling /\ ~ (F <= a < F + 128) /\ ~ (SB + F / 8 <= a < SB + F / 8 + 16)).
{ intros A a HA Ha. pose proof (scs_argfp_slot R A a HA Ha) as Hs.
  destruct (scs_RX_loc ly6 S6 W6 mem8 md8 [] fpos a HAR8 (fun pn H => False_ind _ H) Hfin6 (scs_slot_RX R [] a HC1 Hs))
    as (Hlo & HnF & HnS & _).
  rewrite EFA6 in HnF, HnS. lia. }
pose proof (proj1 HJ10) as HAR10.
destruct (scs_frame_later fpos ly10 S10 W10 mem10 md10 _ HJ10) as (Hfin10 & EFA10 & EFL10). fold F in EFA10. fold FL in EFL10.
destruct (al_frames _ _ LAWS _ _ _ _ _ 1 fpos HAR10 Hfin10) as (_ & _ & HFpres10 & HFSpres10). rewrite EFA10 in HFpres10, HFSpres10.
change (fs_frame_bytes 1) with 128 in HFpres10, HFSpres10. change (128 / 8) with 16 in HFSpres10.
scs_keep_hi fx1 HS 1090%nat regs10 (mrestrict (w_H W10) mem10) HPv10 [0;1;2;3;4;5]%nat HS10.
match type of HS10 with ?tq -> _ => assert (HRK : tq); [|specialize (HS10 HRK); clear HRK] end.
{ cbn [ms_mem restrict mkst]. repeat apply Forall_cons; try apply Forall_nil.
  - eapply (region_kept_fshadow_sub (segs := SEGS) B E5 _ _ _ ly6 S6 W6 (ms_mem ms9) _ ly10 S10 W10 mem10 md10 _ 1041 (SB + F / 8) _ _ _ _ _ 1 fpos HJc10 Z1041 Hfin6);
    [ unfold shadow_addr; rewrite EFA6; rewrite <- SB_SHADOW_OFF; lia
    | unfold shadow_addr; rewrite EFA6; rewrite <- SB_SHADOW_OFF; change (fs_frame_bytes 1 / 8) with 16; lia
    | intros a Ha HFa; destruct (FPA [] a ltac:(cbn; lia) HFa) as (_ & _ & HnS); lia
    | intros a Ha; replace a with (shadow_addr F + (a - (SB + F / 8))) by (unfold shadow_addr; rewrite <- SB_SHADOW_OFF; lia);
      apply (proj1 (HFSpres10 (a - (SB + F / 8)) ltac:(lia))) ].
  - eapply (region_kept_frame_sub (segs := SEGS) B E5 _ _ _ ly6 S6 W6 (ms_mem ms9) _ ly10 S10 W10 mem10 md10 _ 1028 F _ _ _ _ _ 1 fpos HJc10 Z1028 Hfin6);
    [ rewrite EFA6; lia | rewrite EFA6; change (fs_frame_bytes 1) with 128; lia
    | intros a Ha HFa; destruct (FPA [] a ltac:(cbn; lia) HFa) as (_ & HnF & _); lia
    | intros a Ha; lia ].
  - eapply (region_kept_stack_sub SEGS B); [exact HJc10 | exact HJ10 | exact Z34 | cbn; lia | cbn; rewrite FS; lia | cbn; lia | cbn; lia | cbn; lia |].
    intros a Ha HFa. destruct (FPA [] a ltac:(cbn; lia) HFa) as (Hlo & _). lia.
  - eapply (region_kept_stack_sub SEGS B); [exact HJc10 | exact HJ10 | exact Z34 | cbn; lia | cbn; rewrite FS; lia | cbn; lia | cbn; lia | cbn; lia |].
    intros a Ha HFa. destruct (FPA [] a ltac:(cbn; lia) HFa) as (Hlo & _). lia.
  - eapply (region_kept_stack_sub SEGS B); [exact HJc10 | exact HJ10 | exact Z2 | cbn; lia | cbn; rewrite FS; lia | cbn; lia | cbn; lia | cbn; lia |].
    intros a Ha HFa. destruct (FPA [] a ltac:(cbn; lia) HFa) as (Hlo & _). lia.
  - eapply (region_kept_stack_sub SEGS B); [exact HJc10 | exact HJ10 | exact Z34 | cbn; lia | cbn; rewrite FS; lia | cbn; lia | cbn; lia | cbn; lia |].
    intros a Ha HFa. destruct (FPA [] a ltac:(cbn; lia) HFa) as (Hlo & _). lia. }
rewrite <- (restrict_mkst_fx (fx := fx1)) in HS10. clear HS. rename HS10 into HS.
remember (havoc E5 1090 (map (getr regs10) CLOB)) as E6 eqn:HE6 in HS.
assert (HEI6 : img_env VAL A_LIM E6) by (rewrite HE6; apply img_env_havoc_hi; [exact HEI5 | unfold A_LIM; lia]).
assert (OLD6 : forall n, (n < 1090)%nat -> ew E6 n = ew E5 n) by (intros n Hn; rewrite HE6; apply ew_havoc_old; exact Hn).
clear HE6.
assert (AG6 : forall n, (n < 1024)%nat -> ew E6 n = ew E n) by (intros n Hn; rewrite OLD6 by lia; exact (AG5 n Hn)).
assert (T2 : bv_unsigned (ew E6 2) = spZ regs) by (rewrite OLD6 by lia; exact Z2).
assert (T34 : bv_unsigned (ew E6 34) = sp1) by (rewrite OLD6 by lia; exact Z34).
assert (T1028 : bv_unsigned (ew E6 1028) = F) by (rewrite OLD6 by lia; exact Z1028).
assert (T1041 : bv_unsigned (ew E6 1041) = SB + F / 8) by (rewrite OLD6 by lia; exact Z1041).
assert (T1046 : ew E6 1046 = w64 (rec_slot R)) by (rewrite OLD6 by lia; exact Z1046).
clear R1 R2 R3 R4 R8 R10 R11 G1r G1a G3 G4 Qsp9 Hs09 HCH9 ZS9.
(* run 6: unpoison F + 32 (shadow bytes 4, 5), poison F + 64 (8, 9), snprintf(F + 32, 16, "%d", n) *)
paj_run_shc RUNP1 RUNC1 HS HJ10.
{ scs_awr fpos (spZ regs) sp1 FS T1041 T1028 T2 T34 EFA10 ltac:(fail "scs_awr: unknown region"). }
rename ms into ms11, mat into mat11, HF into HF11, HFr into HFr11, HG into HG11.
assert (K1011 : forall a, 0 <= a < 2 ^ 64 -> ~ (alloc_ceiling <= a < 2 ^ 64) ->
  ~ (SB + F / 8 <= a < SB + F / 8 + 16) -> rdW W10 (ms_mem ms11) a = rdW W10 mem10 a).
{ intros a Ha H1 H3.
  apply (kept_of_frame (segs := SEGS) E6 _ (w_H W10) mem10 (ms_mem ms11)
    (fun a => (alloc_ceiling <= a < 2 ^ 64) \/ (SB + F / 8 <= a < SB + F / 8 + 16)) HFr11); [| lia | tauto].
  intros b wlo whi a' Hin Hrr. vm_compute in Hin.
  repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?T2, ?T34, ?T1028, ?T1041 in Hrr; lia|]).
  destruct Hin. }
clear HF11 HFr11 HG11.
pmkst HS.
lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?m |} _ => set (md11 := m) in *; clearbody md11 end.
preg HS (1%bv : bv 5) R1. preg HS (2%bv : bv 5) R2. preg HS (3%bv : bv 5) R3. preg HS (4%bv : bv 5) R4.
preg HS (10%bv : bv 5) R10. preg HS (11%bv : bv 5) R11. preg HS (12%bv : bv 5) R12. preg HS (13%bv : bv 5) R13.
cbn [sv_denot] in R1. rewrite (img_env_codeptr E6 HEI6 24120) in R1.
rewrite scb_denot_off0, AG6, E34 in R2 by lia.
rewrite scb_denot_off0, AG6, (EE 3%nat 3%bv eq_refl) in R3 by lia.
rewrite scb_denot_off0, AG6, (EE 4%nat 4%bv eq_refl) in R4 by lia.
cbn [sv_denot] in R10. rewrite T1028 in R10.
cbn [sv_denot] in R11.
rewrite scb_denot_off0, (img_env_atomP E6 292 HEI6 ltac:(unfold A_TEXT, A_LIM; lia)) in R12.
change (VAL 292) with (VAL (A_OBJ 51)) in R12. rewrite V51 in R12.
rewrite scb_denot_off0, AG6, (EE 12%nat 12%bv eq_refl), H12 in R13 by lia.
assert (Qsp11 : spZ (ms_regs ms11) = spZ regs + (sp1 - spZ regs)) by (unfold spZ at 1; rewrite R2, unsigned_lit_small by lia; lia).
assert (G1r : YK0s.ret_ok (getr (ms_regs ms11) 1)) by (rewrite R1; apply ret_ok_codeptr_v; [lia | reflexivity]).
assert (F32 : (F + 32) / 8 = F / 8 + 4) by (replace (F + 32) with (4 * 8 + F) by lia; rewrite Z.div_add_l by lia; lia).
pose proof (st_ok_region_nth E6 _ _ 0 _ HS eq_refl) as HR0. cbn [ms_mem restrict mkst] in HR0.
assert (ZS11 : forall i, 0 <= i < 2 -> rdW W10 (ms_mem ms11) (SB + (F + 32) / 8 + i) = Some 0).
{ intros i Hi. rewrite F32, Z.add_assoc.
  exact (scs_zs2 E6 W10 (ms_mem ms11) (SB + F / 8) _ 4 5 HR0 T1041 ltac:(cbn [In]; tauto) ltac:(cbn [In]; tauto) eq_refl i Hi). }
clear HR0.
pose proof HJ10 as (_ & Hly10 & _ & _ & _ & _ & Hnev10 & _ & _ & _ & _ & _ & _ & HJ10pres & _).
pose proof Hly10 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Eslo10 & _).
pose proof (proj1 HJ10) as HAR11.
assert (HROD11 : arodata_okP SEGS RLO RHI B (rdW W10 (ms_mem ms11))) by exact (scs_aro _ _ _ _ _ _ _ HJ10).
pose proof (scs_ro_ok_of_aro _ _ _ _ _ HAR11 HROD11) as HROk11.
assert (Hn31 : -2 ^ 31 <= Z.of_nat (length ids) < 2 ^ 31) by lia.
destruct (scs_sn_eqs (Z.of_nat (length ids)) Hn31) as [Ew2 Eb2].
pose proof (scb_pf_dec_len (Z.of_nat (length ids)) Hn31) as Hdl2.
(* the call of the snprintf wrapper (0x8c364): snprintf(F + 32, 16, "%d", n), at fx1 *)
eapply SRr_bind.
{ eapply (aj_art_own_atF (fx := fx1) SEGS B LAWS pa_segs_low RtPFCmd.CMD_SNP_K
    (fun a => F + 32 <= a < F + 32 + RtPFShared.sn_len (16 - 1) (PF.pf_dec (Z.of_nat (length ids)))) _ W10 (ms_regs ms11) (ms_mem ms11)
    SUP_CHAIN_STK (spZ regs) (SCB_FP O) ly S W mem md [(1, fpos)] ly10 S10 md11 _ (sp1 - spZ regs) (getr (ms_regs ms11) 1) _
    HJ10 Qsp11 Hsp1b ltac:(lia) ltac:(unfold RtPFCmd.CMD_SNP_K; lia) ltac:(rewrite FS; unfold RtPFCmd.CMD_SNP_K; lia) eq_refl).
  - intros a Ha. rewrite Ew2 in Ha. right; right; right; left. exists 1, fpos. split; [left; reflexivity|].
    left. unfold in_zr; cbn [fst snd]. rewrite EFA10. change (fs_frame_bytes 1) with 128. lia.
  - apply (scs_snp (fx := fx1) B LAWS HB IMG (ASNPRINTF fx1) ly10 S10 W10 (ms_regs ms11) (ms_mem ms11) md11 (F + 32)
      (Z.of_nat (length ids)) fpos).
    + exact (ecall_pre_at SEGS B SUP_CHAIN_STK (spZ regs) (SCB_FP O) ly S W mem md [(1, fpos)] ly10 S10 W10 (ms_mem ms11) md11 _
        (ms_regs ms11) (sp1 - spZ regs) HJ10 Qsp11 Hsp1b ltac:(lia) ltac:(rewrite FS, Hes; lia) G1r
        ltac:(rewrite R3; exact Hgp) ltac:(rewrite R4; exact Htp)).
    + rewrite Qsp11, Eslo10. unfold RtPFCmd.CMD_SNP_K. lia.
    + intros a Ha. rewrite Qsp11 in Ha. apply HJ10pres. unfold RtPFCmd.CMD_SNP_K in Ha. lia.
    + rewrite Qsp11. unfold RtPFCmd.CMD_SNP_K. lia.
    + rewrite Qsp11. lia.
    + exact R10.
    + exact R11.
    + exact R12.
    + exact R13.
    + exact Hn31.
    + exact HROD11.
    + exact HROk11.
    + exact Hfin10.
    + rewrite EFA10. lia.
    + rewrite EFA10. lia.
    + rewrite Zplus_mod, HF8m. reflexivity.
    + exact ZS11.
    + exact (fxrel_frm0 fx fx1 HRM0 Hfx1). }
cbv beta. intros W12 c12 _ (-> & fx2 & regs12 & mem12 & md12 & Hfx2 & -> & HJ12 & HPv12 & (R10s2 & Hby12) & Hkeep12).
rewrite R1.
pose proof (proj1 HJ12) as HAR12.
destruct (al_frames _ _ LAWS _ _ _ _ _ 1 fpos HAR12 Hfin10) as (_ & _ & HFpres12 & HFSpres12). rewrite EFA10 in HFpres12, HFSpres12.
change (fs_frame_bytes 1) with 128 in HFpres12, HFSpres12. change (128 / 8) with 16 in HFSpres12.
pose proof HJ12 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJ12pres & _).
assert (HKP12 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp1 - 8192 <= a < sp1) -> ~ (F + 32 <= a < F + 48) ->
  rdW W10 mem12 a = rdW W10 (ms_mem ms11) a).
{ intros a Ha H1 H2. apply Hkeep12; [exact Ha | unfold RtPFCmd.CMD_SNP_K; lia | rewrite Ew2; lia]. }
scs_keep_hi fx1 HS 1106%nat regs12 (mrestrict (w_H W10) mem12) HPv12 [0;1;2;3;4;5]%nat HS12.
match type of HS12 with ?tq -> _ => assert (HRK : tq); [|specialize (HS12 HRK); clear HRK] end.
{ cbn [ms_mem restrict mkst]. repeat apply Forall_cons; try apply Forall_nil.
  - eapply scs_region_kept_hi; [exact T1041 | intros a Ha; apply HKP12; unfold SB in *; lia |].
    intros a Ha. replace a with (shadow_addr F + (a - (SB + F / 8))) by (unfold shadow_addr; rewrite <- SB_SHADOW_OFF; lia).
    apply (proj1 (HFSpres12 (a - (SB + F / 8)) ltac:(lia))).
  - eapply scs_region_kept_hi; [exact T1028 | intros a Ha; apply HKP12; lia | intros a Ha; lia].
  - eapply scs_region_kept_hi; [exact T34 | intros a Ha; apply HKP12; lia | intros a Ha; apply HJ12pres; rewrite FS; lia].
  - eapply scs_region_kept_hi; [exact T34 | intros a Ha; apply HKP12; lia | intros a Ha; apply HJ12pres; rewrite FS; lia].
  - eapply scs_region_kept_hi; [exact T2 | intros a Ha; apply HKP12; lia | intros a Ha; apply HJ12pres; rewrite FS; lia].
  - eapply scs_region_kept_hi; [exact T34 | intros a Ha; apply HKP12; lia | intros a Ha; apply HJ12pres; rewrite FS; lia]. }
rewrite <- (restrict_mkst_fx (fx := fx1)) in HS12. clear HS.
(* from here on the walk runs at the FP state fx2 the second snprintf returned *)
pose proof (st_ok_pi_restrict_xfx fx1 fx2 _ _ _ _ _ _ _ _ _ HS12) as HS. clear HS12.
pose proof (SRr_run_pi_AJ (fx := fx2) (L := cmd_listing) (PL := PL_cmd) (PI := PI) B LAWS) as RUNP2.
pose proof (SRr_run_pi_AJ_call (fx := fx2) (L := cmd_listing) (PL := PL_cmd) (PI := PI) B LAWS) as RUNC2.
remember (havoc E6 1106 (map (getr regs12) CLOB)) as E7 eqn:HE7 in HS.
assert (HEI7 : img_env VAL A_LIM E7) by (rewrite HE7; apply img_env_havoc_hi; [exact HEI6 | unfold A_LIM; lia]).
assert (OLD7 : forall n, (n < 1106)%nat -> ew E7 n = ew E6 n) by (intros n Hn; rewrite HE7; apply ew_havoc_old; exact Hn).
clear HE7.
assert (AG7 : forall n, (n < 1024)%nat -> ew E7 n = ew E n) by (intros n Hn; rewrite OLD7 by lia; exact (AG6 n Hn)).
assert (U2 : bv_unsigned (ew E7 2) = spZ regs) by (rewrite OLD7 by lia; exact T2).
assert (U34' : bv_unsigned (ew E7 34) = sp1) by (rewrite OLD7 by lia; exact T34).
assert (U1028 : bv_unsigned (ew E7 1028) = F) by (rewrite OLD7 by lia; exact T1028).
assert (U1041 : bv_unsigned (ew E7 1041) = SB + F / 8) by (rewrite OLD7 by lia; exact T1041).
assert (U1046 : ew E7 1046 = w64 (rec_slot R)) by (rewrite OLD7 by lia; exact T1046).
clear R1 R2 R3 R4 R10 R11 R12 R13 G1r Qsp11 ZS11.
(* run 7: the slot to s1 + 8, a0 := the slot, a1 := F + 32, jal arg_s *)
paj_run_shc RUNP2 RUNC2 HS HJ12.
{ scs_awr fpos (spZ regs) sp1 FS U1041 U1028 U2 U34' EFA10 ltac:(fail "scs_awr: unknown region"). }
rename ms into ms13, mat into mat13, HF into HF13, HFr into HFr13, HG into HG13.
assert (K1213 : forall a, 0 <= a < 2 ^ 64 -> ~ (alloc_ceiling <= a < 2 ^ 64) ->
  ~ (SB + F / 8 <= a < SB + F / 8 + 16) -> rdW W10 (ms_mem ms13) a = rdW W10 mem12 a).
{ intros a Ha H1 H3.
  apply (kept_of_frame (segs := SEGS) E7 _ (w_H W10) mem12 (ms_mem ms13)
    (fun a => (alloc_ceiling <= a < 2 ^ 64) \/ (SB + F / 8 <= a < SB + F / 8 + 16)) HFr13); [| lia | tauto].
  intros b wlo whi a' Hin Hrr. vm_compute in Hin.
  repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?U2, ?U34', ?U1028, ?U1041 in Hrr; lia|]).
  destruct Hin. }
clear HF13 HFr13 HG13.
pmkst HS.
lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?m |} _ => set (md13 := m) in *; clearbody md13 end.
preg HS (1%bv : bv 5) R1. preg HS (2%bv : bv 5) R2. preg HS (3%bv : bv 5) R3. preg HS (4%bv : bv 5) R4.
preg HS (8%bv : bv 5) R8. preg HS (10%bv : bv 5) R10. preg HS (11%bv : bv 5) R11.
cbn [sv_denot] in R1. rewrite (img_env_codeptr E7 HEI7 24136) in R1.
rewrite scb_denot_off0, AG7, E34 in R2 by lia.
rewrite scb_denot_off0, AG7, (EE 3%nat 3%bv eq_refl) in R3 by lia.
rewrite scb_denot_off0, AG7, (EE 4%nat 4%bv eq_refl) in R4 by lia.
rewrite scb_denot_off0, AG7, Esp in R8 by lia.
rewrite scb_denot_off0, U1046 in R10.
cbn [sv_denot] in R11. rewrite U1028 in R11.
pose proof (st_ok_region_nth E7 _ _ 4 _ HS eq_refl) as HR. cbn [ms_mem restrict mkst] in HR.
assert (SVra : rdword (rdW W10 (ms_mem ms13)) (spZ regs - 8) = Some (raZ regs)).
{ apply (rdword_of_val_mem SEGS); [|unfold raZ; apply bv_unsigned_in_range].
  replace (spZ regs - 8) with (spZ regs + -8) by lia.
  refine (field_of_region E7 _ 2 (spZ regs) _ (-104) 0 (-104) 0 (-8) 8%N (SOff 1 0) (raZ regs) HR U2 _ _ _ _);
  [cbn [In]; tauto | rewrite scb_denot_off0, AG7, (EE 1%nat 1%bv eq_refl) by lia; unfold raZ; symmetry; apply Z_to_bv_bv_unsigned
  | unfold raZ; apply bv_unsigned_in_range | lia]. }
assert (SVs0 : rdword (rdW W10 (ms_mem ms13)) (spZ regs - 16) = Some (s0Z regs)).
{ apply (rdword_of_val_mem SEGS); [|unfold s0Z; apply bv_unsigned_in_range].
  replace (spZ regs - 16) with (spZ regs + -16) by lia.
  refine (field_of_region E7 _ 2 (spZ regs) _ (-104) 0 (-104) 0 (-16) 8%N (SOff 8 0) (s0Z regs) HR U2 _ _ _ _);
  [cbn [In]; tauto | rewrite scb_denot_off0, AG7, (EE 8%nat 8%bv eq_refl) by lia; unfold s0Z; symmetry; apply Z_to_bv_bv_unsigned
  | unfold s0Z; apply bv_unsigned_in_range | lia]. }
clear HR.
pose proof (st_ok_region_nth E7 _ _ 0 _ HS eq_refl) as HR0. cbn [ms_mem restrict mkst] in HR0.
assert (ZS13 : forall i, 0 <= i < 2 -> rdW W10 (ms_mem ms13) (SB + (F + 32) / 8 + i) = Some 0).
{ intros i Hi. rewrite F32, Z.add_assoc.
  exact (scs_zs2 E7 W10 (ms_mem ms13) (SB + F / 8) _ 4 5 HR0 U1041 ltac:(cbn [In]; tauto) ltac:(cbn [In]; tauto) eq_refl i Hi). }
clear HR0.
assert (Qsp13 : spZ (ms_regs ms13) = spZ regs + (sp1 - spZ regs)) by (unfold spZ at 1; rewrite R2, unsigned_lit_small by lia; lia).
assert (Hs013 : s0Z (ms_regs ms13) = spZ regs) by (unfold s0Z; rewrite R8, unsigned_lit_small by lia; reflexivity).
destruct (scs_chain ly10 S10 W10 (ms_mem ms13) md13 [(1, fpos)] _ (spZ regs + (sp1 - spZ regs)) HJ12 SVra SVs0 ltac:(lia)) as (ch13 & HCH).
assert (HCH13 : achain ly10 (rdW W10 (ms_mem ms13)) (spZ regs + (sp1 - spZ regs)) (s0Z (ms_regs ms13)) ch13) by (rewrite Hs013; exact HCH).
clear HCH SVra SVs0.
assert (G1r : YK0s.ret_ok (getr (ms_regs ms13) 1)) by (rewrite R1; apply ret_ok_codeptr_v; [lia | reflexivity]).
assert (G1a : 4096 <= bv_unsigned (getr (ms_regs ms13) 1)) by (rewrite R1, unsigned_lit_small; lia).
assert (G3 : getr (ms_regs ms13) 3 = w64 (as_gp B)) by (rewrite R3; exact Hgp).
assert (G4 : getr (ms_regs ms13) 4 = w64 (as_tp B)) by (rewrite R4; exact Htp).
pose proof (proj1 HJ12) as HAR13.
destruct (al_frames _ _ LAWS _ _ _ _ _ 1 fpos HAR13 Hfin10) as (_ & _ & HFpres13 & _). rewrite EFA10 in HFpres13.
change (fs_frame_bytes 1) with 128 in HFpres13.
pose proof HJ12 as (_ & _ & _ & _ & _ & _ & Hnev13 & _).
assert (HROD13 : arodata_okP SEGS RLO RHI B (rdW W10 (ms_mem ms13))) by exact (scs_aro _ _ _ _ _ _ _ HJ12).
pose proof (scs_ro_ok_of_aro _ _ _ _ _ HAR13 HROD13) as HROk13.
(* the recorder's bytes from arg_s's return to this call *)
set (m1 := Z.of_nat (length (dec id)) + 1) in *.
assert (HO1in10 : forall pn, In pn ((p1, m1) :: O1) -> In pn (ablocks B ly10 S10)).
{ intros pn [<- | Hpn]; apply (Permutation_in _ (Permutation_sym Hperm10)); [left; reflexivity|].
  right. exact (H46 _ (HO1in4 _ Hpn)). }
assert (KRA13 : forall a, scs_RX ((p1, m1) :: O1) a -> rdW W10 (ms_mem ms13) a = rdW W10 mem10 a).
{ intros a Ha. destruct (scs_RX_loc ly10 S10 W10 mem10 md10 _ fpos a HAR10 HO1in10 Hfin10 Ha) as (Hlo & HnF & HnS & _).
  rewrite EFA10 in HnF, HnS.
  rewrite (K1213 a ltac:(lia) ltac:(lia) HnS).
  rewrite (HKP12 a ltac:(lia) ltac:(lia) ltac:(lia)).
  exact (K1011 a ltac:(lia) ltac:(lia) HnS). }
assert (HREPA13 : rec_repA B ly10 S10 (rdW W10 (ms_mem ms13)) (rec_record R 17 [dec id]) ((p1, m1) :: O1))
  by exact (scs_rec_repA_ext ly10 S10 (rdW W10 mem10) ly10 S10 _ _ _ HREP10 HO1in10 KRA13).
(* the printed n in the frame at F + 32 *)
rewrite Ew2, Eb2 in Hby12.
pose proof (dec_length (Z.of_nat (length ids)) Hn31) as Hdl2'.
pose proof (scs_dec_len (Z.of_nat (length ids)) Hn31) as Edl2.
assert (HBy13 : forall i, 0 <= i < Z.of_nat (length (PF.pf_dec (Z.of_nat (length ids)) ++ [0])) ->
  rdW W10 (ms_mem ms13) (F + 32 + i) = Some (nth (Z.to_nat i) (PF.pf_dec (Z.of_nat (length ids)) ++ [0]) 0)).
{ intros i Hi. rewrite length_app in Hi. cbn [length] in Hi.
  rewrite (K1213 (F + 32 + i) ltac:(lia) ltac:(lia) ltac:(unfold SB in *; lia)). apply Hby12. lia. }
assert (HSTR13 : astr_atR (rdW W10 (ms_mem ms13)) (F + 32) (dec (Z.of_nat (length ids)))).
{ split; [|exact (dec_no0 _)]. rewrite <- (scs_dec_bytes _ Hn31). exact (scs_abytes_of_view W10 (ms_mem ms13) (F + 32) _ HBy13). }
assert (HAFO13 : afobj SEGS B ly10 S10 W10 (ms_mem ms13) (F + 32) (Z.of_nat (length (dec (Z.of_nat (length ids)))) + 1)).
{ rewrite <- Edl2. split.
  - exists 1, fpos. split; [exact Hfin10|]. split; [lia|]. rewrite EFA10. split; [exact HF8m|]. split; [lia|].
    change (fs_frame_bytes 1) with 128. lia.
  - split; [rewrite Zplus_mod, HF8m; reflexivity|]. apply scs_rng_of_zs; [lia | rewrite Zplus_mod, HF8m; reflexivity | lia | exact ZS13]. }
assert (HTL13 : atail_vis SEGS W10 (ms_mem ms13) (F + 32 + Z.of_nat (length (dec (Z.of_nat (length ids)))))).
{ rewrite <- Edl2. intros a Ha. apply (aview_some_of_apresent SEGS). apply (proj1 (HFpres13 a ltac:(
    pose proof (Z.div_mod (F + 32 + Z.of_nat (length (PF.pf_dec (Z.of_nat (length ids))))) 8 ltac:(lia));
    pose proof (Z.mod_pos_bound (F + 32 + Z.of_nat (length (PF.pf_dec (Z.of_nat (length ids))))) 8 ltac:(lia)); lia))). }
assert (MLS10 : mo_le MT S S10 (XM_RECORD MT R + XM_XMALLOC MT (12 * Z.of_nat (length ids) + 1) + XM_ARG_S MT (Some (dec id))))
  by exact (mo_le_trans MT MTL S S6 S10 _ _ MLS6 MLE10).
rewrite (proj1 (proj2 (proj2 (scb_sigs cmd_sig_prog_PB)))).
(* the call of arg_s(slot, F + 32) (0x8c374), at fx2 *)
eapply SRr_bind.
{ eapply (cl_callS_wide (fx := fx2) B LAWS W10 (ms_regs ms13) (ms_mem ms13) _ SUP_CHAIN_STK (spZ regs) (SCB_FP O) ly S W mem md [(1, fpos)] ly10 S10 _ _
    ARG_S_STK _ EV_ARG_S (sp1 - spZ regs) (getr (ms_regs ms13) 1) ch13 _ HJ12 Qsp13 Hsp1b ltac:(lia)
    ltac:(rewrite HAS; lia) ltac:(rewrite HAS, FS; lia) G3 G4 eq_refl G1r G1a HCH13).
  - intros HPRE1. pose proof (TARG_S fx2 ly10 S10 W10 (ms_regs ms13) (ms_mem ms13) _ ch13 (rec_slot R) (F + 32) 17 [dec id]
      (Some (dec (Z.of_nat (length ids)))) R ((p1, m1) :: O1) HPRE1) as T.
    cbv zeta in T. unfold apost_base in T. apply T.
    + exact HROD13.
    + exact HROk13.
    + exact R10.
    + exact R11.
    + reflexivity.
    + exact HREPA13.
    + right. exists (dec (Z.of_nat (length ids))). split; [reflexivity|]. split; [exact HSTR13|].
      split; [unfold LMAX; lia | exact HAFO13].
    + intros x Hx. injection Hx as <-. exact HTL13.
    + unfold EV_SUP_CHAIN, EV_ARG_S, EV_ANSWER, EV_HAND_BACK, EV_XMALLOC in *. lia.
    + unfold LIVE_SUP_CHAIN in HLIVE. pose proof (LA0 (Some (dec_list ids))). pose proof (LN0 (snd (sup_chain_m R id ids))). lia.
    + apply (mok_station MT S S10 (XM_SUP_CHAIN MT R id ids) _ _ MTL HMOK MLS10 (XA0 _)).
      unfold XM_SUP_CHAIN. pose proof (XA0 (Some (dec_list ids))). pose proof (XN0 (snd (sup_chain_m R id ids))). lia.
  - intros a Ha. apply (scs_awr_slot _ _ _ _ _ _ _ R a HC1). exact (scs_argfp_slot R [dec id] a (le_n 1) Ha).
  - intros ly' S' W' regs' mem' md' _ a Ha Hw _. exfalso.
    pose proof (scs_argfp_slot R [dec id] a (le_n 1) Ha) as Hsl.
    destruct (scs_slot_bounds R HC1) as [Hs | Hs]; [unfold A_G_REC, OFF_CALLS, CALL_SIZE, REC_SIZE in *; rewrite FS in Hw; lia|].
    rewrite Hs in Hsl. unfold A_REC_SPILL, CALL_SIZE in Hsl. rewrite FS in Hw. lia. }
cbv beta. intros W14 c14 Hwle14 (ly14 & S14 & regs14 & mem14 & md14 & -> & HJ14 & HJc14 & HPv14 & HKa14).
destruct HKa14 as (HBB14 & MLE14 & [(Hc7 & _) | (_ & p2 & Hp2 & Hperm14 & Hfresh14 & HREP14)]).
{ exfalso. unfold REC_ARGS_MAX in Hc7. cbn [length Z.of_nat] in Hc7. lia. }
cbn [app sarg] in Hperm14, Hfresh14, HREP14.
rewrite R1.
pose proof (proj1 HJ14) as HAR14.
destruct (scs_frame_later fpos ly14 S14 W14 mem14 md14 _ HJ14) as (Hfin14 & EFA14 & EFL14). fold F in EFA14. fold FL in EFL14.
destruct (al_frames _ _ LAWS _ _ _ _ _ 1 fpos HAR14 Hfin14) as (_ & _ & HFpres14 & HFSpres14). rewrite EFA14 in HFpres14, HFSpres14.
change (fs_frame_bytes 1) with 128 in HFpres14, HFSpres14. change (128 / 8) with 16 in HFSpres14.
scs_keep_hi fx2 HS 1122%nat regs14 (mrestrict (w_H W14) mem14) HPv14 [0;1;2;3;4;5]%nat HS14.
match type of HS14 with ?tq -> _ => assert (HRK : tq); [|specialize (HS14 HRK); clear HRK] end.
{ cbn [ms_mem restrict mkst]. repeat apply Forall_cons; try apply Forall_nil.
  - eapply (region_kept_fshadow_sub (segs := SEGS) B E7 _ _ _ ly10 S10 W10 (ms_mem ms13) _ ly14 S14 W14 mem14 md14 _ 1041 (SB + F / 8) _ _ _ _ _ 1 fpos HJc14 U1041 Hfin10);
    [ unfold shadow_addr; rewrite EFA10; rewrite <- SB_SHADOW_OFF; lia
    | unfold shadow_addr; rewrite EFA10; rewrite <- SB_SHADOW_OFF; change (fs_frame_bytes 1 / 8) with 16; lia
    | intros a Ha HFa; destruct (FPA [dec id] a (le_n 1) HFa) as (_ & _ & HnS); lia
    | intros a Ha; replace a with (shadow_addr F + (a - (SB + F / 8))) by (unfold shadow_addr; rewrite <- SB_SHADOW_OFF; lia);
      apply (proj1 (HFSpres14 (a - (SB + F / 8)) ltac:(lia))) ].
  - eapply (region_kept_frame_sub (segs := SEGS) B E7 _ _ _ ly10 S10 W10 (ms_mem ms13) _ ly14 S14 W14 mem14 md14 _ 1028 F _ _ _ _ _ 1 fpos HJc14 U1028 Hfin10);
    [ rewrite EFA10; lia | rewrite EFA10; change (fs_frame_bytes 1) with 128; lia
    | intros a Ha HFa; destruct (FPA [dec id] a (le_n 1) HFa) as (_ & HnF & _); lia
    | intros a Ha; lia ].
  - eapply (region_kept_stack_sub SEGS B); [exact HJc14 | exact HJ14 | exact U34' | cbn; lia | cbn; rewrite FS; lia | cbn; lia | cbn; lia | cbn; lia |].
    intros a Ha HFa. destruct (FPA [dec id] a (le_n 1) HFa) as (Hlo & _). lia.
  - eapply (region_kept_stack_sub SEGS B); [exact HJc14 | exact HJ14 | exact U34' | cbn; lia | cbn; rewrite FS; lia | cbn; lia | cbn; lia | cbn; lia |].
    intros a Ha HFa. destruct (FPA [dec id] a (le_n 1) HFa) as (Hlo & _). lia.
  - eapply (region_kept_stack_sub SEGS B); [exact HJc14 | exact HJ14 | exact U2 | cbn; lia | cbn; rewrite FS; lia | cbn; lia | cbn; lia | cbn; lia |].
    intros a Ha HFa. destruct (FPA [dec id] a (le_n 1) HFa) as (Hlo & _). lia.
  - eapply (region_kept_stack_sub SEGS B); [exact HJc14 | exact HJ14 | exact U34' | cbn; lia | cbn; rewrite FS; lia | cbn; lia | cbn; lia | cbn; lia |].
    intros a Ha HFa. destruct (FPA [dec id] a (le_n 1) HFa) as (Hlo & _). lia. }
rewrite <- (restrict_mkst_fx (fx := fx2)) in HS14. clear HS. rename HS14 into HS.
remember (havoc E7 1122 (map (getr regs14) CLOB)) as E8 eqn:HE8 in HS.
assert (HEI8 : img_env VAL A_LIM E8) by (rewrite HE8; apply img_env_havoc_hi; [exact HEI7 | unfold A_LIM; lia]).
assert (OLD8 : forall n, (n < 1122)%nat -> ew E8 n = ew E7 n) by (intros n Hn; rewrite HE8; apply ew_havoc_old; exact Hn).
clear HE8.
assert (AG8 : forall n, (n < 1024)%nat -> ew E8 n = ew E n) by (intros n Hn; rewrite OLD8 by lia; exact (AG7 n Hn)).
assert (N2 : bv_unsigned (ew E8 2) = spZ regs) by (rewrite OLD8 by lia; exact U2).
assert (N34 : bv_unsigned (ew E8 34) = sp1) by (rewrite OLD8 by lia; exact U34').
assert (N1028 : bv_unsigned (ew E8 1028) = F) by (rewrite OLD8 by lia; exact U1028).
assert (N1041 : bv_unsigned (ew E8 1041) = SB + F / 8) by (rewrite OLD8 by lia; exact U1041).
assert (N1046 : ew E8 1046 = w64 (rec_slot R)) by (rewrite OLD8 by lia; exact U1046).
assert (E8_1062 : ew E8 1062 = Z_to_bv 64 lst) by (rewrite OLD8, OLD7, OLD6, OLD5 by lia; rewrite E1062; exact R10x).
assert (N1062 : bv_unsigned (ew E8 1062) = lst) by (rewrite E8_1062; apply unsigned_lit_small; lia).
clear R1 R2 R3 R4 R8 R10 R11 G1r G1a G3 G4 Qsp13 Hs013 HCH13 ZS13.
(* list[0]: the text block xmalloc returned, live now, and the journal's leave to write its first byte *)
assert (ELX : LIVE_XMALLOC (12 * Z.of_nat (length ids) + 1) = 12 * Z.of_nat (length ids) + 1) by (unfold LIVE_XMALLOC; lia).
rewrite ELX in HpermX, HfreshX, HinbX, HBBX.
pose proof (req_size_pos (12 * Z.of_nat (length ids) + 1) ltac:(lia)) as RQ.
assert (Hres14 : In (lst, 12 * Z.of_nat (length ids) + 1) (ablocks B ly14 S14)).
{ apply (Permutation_in _ (Permutation_sym Hperm14)). right.
  apply (Permutation_in _ (Permutation_sym Hperm10)). right.
  apply (Permutation_in _ (Permutation_sym HpermX)). left. reflexivity. }
destruct (scs_blk_loc ly14 S14 W14 mem14 md14 fpos lst (12 * Z.of_nat (length ids) + 1) lst HAR14 Hres14 Hfin14 ltac:(lia))
  as (Lst1 & Lst2 & Lst3 & Lst4).
rewrite EFA14 in Lst3, Lst4.
destruct (al_blocks _ _ LAWS _ _ _ _ _ lst _ HAR14 Hres14) as (_ & _ & _ & Hlapp & Hrp14 & _).
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hlapp.
assert (HAWR : awr_byte SEGS B SUP_CHAIN_STK (spZ regs) (SCB_FP O) (ablocks B ly S) (ablocks B ly14 S14) (frames S) ly14 [(1, fpos)] lst).
{ destruct (List.in_dec recb_pair_dec (lst, 12 * Z.of_nat (length ids) + 1) (ablocks B ly S)) as [HinS | HnS].
  - assert (HinF : In (lst, 12 * Z.of_nat (length ids) + 1) Frec).
    { rewrite <- Eab in HinS. apply (Permutation_in _ HPermF) in HinS. apply in_app_or in HinS as [H4 | HF']; [exfalso | exact HF'].
      pose proof (proj1 (Forall_forall _ _) HfreshX _ H4) as Hap. cbn [fst snd] in Hap. unfold iv_apart in Hap. lia. }
    exact (scs_awr_blk _ _ _ _ _ _ _ lst _ lst (HFO _ HinF) Hres14 ltac:(lia)).
  - right; right; left. exists lst, (12 * Z.of_nat (length ids) + 1). split; [exact Hres14|]. split; [exact HnS | lia]. }
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssv ?msv =>
pose proof (st_ok_pi_add_region Ev ssv msv scs_txt HS eq_refl
  ltac:(unfold region_ok, scs_txt; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
    rewrite N1062; split; [lia|]; split; [lia|]; split; [|apply Forall_nil];
    intros o Ho; apply (apresent_writable SEGS); apply (proj1 (Hrp14 (lst + o) ltac:(lia))))
  ltac:(cbn [all_disjoint ss_mem]; unfold extent_disjoint, scs_txt; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
    rewrite N1062, N1041, N1028, N2, N34; unfold SB in *; repeat split; lia)) as HS3 end.
clear HS. rename HS3 into HS. norm_ssp HS.
(* the shadow byte of list[0]: atom 1138 = SB + lst / 8, the walk's (s6 >> 3) + s3 (0x8c384, 0x8c388), at zero shadow
   (xmalloc's fresh block of 12 n + 1 >= 13 bytes: aux scb_chk0) *)
assert (L8 : 0 <= lst / 8 < 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; pose proof asan_consts as (CC1 & _); lia]).
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssv ?msv =>
pose proof (st_ok_pi_havoc_hi 1138 Ev ssv msv [Z_to_bv 64 (SB + lst / 8)] HS ltac:(vm_compute; reflexivity)) as HS3 end.
clear HS. rename HS3 into HS.
remember (havoc E8 1138 [Z_to_bv 64 (SB + lst / 8)]) as E9 eqn:HE9 in HS.
assert (HEI9 : img_env VAL A_LIM E9) by (rewrite HE9; apply img_env_havoc_hi; [exact HEI8 | unfold A_LIM; lia]).
assert (OLD9 : forall n, (n < 1138)%nat -> ew E9 n = ew E8 n) by (intros n Hn; rewrite HE9; apply ew_havoc_old; exact Hn).
assert (E1138 : ew E9 1138 = Z_to_bv 64 (SB + lst / 8))
  by (rewrite HE9; exact (ew_havoc_new E8 1138 [Z_to_bv 64 (SB + lst / 8)] 0 (Z_to_bv 64 0) ltac:(cbn; lia))).
clear HE9.
assert (AG9 : forall n, (n < 1024)%nat -> ew E9 n = ew E n) by (intros n Hn; rewrite OLD9 by lia; exact (AG8 n Hn)).
assert (M2 : bv_unsigned (ew E9 2) = spZ regs) by (rewrite OLD9 by lia; exact N2).
assert (M34 : bv_unsigned (ew E9 34) = sp1) by (rewrite OLD9 by lia; exact N34).
assert (M1028 : bv_unsigned (ew E9 1028) = F) by (rewrite OLD9 by lia; exact N1028).
assert (M1041 : bv_unsigned (ew E9 1041) = SB + F / 8) by (rewrite OLD9 by lia; exact N1041).
assert (M1046 : ew E9 1046 = w64 (rec_slot R)) by (rewrite OLD9 by lia; exact N1046).
assert (E9_1062 : ew E9 1062 = Z_to_bv 64 lst) by (rewrite OLD9 by lia; exact E8_1062).
assert (M1062 : bv_unsigned (ew E9 1062) = lst) by (rewrite OLD9 by lia; exact N1062).
assert (E9_32 : ew E9 32 = Z_to_bv 64 SB) by (rewrite AG9 by lia; exact E32).
assert (M1138 : bv_unsigned (ew E9 1138) = SB + lst / 8) by (rewrite E1138; apply unsigned_lit_small; unfold SB; lia).
assert (E9_12 : ew E9 12 = Z_to_bv 64 (Z.of_nat (length ids))) by (rewrite AG9, (EE 12%nat 12%bv eq_refl) by lia; exact H12).
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssv ?msv =>
pose proof (st_ok_pi_add_alias Ev _ msv (SAlu ALU_ADD (SAlu ALU_SRL (SOff 1062 0) (SLit 3)) (SOff 32 0)) (SOff 1138 0) HS
  (shadow_decl_ok Ev 1062 32 1138 lst SB E9_1062 ltac:(lia) E9_32 E1138)) as HS3 end.
clear HS. rename HS3 into HS. norm_ssp HS.
(* n >= 1 (atom 12), for the test `blez s2` (0x8c398) *)
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssv ?msv =>
pose proof (st_ok_pi_add_fact Ev ssv msv 12 (mkAF 1 62 0) HS
  ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E9_12, unsigned_lit_small by lia;
        replace (2 ^ 0) with 1 by reflexivity; rewrite Z.mod_1_r; lia)) as HS3 end.
clear HS. rename HS3 into HS. norm_ssp HS.
pose proof (scb_chk0 B ly14 S14 W14 mem14 md14 lst _ HAR14 Hres14 ltac:(lia)) as Hchk0.
unfold shadow_of_addr in Hchk0. rewrite <- SB_SHADOW_OFF in Hchk0.
pose proof (Z.div_mod lst 8 ltac:(lia)) as DL8. pose proof (Z.mod_pos_bound lst 8 ltac:(lia)) as ML8.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssv ?msv =>
pose proof (st_ok_pi_add_region Ev ssv msv scs_lsh HS eq_refl
  ltac:(unfold region_ok, scs_lsh; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
    rewrite M1138; split; [unfold SB; lia|]; split; [unfold SB; lia|]; split; [intros o Ho; lia|];
    apply Forall_cons; [|apply Forall_nil];
    apply (chunk_ok_val SEGS Ev _ (SB + lst / 8) 0 1 (SLit 0) 0); [reflexivity | lia | lia |];
    apply scs_val_mem_zero1; rewrite Z.add_0_r; exact Hchk0)
  ltac:(cbn [all_disjoint ss_mem]; unfold extent_disjoint, scs_lsh; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
    rewrite M1138, M1062, M1041, M1028, M2, M34; unfold SB in *; repeat split; lia)) as HS3 end.
clear HS. rename HS3 into HS. norm_ssp HS.
pose proof (SRr_run_to_pi_AJ (fx := fx2) (L := cmd_listing) (PL := PL_cmd) (PI := PI) B LAWS) as RUNTO2.
(* run 8: poison F + 32, SB + F / 8 to s1 + 24, the checked store list[0] := 0, n >= 1, the loop's registers *)
paj_run_to_shc RUNTO2 HS HJ14 SCB_LOOP.
{ scs_awr fpos (spZ regs) sp1 FS M1041 M1028 M2 M34 EFA14
    ltac:(eapply (YCbq.awr_ok_cons_gen _ _) with (k := 1062%nat);
          [reflexivity | exact M1062 | intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha; replace a with lst by lia; exact HAWR |]). }
rename ms into msL, mat into matL, HF into HF_r8, HFr into HFr_r8, HG into HG_r8.
assert (K8 : forall a, 0 <= a < 2 ^ 64 -> ~ (alloc_ceiling <= a < 2 ^ 64) ->
  ~ (SB + F / 8 <= a < SB + F / 8 + 16) -> a <> lst -> rdW W14 (ms_mem msL) a = rdW W14 mem14 a).
{ intros a Ha H1 H3 H4.
  apply (kept_of_frame (segs := SEGS) E9 _ (w_H W14) mem14 (ms_mem msL)
    (fun a => (alloc_ceiling <= a < 2 ^ 64) \/ (SB + F / 8 <= a < SB + F / 8 + 16) \/ a = lst) HFr_r8); [| lia | tauto].
  intros b wlo whi a' Hin Hrr. vm_compute in Hin.
  repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?M2, ?M34, ?M1028, ?M1041, ?M1062 in Hrr; lia|]).
  destruct Hin. }
clear HF_r8 HFr_r8 HG_r8.
pmkst HS.
lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?m |} _ => set (mdL := m) in *; clearbody mdL end.
(* the registers at the loop head *)
preg HS (2%bv : bv 5) R2. preg HS (3%bv : bv 5) R3. preg HS (4%bv : bv 5) R4. preg HS (8%bv : bv 5) R8.
preg HS (9%bv : bv 5) R9. preg HS (18%bv : bv 5) R18. preg HS (19%bv : bv 5) R19. preg HS (20%bv : bv 5) R20.
preg HS (21%bv : bv 5) R21. preg HS (22%bv : bv 5) R22. preg HS (23%bv : bv 5) R23. preg HS (24%bv : bv 5) R24.
preg HS (25%bv : bv 5) R25. preg HS (26%bv : bv 5) R26. preg HS (27%bv : bv 5) R27.
assert (E9_11 : ew E9 11 = Z_to_bv 64 pids) by (rewrite AG9, (EE 11%nat 11%bv eq_refl) by lia; exact H11).
rewrite scb_denot_off0, AG9, E34 in R2 by lia.
rewrite scb_denot_off0, AG9, (EE 3%nat 3%bv eq_refl) in R3 by lia.
rewrite scb_denot_off0, AG9, (EE 4%nat 4%bv eq_refl) in R4 by lia.
rewrite scb_denot_off0, AG9, Esp in R8 by lia.
rewrite scb_denot_off0, AG9, E34 in R9 by lia.
rewrite (scs_den_not E9 1062 lst E9_1062 ltac:(lia)) in R18.
rewrite scb_denot_off0, E9_11 in R19.
rewrite (scs_den_s4 E9 11 pids E9_11 ltac:(lia)) in R20.
cbn [sv_denot] in R21.
rewrite scb_denot_off0, E9_1062 in R22.
rewrite scb_denot_off0, (img_env_atomP E9 292 HEI9 ltac:(unfold A_TEXT, A_LIM; lia)) in R23.
change (VAL 292) with (VAL (A_OBJ 51)) in R23. rewrite V51 in R23.
rewrite scb_denot_off0, E9_11 in R24.
rewrite (scs_den_s9 E9 11 pids E9_11 ltac:(lia) HP4) in R25.
cbn [sv_denot] in R26.
rewrite scb_denot_off0, E9_12 in R27.
(* the memory the loop and the tail read, off the symbolic regions *)
pose proof (st_ok_region_nth E9 _ _ 1 _ HS eq_refl) as HRt. cbn [ms_mem restrict mkst] in HRt.
pose proof (st_ok_region_nth E9 _ _ 2 _ HS eq_refl) as HRs. cbn [ms_mem restrict mkst] in HRs.
pose proof (st_ok_region_nth E9 _ _ 3 _ HS eq_refl) as HRf. cbn [ms_mem restrict mkst] in HRf.
pose proof (st_ok_region_nth E9 _ _ 4 _ HS eq_refl) as HRw2. cbn [ms_mem restrict mkst] in HRw2.
pose proof (st_ok_region_nth E9 _ _ 5 _ HS eq_refl) as HRw1. cbn [ms_mem restrict mkst] in HRw1.
pose proof (st_ok_region_nth E9 _ _ 6 _ HS eq_refl) as HR2. cbn [ms_mem restrict mkst] in HR2.
pose proof (st_ok_region_nth E9 _ _ 7 _ HS eq_refl) as HRw3. cbn [ms_mem restrict mkst] in HRw3.
assert (LZ : rdW W14 (ms_mem msL) lst = Some 0).
{ pose proof (scs_byte_of_region E9 W14 (ms_mem msL) 1062 lst _ _ _ _ _ 0 (SLit 0) HRt M1062 ltac:(cbn [In]; tauto)) as H0.
  rewrite Z.add_0_r in H0. rewrite H0. cbn [sv_denot]. rewrite unsigned_lit_small by lia. reflexivity. }
assert (FSH : scb_fshadow W14 (ms_mem msL) F).
{ intros i Hi. apply (scs_fshadow_of E9 W14 (ms_mem msL) (SB + F / 8) _ _ _ _ _ HRs M1041); [|exact Hi].
  intros j Hj.
  assert (Hj' : j = 0 \/ j = 1 \/ j = 2 \/ j = 3 \/ j = 4 \/ j = 5 \/ j = 6 \/ j = 7 \/ j = 8 \/ j = 9 \/ j = 10 \/ j = 11 \/
    j = 12 \/ j = 13 \/ j = 14 \/ j = 15) by lia.
  repeat (destruct Hj' as [-> | Hj']); try (subst j);
    (eexists; split; [cbn [In]; repeat (first [left; reflexivity | right]) | vm_compute; reflexivity]). }
assert (EF1028 : ew E9 1028 = Z_to_bv 64 F) by (rewrite <- M1028; symmetry; apply Z_to_bv_bv_unsigned).
assert (EF1041 : ew E9 1041 = Z_to_bv 64 (SB + F / 8)) by (rewrite <- M1041; symmetry; apply Z_to_bv_bv_unsigned).
assert (Hslr : 0 <= rec_slot R < 2 ^ 64).
{ destruct (scs_slot_bounds R HC1) as [Hsl | Hsl];
    [unfold A_G_REC, OFF_CALLS, CALL_SIZE, REC_SIZE in Hsl; lia | rewrite Hsl; unfold A_REC_SPILL; lia]. }
assert (WD : scb_words W14 (ms_mem msL) sp1 (rec_slot R) F pids).
{ refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))))).
  - exact (scs_word_of_region E9 W14 (ms_mem msL) 34 sp1 _ _ _ _ _ 8 (SOff 1046 0) (rec_slot R) HRw1 M34
      ltac:(cbn [In]; tauto) ltac:(rewrite scb_denot_off0, M1046; reflexivity) Hslr).
  - exact (scs_word_of_region E9 W14 (ms_mem msL) 34 sp1 _ _ _ _ _ 16 (SOff 1028 0) F HRw1 M34
      ltac:(cbn [In]; tauto) ltac:(rewrite scb_denot_off0; exact EF1028) ltac:(lia)).
  - exact (scs_word_of_region E9 W14 (ms_mem msL) 34 sp1 _ _ _ _ _ 24 (SOff 1041 0) (SB + F / 8) HRw1 M34
      ltac:(cbn [In]; tauto) ltac:(rewrite scb_denot_off0; exact EF1041) ltac:(unfold SB; lia)).
  - exact (scs_word_of_region E9 W14 (ms_mem msL) 34 sp1 _ _ _ _ _ 32 (SOff 1028 0) F HRw1 M34
      ltac:(cbn [In]; tauto) ltac:(rewrite scb_denot_off0; exact EF1028) ltac:(lia)).
  - exact (scs_word_of_region E9 W14 (ms_mem msL) 34 sp1 _ _ _ _ _ 40 (SOff 320 0) 0x21f20 HRw1 M34
      ltac:(cbn [In]; tauto)
      ltac:(rewrite scb_denot_off0, (img_env_atomP E9 320 HEI9 ltac:(unfold A_TEXT, A_LIM; lia));
            change (VAL 320) with (VAL (A_OBJ 79)); rewrite V79; reflexivity) ltac:(lia)).
  - exact (scs_word_of_region E9 W14 (ms_mem msL) 34 sp1 _ _ _ _ _ 48 (SOff 11 0) pids HRw3 M34
      ltac:(cbn [In]; tauto) ltac:(rewrite scb_denot_off0; exact E9_11) HPR).
  - exact (scs_word_of_region E9 W14 (ms_mem msL) 34 sp1 _ _ _ _ _ 56 (SOff 32 0) SB HRw3 M34
      ltac:(cbn [In]; tauto) ltac:(rewrite scb_denot_off0; exact E9_32) ltac:(unfold SB; lia)).
  - exact (scs_word_of_region E9 W14 (ms_mem msL) 34 sp1 _ _ _ _ _ 80 (SOff 1028 0) F HRw2 M34
      ltac:(cbn [In]; tauto) ltac:(rewrite scb_denot_off0; exact EF1028) ltac:(lia)). }
assert (FLG : rdword (rdW W14 (ms_mem msL)) (F + 120) = Some (flag_addr ly14 1 fpos)).
{ rewrite EFL14. apply (rdword_of_val_mem SEGS); [|lia].
  apply (scs_word_of_region E9 W14 (ms_mem msL) 1028 F _ _ _ _ _ 120 (SOff 1040 0) FL HRf M1028 ltac:(cbn [In]; tauto)).
  - rewrite scb_denot_off0, OLD9, OLD8, OLD7, OLD6, OLD5, OLD4, OLD3 by lia. exact E1040.
  - lia. }
assert (FAT : scb_frame_at (mrestrict (w_H W14) (ms_mem msL)) (spZ regs) regs).
{ apply (scs_frame_at E9 W14 (ms_mem msL) (spZ regs) regs _ _ _ _ _ HR2 M2).
  - intros j r Hj.
    do 13 (destruct j as [|j]; [cbn [nth_error scb_saved] in Hj; injection Hj as <-; cbn [In]; repeat (first [left; reflexivity | right]) |]).
    cbn [nth_error scb_saved] in Hj. destruct j; discriminate Hj.
  - intros r Hr. cbn [scb_saved In] in Hr.
    repeat (destruct Hr as [<- | Hr]; [rewrite AG9 by (cbn; lia); apply EE; vm_compute; reflexivity |]). destruct Hr. }
clear HRt HRs HRf HRw1 HRw2 HRw3 HR2.
(* the journal from the entry at the loop head *)
assert (HJL : ajournal SEGS B SUP_CHAIN_STK (spZ regs) (SCB_FP O) ly S W mem md [(1, fpos)] ly14 S14 W14 (ms_mem msL) mdL (scb_kL R)).
{ lazymatch type of HJ14 with ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?k =>
    replace (scb_kL R) with k by (unfold scb_kL; lia); exact HJ14 end. }
(* the blocks: record() freed Frec; xmalloc's text block and the two copies are fresh *)
assert (HPermS : Permutation (ablocks B ly S) (ablocks B ly4 S4 ++ Frec)) by (rewrite <- Eab; exact HPermF).
assert (Hbl1L : forall pn, In pn (ablocks B ly4 S4) -> In pn (ablocks B ly14 S14)).
{ intros pn Hpn. apply (Permutation_in _ (Permutation_sym Hperm14)). right.
  apply (Permutation_in _ (Permutation_sym Hperm10)). right.
  apply (Permutation_in _ (Permutation_sym HpermX)). right. exact Hpn. }
destruct (scs_arr_final fpos ly14 S14 W14 (ms_mem msL) mdL _ lst Frec (ablocks B ly4 S4) HJL HPermS HFO Hbl1L HfreshX Hres14)
  as (AB & ARA & AIV & ACE).
set (m2 := Z.of_nat (length (dec (Z.of_nat (length ids)))) + 1) in *.
assert (HO2in14 : forall pn, In pn ((p2, m2) :: (p1, m1) :: O1) -> In pn (ablocks B ly14 S14)).
{ intros pn [<- | [<- | Hpn]].
  - apply (Permutation_in _ (Permutation_sym Hperm14)). left. reflexivity.
  - apply (Permutation_in _ (Permutation_sym Hperm14)). right. apply (Permutation_in _ (Permutation_sym Hperm10)). left. reflexivity.
  - exact (Hbl1L _ (HO1in4 _ Hpn)). }
assert (HlstS10 : In (lst, 12 * Z.of_nat (length ids) + 1) (ablocks B ly10 S10)).
{ apply (Permutation_in _ (Permutation_sym Hperm10)). right. apply (Permutation_in _ (Permutation_sym HpermX)). left. reflexivity. }
assert (HlstS6 : In (lst, 12 * Z.of_nat (length ids) + 1) (ablocks B ly6 S6)).
{ apply (Permutation_in _ (Permutation_sym HpermX)). left. reflexivity. }
assert (KRL : forall a, scs_RX ((p2, m2) :: (p1, m1) :: O1) a -> rdW W14 (ms_mem msL) a = rdW W14 mem14 a).
{ intros a Ha. destruct (scs_RX_loc ly14 S14 W14 mem14 md14 _ fpos a HAR14 HO2in14 Hfin14 Ha) as (Hlo & _ & HnS & _).
  rewrite EFA14 in HnS.
  assert (Hne : a <> lst).
  { intros ->. destruct Ha as [Ha | [Ha | (pn & Hpn & Ha)]].
    - exact (Lst2 (scs_prog_img lst (recb_grec_in lst Ha))).
    - exact (Lst2 (scs_prog_img lst (recb_spill_in lst Ha))).
    - destruct Hpn as [<- | [<- | Hpn]]; cbn [fst snd] in Ha.
      + pose proof (proj1 (Forall_forall _ _) Hfresh14 _ HlstS10) as Hd. cbn [fst snd] in Hd. unfold iv_apart in Hd. lia.
      + pose proof (proj1 (Forall_forall _ _) Hfresh10 _ HlstS6) as Hd. cbn [fst snd] in Hd. unfold iv_apart in Hd. lia.
      + pose proof (proj1 (Forall_forall _ _) HfreshX _ (HO1in4 _ Hpn)) as Hd. unfold iv_apart in Hd. lia. }
  exact (K8 a ltac:(lia) ltac:(lia) HnS Hne). }
assert (HREPL : rec_repA B ly14 S14 (rdW W14 (ms_mem msL)) (rec_record R 17 [dec id; dec (Z.of_nat (length ids))])
  ((p2, m2) :: (p1, m1) :: O1))
  by exact (scs_rec_repA_ext ly14 S14 (rdW W14 mem14) ly14 S14 _ _ _ HREP14 HO2in14 KRL).
assert (BBL : blocks_bytes S14 <= blocks_bytes S + LIVE_XMALLOC (12 * Z.of_nat (length ids) + 1) + LIVE_ARG_S (Some (dec id)) +
  LIVE_ARG_S (Some (dec (Z.of_nat (length ids))))) by (rewrite ELX; lia).
assert (MLL : mo_le MT S S14 (XM_RECORD MT R + XM_XMALLOC MT (12 * Z.of_nat (length ids) + 1) + XM_ARG_S MT (Some (dec id)) +
  XM_ARG_S MT (Some (dec (Z.of_nat (length ids)))))) by exact (mo_le_trans MT MTL S S10 S14 _ _ MLS10 MLE14).
assert (FXR : fxrel fx fx2) by exact (fxrel_trans fx fx1 fx2 Hfx1 Hfx2).
(* the loop head: scb_lctx and scb_inv 0 *)
apply (K fx2 W14 (ms_regs msL) (ms_mem msL) mdL ly14 S14 fpos lst (ablocks B ly4 S4) Frec O1 p1 p2).
- exact (fxrel_frm0 fx fx2 HRM0 FXR).
- exact FXR.
- split; [exact HJL|]. split; [exact HPermS|]. split; [exact HFO|]. split; [exact HFlen|]. split; [exact HO1|].
  split.
  { eapply perm_trans; [exact Hperm14|]. apply perm_skip. eapply perm_trans; [exact Hperm10|]. apply perm_skip. exact HpermX. }
  split; [exact HfreshX|].
  split.
  { apply Forall_forall. intros q Hq. apply (proj1 (Forall_forall _ _) Hfresh10).
    apply (Permutation_in _ (Permutation_sym HpermX)). exact Hq. }
  split.
  { apply Forall_forall. intros q Hq. apply (proj1 (Forall_forall _ _) Hfresh14).
    apply (Permutation_in _ (Permutation_sym Hperm10)).
    destruct Hq as [<- | Hq]; [left; reflexivity | right; apply (Permutation_in _ (Permutation_sym HpermX)); exact Hq]. }
  split; [exact Hp1|]. split; [exact Hp2|]. split; [exact Hlst|].
  split; [exact HREPL|]. split; [exact BBL|]. split; [exact MLL|].
  split; [exact FAT|]. split; [rewrite EFA14; exact WD|]. split; [rewrite EFA14; exact FSH|].
  split; [rewrite EFA14; exact FLG|]. split; [exact LZ|].
  split; [exact AB|]. split; [exact ARA|]. split; [exact AIV|]. split; [exact ACE|].
  exact (scs_aro _ _ _ _ _ _ _ HJL).
- split; [lia|]. split; [exact HJL|].
  split; [unfold spZ at 1; rewrite R2, unsigned_lit_small by lia; reflexivity|].
  split; [exact (eq_trans R3 Hgp)|]. split; [exact (eq_trans R4 Htp)|].
  split; [rewrite R8; reflexivity|]. split; [rewrite R9; reflexivity|].
  split; [rewrite R18; reflexivity|].
  split; [replace (pids + 4 * Z.of_nat 0) with pids by lia; exact R19|].
  split; [exact R20|].
  split; [rewrite R21; reflexivity|].
  split; [rewrite R22; reflexivity|].
  split; [exact R23|].
  split; [replace (pids + 4 * Z.of_nat 0) with pids by lia; exact R24|].
  split; [exact R25|].
  split; [rewrite R26; reflexivity|].
  split; [rewrite R27; reflexivity|].
  split.
  { intros i Hi. change (i < 1)%nat in Hi. assert (i = 0%nat) by lia. subst i.
    replace (lst + Z.of_nat 0) with lst by lia. rewrite LZ. reflexivity. }
  intros a _ _ _. reflexivity.
Qed.
End e.
End f.
End d.
