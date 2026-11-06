(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the invariant of pins_set's ASan walk at its program calls, after
   proofs/cgif/cgif_file_fuzzer/lib/A/AChc.v (cl_cx / cl_mid, the facts a segment of cgif_close carries) over
   fuzz_command's recorder. *)

(* The walk of pins_set is cut at the four calls of xstrdup. At the entry of the j-th call (j = 1 .. 4) the state
   satisfies `ps_inv j P`: the journal from pins_set's entry, the frame of saved registers, the registers the rest
   of the function reads, the call record() made (fn = 20, nargs = j - 1, the arguments P stored so far), and the
   block and meter bookkeeping that the post-condition needs. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import String ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI04 YG0s YI00.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YI16 YM05 YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdSyms CmdAddr CmdList CmdPa CmdPaLib.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaCall PaCallRun PaLibF PaLibG PaLibH PaSB PaDenot.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob CmdBase CmdRep CmdObj CmdRo CmdZsh.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
rec_calls_free_c xstrdup_c mix_call_c answer_code_c pins_set_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import RecBLemmas pins_set_s2 pins_set_s1.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require CmdRecRest.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* a list of (base, length) ranges that a byte range avoids, by computation *)
Lemma ps_zr_apart : forall (l : list (Z * Z)) lo hi,
forallb (fun r => (fst r + snd r <=? lo) || (hi <=? fst r)) l = true ->
forall a, lo <= a < hi -> ~ Exists (in_zr a) l.
Proof.
intros l lo hi H a Ha Hex. apply Exists_exists in Hex as (r & Hr & Hz).
pose proof (proj1 (forallb_forall _ l) H r Hr) as Hb. cbv beta in Hb.
apply orb_true_iff in Hb as [Hb | Hb]; apply Z.leb_le in Hb; unfold in_zr in Hz; lia.
Qed.

(* the pointer pins_set hands to xstrdup: the argument, or the default literal when the argument is NULL *)
Definition ps_sptr (p : Z) (v : option (list byte)) (d : Z) : Z := match v with Some _ => p | None => d end.
Definition ps_ret (j : nat) : Z :=
match j with 1%nat => PS_RET1 | 2%nat => PS_RET2 | 3%nat => PS_RET3 | _ => PS_RET4 end.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
Hypothesis HB : CmdBSyms B.

(* g_rec, record.spill and the two default literals are none of the runtime's statics and not the errno cell *)
Lemma ps_unowned_range : forall lo hi, 
forallb (fun r => (fst r + snd r <=? lo) || (hi <=? fst r)) Tfib_owned_static = true ->
(hi <= TFIB_ERRNO \/ TFIB_ERRNO + 4 <= lo) ->
forall a, lo <= a < hi -> ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).
Proof.
intros lo hi H He a Ha. rewrite (ts_owned B HB), (ts_errno B HB). split; [exact (ps_zr_apart _ lo hi H a Ha) | lia].
Qed.

Lemma ps_unowned_grec : forall a, A_G_REC <= a < A_G_REC + REC_SIZE ->
~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).
Proof. apply ps_unowned_range; [vm_compute; reflexivity | unfold TFIB_ERRNO, A_G_REC, REC_SIZE; lia]. Qed.
Lemma ps_unowned_spill : forall a, A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE ->
~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).
Proof. apply ps_unowned_range; [vm_compute; reflexivity | unfold TFIB_ERRNO, A_REC_SPILL, SC_SIZE; lia]. Qed.
Lemma ps_unowned_null : forall a, 0x22480 <= a < 0x22480 + 7 ->
~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).
Proof. apply ps_unowned_range; [vm_compute; reflexivity | unfold TFIB_ERRNO; lia]. Qed.
Lemma ps_unowned_dash : forall a, 0x21d40 <= a < 0x21d40 + 2 ->
~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).
Proof. apply ps_unowned_range; [vm_compute; reflexivity | unfold TFIB_ERRNO; lia]. Qed.

Lemma ps_null_lit : RO_lit_22480 = sarg None ++ [Z_to_bv 8 0].
Proof. vm_compute. reflexivity. Qed.
Lemma ps_dash_lit : RO_lit_21d40 = darg None (bstr "-"%string) ++ [Z_to_bv 8 0].
Proof. vm_compute. reflexivity. Qed.
Lemma ps_null_nz : ~ In (Z_to_bv 8 0) (sarg None).
Proof. cbv. intros H. repeat (destruct H as [H|H]; [inversion H|]). exact H. Qed.
Lemma ps_dash_nz : ~ In (Z_to_bv 8 0) (darg None (bstr "-"%string)).
Proof. cbv. intros H. repeat (destruct H as [H|H]; [inversion H|]). exact H. Qed.

(* the per-binary facts the walk needs and the statement does not carry yet (2026-10-28/29: the names and
   forms every recorder walk uses, each to become a lemma of lib/A/Prog/CmdRecFacts.v) *)
#[local] Notation LAWS := (AR_laws_ok SEGS B).
Hypothesis cmd_ro_ok_of_aro : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md ->
arodata_okP SEGS RLO RHI B (rdW W mem) -> cmd_ro_ok (rdW W mem).
Hypothesis RRO : ro_below_ofl SEGS RLO RHI.
Hypothesis RELRO_IMG : forall a, RLO <= a < RHI -> in_img SEGS a.
Hypothesis cmd_ro_prog_apart : forall a, in_roP SEGS RLO RHI a -> in_img SEGS a /\ ~ Exists (in_zr a) recb_PG.
Hypothesis cmd_heap_tail_vis : forall ly S (W : world SEGS) mem md p n e, AR SEGS B ly S W mem md ->
In (p, n) (ablocks B ly S) -> p <= e < p + n -> atail_vis SEGS W mem e.

(* the two default literals as xstrdup's source, at any state of the walk *)
Lemma ps_src_null : forall ly S (W : world SEGS) mem md,
AR SEGS B ly S W mem md -> cmd_ro_ok (rdW W mem) -> cmd_ro_in (in_roP SEGS RLO RHI) ->
astr_argA B ly S (rdW W mem) (in_roP SEGS RLO RHI) [] 0x22480 (Some (sarg None)) /\
atail_vis SEGS W mem (0x22480 + Z.of_nat (length (sarg None))).
Proof.
intros ly S W mem md HAR HRO HIN.
assert (HL : abytes_atR (rdW W mem) 0x22480 RO_lit_22480).
{ clear - HRO. destruct HRO as [HRO _]. unfold cmd_ro_bytes in HRO.
  repeat match type of HRO with
  | abytes_atR _ 0x22480 _ /\ _ => exact (proj1 HRO)
  | _ /\ _ => apply proj2 in HRO
  end. }
assert (HI : forall i, 0 <= i < 7 -> in_roP SEGS RLO RHI (0x22480 + i)).
{ clear - HIN. unfold cmd_ro_in in HIN.
  repeat match type of HIN with
  | (forall i, 0 <= i < 7 -> _ (0x22480 + i)) /\ _ => exact (proj1 HIN)
  | _ /\ _ => apply proj2 in HIN
  end. }
change (Z.of_nat (length (sarg None))) with 6.
split; [|exact (CmdRecRest.cmd_tail_vis SEGS B LAWS HB W mem (0x22480 + 6) HRO ltac:(vm_compute; tauto))].
split; [lia|]. split; [split; [rewrite <- ps_null_lit; exact HL | exact ps_null_nz]|].
split; [change (Z.of_nat (length (sarg None)) + 1) with 7; unfold LMAX; lia|].
right. change (Z.of_nat (length (sarg None)) + 1) with 7.
split; [intros i Hi; split; [exact (HI i Hi) | exact (ps_unowned_null (0x22480 + i) ltac:(lia))]|].
split; [vm_compute; reflexivity|]. split; [vm_compute; reflexivity | vm_compute; tauto].
Qed.

Lemma ps_src_dash : forall ly S (W : world SEGS) mem md,
AR SEGS B ly S W mem md -> cmd_ro_ok (rdW W mem) -> cmd_ro_in (in_roP SEGS RLO RHI) ->
astr_argA B ly S (rdW W mem) (in_roP SEGS RLO RHI) [] 0x21d40 (Some (darg None (bstr "-"%string))) /\
atail_vis SEGS W mem (0x21d40 + Z.of_nat (length (darg None (bstr "-"%string)))).
Proof.
intros ly S W mem md HAR HRO HIN.
assert (HL : abytes_atR (rdW W mem) 0x21d40 RO_lit_21d40).
{ clear - HRO. destruct HRO as [HRO _]. unfold cmd_ro_bytes in HRO.
  repeat match type of HRO with
  | abytes_atR _ 0x21d40 _ /\ _ => exact (proj1 HRO)
  | _ /\ _ => apply proj2 in HRO
  end. }
assert (HI : forall i, 0 <= i < 2 -> in_roP SEGS RLO RHI (0x21d40 + i)).
{ clear - HIN. unfold cmd_ro_in in HIN.
  repeat match type of HIN with
  | (forall i, 0 <= i < 2 -> _ (0x21d40 + i)) /\ _ => exact (proj1 HIN)
  | _ /\ _ => apply proj2 in HIN
  end. }
change (Z.of_nat (length (darg None (bstr "-"%string)))) with 1.
split; [|exact (CmdRecRest.cmd_tail_vis SEGS B LAWS HB W mem (0x21d40 + 1) HRO ltac:(vm_compute; tauto))].
split; [lia|]. split; [split; [rewrite <- ps_dash_lit; exact HL | exact ps_dash_nz]|].
split; [change (Z.of_nat (length (darg None (bstr "-"%string))) + 1) with 2; unfold LMAX; lia|].
right. change (Z.of_nat (length (darg None (bstr "-"%string))) + 1) with 2.
split; [intros i Hi; split; [exact (HI i Hi) | exact (ps_unowned_dash (0x21d40 + i) ltac:(lia))]|].
split; [vm_compute; reflexivity|]. split; [vm_compute; reflexivity | vm_compute; tauto].
Qed.

(* a string argument the caller handed over stays a valid source for xstrdup at every later state of the walk:
   its block stays live (it is none of the recorder's blocks, which are the only ones the walk frees), its bytes
   are outside every footprint, and the read-only bytes are kept by the journal's image clause; its tail is
   readable by cmd_heap_tail_vis (a block) or by the literal ends of cmd_ro_ok (the read-only image) *)
Lemma ps_src_some : forall ly S (W : world SEGS) mem md O p x STK sp0 FP own lyc Sc Wc memc mdc k,
AR SEGS B ly S W mem md ->
astr_argA B ly S (rdW W mem) (in_roP SEGS RLO RHI) O p (Some x) ->
ajournal SEGS B STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k ->
cmd_ro_ok (rdW Wc memc) ->
(forall pn, In pn (ablocks B ly S) -> ~ In pn O -> In pn (ablocks B lyc Sc)) ->
(forall a, inFP FP a -> Exists (in_zr a) recb_PG \/ exists q n, In (q, n) O /\ q <= a < q + req_size n) ->
~ YI16.sink_open_fp FP ->
(forall pn, In pn O -> 0 < snd pn /\ In pn (ablocks B ly S)) ->
astr_argA B lyc Sc (rdW Wc memc) (in_roP SEGS RLO RHI) [] p (Some x) /\
atail_vis SEGS Wc memc (p + Z.of_nat (length x)).
Proof.
intros ly S W mem md O p x STK sp0 FP own lyc Sc Wc memc mdc k HAR (Hp0 & Hstr & Hn & Harm) HJ HRO2 Hlive HFP HSK HOpos.
pose proof HJ as (HAR2 & _ & _ & _ & _ & _ & _ & _ & _ & KB & KI & _).
destruct Harm as [((q & m & Hqm & Hq1 & Hq2) & HapO) | (Hro & Hab & Hhb & Hend)].
- assert (HqO : ~ In (q, m) O).
  { intros HO. pose proof (proj1 (Forall_forall _ O) HapO (q, m) HO) as D. cbn [fst snd] in D.
    unfold iv_apart in D. lia. }
  pose proof (Hlive (q, m) Hqm HqO) as Hqm2.
  destruct (al_blocks _ _ LAWS _ _ _ _ _ q m HAR Hqm) as (_ & _ & _ & _ & _ & _ & Hm0).
  assert (Hrq : req_size m = m) by (unfold req_size; destruct (Z.eqb_spec m 0); lia).
  assert (KEEP : forall i, 0 <= i < Z.of_nat (length x) + 1 -> rdW Wc memc (p + i) = rdW W mem (p + i)).
  { intros i Hi. replace (p + i) with (q + (p + i - q)) by lia.
    apply (KB q m (p + i - q) Hqm Hqm2); [lia|].
    intros Hf. destruct (HFP _ Hf) as [Hpg | (q' & n' & Hq'O & Hq'r)].
    - destruct (blk_off_imgP B ly S W mem md q m HAR Hqm) as [Hlo | Hhi];
        apply Exists_exists in Hpg as (r & Hr & Hz); unfold recb_PG in Hr; unfold in_zr in Hz;
        destruct Hr as [<- | [<- | [<- | []]]]; cbn [fst snd] in Hz;
        unfold A_G_REC, A_REC_SPILL, A_G_QUITTING, REC_SIZE, SC_SIZE in Hz; lia.
    - pose proof (proj1 (Forall_forall _ O) HapO (q', n') Hq'O) as D. cbn [fst snd] in D.
      pose proof (proj1 (HOpos (q', n') Hq'O)) as Hn'. cbn [snd] in Hn'.
      assert (req_size n' = n') by (unfold req_size; destruct (Z.eqb_spec n' 0); lia).
      unfold iv_apart in D. lia. }
  split.
  + split; [exact Hp0|]. split.
    { apply (ps_astr_kept (rdW W mem)); [exact Hstr|]. intros y Hy. replace y with (p + (y - p)) by lia. apply KEEP. lia. }
    split; [exact Hn|]. left. split; [exists q, m; split; [exact Hqm2 | lia] | constructor].
  + apply (cmd_heap_tail_vis lyc Sc Wc memc mdc q m); [exact HAR2 | exact Hqm2 | lia].
- assert (KEEP : forall i, 0 <= i < Z.of_nat (length x) + 1 -> rdW Wc memc (p + i) = rdW W mem (p + i)).
  { intros i Hi. destruct (Hro i Hi) as (Hr & Hown & Herr).
    destruct (cmd_ro_prog_apart (p + i) Hr) as [Himg Hnpg].
    apply KI; [exact Himg | exact Hown | exact Herr |].
    apply fp_spares_closed; [exact HSK|].
    intros Hf. destruct (HFP _ Hf) as [Hpg | (q' & n' & Hq'O & Hq'r)]; [exact (Hnpg Hpg)|].
    destruct (HOpos (q', n') Hq'O) as [_ Hq'S].
    pose proof (pa_img_range _ Himg) as HR.
    destruct (blk_off_imgP B ly S W mem md q' n' HAR Hq'S) as [Hlo | Hhi]; lia. }
  split.
  + split; [exact Hp0|]. split.
    { apply (ps_astr_kept (rdW W mem)); [exact Hstr|]. intros y Hy. replace y with (p + (y - p)) by lia. apply KEEP. lia. }
    split; [exact Hn|]. right.
    split; [exact Hro|]. split; [exact Hab|]. split; [exact Hhb | exact Hend].
  + exact (CmdRecRest.cmd_tail_vis SEGS B LAWS HB Wc memc _ HRO2 Hend).
Qed.

Lemma ps_acall_pos : forall bl rd a c P, acall_at bl rd a c P -> forall pn, In pn P -> 0 < snd pn.
Proof.
intros bl rd a c P (_ & _ & HL & _ & _ & _ & H7) pn Hpn.
apply In_nth_error in Hpn as (k & Hk).
destruct (nth_error (snd c) k) as [s|] eqn:Hs.
- destruct (H7 k s pn Hs Hk) as (_ & _ & _ & Hlen & _). lia.
- exfalso. apply nth_error_None in Hs. pose proof (proj1 (nth_error_Some P k) ltac:(rewrite Hk; discriminate)). lia.
Qed.

(* the recorder's own blocks are live blocks of positive size *)
Lemma ps_O_facts : forall ly S rd R O, rec_repA B ly S rd R O ->
forall pn, In pn O -> 0 < snd pn /\ In pn (ablocks B ly S).
Proof.
intros ly S rd R O (Q & HA & HO) pn Hpn. apply HO in Hpn.
split; [|exact (lay_blocks_in _ _ _ _ _ _ HA pn Hpn)].
destruct HA as (_ & _ & _ & (_ & HlenQ & _ & Hc4 & Hsp & _) & Ha & Hr & _ & _).
unfold lay_blocks in Hpn. apply in_app_or in Hpn as [Hpn | Hpn];
  [|apply in_app_or in Hpn as [Hpn | Hpn]; [|apply in_app_or in Hpn as [Hpn | Hpn]]].
- apply in_concat in Hpn as (P & HP & Hin). apply In_nth_error in HP as (i & Hi).
  destruct (nth_error (r_calls R) i) as [c|] eqn:Hc.
  + exact (ps_acall_pos _ _ _ _ _ (proj1 (Hc4 i c P Hc Hi)) pn Hin).
  + exfalso. apply nth_error_None in Hc. pose proof (proj1 (nth_error_Some (l_calls Q) i) ltac:(rewrite Hi; discriminate)). lia.
- exact (ps_acall_pos _ _ _ _ _ Hsp pn Hpn).
- unfold aanswer_at in Ha. destruct (r_answer R) as [x|], (l_answer Q) as [q|]; cbn [oblk] in Hpn; try contradiction.
  destruct Hpn as [<- | []]. destruct Ha as (_ & _ & _ & Hl & _). lia.
- unfold areply_at in Hr. destruct (r_reply R) as [x|], (l_reply Q) as [q|]; cbn [oblk] in Hpn; try contradiction.
  destruct Hpn as [<- | []]. destruct Hr as (_ & _ & _ & Hne & _ & Hl & _).
  destruct x as [|b x]; [exfalso; exact (Hne eq_refl)|]. cbn [length] in Hl. lia.
Qed.

Section entry.
Variables (ly : alayout) (S : astate) (W : world SEGS) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
  (ch : list (Z * Z * Z)) (pu pf pl pv : Z) (uri files layout verdict : option (list byte)) (R : rstate)
  (O : list (Z * Z)).

Definition ps_sp0 : Z := spZ regs.
Definition ps_n : Z := Z.of_nat (length (r_calls R)).
Definition ps_c : Z := ps_slot_of ps_n.
Definition ps_A : list (list byte) := [sarg uri; sarg files; sarg layout; darg verdict (bstr "-"%string)].
Definition ps_V : list (option (list byte)) := [uri; files; layout; verdict].
Definition ps_ptrs : list Z :=
[ps_sptr pu uri 0x22480; ps_sptr pf files 0x22480; ps_sptr pl layout 0x22480; ps_sptr pv verdict 0x21d40].
Definition ps_FP : list (Z * Z) := (A_G_REC, A_G_REC + REC_SIZE) :: (A_REC_SPILL, A_REC_SPILL + SC_SIZE) :: ablocks_fp O.
Definition ps_xm (m : nat) : Z := fold_right Z.add 0 (map (XM_XSTRDUP MT) (firstn m ps_A)).
Definition ps_live (m : nat) : Z := fold_right Z.add 0 (map LIVE_XSTRDUP (firstn m ps_A)).

(* pins_set's post-condition, the statement's (pins_set_c.v; FP-existential since pass 4) *)
Definition ps_post : world SEGS -> config -> Prop :=
apost_baseF SEGS B PINS_SET_STK ps_FP regs ly S W mem md (EV_PINS_SET R)
(fun ly' S' W' regs' mem' md' => exists (R' : rstate) (r : Z) (O' : list (Z * Z)),
 pins_set_m R uri files layout verdict = (R', r) /\
 getr regs' 10 = w64 r /\ -2 ^ 31 <= r < 2 ^ 31 /\
 rec_repA B ly' S' (rdW W' mem') R' O' /\
 (forall pn, In pn O' -> In pn O \/ ~ In pn (ablocks B ly S)) /\
 (forall pn, In pn (ablocks B ly S) -> ~ In pn O -> In pn (ablocks B ly' S')) /\
 (forall pn, In pn (ablocks B ly' S') -> (In pn (ablocks B ly S) /\ ~ In pn O) \/ In pn O') /\
 blocks_bytes S' <= blocks_bytes S + LIVE_PINS_SET R uri files layout verdict /\
 mo_le MT S S' (XM_PINS_SET MT R uri files layout verdict)).

(* a block an xstrdup of the walk made: the i-th argument's copy *)
Definition ps_newb (i : nat) (pn : Z * Z) (Qb : rlay) lyc Sc (rd : reader) : Prop :=
fst pn <> 0 /\ snd pn = Z.of_nat (length (nth i ps_A [])) + 1 /\ astr_atR rd (fst pn) (nth i ps_A []) /\
In pn (ablocks B lyc Sc) /\ iv_apart (fst pn) (snd pn) A_G_REC REC_SIZE /\ iv_apart (fst pn) (snd pn) A_REC_SPILL SC_SIZE /\
~ In (fst pn) (map fst (lay_blocks Qb)) /\ (~ In pn (ablocks B ly S) \/ In pn O).

(* the recorder at a call of the walk: a representation Rb / Qb of the recorder with g_rec.calls / record.spill
   ready for the new call (the entry's, or the one after rec_calls_free emptied the spill), whose bytes the walk
   kept, and the slot record() filled: fn = 20, nargs = |P|, the arguments P; Pn the copies made but not stored *)
Definition ps_rec (P Pn : list (Z * Z)) lyc Sc (Wc : world SEGS) memc : Prop :=
exists Rb Qb (rdb : reader) blb,
arep_at blb rdb A_G_REC A_REC_SPILL Rb Qb /\
length (r_calls Rb) = length (r_calls R) /\ (forall A, rec_record Rb REC_PINS_SET A = rec_record R REC_PINS_SET A) /\
(16 <= ps_n -> l_spill Qb = []) /\
(forall x, put_prot ps_n Qb x -> rdW Wc memc x = rdb x) /\
(forall pn, In pn (lay_blocks Qb) -> In pn (ablocks B lyc Sc) /\ In pn O /\ 0 < snd pn) /\
(forall pn, In pn (ablocks B lyc Sc) -> (In pn (ablocks B ly S) /\ ~ In pn O) \/ In pn (lay_blocks Qb) \/ In pn (P ++ Pn)) /\
(ps_n < 16 -> aval_mem (rdW Wc memc) (A_G_REC + OFF_NCALLS) 4 (ps_n + 1)) /\
aval_mem (rdW Wc memc) ps_c 4 REC_PINS_SET /\
aval_mem (rdW Wc memc) (ps_c + 4) 4 (Z.of_nat (length P)) /\
NoDup (map fst (P ++ Pn)) /\
(forall i pn, nth_error P i = Some pn -> aval_mem (rdW Wc memc) (ps_c + 8 + 8 * Z.of_nat i) 8 (fst pn)) /\
(forall i pn, nth_error (P ++ Pn) i = Some pn -> ps_newb i pn Qb lyc Sc (rdW Wc memc)).

Record ps_core (P Pn : list (Z * Z)) lyc Sc (Wc : world SEGS) memc mdc (k : Z) : Prop := mkPsCore {
pc_J : ajournal SEGS B PINS_SET_STK ps_sp0 ps_FP ly S W mem md [] lyc Sc Wc memc mdc k;
pc_k : k <= rec_spill_frees R + Z.of_nat (length (P ++ Pn));
pc_len : (length (P ++ Pn) <= 4)%nat;
pc_mo : mo_le MT S Sc (rec_spill_frees R * mo_free MT + ps_xm (length (P ++ Pn)));
pc_bb : blocks_bytes Sc <= blocks_bytes S + ps_live (length (P ++ Pn));
pc_frame : forall i r, nth_error ps_saved i = Some r ->
  aval_mem (rdW Wc memc) (ps_sp0 - 8 - 8 * Z.of_nat i) 8 (bv_unsigned (getr regs (Z_to_bv 5 r)));
pc_live : forall pn, In pn (ablocks B ly S) -> ~ In pn O -> In pn (ablocks B lyc Sc);
pc_rec : ps_rec P Pn lyc Sc Wc memc }.

(* the registers the rest of pins_set reads, which a callee keeps *)
Definition ps_keep (j : nat) (rg : bvmap 5 word) : Prop :=
getr rg 2 = w64 (ps_sp0 - 80) /\ getr rg 3 = w64 (as_gp B) /\ getr rg 4 = w64 (as_tp B) /\
getr rg 8 = w64 ps_c /\ getr rg 18 = w64 (ps_c + 4) /\ getr rg 22 = w64 A_G_REC /\ getr rg 23 = w64 SB /\
getr rg 24 = w64 (SB + (ps_c + 4) / 8) /\ ((1 < j)%nat -> getr rg 21 = w64 (ps_c + 8)) /\
((j <= 1)%nat -> getr rg 20 = w64 pf) /\ ((j <= 2)%nat -> getr rg 19 = w64 pl) /\ ((j <= 3)%nat -> getr rg 9 = w64 pv) /\
(forall r, 25 <= r <= 27 -> getr rg (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)).

End entry.

End e.
End f.
End d.
