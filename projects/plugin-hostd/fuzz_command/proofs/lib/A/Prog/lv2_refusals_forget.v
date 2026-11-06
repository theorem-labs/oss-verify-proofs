(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the ASan walk of lv2_refusals_forget (plugin-hostd/fuzz_command, 0x8d278, 91
   instructions), in the form of proofs/cgif/cgif_file_fuzzer/lib/A/ACh1.v .. ACh8.v (cgif_close's segment walk) at
   c8557374ad2e: the symbolic executor over the position-abstract listing between the calls, the callees' contracts
   through cl_callS, and the return through paj_ret_at. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import String ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI04 YI00 YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YI16 YM05 YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdSyms CmdAddr CmdList CmdPa CmdPaLib.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaCall PaCallRun PaLibF PaLibG PaLibH PaSB PaDenot PaNoChain.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob CmdBase CmdRep CmdObj CmdRo CmdZsh PaArt.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
rec_calls_free_c xstrdup_c mix_call_c lv2_refusals_forget_c lv2_refusals_forget_s2 lv2_refusals_forget_s1.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import RecBLemmas.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

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
(* the statement's Section hypotheses (lv2_refusals_forget_c.v:62-65) *)
Hypothesis TRCF : forall fx0 : YK11.FPState, @trec_calls_free_spec fx0 rc SK PI B MT.
Hypothesis TXSTRDUP : forall fx0 : YK11.FPState, @txstrdup_spec fx0 rc SK PI B MT.
Hypothesis TMIX_CALL : forall fx0 : YK11.FPState, @tmix_call_spec fx0 rc SK PI B MT.
Hypothesis VOBJS : cmd_val_objs.
(* the walk's hypotheses with cgif's names *)
Hypothesis HB : CmdBSyms B.
Hypothesis TL : PALib B.
Hypothesis MTL : ameter_laws MT.
Hypothesis SIGP : cmd_sig_prog.
(* the per-binary facts the statement does not carry yet, with the names
   the recorder walks share *)
Hypothesis cmd_prog_img : forall a, Exists (in_zr a) recb_PG -> in_img SEGS a.
Hypothesis cmd_prog_writable : forall ly S (W : world SEGS) mem md a,
AR SEGS B ly S W mem md -> Exists (in_zr a) recb_PG -> writable_at SEGS (mrestrict (w_H W) mem) a.
Hypothesis cmd_ro_ok_of_aro : forall ly S (W : world SEGS) mem md,
AR SEGS B ly S W mem md -> arodata_okP SEGS RLO RHI B (rdW W mem) -> cmd_ro_ok (rdW W mem).
Hypothesis RRO : ro_below_ofl SEGS RLO RHI.
Hypothesis RELRO_IMG : forall a, RLO <= a < RHI -> in_img SEGS a.
Hypothesis cmd_ro_prog_apart : forall a, in_roP SEGS RLO RHI a -> in_img SEGS a /\ ~ Exists (in_zr a) recb_PG.
(* a live block's bytes up to the end of the 8-byte word of its last byte are readable *)
Hypothesis cmd_heap_tail_vis : forall ly S (W : world SEGS) mem md p n e, AR SEGS B ly S W mem md ->
In (p, n) (ablocks B ly S) -> p <= e < p + n -> atail_vis SEGS W mem e.
(* the image literals are read-only bytes (the premise a statement revision deleted; "*" = .str.21 at 0x21fa0 here) *)
Hypothesis CMD_RO_IN : cmd_ro_in (in_roP SEGS CMD_RLO CMD_RHI).
Let LAWS : AR_laws SEGS B := AR_laws_ok SEGS B.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_cmd) (PI := PI).

(* ---- what a journal with the call's footprint keeps ------------------------------------------------------ *)
Lemma lrf_PG_img : forall a, Exists (in_zr a) recb_PG -> 0x10000 <= a < 0x606000.
Proof. intros a H. exact (pa_img_range a (cmd_prog_img a H)). Qed.
Lemma lrf_inFP_inv : forall O a, inFP (lrf_FP O) a ->
Exists (in_zr a) recb_PG \/ exists pn, In pn O /\ fst pn <= a < fst pn + req_size (snd pn).
Proof.
intros O a (r & Hr & Ha). destruct Hr as [<- | [<- | Hr]]; cbn [fst snd] in Ha.
- left. apply recb_grec_in. exact Ha.
- left. apply recb_spill_in. exact Ha.
- right. unfold ablocks_fp in Hr. apply in_map_iff in Hr as ([p n] & <- & Hin). exists (p, n). split; [exact Hin | exact Ha].
Qed.
Lemma lrf_sink_closed : forall O ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md ->
(forall pn, In pn O -> In pn (ablocks B ly S)) -> ~ YI16.sink_open_fp (lrf_FP O).
Proof.
intros O ly S W mem md HAR HO. apply sink_closed_pos. unfold lrf_FP.
constructor; [cbn; unfold A_G_REC; lia|]. constructor; [cbn; unfold A_REC_SPILL; lia|].
unfold ablocks_fp. apply Forall_map. apply Forall_forall. intros [p n] Hin. cbn [fst].
destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR (HO _ Hin)) as (_ & H4096 & _). lia.
Qed.
(* a read-only byte outside the runtime's statics is kept by the journal of the call *)
Lemma lrf_kept_ro : forall STK sp0 O ly S (W : world SEGS) mem md own ly' S' (W' : world SEGS) mem' md' k a,
ajournal SEGS B STK sp0 (lrf_FP O) ly S W mem md own ly' S' W' mem' md' k -> AR SEGS B ly S W mem md ->
(forall pn, In pn O -> In pn (ablocks B ly S)) ->
in_roP SEGS RLO RHI a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
rdW W' mem' a = rdW W mem a.
Proof.
intros STK sp0 O ly S W mem md own ly' S' W' mem' md' k a HJ HAR HO Hro Hown Herr.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HIMG & _).
destruct (cmd_ro_prog_apart a Hro) as [Himg HnPG].
apply HIMG; [exact Himg | exact Hown | exact Herr |].
split; [intros Hso; exfalso; exact (lrf_sink_closed O ly S W mem md HAR HO Hso)|].
intros Hfp. destruct (lrf_inFP_inv O a Hfp) as [HPG | ([p n] & Hin & Ha)]; [exact (HnPG HPG)|].
exact (recb_heap_noimg_m B ly S W mem md p n a HAR (HO _ Hin) Ha Himg).
Qed.
(* a byte of a live block the recorder does not own is kept by the journal of the call *)
Lemma lrf_kept_heap : forall STK sp0 O ly S (W : world SEGS) mem md own ly' S' (W' : world SEGS) mem' md' k q m i,
ajournal SEGS B STK sp0 (lrf_FP O) ly S W mem md own ly' S' W' mem' md' k -> AR SEGS B ly S W mem md ->
(forall pn, In pn O -> In pn (ablocks B ly S)) ->
In (q, m) (ablocks B ly S) -> ~ In (q, m) O -> In (q, m) (ablocks B ly' S') -> 0 <= i < req_size m ->
rdW W' mem' (q + i) = rdW W mem (q + i).
Proof.
intros STK sp0 O ly S W mem md own ly' S' W' mem' md' k q m i HJ HAR HO Hin HnO Hin' Hi.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HBLK & _).
apply (HBLK q m i Hin Hin' Hi). intros Hfp.
destruct (lrf_inFP_inv O (q + i) Hfp) as [HPG | ([p n] & HinO & Ha)].
- exact (recb_heap_noimg_m B ly S W mem md q m (q + i) HAR Hin ltac:(lia) (cmd_prog_img _ HPG)).
- assert (Hne : (q, m) <> (p, n)) by (intros E; apply HnO; rewrite E; exact HinO).
  pose proof (sep_blocks SEGS B LAWS ly S W mem md q m p n HAR Hin (HO _ HinO) Hne) as D.
  unfold zdisjoint in D. cbn [fst snd] in D, Ha. lia.
Qed.
(* arodata_okP survives a journal with the call's footprint (CmdBase.v arodata_ok_journalP) *)
Lemma lrf_aro_kept : forall STK sp0 O ly S (W : world SEGS) mem md own ly' S' (W' : world SEGS) mem' md' k,
ajournal SEGS B STK sp0 (lrf_FP O) ly S W mem md own ly' S' W' mem' md' k -> AR SEGS B ly S W mem md ->
(forall pn, In pn O -> In pn (ablocks B ly S)) ->
arodata_okP SEGS RLO RHI B (rdW W mem) -> arodata_okP SEGS RLO RHI B (rdW W' mem').
Proof.
intros STK sp0 O ly S W mem md own ly' S' W' mem' md' k HJ HAR HO HR.
apply (arodata_ok_journalP SEGS RLO RHI RELRO_IMG (RO := RRO) B STK sp0 (lrf_FP O) ly S W mem md own ly' S' W' mem' md' k HJ);
[| exact HR].
intros a Hro Hfp. destruct (cmd_ro_prog_apart a Hro) as [Himg HnPG].
destruct (lrf_inFP_inv O a Hfp) as [HPG | ([p n] & Hin & Ha)]; [exact (HnPG HPG)|].
exact (recb_heap_noimg_m B ly S W mem md p n a HAR (HO _ Hin) Ha Himg).
Qed.
(* the bytes rec_calls_free(&record.spill, 1) may write *)
Lemma lrf_rcf_inv : forall P a, inFP (rcf_fp A_REC_SPILL [P]) a ->
(A_REC_SPILL + 4 <= a < A_REC_SPILL + 8) \/ exists pn, In pn P /\ fst pn <= a < fst pn + req_size (snd pn).
Proof.
intros P a (r & Hr & Ha). unfold rcf_fp in Hr. cbn [seq map length app] in Hr. destruct Hr as [<- | Hr].
- left. cbn [fst snd] in Ha. unfold CALL_SIZE, CALL_OFF_NARGS in Ha. lia.
- right. unfold ablocks_fp in Hr. cbn [concat] in Hr. rewrite app_nil_r in Hr.
  apply in_map_iff in Hr as ([p n] & <- & Hin). exists (p, n). split; [exact Hin | exact Ha].
Qed.
Lemma lrf_rep_O_in : forall ly S rd R O, rec_repA B ly S rd R O -> forall pn, In pn O -> In pn (ablocks B ly S).
Proof.
intros ly S rd R O (Q & HA & HOQ) pn Hpn. exact (proj1 (arep_lay_in _ _ _ _ R Q pn HA (proj1 (HOQ pn) Hpn))).
Qed.

Lemma lrf_bsum_perm : forall l1 l2, Permutation l1 l2 -> bsum l1 = bsum l2.
Proof.
intros l1 l2 H. induction H as [| x l1 l2 _ IH | x y l | l1 l2 l3 _ IH1 _ IH2]; cbn [bsum fold_right] in *;
unfold bsum in *; cbn [fold_right] in *; lia.
Qed.
Lemma lrf_bsum_nonneg : forall ly S (W : world SEGS) mem md l, AR SEGS B ly S W mem md ->
(forall pn, In pn l -> In pn (ablocks B ly S)) -> 0 <= bsum l.
Proof.
intros ly S W mem md l HAR Hl. induction l as [|[p n] l IH]; cbn [bsum fold_right]; [lia|].
unfold bsum in IH. cbn [fold_right snd].
destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR (Hl _ (or_introl eq_refl))) as (_ & _ & _ & _ & _ & _ & Hn).
assert (0 <= fold_right (fun b acc => snd b + acc) 0 l) by (apply IH; intros pn Hpn; apply Hl; right; exact Hpn). lia.
Qed.
(* the literal "*" is no runtime-owned byte and not the errno cell (the record's tables, lib/A/AF0m.v) *)
Lemma lrf_star_unowned : forall i, 0 <= i < 2 ->
in_roP SEGS RLO RHI (0x21fa0 + i) -> in_roP SEGS RLO RHI (0x21fa0 + i) /\ ~ Exists (in_zr (0x21fa0 + i)) (as_owned_static B) /\
~ (as_errno B <= 0x21fa0 + i < as_errno B + 4).
Proof.
intros i Hi Hro. split; [exact Hro|]. rewrite (ts_owned B HB), (ts_errno B HB). split; [|unfold TFIB_ERRNO; lia].
intros Hex. apply Exists_exists in Hex as (r & Hr & Ha). unfold in_zr in Ha.
assert (Hb : existsb (fun r => (fst r <=? 0x21fa0 + i) && (0x21fa0 + i <? fst r + snd r)) Tfib_owned_static = true).
{ apply existsb_exists. exists r. split; [exact Hr|]. apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia. }
assert (E : i = 0 \/ i = 1) by lia. destruct E as [-> | ->]; vm_compute in Hb; discriminate Hb.
Qed.
(* the string xstrdup copies: uri, or the literal "*" when uri is NULL, at the state of the call *)
Lemma lrf_xs_arg : forall ly S (W : world SEGS) mem md ly1 S1 (W1 : world SEGS) mem1 md1 STK sp0 own k pu uri O F,
AR SEGS B ly S W mem md -> ajournal SEGS B STK sp0 (lrf_FP O) ly S W mem md own ly1 S1 W1 mem1 md1 k ->
(forall pn, In pn O -> In pn (ablocks B ly S)) ->
Permutation (ablocks B ly S) (ablocks B ly1 S1 ++ F) -> (forall pn, In pn F -> In pn O) ->
arodata_okP SEGS RLO RHI B (rdW W mem) ->
astr_argA B ly S (rdW W mem) (in_roP SEGS RLO RHI) O pu uri ->
astr_argA B ly1 S1 (rdW W1 mem1) (in_roP SEGS RLO RHI) [] (lrf_s pu) (Some (lrf_x uri)) /\
atail_vis SEGS W1 mem1 (lrf_s pu + Z.of_nat (length (lrf_x uri))).
Proof.
intros ly S W mem md ly1 S1 W1 mem1 md1 STK sp0 own k pu uri O F HAR HJ HO HPERM HFO HROD HSTR.
pose proof (proj1 HJ) as HAR1.
pose proof (lrf_aro_kept STK sp0 O ly S W mem md own ly1 S1 W1 mem1 md1 k HJ HAR HO HROD) as HROD1.
pose proof (cmd_ro_ok_of_aro ly1 S1 W1 mem1 md1 HAR1 HROD1) as [HROB HROT].
destruct uri as [x|].
- (* uri *)
  destruct HSTR as (Hp0 & Hx & Hn & [(HBLK & HAP) | (HRO & HZ & HHV & HEND)]).
  + destruct HBLK as (q & m & Hqm & Hq & Hqe).
    assert (HnO : ~ In (q, m) O).
    { intros HqO. pose proof (proj1 (Forall_forall _ _) HAP (q, m) HqO) as Hap. unfold iv_apart in Hap. cbn [fst snd] in Hap. lia. }
    assert (Hqm1 : In (q, m) (ablocks B ly1 S1)).
    { pose proof (Permutation_in _ HPERM Hqm) as H. apply in_app_or in H as [H|H]; [exact H | exfalso; exact (HnO (HFO _ H))]. }
    destruct (al_blocks _ _ LAWS _ _ _ _ _ q m HAR Hqm) as (_ & _ & _ & _ & _ & _ & Hm).
    pose proof (req_size_pos m ltac:(lia)) as [_ Hreq].
    assert (Hpu : lrf_s pu = pu) by (unfold lrf_s; destruct (Z.eqb_spec pu 0); [contradiction | reflexivity]).
    rewrite Hpu. cbn [lrf_x darg]. split.
    * split; [exact Hp0|]. split.
      { apply (rastr_kept (rdW W mem)); [exact Hx|]. intros i Hi.
        replace (pu + i) with (q + (pu - q + i)) by lia.
        apply (lrf_kept_heap STK sp0 O ly S W mem md own ly1 S1 W1 mem1 md1 k q m); try assumption; lia. }
      split; [exact Hn|]. left. split; [|constructor]. exists q, m. split; [exact Hqm1 | lia].
    * apply (cmd_heap_tail_vis ly1 S1 W1 mem1 md1 q m); [exact HAR1 | exact Hqm1 | lia].
  + assert (Hpu : lrf_s pu = pu) by (unfold lrf_s; destruct (Z.eqb_spec pu 0); [contradiction | reflexivity]).
    rewrite Hpu. cbn [lrf_x darg]. split.
    * split; [exact Hp0|]. split.
      { apply (rastr_kept (rdW W mem)); [exact Hx|]. intros i Hi.
        destruct (HRO i Hi) as (Hro & Hown & Herr).
        exact (lrf_kept_ro STK sp0 O ly S W mem md own ly1 S1 W1 mem1 md1 k (pu + i) HJ HAR HO Hro Hown Herr). }
      split; [exact Hn|]. right. split; [exact HRO|]. split; [exact HZ|]. split; [exact HHV | exact HEND].
    * intros a Ha. exact (HROT _ HEND a Ha).
- (* the literal "*" *)
  cbn in HSTR. subst pu. unfold lrf_s, lrf_x. cbn [darg Z.eqb].
  assert (HLIT : abytes_atR (rdW W1 mem1) 0x21fa0 RO_lit_21fa0).
  { clear - HROB. unfold cmd_ro_bytes in HROB.
    repeat match type of HROB with
    | abytes_atR _ 0x21fa0 _ /\ _ => exact (proj1 HROB)
    | _ /\ _ => apply proj2 in HROB
    end. }
  assert (Hlin : forall i, 0 <= i < 2 -> in_roP SEGS RLO RHI (0x21fa0 + i)).
  { pose proof CMD_RO_IN as HROIN. clear - HROIN. unfold cmd_ro_in in HROIN.
    repeat match type of HROIN with
    | (forall i, 0 <= i < 2 -> _ (0x21fa0 + i)) /\ _ => exact (proj1 HROIN)
    | _ /\ _ => apply proj2 in HROIN
    end. }
  assert (HEND : In (0x21fa0 + Z.of_nat (length (bstr "*"))) cmd_ro_ends) by (apply In_of_existsb; vm_compute; reflexivity).
  split.
  + split; [lia|]. split.
    { split; [exact HLIT | cbn; intros [H|[]]; vm_compute in H; discriminate H]. }
    split; [cbn; unfold LMAX; lia|]. right. split.
    { intros i Hi. apply lrf_star_unowned; [cbn in Hi; lia | apply Hlin; cbn in Hi; lia]. }
    split; [vm_compute; reflexivity|]. split; [vm_compute; reflexivity | exact HEND].
  + intros a Ha. exact (HROT _ HEND a Ha).
Qed.

(* a callee's journal keeps a byte of the program's statics outside its footprint *)
Lemma lrf_callee_keeps_PG : forall STK1 sp1 FP1 lyc Sc (W : world SEGS) memc mdc own ly2 S2 (W2 : world SEGS) mem2 md2 k1 a,
ajournal SEGS B STK1 sp1 FP1 lyc Sc W memc mdc own ly2 S2 W2 mem2 md2 k1 -> ~ YI16.sink_open_fp FP1 ->
~ inFP FP1 a -> Exists (in_zr a) recb_PG -> rdW W2 mem2 a = rdW W memc a.
Proof.
intros STK1 sp1 FP1 lyc Sc W memc mdc own ly2 S2 W2 mem2 md2 k1 a HJ Hso Hfp HP.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HIMG & _).
destruct (recb_prog_unowned_m B HB cmd_prog_img a HP) as (Himg & Hown & Herr).
apply HIMG; [exact Himg | exact Hown | exact Herr |]. split; [intros H; exfalso; exact (Hso H) | exact Hfp].
Qed.
Lemma lrf_region_kept_PG : forall E (W W2 : world SEGS) m m2 nn b lo hi wlo whi cs,
bv_unsigned (ew E nn) = b ->
(forall a, b + lo <= a < b + hi -> rdW W2 m2 a = rdW W m a) ->
(forall a, b + wlo <= a < b + whi -> writable_at SEGS (mrestrict (w_H W2) m2) a) ->
region_kept SEGS E (mrestrict (w_H W) m) (mrestrict (w_H W2) m2) (YP09.mkRegion (Some nn) lo hi wlo whi cs).
Proof.
intros E W W2 m m2 nn b lo hi wlo whi cs U Hv Hw.
split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite U.
- intros a Ha. apply (mbyte_of_aview SEGS). exact (Hv a Ha).
- intros a Ha _. exact (Hw a Ha).
Qed.

(* what the call leaves, as the statement says it (lv2_refusals_forget_c.v:82-90) *)
Definition lrf_post (ly : alayout) (S : astate) (O : list (Z * Z)) (R : rstate) (uri : option (list byte)) :
alayout -> astate -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop :=
fun ly' S' W' regs' mem' md' => exists O' : list (Z * Z),
 rec_repA B ly' S' (rdW W' mem') (lv2_refusals_forget_m R uri) O' /\
 (forall pn, In pn O' -> In pn O \/ ~ In pn (ablocks B ly S)) /\
 (forall pn, In pn (ablocks B ly S) -> ~ In pn O -> In pn (ablocks B ly' S')) /\
 (forall pn, In pn (ablocks B ly' S') -> (In pn (ablocks B ly S) /\ ~ In pn O) \/ In pn O') /\
 blocks_bytes S' <= blocks_bytes S + LIVE_LV2_REFUSALS_FORGET uri /\
 mo_le MT S S' (XM_LV2_REFUSALS_FORGET MT R uri).

(* a byte outside the write ranges of a segment's regions *)
Ltac lrf_nwr UG UC :=
  let r := fresh "r" in let Hr := fresh "Hr" in let Ha := fresh "Ha" in
  intros (r & Hr & Ha); vm_compute in Hr;
  repeat (destruct Hr as [Hq | Hr];
    [subst r; cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; rewrite ?UG, ?UC in Ha;
     unfold A_G_REC, A_REC_SPILL, OFF_STATE, OFF_CALLS, CALL_SIZE in *; lia | ]);
  destruct Hr.
(* the same, for the entry segments, whose frame region is written *)
Ltac lrf_nwr2 UG UC US :=
  let r := fresh "r" in let Hr := fresh "Hr" in let Ha := fresh "Ha" in
  intros (r & Hr & Ha); vm_compute in Hr;
  repeat (destruct Hr as [Hq | Hr];
    [subst r; cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; rewrite ?UG, ?UC, ?US in Ha;
     unfold A_G_REC, A_REC_SPILL, OFF_STATE, OFF_CALLS, OFF_NCALLS, CALL_SIZE in *; lia | ]);
  destruct Hr.

(* a word of the frame the prologue wrote: the entry value of a callee-saved register *)
Lemma lrf_frame_word : forall E m lo hi wlo whi cs sp (regs : bvmap 5 word) k (r : bv 5) off,
region_ok SEGS E m (YP09.mkRegion (Some 2%nat) lo hi wlo whi cs) -> bv_unsigned (ew E 2) = sp ->
In (YP09.mkChunk off (CVal 8 (SOff k 0))) cs -> ew E k = getr regs r ->
val_mem SEGS m (sp + off) 8 (bv_unsigned (getr regs r)).
Proof.
intros E m lo hi wlo whi cs sp regs k r off HR Hsp Hin Hk.
apply (field_of_region E m 2 sp cs lo hi wlo whi off 8 (SOff k 0) _ HR Hsp Hin); [| | cbn; lia].
- cbn [sv_denot]. rewrite Hk, Z.add_0_r. reflexivity.
- pose proof (bv_unsigned_in_range 64 (getr regs r)) as H. change (bv_modulus 64) with (2 ^ 64) in H. exact H.
Qed.

(* the slot the inlined record() computes on the table arm: g_rec + 16 + 56 * ncalls (after sup_worker_list.v's
   swl_denot_slot, in an earlier version of that file) *)
Lemma lrf_denot_slot : forall E n, ew E 33 = Z_to_bv 64 n -> 0 <= n <= 16 -> ew E 285 = Z_to_bv 64 A_G_REC ->
alu64 ALU_ADD (alu64 ALU_ADD (mul_div M_MUL (ew E 33) (Z_to_bv 64 56)) (Z_to_bv 64 16)) (ew E 285) =
Z_to_bv 64 (A_G_REC + OFF_CALLS + CALL_SIZE * n).
Proof.
intros E n HN Hn HG. rewrite HN, HG. apply bv_eq.
assert (HC64 : 0 <= A_G_REC + OFF_CALLS + CALL_SIZE * n < 2 ^ 64) by (cbv [A_G_REC OFF_CALLS CALL_SIZE]; lia).
rewrite (unsigned_lit_small _ HC64).
rewrite zmd64_sound, !zalu64_sound.
cbv [zmd64 zalu64 zcanon M64 zmd_raw zalu_raw bv_swrap bv_half_modulus bv_modulus].
cbn [Z.of_N]. cbv [A_G_REC OFF_CALLS CALL_SIZE] in *.
assert (H56 : 56 mod 2 ^ 64 = 56) by reflexivity.
assert (H16 : 16 mod 2 ^ 64 = 16) by reflexivity.
assert (HGR : 6174528 mod 2 ^ 64 = 6174528) by reflexivity.
assert (Hnm : n mod 2 ^ 64 = n) by (apply Z.mod_small; lia).
rewrite ?H56, ?H16, ?HGR, ?Hnm, ?Zmod_mod.
rewrite ?(Z.mod_small (n * 56) (2 ^ 64)) by lia.
rewrite ?(Z.mod_small (n * 56 + 16) (2 ^ 64)) by lia.
rewrite ?(Z.mod_small (n * 56 + 16 + 6174528) (2 ^ 64)) by lia.
rewrite ?unsigned_lit_small by lia. lia.
Qed.

(* the callee-saved register cases of the return *)
Ltac lrf_l5 k b := let H := fresh in assert (H : Z_to_bv 5 k = b) by (apply bv_eq; reflexivity); rewrite H; clear H.
Ltac lrf_l5a k b := let H := fresh in assert (H : Z_to_bv 5 k = b) by (apply bv_eq; reflexivity); rewrite H at 1; clear H.
Ltac lrf_keep k kn b G O1 O2 EE Hcs := lrf_l5 k b; rewrite G, O1, O2 by lia; rewrite (EE kn b eq_refl);
  apply Hcs; right; right; change (bv_unsigned b) with k; lia.

Lemma lrf_cont2 : forall ly S W (regs : bvmap 5 word) mem md ch (pu : Z) (uri : option (list byte)) (R : rstate) (O : list (Z * Z))
  ly1 S1 (W1 : world SEGS) (regs1 : bvmap 5 word) md1 (Rb : rstate) (Qb : rlay) (Ob F : list (Z * Z)) (rdb : reader)
  (ms : machine_state) (mat : list word),
afn_pre SEGS B LV2_REFUSALS_FORGET_STK ly S W regs mem md ch ->
arodata_okP SEGS RLO RHI B (rdW W mem) ->
getr regs 10 = w64 pu ->
astr_argA B ly S (rdW W mem) (in_roP SEGS RLO RHI) O pu uri ->
(forall x, uri = Some x -> atail_vis SEGS W mem (pu + Z.of_nat (length x))) ->
rec_repA B ly S (rdW W mem) R O ->
st_nev S + EV_LV2_REFUSALS_FORGET R <= EV_MAX -> blocks_bytes S + LIVE_LV2_REFUSALS_FORGET uri <= LIVE_MAX ->
mo_ok MT S (XM_LV2_REFUSALS_FORGET MT R uri) ->
(* the base representation: the entry's (table not full), or record.spill after rec_calls_free *)
arep_at (ablocks B ly1 S1) rdb A_G_REC A_REC_SPILL Rb Qb -> (forall pn, In pn Ob <-> In pn (lay_blocks Qb)) ->
length (r_calls Rb) = length (r_calls R) -> r_state Rb = r_state R ->
rec_mix (rec_record Rb REC_LV2_REFUSALS_FORGET [lrf_x uri]) (REC_LV2_REFUSALS_FORGET, [lrf_x uri]) = lv2_refusals_forget_m R uri ->
((16 <= length (r_calls R))%nat -> snd (r_spill Rb) = []) ->
Permutation (ablocks B ly S) (ablocks B ly1 S1 ++ F) -> (forall pn, In pn F -> In pn O) ->
(forall pn, In pn O -> In pn Ob \/ In pn F) -> (forall pn, In pn Ob -> In pn O) ->
(forall pn, In pn F -> ~ In pn (ablocks B ly1 S1)) ->
mo_le MT S S1 (rec_spill_frees R * mo_free MT) ->
(* the machine at the call of xstrdup *)
st_ok_pi SEGS VAL (Eimg (Ereg regs1 (lrf_extra1 regs (Z.of_nat (length (r_calls R))) (lrf_c (Z.of_nat (length (r_calls R)))) (r_state R) (lrf_s pu))))
  lrf_ss2 (restrict (w_H W1) ms) ->
sh_ok SEGS L_Bx L_SH (Eimg (Ereg regs1 (lrf_extra1 regs (Z.of_nat (length (r_calls R))) (lrf_c (Z.of_nat (length (r_calls R)))) (r_state R) (lrf_s pu))))
  (mrestrict (w_H W1) (ms_mem ms)) ->
ajournal SEGS B LV2_REFUSALS_FORGET_STK (spZ regs) (lrf_FP O) ly S W mem md [] ly1 S1 W1 (ms_mem ms)
  (with_vm_backing (m_vm_lazy md1) mat md1) (rec_spill_frees R) ->
spZ regs1 = spZ regs - 64 ->
(forall r, (bv_unsigned r = 3 \/ bv_unsigned r = 4 \/ 22 <= bv_unsigned r <= 27) -> getr regs1 r = getr regs r) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - LV2_REFUSALS_FORGET_STK <= a < spZ regs) ->
  ~ (lrf_c (Z.of_nat (length (r_calls R))) <= a < lrf_c (Z.of_nat (length (r_calls R))) + CALL_SIZE) ->
  ~ (A_G_REC + OFF_STATE <= a < A_G_REC + OFF_STATE + 8) ->
  ~ ((length (r_calls R) < 16)%nat /\ A_G_REC + OFF_NCALLS <= a < A_G_REC + OFF_NCALLS + 4) ->
  rdW W1 (ms_mem ms) a = rdb a) ->
((length (r_calls R) < 16)%nat -> aval_mem (rdW W1 (ms_mem ms)) (A_G_REC + OFF_NCALLS) 4 (Z.of_nat (length (r_calls R)) + 1)) ->
SRr SEGS W1 (mkCfg ms (with_vm_backing (m_vm_lazy md1) mat md1))
(apost_base SEGS B LV2_REFUSALS_FORGET_STK (lrf_FP O) regs ly S W mem md (EV_LV2_REFUSALS_FORGET R)
  (lrf_post ly S O R uri)).
Proof.
intros ly S W regs mem md ch pu uri R O ly1 S1 W1 regs1 md1 Rb Qb Ob F rdb ms mat
  HPRE HROD H10 HSTR HTAIL HREP HEV HLIVE HMOK HAB HOB HLR HSR HMOD HSPE HPERM HFO HOF HObO HFn MLE1
  HS SHOK HJ Hsp1 Hcs HKB HNCB.
pose proof HPRE as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hsp16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
set (sp0 := spZ regs) in *.
set (n := Z.of_nat (length (r_calls R))) in *.
set (c := lrf_c n) in *.
assert (HSTK : LV2_REFUSALS_FORGET_STK = 16560) by (vm_compute; reflexivity).
assert (HO : forall pn, In pn O -> In pn (ablocks B ly S)) by exact (lrf_rep_O_in ly S _ R O HREP).
assert (Hn16 : 0 <= n <= 16) by (destruct HREP as (Q & (_ & _ & _ & (H16 & _) & _) & _); unfold n; lia).
pose proof (lrf_c_ok n Hn16) as Hc. fold c in Hc.
destruct (lrf_slot_bounds c Hc) as [Hcb Hc8].
remember (Eimg (Ereg regs1 (lrf_extra1 regs n c (r_state R) (lrf_s pu)))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (rewrite HE; apply Eimg_env).
assert (EE : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew E k = getr regs1 r).
{ intros k r Hk. rewrite HE. pose proof (bv_unsigned_in_range 5 r) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hk. }
assert (EX : forall j, (j < 12)%nat -> ew E (32 + j) = nth j (lrf_extra1 regs n c (r_state R) (lrf_s pu)) (Z_to_bv 64 0)).
{ intros j Hj. rewrite HE, Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_extra. }
assert (E32 : ew E 32 = Z_to_bv 64 SB) by exact (EX 0%nat ltac:(lia)).
assert (E34 : ew E 34 = Z_to_bv 64 c) by exact (EX 2%nat ltac:(lia)).
assert (E35 : ew E 35 = Z_to_bv 64 (r_state R)) by exact (EX 3%nat ltac:(lia)).
assert (E36 : ew E 36 = Z_to_bv 64 (lrf_s pu)) by exact (EX 4%nat ltac:(lia)).
assert (UGR : bv_unsigned (ew E L_GREC) = A_G_REC)
  by (rewrite (HEI L_GREC ltac:(unfold L_GREC, A_OBJ, A_TEXT, A_LIM; lia)); exact (lrf_grec_val VOBJS)).
assert (Usp : bv_unsigned (ew E 2) = sp0 - 64) by (rewrite (EE 2%nat 2%bv eq_refl); exact Hsp1).
assert (E3 : ew E 3 = w64 (as_gp B)) by (rewrite (EE 3%nat 3%bv eq_refl), (Hcs 3%bv (or_introl eq_refl)); exact Hgp).
assert (E4 : ew E 4 = w64 (as_tp B)) by (rewrite (EE 4%nat 4%bv eq_refl), (Hcs 4%bv (or_intror (or_introl eq_refl))); exact Htp).
clear HE.
(* 0x8d330: the call of xstrdup on the string *)
paj_run_tok RUN HS HJ SHOK Bspan.
{ lazymatch goal with |- awr_ok _ _ ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr ?lyx ?own =>
  let rs' := eval vm_compute in rs in change (awr_ok SEGS B Ex rs' stk spx fp b0 bc fr lyx own) end.
  apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|].
  eapply (lrf_awr_cons_grec B HB VOBJS cmd_prog_img); [reflexivity | exact HEI | cbn; unfold OFF_STATE; lia | cbn; unfold OFF_STATE, REC_SIZE; lia |].
  eapply (lrf_awr_cons_slot B HB cmd_prog_img); [reflexivity | exact E34 | exact Hc | cbn; lia | cbn; unfold CALL_SIZE; lia | apply awr_ok_nil]. }
pmkst HS.
prreg HS (1%bv : bv 5) P1. prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
prreg HS (8%bv : bv 5) P8. prreg HS (10%bv : bv 5) P10.
assert (SIGX : SIG CS_xstrdup = BASE + AF_xstrdup).
{ rewrite (SIGP CS_xstrdup ltac:(unfold cmd_prog_syms; cbn [In]; tauto)); f_equal; vm_compute; reflexivity. }
rewrite SIGX.
pose proof (proj1 HJ) as HAR1.
destruct (lrf_xs_arg ly S W mem md ly1 S1 W1 (ms_mem ms0) _ _ _ _ _ pu uri O F HAR0 HJ HO HPERM HFO HROD HSTR)
  as [HSTR1 HTAIL1].
pose proof (lrf_aro_kept _ _ O ly S W mem md _ ly1 S1 W1 (ms_mem ms0) _ _ HJ HAR0 HO HROD) as HROD1.
assert (HBB : blocks_bytes S1 <= blocks_bytes S).
{ rewrite (blocks_bytes_bsum B ly1 S1), (blocks_bytes_bsum B ly S), (lrf_bsum_perm _ _ HPERM), bsum_app.
  pose proof (lrf_bsum_nonneg ly S W mem md F HAR0 ltac:(intros pn Hpn; apply HO, HFO, Hpn)). lia. }
pose proof HJ as (_ & _ & _ & _ & _ & _ & Hnev1 & _).
set (Kx := fun ly2 S2 (W2 : world SEGS) (regs2 : bvmap 5 word) mem2 (md2 : Model) => exists p : Z,
  getr regs2 10 = w64 p /\ 4096 <= p < 2 ^ 64 /\
  Permutation (ablocks B ly2 S2) ((p, LIVE_XSTRDUP (lrf_x uri)) :: ablocks B ly1 S1) /\
  Forall (fun qk => iv_apart p (LIVE_XSTRDUP (lrf_x uri)) (fst qk) (snd qk)) (ablocks B ly1 S1) /\
  in_blockA (ablocks B ly2 S2) p (LIVE_XSTRDUP (lrf_x uri)) /\
  astr_atR (rdW W2 mem2) p (lrf_x uri) /\ astr_atR (rdW W2 mem2) (lrf_s pu) (lrf_x uri) /\
  blocks_bytes S2 <= blocks_bytes S1 + LIVE_XSTRDUP (lrf_x uri) /\
  mo_le MT S1 S2 (XM_XSTRDUP MT (lrf_x uri))).
eapply SRr_bind.
{ eapply (cl_callS_wide B LAWS W1 (ms_regs ms0) (ms_mem ms0) _ LV2_REFUSALS_FORGET_STK sp0 (lrf_FP O) ly S W mem md []
    ly1 S1 _ (rec_spill_frees R) XSTRDUP_STK [] EV_XSTRDUP (-64) (getr (ms_regs ms0) 1) [] Kx HJ).
  - unfold spZ at 1. rewrite P2, Usp. lia.
  - reflexivity.
  - lia.
  - vm_compute. discriminate.
  - rewrite HSTK. vm_compute. discriminate.
  - rewrite P3. exact E3.
  - rewrite P4. exact E4.
  - reflexivity.
  - rewrite P1. apply ret_ok_codeptr_v; [lia | reflexivity].
  - rewrite P1, unsigned_lit_small by lia. lia.
  - apply achain_low. unfold s0Z. rewrite P8, E34, unsigned_lit_small by (unfold A_G_REC, OFF_CALLS, A_REC_SPILL in *; lia).
    unfold A_G_REC, OFF_CALLS, A_REC_SPILL in *. lia.
  - intros HPRE1. eapply SRr_mono.
    { apply (TXSTRDUP fx ly1 S1 W1 (ms_regs ms0) (ms_mem ms0) _ [] (lrf_s pu) (lrf_x uri) HPRE1 HROD1).
      - rewrite P10, E36. reflexivity.
      - left. exact HSTR1.
      - exact HTAIL1.
      - unfold EV_LV2_REFUSALS_FORGET in HEV. lia.
      - unfold LIVE_LV2_REFUSALS_FORGET in HLIVE. unfold lrf_x, lrf_star. lia.
      - apply (mo_ok_step MT MTL S S1 (rec_spill_frees R * mo_free MT)); [|exact MLE1].
        exact HMOK. }
    intros W2 c2 _ H. exact H.
  - intros a Ha. destruct (inFP_nil a Ha).
  - intros ? ? ? ? ? ? _ a Ha. destruct (inFP_nil a Ha). }
cbv beta. intros W2 c2 Hwle2 (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HJc2 & HP2 & (p & Hp10 & [Hp4096 _] & HPm & HFap & _ & Hpx & Hsx & HBB2 & MLE2)).
pose proof (proj1 HJ2) as HAR2.
assert (HKc2 : forall a, Exists (in_zr a) recb_PG -> rdW W2 mem2 a = rdW W1 (ms_mem ms0) a).
{ intros a HP. apply (lrf_callee_keeps_PG _ _ [] _ _ _ _ _ _ _ _ _ _ _ _ a HJc2); [intros (r & Hr & _); destruct Hr | apply inFP_nil | exact HP]. }
assert (HKs2 : forall a, sp0 - 64 <= a < sp0 -> rdW W2 mem2 a = rdW W1 (ms_mem ms0) a).
{ intros a Ha. pose proof HJc2 as (_ & _ & _ & _ & _ & _ & _ & _ & HHI & _).
  apply HHI; [unfold sp0 in *; rewrite HSTK in Hslo; lia | unfold XSTRDUP_STK, ASTACK; lia | apply inFP_nil]. }
(* back at 0x8d334: the frame, g_rec.state and the slot are kept; the GOT word and the shadow cell are not needed *)
jafter_call_keep_pi HS 48%nat regs2 (mrestrict (w_H W2) mem2) HP2 [0; 3; 4]%nat HS2.
match type of HS2 with ?t -> _ => assert (HRK : t); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; [| | | apply Forall_nil].
  - apply (lrf_region_kept_PG E W1 W2 (ms_mem ms0) mem2 2 (sp0 - 64)); [exact Usp | | intros a Ha; cbn in Ha; lia].
    intros a Ha. apply HKs2. lia.
  - apply (lrf_region_kept_PG E W1 W2 (ms_mem ms0) mem2 L_GREC A_G_REC); [exact UGR | |].
    + intros a Ha. apply HKc2. apply recb_grec_in. unfold OFF_STATE, REC_SIZE in *. lia.
    + intros a Ha. apply (cmd_prog_writable _ _ _ _ _ a HAR2). apply recb_grec_in. unfold OFF_STATE, REC_SIZE in *. lia.
  - apply (lrf_region_kept_PG E W1 W2 (ms_mem ms0) mem2 L_C c);
    [unfold L_C; rewrite E34; apply unsigned_lit_small; unfold A_G_REC, OFF_CALLS, A_REC_SPILL in *; lia | |].
    + intros a Ha. apply HKc2. apply (lrf_slot_PG c); [exact Hc | unfold CALL_SIZE in *; lia].
    + intros a Ha. apply (cmd_prog_writable _ _ _ _ _ a HAR2). apply (lrf_slot_PG c); [exact Hc | unfold CALL_SIZE in *; lia]. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
remember (havoc E 48 (map (getr regs2) CLOB)) as E2 eqn:HE2 in HS.
assert (HEI2 : img_env VAL A_LIM E2) by (rewrite HE2; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLD2 : forall k, (k < 48)%nat -> ew E2 k = ew E k) by (intros k Hk; rewrite HE2; apply YN3v.ew_havoc_old; exact Hk).
assert (UGR2 : bv_unsigned (ew E2 L_GREC) = A_G_REC)
  by (rewrite (HEI2 L_GREC ltac:(unfold L_GREC, A_OBJ, A_TEXT, A_LIM; lia)); exact (lrf_grec_val VOBJS)).
assert (SHOK2 : sh_ok SEGS L_Bx L_SH E2 (mrestrict (w_H W2) mem2)).
{ apply (lrf_sh_ok B HB ly2 S2 W2 mem2 md2 E2 c HAR2); [rewrite OLD2 by (unfold L_SB; lia); exact E32 |
  rewrite OLD2 by (unfold L_C; lia); exact E34 | exact Hc]. }
clear SHOK.
(* 0x8d334 .. 0x8d374: c->nargs := 1, c->args[0] := the copy, then the call of mix_call(g_rec.state, c) *)
rewrite P1.
paj_run_tok RUN HS HJ2 SHOK2 Bspan.
{ lazymatch goal with |- awr_ok _ _ ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr ?lyx ?own =>
  let rs' := eval vm_compute in rs in change (awr_ok SEGS B Ex rs' stk spx fp b0 bc fr lyx own) end.
  apply awr_ok_cons_ro; [cbn; lia|].
  eapply (lrf_awr_cons_grec B HB VOBJS cmd_prog_img); [reflexivity | exact HEI2 | cbn; unfold OFF_STATE; lia | cbn; unfold OFF_STATE, REC_SIZE; lia |].
  eapply (lrf_awr_cons_slot B HB cmd_prog_img); [reflexivity | rewrite OLD2 by (unfold L_C; lia); exact E34 | exact Hc | cbn; lia
  | cbn; unfold CALL_SIZE; lia | apply awr_ok_nil]. }
pmkst HS.
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
prreg HS (8%bv : bv 5) Q8. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11.
assert (SIGM : SIG CS_mix_call = BASE + AF_mix_call).
{ rewrite (SIGP CS_mix_call ltac:(unfold cmd_prog_syms; cbn [In]; tauto)); f_equal; vm_compute; reflexivity. }
rewrite SIGM.
pose proof (proj1 HJ2) as HAR3.
(* the slot's three words, from the symbolic state *)
lazymatch type of HS with st_ok _ _ ?ssx (restrict _ ?msx) =>
  let r := eval vm_compute in (nth 2 (ss_mem ssx) got_regionP) in
  pose proof (st_ok_region_nth E2 ssx (restrict _ msx) 2 r HS ltac:(vm_compute; reflexivity)) as HRs;
  cbn [ms_mem restrict mkst] in HRs end.
assert (UC2 : bv_unsigned (ew E2 L_C) = c).
{ unfold L_C. rewrite OLD2 by lia. rewrite E34. apply unsigned_lit_small. unfold A_G_REC, OFF_CALLS, A_REC_SPILL in *. lia. }
assert (A52 : ew E2 52 = getr regs2 10) by (rewrite HE2; reflexivity).
destruct (al_blocks _ _ LAWS _ _ _ _ _ p (LIVE_XSTRDUP (lrf_x uri)) HAR2
  ltac:(eapply Permutation_in; [apply Permutation_sym; exact HPm | left; reflexivity])) as (_ & _ & Hpceil & _).
pose proof (req_size_pos (LIVE_XSTRDUP (lrf_x uri)) ltac:(unfold LIVE_XSTRDUP; lia)) as [HreqL1 HreqL].
assert (Vfn : val_mem SEGS (mrestrict (w_H W2) (ms_mem ms1)) (c + 0) 4 25).
{ refine (field_of_region E2 _ L_C c _ 0 CALL_SIZE 0 CALL_SIZE 0 4 (SLit 25) 25 _ UC2 _ eq_refl _ _);
  [exact HRs | cbn; tauto | cbn; lia | cbn; lia]. }
assert (Vna : val_mem SEGS (mrestrict (w_H W2) (ms_mem ms1)) (c + 4) 4 1).
{ refine (field_of_region E2 _ L_C c _ 0 CALL_SIZE 0 CALL_SIZE 4 4 (SLit 1) 1 _ UC2 _ eq_refl _ _);
  [exact HRs | cbn; tauto | cbn; lia | cbn; lia]. }
assert (Hp64 : 0 <= p < 2 ^ 64) by (pose proof asan_consts as (CC & _); lia).
assert (Varg : val_mem SEGS (mrestrict (w_H W2) (ms_mem ms1)) (c + 8) 8 p).
{ refine (field_of_region E2 _ L_C c _ 0 CALL_SIZE 0 CALL_SIZE 8 8 (SOff 52 0) p _ UC2 _ _ _ _);
  [exact HRs | cbn; tauto | | rewrite lrf_pow8; exact Hp64 | cbn; lia].
  cbn [sv_denot]. rewrite A52, Hp10, Z.add_0_r. unfold w64. apply Z_to_bv_bv_unsigned. }
(* the copy is kept by the run: its block is no byte of g_rec, record.spill or the frame *)
assert (UGR2' : bv_unsigned (ew E2 285) = A_G_REC) by exact UGR2.
assert (UC2' : bv_unsigned (ew E2 34) = c) by exact UC2.
assert (Hpx1 : astr_atR (rdW W2 (ms_mem ms1)) p (lrf_x uri)).
{ apply (rastr_kept (rdW W2 mem2)); [exact Hpx|]. intros i Hi.
  apply (recb_run_keeps_m E2 _ (w_H W2) mem2 (ms_mem ms1) (p + i) HFr0); [unfold LIVE_XSTRDUP in *; lia|].
  intros (r & Hr & Ha). vm_compute in Hr.
  pose proof (blk_off_imgP B ly2 S2 W2 mem2 md2 p (LIVE_XSTRDUP (lrf_x uri)) HAR2
    ltac:(eapply Permutation_in; [apply Permutation_sym; exact HPm | left; reflexivity])) as Hoff.
  unfold off_img, LIVE_XSTRDUP in *.
  repeat (destruct Hr as [Hq | Hr]; [subst r; cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi] in Ha;
    rewrite ?UGR2', ?UC2' in Ha; unfold A_G_REC, A_REC_SPILL, OFF_CALLS in *; lia|]); destruct Hr. }
pose proof (lrf_aro_kept _ _ O ly S W mem md _ ly2 S2 W2 (ms_mem ms1) _ _ HJ2 HAR0 HO HROD) as HROD3.
pose proof HJ2 as (_ & _ & _ & _ & _ & _ & Hnev3 & _).
set (Km := fun ly3 S3 (W3 : world SEGS) (regs3 : bvmap 5 word) (mem3 : word -> option byte) (md3 : Model) =>
  getr regs3 10 = w64 (mixcall (r_state R) (fst (REC_LV2_REFUSALS_FORGET, [lrf_x uri])) (snd (REC_LV2_REFUSALS_FORGET, [lrf_x uri]))) /\
  Permutation (ablocks B ly3 S3) (ablocks B ly2 S2) /\ ly3 = ly2 /\ S3 = S2).
eapply SRr_bind.
{ eapply (cl_callS_wide B LAWS W2 (ms_regs ms1) (ms_mem ms1) _ LV2_REFUSALS_FORGET_STK sp0 (lrf_FP O) ly S W mem md []
    ly2 S2 _ (rec_spill_frees R + EV_XSTRDUP) MIX_CALL_STK [] EV_MIX_CALL (-64) (getr (ms_regs ms1) 1) [] Km HJ2).
  - unfold spZ at 1. rewrite Q2, OLD2, Usp by lia. lia.
  - reflexivity.
  - lia.
  - vm_compute. discriminate.
  - rewrite HSTK. vm_compute. discriminate.
  - rewrite Q3, OLD2 by lia. exact E3.
  - rewrite Q4, OLD2 by lia. exact E4.
  - reflexivity.
  - rewrite Q1. apply ret_ok_codeptr_v; [lia | reflexivity].
  - rewrite Q1, unsigned_lit_small by lia. lia.
  - apply achain_low. unfold s0Z. rewrite Q8, OLD2, E34, unsigned_lit_small by (unfold A_G_REC, OFF_CALLS, A_REC_SPILL in *; lia).
    unfold A_G_REC, OFF_CALLS, A_REC_SPILL in *. lia.
  - intros HPRE3. eapply SRr_mono.
    { apply (TMIX_CALL fx ly2 S2 W2 (ms_regs ms1) (ms_mem ms1) _ (r_state R) c (REC_LV2_REFUSALS_FORGET, [lrf_x uri])
        [(p, LIVE_XSTRDUP (lrf_x uri))] (afn_pre_na_of SEGS B _ _ _ _ _ _ _ _ HPRE3) HROD3).
      - rewrite Q10, OLD2, E35 by lia. reflexivity.
      - destruct HREP as (Q & (_ & _ & _ & _ & _ & _ & (_ & _ & _ & _ & _ & _ & _ & _ & HR4 & _) & _) & _). exact HR4.
      - rewrite Q11, OLD2, E34 by lia. reflexivity.
      - unfold c, lrf_c. destruct (Z.eqb_spec n 16) as [E16 | E16]; [right; reflexivity | left].
        exists n. split; [unfold REC_CALLS_MAX; lia | reflexivity].
      - split; [cbn; unfold REC_LV2_REFUSALS_FORGET, REC_FN_COUNT; lia|]. split; [cbn; lia|]. split; [reflexivity|].
        split; [unfold CALL_OFF_FN; apply (aval_mem_view SEGS); exact Vfn|].
        split; [unfold CALL_OFF_NARGS; apply (aval_mem_view SEGS); exact Vna|].
        split; [cbn; apply NoDup_ListNoDup; apply List.NoDup_cons; [cbn; tauto | apply List.NoDup_nil]|].
        intros k s pn Hs Hpn. destruct k as [|k]; [|destruct k; discriminate Hs].
        cbn in Hs, Hpn. injection Hs as <-. injection Hpn as <-. cbn [fst snd]. unfold CALL_OFF_ARGS.
        split; [rewrite Z.mul_0_r, Z.add_0_r; apply (aval_mem_view SEGS); exact Varg|].
        split; [lia|]. split; [eapply Permutation_in; [apply Permutation_sym; exact HPm | left; reflexivity]|].
        split; [|exact Hpx1]. destruct HSTR1 as (_ & _ & HnL & _). unfold LIVE_XSTRDUP, LMAX in *. lia.
      - exact (cmd_ro_ok_of_aro ly2 S2 W2 (ms_mem ms1) _ HAR3 HROD3).
      - unfold EV_MIX_CALL, EV_LV2_REFUSALS_FORGET, EV_XSTRDUP in *. lia. }
    intros W3 c3 _ H. exact H.
  - intros a Ha. destruct (inFP_nil a Ha).
  - intros ? ? ? ? ? ? _ a Ha. destruct (inFP_nil a Ha). }
cbv beta. intros W3 c3 Hwle3 (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ3 & HJc3 & HP3 & (Hm10 & HPm3 & ELY3 & ES3)).
pose proof (proj1 HJ3) as HAR4.
assert (HKc3 : forall a, Exists (in_zr a) recb_PG -> rdW W3 mem3 a = rdW W2 (ms_mem ms1) a).
{ intros a HP. apply (lrf_callee_keeps_PG _ _ [] _ _ _ _ _ _ _ _ _ _ _ _ a HJc3); [intros (r & Hr & _); destruct Hr | apply inFP_nil | exact HP]. }
assert (HKs3 : forall a, sp0 - 64 <= a < sp0 -> rdW W3 mem3 a = rdW W2 (ms_mem ms1) a).
{ intros a Ha. pose proof HJc3 as (_ & _ & _ & _ & _ & _ & _ & _ & HHI & _).
  apply HHI; [unfold sp0 in *; rewrite HSTK in Hslo; lia | unfold MIX_CALL_STK, ESTACK; lia | apply inFP_nil]. }
assert (Usp2 : bv_unsigned (ew E2 2) = sp0 - 64) by (rewrite OLD2 by lia; exact Usp).
(* back at 0x8d378 *)
jafter_call_keep_pi HS 64%nat regs3 (mrestrict (w_H W3) mem3) HP3 [0; 1; 2]%nat HS3.
match type of HS3 with ?t -> _ => assert (HRK : t); [|specialize (HS3 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; [| | | apply Forall_nil].
  - apply (lrf_region_kept_PG E2 W2 W3 (ms_mem ms1) mem3 2 (sp0 - 64)); [exact Usp2 | | intros a Ha; cbn in Ha; lia].
    intros a Ha. apply HKs3. lia.
  - apply (lrf_region_kept_PG E2 W2 W3 (ms_mem ms1) mem3 L_GREC A_G_REC); [exact UGR2 | |].
    + intros a Ha. apply HKc3. apply recb_grec_in. unfold OFF_STATE, REC_SIZE in *. lia.
    + intros a Ha. apply (cmd_prog_writable _ _ _ _ _ a HAR4). apply recb_grec_in. unfold OFF_STATE, REC_SIZE in *. lia.
  - apply (lrf_region_kept_PG E2 W2 W3 (ms_mem ms1) mem3 L_C c); [exact UC2 | |].
    + intros a Ha. apply HKc3. apply (lrf_slot_PG c); [exact Hc | unfold CALL_SIZE in *; lia].
    + intros a Ha. apply (cmd_prog_writable _ _ _ _ _ a HAR4). apply (lrf_slot_PG c); [exact Hc | unfold CALL_SIZE in *; lia]. }
clear HS. rewrite <- restrict_mkst_fx in HS3. rename HS3 into HS.
remember (havoc E2 64 (map (getr regs3) CLOB)) as Ef eqn:HEf in HS.
assert (HEIf : img_env VAL A_LIM Ef) by (rewrite HEf; apply img_env_havoc; [exact HEI2 | cbv; lia]).
assert (OLDf : forall k, (k < 64)%nat -> ew Ef k = ew E2 k) by (intros k Hk; rewrite HEf; apply YN3v.ew_havoc_old; exact Hk).
assert (UGRf : bv_unsigned (ew Ef L_GREC) = A_G_REC)
  by (rewrite (HEIf L_GREC ltac:(unfold L_GREC, A_OBJ, A_TEXT, A_LIM; lia)); exact (lrf_grec_val VOBJS)).
assert (SHOK3 : sh_ok SEGS L_Bx L_SH Ef (mrestrict (w_H W3) mem3)).
{ apply (lrf_sh_ok B HB ly3 S3 W3 mem3 md3 Ef c HAR4); [rewrite OLDf, OLD2 by (unfold L_SB; lia); exact E32 |
  rewrite OLDf, OLD2 by (unfold L_C; lia); exact E34 | exact Hc]. }
clear SHOK2.
(* 0x8d378 .. 0x8d39c: g_rec.state := the digest, the callee-saved registers back, return *)
rewrite Q1.
paj_run_tok RUN HS HJ3 SHOK3 Bspan.
{ lazymatch goal with |- awr_ok _ _ ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr ?lyx ?own =>
  let rs' := eval vm_compute in rs in change (awr_ok SEGS B Ex rs' stk spx fp b0 bc fr lyx own) end.
  apply awr_ok_cons_ro; [cbn; lia|].
  eapply (lrf_awr_cons_grec B HB VOBJS cmd_prog_img); [reflexivity | exact HEIf | cbn; unfold OFF_STATE; lia | cbn; unfold OFF_STATE, REC_SIZE; lia |].
  eapply (lrf_awr_cons_slot B HB cmd_prog_img); [reflexivity | rewrite OLDf, OLD2 by (unfold L_C; lia); exact E34 | exact Hc | cbn; lia
  | cbn; unfold CALL_SIZE; lia | apply awr_ok_nil]. }
(* 0x8d39c: return *)
eapply (RET W3 _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros matF.
prreg HS (1%bv : bv 5) F1.
(* the facts the run and the calls leave *)
assert (UGR' : bv_unsigned (ew E 285) = A_G_REC) by exact UGR.
assert (UC' : bv_unsigned (ew E 34) = c) by (rewrite E34; apply unsigned_lit_small; unfold A_G_REC, OFF_CALLS, A_REC_SPILL in *; lia).
assert (UGRf' : bv_unsigned (ew Ef 285) = A_G_REC) by exact UGRf.
assert (UCf' : bv_unsigned (ew Ef 34) = c) by (rewrite OLDf by lia; exact UC2').
assert (KPG : forall a, 0 <= a < 2 ^ 64 -> ~ (c <= a < c + CALL_SIZE) -> ~ (A_G_REC + OFF_STATE <= a < A_G_REC + OFF_STATE + 8) ->
  Exists (in_zr a) recb_PG -> rdW W3 (ms_mem ms2) a = rdW W1 (ms_mem ms) a).
{ intros a Ha Hns Hnt HP.
  rewrite (recb_run_keeps_m Ef _ (w_H W3) mem3 (ms_mem ms2) a HFr1 Ha) by lrf_nwr UGRf' UCf'.
  rewrite (HKc3 a HP).
  rewrite (recb_run_keeps_m E2 _ (w_H W2) mem2 (ms_mem ms1) a HFr0 Ha) by lrf_nwr UGR2' UC2'.
  rewrite (HKc2 a HP).
  rewrite (recb_run_keeps_m E _ (w_H W1) (ms_mem ms) (ms_mem ms0) a HFr Ha) by lrf_nwr UGR' UC'.
  reflexivity. }
assert (HAR1' := HAR1).
assert (KHP : forall q k i, In (q, k) (ablocks B ly1 S1) -> 0 <= i < req_size k ->
  rdW W3 (ms_mem ms2) (q + i) = rdW W1 (ms_mem ms) (q + i)).
{ intros q k i Hin Hi.
  pose proof (blk_off_imgP B ly1 S1 W1 (ms_mem ms0) _ q k HAR1 Hin) as Hoff. unfold off_img in Hoff.
  destruct (al_blocks _ _ LAWS _ _ _ _ _ q k HAR1 Hin) as (_ & Hq4096 & Hqc & _).
  assert (Hin2 : In (q, k) (ablocks B ly2 S2)) by (eapply Permutation_in; [apply Permutation_sym; exact HPm | right; exact Hin]).
  assert (Hin3 : In (q, k) (ablocks B ly3 S3)) by (eapply Permutation_in; [apply Permutation_sym; exact HPm3 | exact Hin2]).
  assert (Hqi : 0 <= q + i < 2 ^ 64) by (pose proof asan_consts as (CC & _); lia).
  rewrite (recb_run_keeps_m Ef _ (w_H W3) mem3 (ms_mem ms2) (q + i) HFr1 Hqi) by lrf_nwr UGRf' UCf'.
  pose proof HJc3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HB3 & _).
  rewrite (HB3 q k i Hin2 Hin3 Hi (inFP_nil _)).
  rewrite (recb_run_keeps_m E2 _ (w_H W2) mem2 (ms_mem ms1) (q + i) HFr0 Hqi) by lrf_nwr UGR2' UC2'.
  pose proof HJc2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HB2 & _).
  rewrite (HB2 q k i Hin Hin2 Hi (inFP_nil _)).
  rewrite (recb_run_keeps_m E _ (w_H W1) (ms_mem ms) (ms_mem ms0) (q + i) HFr Hqi) by lrf_nwr UGR' UC'.
  reflexivity. }
(* the slot and the state word at the return *)
lazymatch type of HS with st_ok_pi _ _ _ ?ssx (restrict _ ?msx) =>
  let r1 := eval vm_compute in (nth 1 (ss_mem ssx) got_regionP) in
  let r2 := eval vm_compute in (nth 2 (ss_mem ssx) got_regionP) in
  pose proof (st_ok_region_nth Ef (abs_ss VAL ssx) (restrict _ msx) 1 r1 HS ltac:(vm_compute; reflexivity)) as HRt;
  pose proof (st_ok_region_nth Ef (abs_ss VAL ssx) (restrict _ msx) 2 r2 HS ltac:(vm_compute; reflexivity)) as HRs3;
  cbn [ms_mem restrict mkst] in HRt, HRs3 end.
assert (UCf : bv_unsigned (ew Ef L_C) = c) by exact UCf'.
assert (Wfn : val_mem SEGS (mrestrict (w_H W3) (ms_mem ms2)) (c + 0) 4 25).
{ refine (field_of_region Ef _ L_C c _ 0 CALL_SIZE 0 CALL_SIZE 0 4 (SLit 25) 25 _ UCf _ eq_refl _ _);
  [exact HRs3 | cbn; tauto | cbn; lia | cbn; lia]. }
assert (Wna : val_mem SEGS (mrestrict (w_H W3) (ms_mem ms2)) (c + 4) 4 1).
{ refine (field_of_region Ef _ L_C c _ 0 CALL_SIZE 0 CALL_SIZE 4 4 (SLit 1) 1 _ UCf _ eq_refl _ _);
  [exact HRs3 | cbn; tauto | cbn; lia | cbn; lia]. }
assert (Warg : val_mem SEGS (mrestrict (w_H W3) (ms_mem ms2)) (c + 8) 8 p).
{ refine (field_of_region Ef _ L_C c _ 0 CALL_SIZE 0 CALL_SIZE 8 8 (SOff 52 0) p _ UCf _ _ _ _);
  [exact HRs3 | cbn; tauto | | rewrite lrf_pow8; exact Hp64 | cbn; lia].
  cbn [sv_denot]. rewrite OLDf by lia. rewrite A52, Hp10, Z.add_0_r. unfold w64. apply Z_to_bv_bv_unsigned. }
set (hF := mixcall (r_state R) REC_LV2_REFUSALS_FORGET [lrf_x uri]).
assert (HhF : 0 <= hF < 2 ^ 64).
{ unfold hF. apply mixcall_range. destruct HREP as (Q & (_ & _ & _ & _ & _ & _ & (_ & _ & _ & _ & _ & _ & _ & _ & HR4 & _) & _) & _). exact HR4. }
assert (Wst : val_mem SEGS (mrestrict (w_H W3) (ms_mem ms2)) (A_G_REC + OFF_STATE) 8 hF).
{ refine (field_of_region Ef _ L_GREC A_G_REC _ OFF_STATE (OFF_STATE + 8) OFF_STATE (OFF_STATE + 8) OFF_STATE 8 (SOff 68 0) hF _ UGRf _ _ _ _);
  [exact HRt | cbn; tauto | | rewrite lrf_pow8; exact HhF | cbn; lia].
  cbn [sv_denot]. assert (A68 : ew Ef 68 = getr regs3 10) by (rewrite HEf; reflexivity).
  rewrite A68, Hm10, Z.add_0_r. unfold w64. apply Z_to_bv_bv_unsigned. }
prreg HS (2%bv : bv 5) G2. prreg HS (3%bv : bv 5) G3. prreg HS (4%bv : bv 5) G4.
prreg HS (8%bv : bv 5) G8. prreg HS (9%bv : bv 5) G9.
prreg HS (18%bv : bv 5) G18. prreg HS (19%bv : bv 5) G19. prreg HS (20%bv : bv 5) G20. prreg HS (21%bv : bv 5) G21.
prreg HS (22%bv : bv 5) G22. prreg HS (23%bv : bv 5) G23. prreg HS (24%bv : bv 5) G24.
prreg HS (25%bv : bv 5) G25. prreg HS (26%bv : bv 5) G26. prreg HS (27%bv : bv 5) G27.
(* the callee-saved registers come back: the frame's words, sp + 64, and the untouched ones *)
assert (HEXr : forall j r, (j < 7)%nat -> nth_error lrf_saved j = Some r -> ew E (37 + j) = getr regs (Z_to_bv 5 r)).
{ intros j r Hj Hr. replace (37 + j)%nat with (32 + (5 + j))%nat by lia. rewrite (EX (5 + j)%nat ltac:(lia)).
  do 7 (destruct j as [|j]; [cbn [nth_error lrf_saved] in Hr; injection Hr as <-;
    cbn [nth lrf_extra1 lrf_extra0 lrf_saved map app Nat.add]; reflexivity|]). lia. }
assert (HPRES : aregs_preserved regs (ms_regs ms2)).
{ intros r Hr. unfold acallee_saved in Hr.
  assert (Hr' : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/
                r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
  destruct Hr' as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]]]]]].
  - lrf_l5 2 (2%bv : bv 5). rewrite G2, OLDf, OLD2 by lia. apply bv_eq.
    rewrite Z_to_bv_unsigned, Usp. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
    pose proof (bv_unsigned_in_range 64 (getr regs 2)) as HR2. change (bv_modulus 64) with (2 ^ 64) in HR2.
    unfold sp0, spZ. rewrite Z.sub_add, Z.mod_small by lia. reflexivity.
  - lrf_l5 3 (3%bv : bv 5). rewrite G3, OLDf, OLD2 by lia. rewrite (EE 3%nat 3%bv eq_refl).
    exact (Hcs 3%bv (or_introl eq_refl)).
  - lrf_l5 4 (4%bv : bv 5). rewrite G4, OLDf, OLD2 by lia. rewrite (EE 4%nat 4%bv eq_refl).
    exact (Hcs 4%bv (or_intror (or_introl eq_refl))).
  - lrf_l5a 8 (8%bv : bv 5). rewrite G8, OLDf, OLD2 by lia. exact (HEXr 1%nat 8 ltac:(lia) eq_refl).
  - lrf_l5a 9 (9%bv : bv 5). rewrite G9, OLDf, OLD2 by lia. exact (HEXr 2%nat 9 ltac:(lia) eq_refl).
  - lrf_l5a 18 (18%bv : bv 5). rewrite G18, OLDf, OLD2 by lia. exact (HEXr 3%nat 18 ltac:(lia) eq_refl).
  - lrf_l5a 19 (19%bv : bv 5). rewrite G19, OLDf, OLD2 by lia. exact (HEXr 4%nat 19 ltac:(lia) eq_refl).
  - lrf_l5a 20 (20%bv : bv 5). rewrite G20, OLDf, OLD2 by lia. exact (HEXr 5%nat 20 ltac:(lia) eq_refl).
  - lrf_l5a 21 (21%bv : bv 5). rewrite G21, OLDf, OLD2 by lia. exact (HEXr 6%nat 21 ltac:(lia) eq_refl).
  - lrf_keep 22 22%nat (22%bv : bv 5) G22 OLDf OLD2 EE Hcs.
  - lrf_keep 23 23%nat (23%bv : bv 5) G23 OLDf OLD2 EE Hcs.
  - lrf_keep 24 24%nat (24%bv : bv 5) G24 OLDf OLD2 EE Hcs.
  - lrf_keep 25 25%nat (25%bv : bv 5) G25 OLDf OLD2 EE Hcs.
  - lrf_keep 26 26%nat (26%bv : bv 5) G26 OLDf OLD2 EE Hcs.
  - lrf_keep 27 27%nat (27%bv : bv 5) G27 OLDf OLD2 EE Hcs. }
assert (Hra1 : getr (ms_regs ms2) 1 = getr regs 1).
{ rewrite F1, OLDf, OLD2 by lia. exact (HEXr 0%nat 1 ltac:(lia) eq_refl). }
pose proof Hra as Hra'. unfold YK0s.ret_ok in Hra'.
(* the block of the copy, kept by mix_call and the last segment *)
set (x := lrf_x uri) in *. set (L := LIVE_XSTRDUP x) in *.
assert (HinF2 : In (p, L) (ablocks B ly2 S2)) by (eapply Permutation_in; [apply Permutation_sym; exact HPm | left; reflexivity]).
assert (HinF3 : In (p, L) (ablocks B ly3 S3)) by (eapply Permutation_in; [apply Permutation_sym; exact HPm3 | exact HinF2]).
assert (Hbl13 : forall pn, In pn (ablocks B ly1 S1) -> In pn (ablocks B ly3 S3)).
{ intros pn Hpn. eapply Permutation_in; [apply Permutation_sym; exact HPm3|].
  eapply Permutation_in; [apply Permutation_sym; exact HPm | right; exact Hpn]. }
pose proof (blk_off_imgP B ly2 S2 W2 mem2 md2 p L HAR2 HinF2) as Hpoff. unfold off_img in Hpoff.
assert (KHP2 : forall i, 0 <= i < req_size L -> rdW W3 (ms_mem ms2) (p + i) = rdW W2 (ms_mem ms1) (p + i)).
{ intros i Hi. assert (Hqi : 0 <= p + i < 2 ^ 64) by lia.
  rewrite (recb_run_keeps_m Ef _ (w_H W3) mem3 (ms_mem ms2) (p + i) HFr1 Hqi) by lrf_nwr UGRf' UCf'.
  pose proof HJc3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HB3 & _).
  exact (HB3 p L i HinF2 HinF3 Hi (inFP_nil _)). }
assert (HxL : Z.of_nat (length x) <= LMAX) by (destruct HSTR1 as (_ & _ & HnL & _); lia).
assert (Hnc : A_G_REC + OFF_CALLS <= c <= A_REC_SPILL) by exact Hcb.
assert (Hstkg : alloc_ceiling <= sp0 - LV2_REFUSALS_FORGET_STK) by lia.
(* the recorder after the call *)
pose proof (lrf_rep_post (ablocks B ly1 S1) (ablocks B ly3 S3) rdb (rdW W3 (ms_mem ms2)) Rb Qb REC_LV2_REFUSALS_FORGET p L x HAB)
  as HRP.
rewrite HLR, HSR, HMOD in HRP. fold n in HRP. fold c in HRP.
specialize (HRP ltac:(intros Hlt; apply (aval_mem_kept (rdW W1 (ms_mem ms))); [exact (HNCB Hlt)|];
  intros k Hk; apply KPG; [| | |apply recb_grec_in];
  unfold A_G_REC, OFF_NCALLS, OFF_STATE, OFF_CALLS, A_REC_SPILL, CALL_SIZE, REC_SIZE in *; lia)).
specialize (HRP ltac:(intros H16; apply HSPE; exact H16)).
specialize (HRP ltac:(vm_compute; split; congruence)).
specialize (HRP ltac:(rewrite <- (Z.add_0_r c) at 1; exact (aval_mem_view SEGS _ _ _ _ _ Wfn))).
specialize (HRP (aval_mem_view SEGS _ _ _ _ _ Wna) (aval_mem_view SEGS _ _ _ _ _ Warg) (aval_mem_view SEGS _ _ _ _ _ Wst)).
specialize (HRP ltac:(intros a Ha Hns Hnt Hnn;
  assert (HPa : Exists (in_zr a) recb_PG) by (destruct Ha; [apply recb_grec_in | apply recb_spill_in]; assumption);
  pose proof (lrf_PG_img a HPa) as HIa;
  rewrite (KPG a ltac:(lia) Hns Hnt HPa); apply HKB; [lia | lia | exact Hns | exact Hnt | exact Hnn])).
specialize (HRP ltac:(intros q k i Hin Hi;
  destruct (al_blocks _ _ LAWS _ _ _ _ _ q k HAR1 Hin) as (_ & Hq4 & Hqc & _ & _ & _ & Hk);
  pose proof (req_size_pos k ltac:(lia)) as [_ Hrk];
  pose proof (blk_off_imgP B ly1 S1 W1 (ms_mem ms0) _ q k HAR1 Hin) as Hoff; unfold off_img in Hoff;
  rewrite (KHP q k i Hin ltac:(lia)); apply HKB;
  unfold A_G_REC, OFF_NCALLS, OFF_STATE, OFF_CALLS, A_REC_SPILL, CALL_SIZE in *; lia)).
specialize (HRP Hbl13 HinF3 eq_refl HxL ltac:(lia)).
specialize (HRP ltac:(apply (rastr_kept (rdW W2 (ms_mem ms1))); [exact Hpx1 | intros i Hi; apply KHP2; unfold L, LIVE_XSTRDUP in *; lia])).
specialize (HRP HFap ltac:(unfold iv_apart, A_G_REC, REC_SIZE in *; lia) ltac:(unfold iv_apart, A_REC_SPILL, SC_SIZE in *; lia)).
set (Q' := lrf_lay Qb (length (r_calls R)) (p, L)) in HRP.
assert (HlS : (16 <= length (r_calls R))%nat -> l_spill Qb = []) by (intros H16; exact (lrf_spill_nil _ _ _ _ Rb Qb HAB (HSPE H16))).
assert (HFx : forall pn, In pn F -> ~ In pn (ablocks B ly1 S1)) by exact HFn.
(* the meter: the spill arm's frees, the copy, and mix_call's nothing *)
assert (MLE3 : mo_le MT S2 S3 0) by (rewrite ES3; exact (mo_le_refl MT MTL S2)).
unfold apost_base. eexists ly3, S3, (ms_regs ms2), (ms_mem ms2), _.
split; [rewrite Hra1, Hra'; reflexivity|].
split; [apply (ajournal_mono_k SEGS B) with (k := rec_spill_frees R + EV_XSTRDUP + EV_MIX_CALL);
  [apply (ajournal_materialize SEGS B LAWS pa_segs_low); exact HJ3 | unfold EV_LV2_REFUSALS_FORGET, EV_MIX_CALL; lia]|].
split; [exact HPRES|].
exists (lay_blocks Q').
split; [exists Q'; split; [exact HRP | intros pn; tauto]|].
split.
{ intros pn Hpn. destruct (lrf_lay_new Qb _ (p, L) pn Hpn) as [Hold | ->].
  - left. apply HObO. apply HOB. exact Hold.
  - destruct (in_dec lrf_pair_dec (p, L) (ablocks B ly S)) as [Hin | Hnin]; [left | right; exact Hnin].
    apply (Permutation_in _ HPERM) in Hin. apply in_app_or in Hin as [Hin | Hin]; [|exact (HFO _ Hin)].
    exfalso. pose proof (proj1 (Forall_forall _ _) HFap (p, L) Hin) as Hap. unfold iv_apart, L, LIVE_XSTRDUP in Hap.
    cbn [fst snd] in Hap. lia. }
split.
{ intros pn Hin HnO. apply (Permutation_in _ HPERM) in Hin. apply in_app_or in Hin as [Hin | Hin];
  [exact (Hbl13 pn Hin) | exfalso; exact (HnO (HFO _ Hin))]. }
split.
{ intros pn Hin. apply (Permutation_in _ HPm3) in Hin. apply (Permutation_in _ HPm) in Hin.
  destruct Hin as [<- | Hin]; [right; apply lrf_lay_pn|].
  assert (Hin0 : In pn (ablocks B ly S)) by (eapply Permutation_in; [apply Permutation_sym; exact HPERM | apply in_or_app; left; exact Hin]).
  destruct (in_dec lrf_pair_dec pn O) as [HinO | HnO]; [right | left; split; [exact Hin0 | exact HnO]].
  destruct (HOF pn HinO) as [HOb | HFp]; [|exfalso; exact (HFx pn HFp Hin)].
  apply lrf_lay_old; [exact HlS | apply HOB; exact HOb]. }
split.
{ rewrite ES3. unfold LIVE_LV2_REFUSALS_FORGET. change (darg uri (bstr "*"%string)) with x. lia. }
apply (mo_le_mono MT MTL S S3 (rec_spill_frees R * mo_free MT + XM_XSTRDUP MT x + 0)).
- exact (mo_le_trans MT MTL _ _ _ _ _ (mo_le_trans MT MTL _ _ _ _ _ MLE1 MLE2) MLE3).
- unfold XM_LV2_REFUSALS_FORGET, x, lrf_x, lrf_star. rewrite Z.add_0_r. apply Z.le_refl.
Qed.

(* the string argument's address: 0 for NULL, else a byte of a live block or of the image *)
Lemma lrf_pu_cases : forall ly S (W : world SEGS) mem md O pu uri, AR SEGS B ly S W mem md ->
astr_argA B ly S (rdW W mem) (in_roP SEGS RLO RHI) O pu uri ->
(uri = None /\ pu = 0) \/ (uri <> None /\ 0 < pu < 2 ^ 64).
Proof.
intros ly S W mem md O pu uri HAR HSTR. destruct uri as [x|]; [right | left; split; [reflexivity | exact HSTR]].
split; [discriminate|].
destruct HSTR as (Hp0 & _ & _ & [((q & m & Hqm & Hq & Hqe) & _) | (HRO & _)]).
- destruct (al_blocks _ _ LAWS _ _ _ _ _ q m HAR Hqm) as (_ & Hq4 & Hqc & _ & _ & _ & Hm).
  pose proof (req_size_pos m ltac:(lia)) as [_ Hrm]. pose proof asan_consts as (C1 & _). lia.
- destruct (HRO 0 ltac:(lia)) as (Hro & _). rewrite Z.add_0_r in Hro.
  pose proof (pa_img_range pu (proj1 (cmd_ro_prog_apart pu Hro))). lia.
Qed.

(* from the join of record()'s two arms (0x8d2f0) to the call of xstrdup *)
Lemma lrf_cont1 : forall ly S W (regs : bvmap 5 word) mem md ch (pu : Z) (uri : option (list byte)) (R : rstate) (O : list (Z * Z))
  ly1 S1 (W1 : world SEGS) (regsJ : bvmap 5 word) memJ mdJ (Rb : rstate) (Qb : rlay) (Ob F : list (Z * Z)) (rdb : reader),
afn_pre SEGS B LV2_REFUSALS_FORGET_STK ly S W regs mem md ch ->
arodata_okP SEGS RLO RHI B (rdW W mem) ->
getr regs 10 = w64 pu ->
astr_argA B ly S (rdW W mem) (in_roP SEGS RLO RHI) O pu uri ->
(forall x, uri = Some x -> atail_vis SEGS W mem (pu + Z.of_nat (length x))) ->
rec_repA B ly S (rdW W mem) R O ->
st_nev S + EV_LV2_REFUSALS_FORGET R <= EV_MAX -> blocks_bytes S + LIVE_LV2_REFUSALS_FORGET uri <= LIVE_MAX ->
mo_ok MT S (XM_LV2_REFUSALS_FORGET MT R uri) ->
arep_at (ablocks B ly1 S1) rdb A_G_REC A_REC_SPILL Rb Qb -> (forall pn, In pn Ob <-> In pn (lay_blocks Qb)) ->
length (r_calls Rb) = length (r_calls R) -> r_state Rb = r_state R ->
rec_mix (rec_record Rb REC_LV2_REFUSALS_FORGET [lrf_x uri]) (REC_LV2_REFUSALS_FORGET, [lrf_x uri]) = lv2_refusals_forget_m R uri ->
((16 <= length (r_calls R))%nat -> snd (r_spill Rb) = []) ->
Permutation (ablocks B ly S) (ablocks B ly1 S1 ++ F) -> (forall pn, In pn F -> In pn O) ->
(forall pn, In pn O -> In pn Ob \/ In pn F) -> (forall pn, In pn Ob -> In pn O) ->
(forall pn, In pn F -> ~ In pn (ablocks B ly1 S1)) ->
mo_le MT S S1 (rec_spill_frees R * mo_free MT) ->
(* the machine at the join *)
ajournal SEGS B LV2_REFUSALS_FORGET_STK (spZ regs) (lrf_FP O) ly S W mem md [] ly1 S1 W1 memJ mdJ (rec_spill_frees R) ->
spZ regsJ = spZ regs - 64 ->
getr regsJ 8 = w64 (lrf_c (Z.of_nat (length (r_calls R)))) -> getr regsJ 9 = w64 pu ->
getr regsJ 19 = w64 A_G_REC -> getr regsJ 20 = w64 SB ->
(forall r, (bv_unsigned r = 3 \/ bv_unsigned r = 4 \/ 22 <= bv_unsigned r <= 27) -> getr regsJ r = getr regs r) ->
(forall j r, nth_error lrf_saved j = Some r ->
  val_mem SEGS (mrestrict (w_H W1) memJ) (spZ regs - 8 - 8 * Z.of_nat j) 8 (bv_unsigned (getr regs (Z_to_bv 5 r)))) ->
aval_mem (rdW W1 memJ) (A_G_REC + OFF_STATE) 8 (r_state R) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - LV2_REFUSALS_FORGET_STK <= a < spZ regs) ->
  ~ (lrf_c (Z.of_nat (length (r_calls R))) <= a < lrf_c (Z.of_nat (length (r_calls R))) + CALL_SIZE) ->
  ~ (A_G_REC + OFF_STATE <= a < A_G_REC + OFF_STATE + 8) ->
  ~ ((length (r_calls R) < 16)%nat /\ A_G_REC + OFF_NCALLS <= a < A_G_REC + OFF_NCALLS + 4) ->
  rdW W1 memJ a = rdb a) ->
((length (r_calls R) < 16)%nat -> aval_mem (rdW W1 memJ) (A_G_REC + OFF_NCALLS) 4 (Z.of_nat (length (r_calls R)) + 1)) ->
SRr SEGS W1 (mkCfg (mkst regsJ (Z_to_bv 64 (BASE + L_JOIN)) memJ (seg_rom SEGS)) mdJ)
(apost_base SEGS B LV2_REFUSALS_FORGET_STK (lrf_FP O) regs ly S W mem md (EV_LV2_REFUSALS_FORGET R)
  (lrf_post ly S O R uri)).
Proof.
intros ly S W regs mem md ch pu uri R O ly1 S1 W1 regsJ memJ mdJ Rb Qb Ob F rdb
  HPRE HROD H10 HSTR HTAIL HREP HEV HLIVE HMOK HAB HOB HLR HSR HMOD HSPE HPERM HFO HOF HObO HFn MLE1
  HJ HspJ R8 R9 R19 R20 Hcs HFR HST HKB HNCB.
pose proof HPRE as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hsp16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HSTK : LV2_REFUSALS_FORGET_STK = 16560) by (vm_compute; reflexivity).
assert (Hn16 : 0 <= Z.of_nat (length (r_calls R)) <= 16) by (destruct HREP as (Q & (_ & _ & _ & (H16 & _) & _) & _); lia).
assert (Hh : 0 <= r_state R < 2 ^ 64)
  by (destruct HREP as (Q & (_ & _ & _ & _ & _ & _ & (_ & _ & _ & _ & _ & _ & _ & _ & HR4 & _) & _) & _); exact HR4).
set (n := Z.of_nat (length (r_calls R))) in *.
pose proof (lrf_c_ok n Hn16) as Hcok. set (c := lrf_c n) in *.
destruct (lrf_slot_bounds c Hcok) as [Hcb Hc8].
pose proof (proj1 HJ) as HAR1.
destruct (lrf_seed1 B TL HB VOBJS cmd_prog_writable ly1 S1 W1 memJ mdJ regs regsJ n c (r_state R) (lrf_s pu) HAR1
  ltac:(rewrite HSTK in Hslo; lia) Hsp16 HspJ R8 R19 R20 HFR HST Hh Hcok) as [HS SHOK].
set (E := Eimg (Ereg regsJ (lrf_extra1 regs n c (r_state R) (lrf_s pu)))) in *.
assert (HEI : img_env VAL A_LIM E) by (unfold E; apply Eimg_env).
assert (EX : forall j, (j < 12)%nat -> ew E (32 + j) = nth j (lrf_extra1 regs n c (r_state R) (lrf_s pu)) (Z_to_bv 64 0)).
{ intros j Hj. unfold E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_extra. }
assert (E34 : ew E 34 = Z_to_bv 64 c) by exact (EX 2%nat ltac:(lia)).
assert (UGR : bv_unsigned (ew E L_GREC) = A_G_REC)
  by (rewrite (HEI L_GREC ltac:(unfold L_GREC, A_OBJ, A_TEXT, A_LIM; lia)); exact (lrf_grec_val VOBJS)).
assert (UGR' : bv_unsigned (ew E 285) = A_G_REC) by exact UGR.
assert (UC' : bv_unsigned (ew E 34) = c) by (rewrite E34; apply unsigned_lit_small; unfold A_G_REC, OFF_CALLS, A_REC_SPILL in *; lia).
(* 0x8d2f0 .. 0x8d320: c->fn := 25, c->nargs := 0 *)
paj_run_tok RUN HS HJ SHOK Bspan.
{ lazymatch goal with |- awr_ok _ _ ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr ?lyx ?own =>
  let rs' := eval vm_compute in rs in change (awr_ok SEGS B Ex rs' stk spx fp b0 bc fr lyx own) end.
  apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|].
  eapply (lrf_awr_cons_grec B HB VOBJS cmd_prog_img); [reflexivity | exact HEI | cbn; unfold OFF_STATE; lia | cbn; unfold OFF_STATE, REC_SIZE; lia |].
  eapply (lrf_awr_cons_slot B HB cmd_prog_img); [reflexivity | exact E34 | exact Hcok | cbn; lia | cbn; unfold CALL_SIZE; lia | apply awr_ok_nil]. }
lazymatch goal with |- SRr _ _ (mkCfg _ ?mdx) _ => set (mdv := mdx) in *; clearbody mdv end.
assert (E9 : ew E 9 = Z_to_bv 64 pu).
{ unfold E. rewrite Eimg_low by (unfold A_TEXT; lia). rewrite (ew_Ereg_nat regsJ _ 9 9%bv eq_refl). exact R9. }
assert (E36 : ew E 36 = Z_to_bv 64 (lrf_s pu)) by exact (EX 4%nat ltac:(lia)).
assert (Hpu : (uri = None /\ pu = 0) \/ (uri <> None /\ 0 < pu < 2 ^ 64)) by exact (lrf_pu_cases ly S W mem md O pu uri HAR0 HSTR).
assert (U9 : U E (SOff 9 0) = pu) by (apply lrf_U_atom; [exact E9 | lia]).
psrr_branch_tok RUN BR HS SHOK Bspan.
- (* s1 = uri <> NULL *)
  rewrite branch_ne_U, U9 in Hc. change (U E (SLit 0)) with 0 in Hc. apply Bool.negb_true_iff, Z.eqb_neq in Hc.
  assert (Hspu : lrf_s pu = pu) by (unfold lrf_s; rewrite (proj2 (Z.eqb_neq pu 0) Hc); reflexivity).
  paj_run_to_tok RUNTO HS HJ SHOK Bspan L_XS_CALL.
  { lazymatch goal with |- awr_ok _ _ ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok SEGS B Ex rs' stk spx fp b0 bc fr lyx own) end.
    apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|].
    eapply (lrf_awr_cons_grec B HB VOBJS cmd_prog_img); [reflexivity | exact HEI | cbn; unfold OFF_STATE; lia | cbn; unfold OFF_STATE, REC_SIZE; lia |].
    eapply (lrf_awr_cons_slot B HB cmd_prog_img); [reflexivity | exact E34 | exact Hcok | cbn; lia | cbn; unfold CALL_SIZE; lia | apply awr_ok_nil]. }
  pose proof (lrf_canon2 E _ _ (SOff 9 0) HS ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
    ltac:(cbn [sv_denot]; unfold L_S; rewrite E9, E36, Hspu; reflexivity)) as HS2.
  eapply (lrf_cont2 ly S W regs mem md ch pu uri R O ly1 S1 W1 regsJ mdv Rb Qb Ob F rdb _ _ HPRE HROD H10 HSTR HTAIL HREP
    HEV HLIVE HMOK HAB HOB HLR HSR HMOD HSPE HPERM HFO HOF HObO HFn MLE1 HS2 SHOK HJ HspJ Hcs).
  + intros a Ha Hs Hsl Hst Hnc. change (lrf_c (Z.of_nat (length (r_calls R)))) with c in Hsl.
    rewrite (recb_run_keeps_m E _ (w_H W1) _ _ a HFr0 Ha) by lrf_nwr UGR' UC'.
    rewrite (recb_run_keeps_m E _ (w_H W1) _ _ a HFr Ha) by lrf_nwr UGR' UC'.
    exact (HKB a Ha Hs Hsl Hst Hnc).
  + intros Hlt. apply (aval_mem_kept (rdW W1 memJ)); [exact (HNCB Hlt)|]. intros k Hk.
    assert (Hk64 : 0 <= A_G_REC + OFF_NCALLS + Z.of_nat k < 2 ^ 64) by (unfold A_G_REC, OFF_NCALLS; lia).
    unfold OFF_NCALLS in Hk64 |- *.
    rewrite (recb_run_keeps_m E _ (w_H W1) _ _ _ HFr0 Hk64) by lrf_nwr UGR' UC'.
    rewrite (recb_run_keeps_m E _ (w_H W1) _ _ _ HFr Hk64) by lrf_nwr UGR' UC'.
    reflexivity.
- (* uri = NULL: s1 := "*" *)
  rewrite branch_ne_U, U9 in Hc. change (U E (SLit 0)) with 0 in Hc. apply Bool.negb_false_iff, Z.eqb_eq in Hc.
  assert (Hspu : lrf_s pu = 0x21fa0) by (rewrite Hc; reflexivity).
  paj_run_to_tok RUNTO HS HJ SHOK Bspan L_XS_CALL.
  { lazymatch goal with |- awr_ok _ _ ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok SEGS B Ex rs' stk spx fp b0 bc fr lyx own) end.
    apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|].
    eapply (lrf_awr_cons_grec B HB VOBJS cmd_prog_img); [reflexivity | exact HEI | cbn; unfold OFF_STATE; lia | cbn; unfold OFF_STATE, REC_SIZE; lia |].
    eapply (lrf_awr_cons_slot B HB cmd_prog_img); [reflexivity | exact E34 | exact Hcok | cbn; lia | cbn; unfold CALL_SIZE; lia | apply awr_ok_nil]. }
  assert (E319 : ew E 319 = Z_to_bv 64 0x21fa0).
  { rewrite (img_env_atomP E 319 HEI ltac:(unfold A_TEXT, A_LIM; lia)). exact (f_equal (Z_to_bv 64) (lrf_star_val VOBJS)). }
  pose proof (lrf_canon2 E _ _ (SOff 319 0) HS ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
    ltac:(cbn [sv_denot]; unfold L_S; rewrite E319, E36, Hspu; reflexivity)) as HS2.
  eapply (lrf_cont2 ly S W regs mem md ch pu uri R O ly1 S1 W1 regsJ mdv Rb Qb Ob F rdb _ _ HPRE HROD H10 HSTR HTAIL HREP
    HEV HLIVE HMOK HAB HOB HLR HSR HMOD HSPE HPERM HFO HOF HObO HFn MLE1 HS2 SHOK HJ HspJ Hcs).
  + intros a Ha Hs Hsl Hst Hnc. change (lrf_c (Z.of_nat (length (r_calls R)))) with c in Hsl.
    rewrite (recb_run_keeps_m E _ (w_H W1) _ _ a HFr0 Ha) by lrf_nwr UGR' UC'.
    rewrite (recb_run_keeps_m E _ (w_H W1) _ _ a HFr Ha) by lrf_nwr UGR' UC'.
    exact (HKB a Ha Hs Hsl Hst Hnc).
  + intros Hlt. apply (aval_mem_kept (rdW W1 memJ)); [exact (HNCB Hlt)|]. intros k Hk.
    assert (Hk64 : 0 <= A_G_REC + OFF_NCALLS + Z.of_nat k < 2 ^ 64) by (unfold A_G_REC, OFF_NCALLS; lia).
    unfold OFF_NCALLS in Hk64 |- *.
    rewrite (recb_run_keeps_m E _ (w_H W1) _ _ _ HFr0 Hk64) by lrf_nwr UGR' UC'.
    rewrite (recb_run_keeps_m E _ (w_H W1) _ _ _ HFr Hk64) by lrf_nwr UGR' UC'.
    reflexivity.
Qed.

(* the walk: the statement's premises and the string's tail at the entry (statement gap G2) *)
Lemma lrf_walk : forall ly S W (regs : bvmap 5 word) mem md ch (pu : Z) (uri : option (list byte)) (R : rstate) (O : list (Z * Z)),
afn_pre SEGS B LV2_REFUSALS_FORGET_STK ly S W regs mem md ch ->
arodata_okP SEGS RLO RHI B (rdW W mem) ->
cmd_ro_ok (rdW W mem) ->
getr regs 10 = w64 pu -> 0 <= pu < 2 ^ 64 ->
astr_argA B ly S (rdW W mem) (in_roP SEGS RLO RHI) O pu uri ->
(forall x, uri = Some x -> atail_vis SEGS W mem (pu + Z.of_nat (length x))) ->
rec_repA B ly S (rdW W mem) R O ->
st_nev S + EV_LV2_REFUSALS_FORGET R <= EV_MAX -> blocks_bytes S + LIVE_LV2_REFUSALS_FORGET uri <= LIVE_MAX ->
mo_ok MT S (XM_LV2_REFUSALS_FORGET MT R uri) ->
SRr SEGS W (cfg_at SEGS (BASE + AF_lv2_refusals_forget) regs mem md)
(apost_base SEGS B LV2_REFUSALS_FORGET_STK (lrf_FP O) regs ly S W mem md (EV_LV2_REFUSALS_FORGET R)
  (lrf_post ly S O R uri)).
Proof.
intros ly S W regs mem md ch pu uri R O HPRE HROD HROOK H10 Hpu64 HSTR HTAIL HREP HEV HLIVE HMOK.
pose proof HPRE as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hsp16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
set (sp0 := spZ regs) in *.
assert (HSTK : LV2_REFUSALS_FORGET_STK = 16560) by (vm_compute; reflexivity).
assert (Hsp46 : 2 ^ 46 <= sp0 <= 2 ^ 47).
{ change (2 ^ 46) with 70368744177664. change (2 ^ 47) with 140737488355328. clear - Hceil Hslo Hshi H47 Hstk0 C1 HSTK. lia. }
pose proof HREP as (Q & HAREP & HOQ).
pose proof HAREP as (Hgr8 & Hsc8 & Hapart & HG1 & HANS & HRPL & HSCAL & HOWN).
pose proof HG1 as (Hlen16 & HlenQ & HNC & HCALLS & HSPILL & HSPMAX).
pose proof HSCAL as (SC1 & SC2 & SC3 & SCst & SC5 & _).
set (n := Z.of_nat (length (r_calls R))) in *.
assert (Hn16 : 0 <= n <= 16) by (unfold n; lia).
pose proof (lrf_c_ok n Hn16) as Hcok. set (c := lrf_c n) in *.
destruct (lrf_slot_bounds c Hcok) as [Hcb Hc8].
pose proof (ajournal_init SEGS B LV2_REFUSALS_FORGET_STK (lrf_FP O) ly S W regs mem md ch HPRE) as HJ.
destruct (Nat.ltb_spec (length (r_calls R)) 16) as [Hlt | Hge].
- (* record()'s table arm: the call takes g_rec.calls[ncalls] *)
  destruct (lrf_seed0 B TL HB VOBJS cmd_prog_writable ly S W mem md regs n c (r_state R) (lrf_s pu) 0 15 HAR0
    ltac:(lia) Hsp16 ltac:(intros a Ha; apply Hpres; rewrite HSTK; lia) HNC ltac:(lia) ltac:(unfold n; lia) ltac:(lia) Hcok)
    as [HS SHOK].
  set (E := Eimg (Ereg regs (lrf_extra0 n c (r_state R) (lrf_s pu)))) in *.
  assert (HEI : img_env VAL A_LIM E) by (unfold E; apply Eimg_env).
  assert (Usp : bv_unsigned (ew E 2) = sp0).
  { unfold E. rewrite Eimg_low by (unfold A_TEXT; lia). rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl). reflexivity. }
  unfold cfg_at, w64.
  paj_run_to_tok RUNTO HS HJ SHOK Bspan L_JOIN.
  { lazymatch goal with |- awr_ok _ _ ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok SEGS B Ex rs' stk spx fp b0 bc fr lyx own) end.
    eapply awr_ok_cons_stack; [reflexivity | exact Usp | cbn; rewrite HSTK; lia | cbn; lia |].
    apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|].
    eapply (lrf_awr_cons_grec B HB VOBJS cmd_prog_img); [reflexivity | exact HEI | cbn; unfold OFF_NCALLS; lia | cbn; unfold OFF_NCALLS, REC_SIZE; lia | apply awr_ok_nil]. }
  lazymatch goal with |- SRr _ _ (mkCfg _ ?mdx) _ => set (mdv := mdx) in *; clearbody mdv end.
  (* the facts at the join *)
  assert (EE : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew E k = getr regs r).
  { intros k r Hk. unfold E. pose proof (bv_unsigned_in_range 5 r) as Hr5. change (bv_modulus 5) with 32 in Hr5.
    rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hk. }
  assert (EX : forall j, (j < 5)%nat -> ew E (32 + j) = nth j (lrf_extra0 n c (r_state R) (lrf_s pu)) (Z_to_bv 64 0)).
  { intros j Hj. unfold E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_extra. }
  assert (E32 : ew E 32 = Z_to_bv 64 SB) by exact (EX 0%nat ltac:(lia)).
  assert (E33 : ew E 33 = Z_to_bv 64 n) by exact (EX 1%nat ltac:(lia)).
  assert (E285 : ew E 285 = Z_to_bv 64 A_G_REC).
  { rewrite (img_env_atomP E 285 HEI ltac:(unfold A_TEXT, A_LIM; lia)). exact (f_equal (Z_to_bv 64) (lrf_grec_val VOBJS)). }
  assert (UGR' : bv_unsigned (ew E 285) = A_G_REC) by (rewrite E285; apply unsigned_lit_small; unfold A_G_REC; lia).
  assert (UC' : bv_unsigned (ew E 34) = c).
  { change 34%nat with (32 + 2)%nat. rewrite (EX 2%nat ltac:(lia)). cbn [nth lrf_extra0 map].
    apply unsigned_lit_small. unfold A_G_REC, OFF_CALLS, A_REC_SPILL in *. lia. }
  assert (Hcv : c = A_G_REC + OFF_CALLS + CALL_SIZE * n).
  { unfold c, lrf_c. rewrite (proj2 (Z.eqb_neq n 16) ltac:(unfold n; lia)). reflexivity. }
  lazymatch type of HS with st_ok_pi _ _ _ ?ssx (restrict _ ?msx) =>
    let r0 := eval vm_compute in (nth 0 (ss_mem ssx) got_regionP) in
    let r3 := eval vm_compute in (nth 3 (ss_mem ssx) got_regionP) in
    pose proof (st_ok_region_nth E (abs_ss VAL ssx) (restrict _ msx) 0 r0 HS ltac:(vm_compute; reflexivity)) as HRf;
    pose proof (st_ok_region_nth E (abs_ss VAL ssx) (restrict _ msx) 3 r3 HS ltac:(vm_compute; reflexivity)) as HRn;
    cbn [ms_mem restrict mkst] in HRf, HRn end.
  pmkst HS.
  prreg HS (2%bv : bv 5) J2. prreg HS (3%bv : bv 5) J3. prreg HS (4%bv : bv 5) J4.
  prreg HS (8%bv : bv 5) J8. prreg HS (9%bv : bv 5) J9. prreg HS (19%bv : bv 5) J19. prreg HS (20%bv : bv 5) J20.
  prreg HS (22%bv : bv 5) J22. prreg HS (23%bv : bv 5) J23. prreg HS (24%bv : bv 5) J24.
  prreg HS (25%bv : bv 5) J25. prreg HS (26%bv : bv 5) J26. prreg HS (27%bv : bv 5) J27.
  assert (HspJ : spZ (ms_regs ms) = sp0 - 64).
  { unfold spZ. rewrite J2, Usp. rewrite unsigned_lit_small by lia. lia. }
  assert (R8 : getr (ms_regs ms) 8 = w64 c).
  { rewrite J8, Hcv. exact (lrf_denot_slot E n E33 Hn16 E285). }
  assert (R9 : getr (ms_regs ms) 9 = w64 pu) by (rewrite J9, (EE 10%nat 10%bv eq_refl); exact H10).
  assert (R19 : getr (ms_regs ms) 19 = w64 A_G_REC) by (rewrite J19, E285; reflexivity).
  assert (R20 : getr (ms_regs ms) 20 = w64 SB) by (rewrite J20, E32; reflexivity).
  assert (Hcs : forall r : bv 5, (bv_unsigned r = 3 \/ bv_unsigned r = 4 \/ 22 <= bv_unsigned r <= 27) ->
    getr (ms_regs ms) r = getr regs r).
  { intros r Hr.
    assert (Hk : bv_unsigned r = 3 \/ bv_unsigned r = 4 \/ bv_unsigned r = 22 \/ bv_unsigned r = 23 \/
                 bv_unsigned r = 24 \/ bv_unsigned r = 25 \/ bv_unsigned r = 26 \/ bv_unsigned r = 27) by lia.
    destruct Hk as [Hk|[Hk|[Hk|[Hk|[Hk|[Hk|[Hk|Hk]]]]]]].
    - replace r with (3%bv : bv 5) by (apply bv_eq; rewrite Hk; reflexivity). rewrite J3. exact (EE 3%nat 3%bv eq_refl).
    - replace r with (4%bv : bv 5) by (apply bv_eq; rewrite Hk; reflexivity). rewrite J4. exact (EE 4%nat 4%bv eq_refl).
    - replace r with (22%bv : bv 5) by (apply bv_eq; rewrite Hk; reflexivity). rewrite J22. exact (EE 22%nat 22%bv eq_refl).
    - replace r with (23%bv : bv 5) by (apply bv_eq; rewrite Hk; reflexivity). rewrite J23. exact (EE 23%nat 23%bv eq_refl).
    - replace r with (24%bv : bv 5) by (apply bv_eq; rewrite Hk; reflexivity). rewrite J24. exact (EE 24%nat 24%bv eq_refl).
    - replace r with (25%bv : bv 5) by (apply bv_eq; rewrite Hk; reflexivity). rewrite J25. exact (EE 25%nat 25%bv eq_refl).
    - replace r with (26%bv : bv 5) by (apply bv_eq; rewrite Hk; reflexivity). rewrite J26. exact (EE 26%nat 26%bv eq_refl).
    - replace r with (27%bv : bv 5) by (apply bv_eq; rewrite Hk; reflexivity). rewrite J27. exact (EE 27%nat 27%bv eq_refl). }
  assert (HFR : forall j r, nth_error lrf_saved j = Some r ->
    val_mem SEGS (mrestrict (w_H W) (ms_mem ms)) (sp0 - 8 - 8 * Z.of_nat j) 8 (bv_unsigned (getr regs (Z_to_bv 5 r)))).
  { intros j r Hj.
    do 7 (destruct j as [|j]; [cbn [nth_error lrf_saved] in Hj; injection Hj as <-;
      lazymatch goal with |- val_mem _ _ (_ - 8 - 8 * Z.of_nat ?jj) _ (bv_unsigned (getr _ (Z_to_bv 5 ?rr))) =>
        let off := eval vm_compute in (-8 - 8 * Z.of_nat jj) in
        let k := eval vm_compute in (Z.to_nat rr) in
        replace (sp0 - 8 - 8 * Z.of_nat jj) with (sp0 + off) by lia;
        apply (lrf_frame_word E _ _ _ _ _ _ sp0 regs k (Z_to_bv 5 rr) off HRf Usp); [cbn; tauto | apply EE; reflexivity] end |]).
    destruct j; cbn in Hj; discriminate. }
  assert (HST : aval_mem (rdW W (ms_mem ms)) (A_G_REC + OFF_STATE) 8 (r_state R)).
  { apply (aval_mem_kept (rdW W mem)); [exact SCst|]. intros k Hk.
    assert (Hk64 : 0 <= A_G_REC + OFF_STATE + Z.of_nat k < 2 ^ 64) by (unfold A_G_REC, OFF_STATE; lia).
    unfold OFF_STATE in Hk64 |- *.
    rewrite (recb_run_keeps_m E _ (w_H W) _ _ _ HFr Hk64) by lrf_nwr2 UGR' UC' Usp. reflexivity. }
  assert (Hsf : rec_spill_frees R = 0) by (unfold rec_spill_frees; rewrite (proj2 (Nat.ltb_lt _ _) Hlt); reflexivity).
  apply (lrf_cont1 ly S W regs mem md ch pu uri R O ly S W (ms_regs ms) (ms_mem ms) mdv R Q O [] (rdW W mem)
    HPRE HROD H10 HSTR HTAIL HREP HEV HLIVE HMOK HAREP HOQ eq_refl eq_refl eq_refl
    ltac:(intros H16; exfalso; lia) ltac:(rewrite app_nil_r; apply Permutation_refl)
    ltac:(intros pn []) ltac:(intros pn H; left; exact H) ltac:(intros pn H; exact H) ltac:(intros pn [])
    ltac:(rewrite Hsf, Z.mul_0_l; exact (mo_le_refl MT MTL S)) ltac:(rewrite Hsf; exact HJ)
    HspJ R8 R9 R19 R20 Hcs HFR HST).
  + intros a Ha Hs Hsl Hst Hnc.
    rewrite (recb_run_keeps_m E _ (w_H W) _ _ a HFr Ha) by lrf_nwr2 UGR' UC' Usp. reflexivity.
  + intros _.
    pose proof (field_of_region E _ 285 A_G_REC _ _ _ _ _ 8 4 (SOff 33 1) (n + 1) HRn UGR' ltac:(cbn; tauto)
      ltac:(cbn [sv_denot]; rewrite E33, unsigned_lit_small by lia; reflexivity)
      ltac:(rewrite lrf_pow4; lia) ltac:(cbn; lia)) as HN1.
    exact (aval_mem_view SEGS _ _ _ _ _ HN1).
- (* record()'s spill arm: the table is full; record() frees record.spill's arguments, then takes it *)
  assert (En : length (r_calls R) = 16%nat) by lia.
  assert (Hn16' : n = 16) by (unfold n; rewrite En; reflexivity).
  assert (Hcv : c = A_REC_SPILL) by (unfold c, lrf_c; rewrite Hn16'; reflexivity).
  destruct (lrf_seed0 B TL HB VOBJS cmd_prog_writable ly S W mem md regs n c (r_state R) (lrf_s pu) 16 16 HAR0
    ltac:(lia) Hsp16 ltac:(intros a Ha; apply Hpres; rewrite HSTK; lia) HNC ltac:(lia) ltac:(lia) ltac:(lia) Hcok)
    as [HS SHOK].
  set (E := Eimg (Ereg regs (lrf_extra0 n c (r_state R) (lrf_s pu)))) in *.
  assert (HEI : img_env VAL A_LIM E) by (unfold E; apply Eimg_env).
  assert (Usp : bv_unsigned (ew E 2) = sp0).
  { unfold E. rewrite Eimg_low by (unfold A_TEXT; lia). rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl). reflexivity. }
  unfold cfg_at, w64.
  paj_run_tok RUN HS HJ SHOK Bspan.
  { lazymatch goal with |- awr_ok _ _ ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok SEGS B Ex rs' stk spx fp b0 bc fr lyx own) end.
    eapply awr_ok_cons_stack; [reflexivity | exact Usp | cbn; rewrite HSTK; lia | cbn; lia |].
    apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|].
    eapply (lrf_awr_cons_grec B HB VOBJS cmd_prog_img); [reflexivity | exact HEI | cbn; unfold OFF_NCALLS; lia | cbn; unfold OFF_NCALLS, REC_SIZE; lia | apply awr_ok_nil]. }
  lazymatch goal with |- SRr _ _ (mkCfg _ ?mdx) _ => set (mdv := mdx) in *; clearbody mdv end.
  assert (E33 : ew E 33 = Z_to_bv 64 16).
  { unfold E. rewrite Eimg_low by (unfold A_TEXT; lia). change 33%nat with (32 + 1)%nat.
    rewrite ew_Ereg_extra. cbn [nth lrf_extra0 map]. rewrite Hn16'. reflexivity. }
  assert (U33 : U E (SOff 33 0) = 16) by (apply lrf_U_atom; [exact E33 | lia]).
  psrr_branch_tok RUN BR HS SHOK Bspan.
  + (* `bne ncalls, 16` taken: impossible, ncalls = 16 *)
    exfalso. rewrite branch_ne_U, U33 in Hc. change (U E (SLit 16)) with 16 in Hc. discriminate Hc.
  + clear Hc.
    paj_run_tok RUN HS HJ SHOK Bspan.
    { lazymatch goal with |- awr_ok _ _ ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr ?lyx ?own =>
      let rs' := eval vm_compute in rs in change (awr_ok SEGS B Ex rs' stk spx fp b0 bc fr lyx own) end.
      eapply awr_ok_cons_stack; [reflexivity | exact Usp | cbn; rewrite HSTK; lia | cbn; lia |].
      apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|].
      eapply (lrf_awr_cons_grec B HB VOBJS cmd_prog_img); [reflexivity | exact HEI | cbn; unfold OFF_NCALLS; lia | cbn; unfold OFF_NCALLS, REC_SIZE; lia | apply awr_ok_nil]. }
    lazymatch goal with |- SRr _ _ (mkCfg _ ?mdx) _ => set (mdv2 := mdx) in *; clearbody mdv2 end.
    assert (EE : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew E k = getr regs r).
    { intros k r Hk. unfold E. pose proof (bv_unsigned_in_range 5 r) as Hr5. change (bv_modulus 5) with 32 in Hr5.
      rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hk. }
    assert (EX : forall j, (j < 5)%nat -> ew E (32 + j) = nth j (lrf_extra0 n c (r_state R) (lrf_s pu)) (Z_to_bv 64 0)).
    { intros j Hj. unfold E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_extra. }
    assert (E32 : ew E 32 = Z_to_bv 64 SB) by exact (EX 0%nat ltac:(lia)).
    assert (E34 : ew E 34 = Z_to_bv 64 c) by exact (EX 2%nat ltac:(lia)).
    assert (E285 : ew E 285 = Z_to_bv 64 A_G_REC).
    { rewrite (img_env_atomP E 285 HEI ltac:(unfold A_TEXT, A_LIM; lia)). exact (f_equal (Z_to_bv 64) (lrf_grec_val VOBJS)). }
    assert (E292 : ew E 292 = Z_to_bv 64 A_REC_SPILL).
    { rewrite (img_env_atomP E 292 HEI ltac:(unfold A_TEXT, A_LIM; lia)). exact (f_equal (Z_to_bv 64) (lrf_spill_val VOBJS)). }
    assert (UGR' : bv_unsigned (ew E 285) = A_G_REC) by (rewrite E285; apply unsigned_lit_small; unfold A_G_REC; lia).
    assert (HO : forall pn, In pn O -> In pn (ablocks B ly S)) by exact (lrf_rep_O_in ly S _ R O HREP).
    (* the call count and the recorder at the call: the two segments wrote only the frame *)
    lazymatch type of HS with st_ok _ _ ?ssx ?msx =>
      let r3 := eval vm_compute in (nth 3 (ss_mem ssx) got_regionP) in
      let r0 := eval vm_compute in (nth 0 (ss_mem ssx) got_regionP) in
      pose proof (st_ok_region_nth E ssx msx 3 r3 HS ltac:(vm_compute; reflexivity)) as HRn;
      pose proof (st_ok_region_nth E ssx msx 0 r0 HS ltac:(vm_compute; reflexivity)) as HRf;
      cbn [ms_mem restrict mkst] in HRn, HRf end.
    (* the frame the prologue wrote, at the call *)
    assert (HFR0 : forall j r, nth_error lrf_saved j = Some r ->
      val_mem SEGS (mrestrict (w_H W) (ms_mem ms0)) (sp0 - 8 - 8 * Z.of_nat j) 8 (bv_unsigned (getr regs (Z_to_bv 5 r)))).
    { intros j r Hj.
      do 7 (destruct j as [|j]; [cbn [nth_error lrf_saved] in Hj; injection Hj as <-;
        lazymatch goal with |- val_mem _ _ (_ - 8 - 8 * Z.of_nat ?jj) _ (bv_unsigned (getr _ (Z_to_bv 5 ?rr))) =>
          let off := eval vm_compute in (-8 - 8 * Z.of_nat jj) in
          let k := eval vm_compute in (Z.to_nat rr) in
          replace (sp0 - 8 - 8 * Z.of_nat jj) with (sp0 + off) by lia;
          apply (lrf_frame_word E _ _ _ _ _ _ sp0 regs k (Z_to_bv 5 rr) off HRf Usp); [cbn; tauto | apply EE; reflexivity] end |]).
      destruct j; cbn in Hj; discriminate. }
    pose proof (field_of_region E _ 285 A_G_REC _ _ _ _ _ 8 4 (SOff 33 0) 16 HRn UGR' ltac:(cbn; tauto)
      ltac:(cbn [sv_denot]; rewrite E33, unsigned_lit_small by lia; reflexivity)
      ltac:(rewrite lrf_pow4; lia) ltac:(cbn; lia)) as HN1.
    assert (KRUN : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 64 <= a < sp0) -> ~ (A_G_REC + OFF_NCALLS <= a < A_G_REC + OFF_NCALLS + 4) ->
      rdW W (ms_mem ms0) a = rdW W mem a).
    { intros a Ha Hs Hn.
      rewrite (recb_run_keeps_m E _ (w_H W) _ _ a HFr0 Ha) by lrf_nwr2 UGR' UGR' Usp.
      rewrite (recb_run_keeps_m E _ (w_H W) _ _ a HFr Ha) by lrf_nwr2 UGR' UGR' Usp. reflexivity. }
    assert (HAREP1 : arep_at (ablocks B ly S) (rdW W (ms_mem ms0)) A_G_REC A_REC_SPILL R Q).
    { apply (lrf_rep_kept _ (rdW W mem) _ R Q HAREP).
      - intros a Hr Hn. apply KRUN; [unfold A_G_REC, A_REC_SPILL, REC_SIZE, SC_SIZE in *; lia | unfold A_G_REC, A_REC_SPILL, REC_SIZE, SC_SIZE in *; lia | exact Hn].
      - intros [q k] i Hin Hi. cbn [fst snd] in *.
        destruct (arep_lay_in _ _ _ _ R Q (q, k) HAREP Hin) as [Hb Hk1].
        destruct (al_blocks _ _ LAWS _ _ _ _ _ q k HAR0 Hb) as (_ & Hq4 & Hqc & _).
        pose proof (req_size_pos k ltac:(lia)) as [_ Hrk].
        pose proof (blk_off_imgP B ly S W mem md q k HAR0 Hb) as Hoff. unfold off_img in Hoff.
        apply KRUN; unfold A_G_REC, OFF_NCALLS in *; lia.
      - rewrite En. exact (aval_mem_view SEGS _ _ _ _ _ HN1). }
    pose proof HAREP1 as (_ & _ & _ & (_ & _ & _ & _ & HSp1 & _) & _ & _ & _ & (HND & _)).
    pose proof HSp1 as (Hsfn & Hsc6 & HslP & _ & Hsna & _ & Hsargs).
    assert (Hsf : rec_spill_frees R = Z.of_nat (length (l_spill Q))).
    { unfold rec_spill_frees. rewrite (proj2 (Nat.ltb_ge _ _) Hge), HslP. reflexivity. }
    pmkst HS.
    prreg HS (1%bv : bv 5) P1. prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
    prreg HS (8%bv : bv 5) P8. prreg HS (10%bv : bv 5) P10. prreg HS (11%bv : bv 5) P11.
    assert (SIGR : SIG CS_rec_calls_free = BASE + AF_rec_calls_free).
    { rewrite (SIGP CS_rec_calls_free ltac:(unfold cmd_prog_syms; cbn [In]; tauto)); f_equal; vm_compute; reflexivity. }
    rewrite SIGR.
    pose proof (lrf_aro_kept _ _ O ly S W mem md _ ly S W (ms_mem ms0) _ _ HJ HAR0 HO HROD) as HROD1.
    set (Kr := fun ly2 S2 (W2 : world SEGS) (regs2 : bvmap 5 word) mem2 (md2 : Model) =>
      Permutation (ablocks B ly S) (ablocks B ly2 S2 ++ concat [l_spill Q]) /\
      rec_repA B ly2 S2 (rdW W2 mem2) (set_spill R (fst (r_spill R), []))
        (concat (l_calls Q) ++ oblk (l_answer Q) ++ oblk (l_reply Q)) /\
      blocks_bytes S2 <= blocks_bytes S + LIVE_REC_CALLS_FREE /\
      mo_le MT S S2 (XM_REC_CALLS_FREE MT [l_spill Q])).
    eapply SRr_bind.
    { eapply (cl_callS_wide B LAWS W (ms_regs ms0) (ms_mem ms0) _ LV2_REFUSALS_FORGET_STK sp0 (lrf_FP O) ly S W mem md []
        ly S _ 0 REC_CALLS_FREE_STK (rcf_fp A_REC_SPILL [l_spill Q]) (EV_REC_CALLS_FREE [l_spill Q]) (-64)
        (getr (ms_regs ms0) 1) [] Kr HJ).
      - unfold spZ at 1. rewrite P2, Usp, unsigned_lit_small by lia. lia.
      - reflexivity.
      - lia.
      - vm_compute. discriminate.
      - rewrite HSTK. vm_compute. discriminate.
      - rewrite P3, (EE 3%nat 3%bv eq_refl). exact Hgp.
      - rewrite P4, (EE 4%nat 4%bv eq_refl). exact Htp.
      - reflexivity.
      - rewrite P1. apply ret_ok_codeptr_v; [lia | reflexivity].
      - rewrite P1, unsigned_lit_small by lia. lia.
      - apply achain_low. unfold s0Z. rewrite P8, E292, unsigned_lit_small by (unfold A_REC_SPILL; lia).
        unfold A_REC_SPILL. lia.
      - intros HPRE1. eapply SRr_mono.
        { apply (TRCF fx ly S W (ms_regs ms0) (ms_mem ms0) _ [] A_REC_SPILL [l_spill Q] HPRE1 HROD1).
          - rewrite P10, E292. reflexivity.
          - rewrite P11. reflexivity.
          - cbn. lia.
          - right. left. unfold A_REC_SPILL, CALL_SIZE, SC_SIZE. cbn. lia.
          - unfold A_REC_SPILL. reflexivity.
          - intros i P Hi. destruct i as [|i]; [|destruct i; discriminate Hi]. cbn in Hi. injection Hi as <-.
            split; [rewrite HslP; exact Hsc6|].
            split; [replace (A_REC_SPILL + CALL_SIZE * Z.of_nat 0 + CALL_OFF_NARGS) with (A_REC_SPILL + CALL_OFF_NARGS) by lia;
                    rewrite HslP; exact Hsna|].
            intros a pn Hpn.
            destruct (nth_error (snd (r_spill R)) a) as [s|] eqn:Es;
              [| apply nth_error_None in Es; pose proof (proj1 (nth_error_Some _ _) ltac:(rewrite Hpn; discriminate)); lia].
            destruct (Hsargs a s pn Es Hpn) as (G1 & G2 & G3 & G4 & G5).
            split; [replace (A_REC_SPILL + CALL_SIZE * Z.of_nat 0 + CALL_OFF_ARGS + 8 * Z.of_nat a)
                       with (A_REC_SPILL + CALL_OFF_ARGS + 8 * Z.of_nat a) by lia; exact G1 | exact G3].
          - apply NoDup_ListNoDup in HND. unfold lay_blocks in HND. rewrite !map_app in HND.
            apply lrf_nodup_app_r in HND. apply lrf_nodup_app_l in HND.
            cbn [concat]. rewrite app_nil_r. apply NoDup_ListNoDup. exact HND.
          - unfold EV_REC_CALLS_FREE, EV_LV2_REFUSALS_FORGET, EV_XSTRDUP in *. cbn [concat]. rewrite app_nil_r. lia.
          - apply (mo_ok_le MT MTL S _ _ HMOK). unfold XM_REC_CALLS_FREE, XM_LV2_REFUSALS_FORGET.
            cbn [concat]. rewrite app_nil_r, <- Hsf.
            pose proof (mo_malloc_nonneg MT MTL (Z.of_nat (length (darg uri (bstr "*"%string))) + 1) ltac:(lia)).
            unfold XM_XSTRDUP. lia. }
        cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & Hc2 & HJr & HPr & Hperm & _ & _ & _ & _ & Hr2 & _ & HBBr & MLEr).
        exists ly2, S2, regs2, mem2, md2. split; [exact Hc2|]. split; [exact HJr|]. split; [exact HPr|].
        split; [exact Hperm|]. split; [exact (Hr2 R Q HAREP1 eq_refl eq_refl)|].
        split; [exact HBBr | exact MLEr].
      - intros a Ha. destruct (lrf_rcf_inv _ a Ha) as [Hsn | ([q k] & Hin & Hpa)].
        + exact (lrf_awr_PG B HB cmd_prog_img _ _ O _ _ _ _ _ a
            (lrf_inFP_spill O a ltac:(unfold A_REC_SPILL, SC_SIZE in *; lia)) (recb_spill_in a ltac:(unfold A_REC_SPILL, SC_SIZE in *; lia))).
        + cbn [fst snd] in Hpa. right. left. split.
          * exists (q, q + req_size k). split; [right; right|cbn [fst snd]; exact Hpa].
            unfold ablocks_fp. apply in_map_iff. exists (q, k). split; [reflexivity|].
            apply (proj2 (HOQ (q, k))). unfold lay_blocks. apply in_or_app. right. apply in_or_app. left. exact Hin.
          * exists q, k. split; [|exact Hpa].
            eapply proj1. apply (arep_lay_in _ _ _ _ R Q (q, k) HAREP).
            unfold lay_blocks. apply in_or_app. right. apply in_or_app. left. exact Hin.
      - intros ? ? ? ? ? ? _ a Ha Hs Hn. exfalso.
        destruct (lrf_rcf_inv _ a Ha) as [Hsn | ([q k] & Hin & Hpa)]; [unfold A_REC_SPILL in Hsn; lia|].
        cbn [fst snd] in Hpa.
        assert (Hb : In (q, k) (ablocks B ly S)).
        { eapply proj1. apply (arep_lay_in _ _ _ _ R Q (q, k) HAREP).
          unfold lay_blocks. apply in_or_app. right. apply in_or_app. left. exact Hin. }
        destruct (al_blocks _ _ LAWS _ _ _ _ _ q k HAR0 Hb) as (_ & Hq4 & Hqc & _). lia. }
    cbv beta. intros W2 c2 Hwle2 (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HJc2 & HP2 & (Hperm2 & Hrep2 & HBB2 & MLE2)).
    pose proof (proj1 HJ2) as HAR2.
    (* the bytes the call keeps: the frame above its window, g_rec and record.spill outside its footprint *)
    assert (HnFP : forall a, alloc_ceiling <= a -> ~ inFP (rcf_fp A_REC_SPILL [l_spill Q]) a).
    { intros a Hac Hf. destruct (lrf_rcf_inv _ a Hf) as [Hsn | ([q k] & Hin & Hpa)];
      [unfold A_REC_SPILL in Hsn; pose proof asan_consts as (CC & _); lia|].
      cbn [fst snd] in Hpa.
      assert (Hb : In (q, k) (ablocks B ly S)).
      { eapply proj1. apply (arep_lay_in _ _ _ _ R Q (q, k) HAREP).
        unfold lay_blocks. apply in_or_app. right. apply in_or_app. left. exact Hin. }
      destruct (al_blocks _ _ LAWS _ _ _ _ _ q k HAR0 Hb) as (_ & _ & Hqc & _). lia. }
    assert (HKs2 : forall a, sp0 - 64 <= a < sp0 -> rdW W2 mem2 a = rdW W (ms_mem ms0) a).
    { intros a Ha. pose proof HJc2 as (_ & _ & _ & _ & _ & _ & _ & _ & HHI & _).
      apply HHI; [lia | unfold REC_CALLS_FREE_STK, ASTACK; lia | apply HnFP; lia]. }
    assert (HKc2 : forall a, Exists (in_zr a) recb_PG -> ~ inFP (rcf_fp A_REC_SPILL [l_spill Q]) a ->
      rdW W2 mem2 a = rdW W (ms_mem ms0) a).
    { intros a HP Hf. apply (lrf_callee_keeps_PG _ _ (rcf_fp A_REC_SPILL [l_spill Q]) _ _ _ _ _ _ _ _ _ _ _ _ a HJc2);
      [| exact Hf | exact HP].
      apply sink_closed_pos. unfold rcf_fp. apply Forall_app. split.
      - apply Forall_map. apply Forall_forall. intros i _. cbn [fst]. unfold A_REC_SPILL, CALL_SIZE, CALL_OFF_NARGS. lia.
      - unfold ablocks_fp. apply Forall_map. apply Forall_forall. intros [b m] Hin. cbn [fst].
        assert (Hb : In (b, m) (ablocks B ly S)).
        { eapply proj1. apply (arep_lay_in _ _ _ _ R Q (b, m) HAREP).
          unfold lay_blocks. apply in_or_app. right. apply in_or_app. left.
          cbn [concat] in Hin. rewrite app_nil_r in Hin. exact Hin. }
        destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR0 Hb) as (_ & Hb4 & _). lia. }
    (* 0x8d2d0: the jump to the join; it writes nothing *)
    jafter_call_keep_pi HS 48%nat regs2 (mrestrict (w_H W2) mem2) HP2 ([] : list nat) HS2.
    match type of HS2 with ?t -> _ => assert (HRK : t); [constructor | specialize (HS2 HRK); clear HRK] end.
    clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
    remember (havoc E 48 (map (getr regs2) CLOB)) as E2 eqn:HE2 in HS.
    assert (HEI2 : img_env VAL A_LIM E2) by (rewrite HE2; apply img_env_havoc; [exact HEI | cbv; lia]).
    assert (OLD2 : forall k, (k < 48)%nat -> ew E2 k = ew E k) by (intros k Hk; rewrite HE2; apply YN3v.ew_havoc_old; exact Hk).
    assert (SHOK2 : sh_ok SEGS L_Bx L_SH E2 (mrestrict (w_H W2) mem2)).
    { apply (lrf_sh_ok B HB ly2 S2 W2 mem2 md2 E2 c HAR2); [rewrite OLD2 by (unfold L_SB; lia); exact E32 |
      rewrite OLD2 by (unfold L_C; lia); exact E34 | exact Hcok]. }
    clear SHOK.
    rewrite P1.
    paj_run_to_tok RUNTO HS HJ2 SHOK2 Bspan L_JOIN.
    { lazymatch goal with |- awr_ok _ _ ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr ?lyx ?own =>
      let rs' := eval vm_compute in rs in change (awr_ok SEGS B Ex rs' stk spx fp b0 bc fr lyx own) end.
      apply awr_ok_nil. }
    lazymatch goal with |- SRr _ _ (mkCfg _ ?mdx) _ => set (mdv3 := mdx) in *; clearbody mdv3 end.
    (* the join: memory as the call left it *)
    assert (KJ : forall a, 0 <= a < 2 ^ 64 -> rdW W2 (ms_mem ms1) a = rdW W2 mem2 a).
    { intros a Ha. apply (recb_run_keeps_m E2 _ (w_H W2) mem2 (ms_mem ms1) a HFr1 Ha).
      intros (r & Hr & _). vm_compute in Hr. destruct Hr. }
    destruct Hrep2 as (Qb & HABq & HOBq).
    pose proof HABq as (_ & _ & _ & _ & _ & _ & (_ & _ & _ & SCst2 & _) & _).
    assert (HST : aval_mem (rdW W2 (ms_mem ms1)) (A_G_REC + OFF_STATE) 8 (r_state R)).
    { apply (aval_mem_kept (rdW W2 mem2)); [exact SCst2|]. intros k Hk. apply KJ. unfold A_G_REC, OFF_STATE. lia. }
    assert (HFR : forall j r, nth_error lrf_saved j = Some r ->
      val_mem SEGS (mrestrict (w_H W2) (ms_mem ms1)) (sp0 - 8 - 8 * Z.of_nat j) 8 (bv_unsigned (getr regs (Z_to_bv 5 r)))).
    { intros j r Hj. pose proof (HFR0 j r Hj) as Hv.
      assert (Hj7 : (j < length lrf_saved)%nat) by (apply (proj1 (nth_error_Some lrf_saved j)); rewrite Hj; discriminate).
      cbn [length lrf_saved] in Hj7.
      apply (recb_val_mem_frame_m (w_H W) (w_H W2) (ms_mem ms0) (ms_mem ms1) _ 8 _ Hv).
      intros k Hk. change (Z.of_nat 8) with 8 in Hk.
      rewrite KJ by lia. apply HKs2. lia. }
    pmkst HS.
    prreg HS (2%bv : bv 5) G2. prreg HS (3%bv : bv 5) G3. prreg HS (4%bv : bv 5) G4.
    prreg HS (8%bv : bv 5) G8. prreg HS (9%bv : bv 5) G9. prreg HS (19%bv : bv 5) G19. prreg HS (20%bv : bv 5) G20.
    prreg HS (22%bv : bv 5) G22. prreg HS (23%bv : bv 5) G23. prreg HS (24%bv : bv 5) G24.
    prreg HS (25%bv : bv 5) G25. prreg HS (26%bv : bv 5) G26. prreg HS (27%bv : bv 5) G27.
    assert (HspJ : spZ (ms_regs ms1) = sp0 - 64).
    { unfold spZ. rewrite G2, (OLD2 2%nat ltac:(lia)), Usp. rewrite unsigned_lit_small by lia. lia. }
    assert (E292' : ew E2 292 = Z_to_bv 64 A_REC_SPILL).
    { rewrite (img_env_atomP E2 292 HEI2 ltac:(unfold A_TEXT, A_LIM; lia)). exact (f_equal (Z_to_bv 64) (lrf_spill_val VOBJS)). }
    assert (E285' : ew E2 285 = Z_to_bv 64 A_G_REC).
    { rewrite (img_env_atomP E2 285 HEI2 ltac:(unfold A_TEXT, A_LIM; lia)). exact (f_equal (Z_to_bv 64) (lrf_grec_val VOBJS)). }
    assert (R8 : getr (ms_regs ms1) 8 = w64 c) by (rewrite G8, E292', Hcv; reflexivity).
    assert (R9 : getr (ms_regs ms1) 9 = w64 pu) by (rewrite G9, (OLD2 10%nat ltac:(lia)), (EE 10%nat 10%bv eq_refl); exact H10).
    assert (R19 : getr (ms_regs ms1) 19 = w64 A_G_REC) by (rewrite G19, E285'; reflexivity).
    assert (R20 : getr (ms_regs ms1) 20 = w64 SB) by (rewrite G20, (OLD2 32%nat ltac:(lia)), E32; reflexivity).
    assert (Hcs : forall r : bv 5, (bv_unsigned r = 3 \/ bv_unsigned r = 4 \/ 22 <= bv_unsigned r <= 27) ->
      getr (ms_regs ms1) r = getr regs r).
    { intros r Hr.
      assert (Hk : bv_unsigned r = 3 \/ bv_unsigned r = 4 \/ bv_unsigned r = 22 \/ bv_unsigned r = 23 \/
                   bv_unsigned r = 24 \/ bv_unsigned r = 25 \/ bv_unsigned r = 26 \/ bv_unsigned r = 27) by lia.
      destruct Hk as [Hk|[Hk|[Hk|[Hk|[Hk|[Hk|[Hk|Hk]]]]]]].
      - replace r with (3%bv : bv 5) by (apply bv_eq; rewrite Hk; reflexivity). rewrite G3, (OLD2 3%nat ltac:(lia)). exact (EE 3%nat 3%bv eq_refl).
      - replace r with (4%bv : bv 5) by (apply bv_eq; rewrite Hk; reflexivity). rewrite G4, (OLD2 4%nat ltac:(lia)). exact (EE 4%nat 4%bv eq_refl).
      - replace r with (22%bv : bv 5) by (apply bv_eq; rewrite Hk; reflexivity). rewrite G22, (OLD2 22%nat ltac:(lia)). exact (EE 22%nat 22%bv eq_refl).
      - replace r with (23%bv : bv 5) by (apply bv_eq; rewrite Hk; reflexivity). rewrite G23, (OLD2 23%nat ltac:(lia)). exact (EE 23%nat 23%bv eq_refl).
      - replace r with (24%bv : bv 5) by (apply bv_eq; rewrite Hk; reflexivity). rewrite G24, (OLD2 24%nat ltac:(lia)). exact (EE 24%nat 24%bv eq_refl).
      - replace r with (25%bv : bv 5) by (apply bv_eq; rewrite Hk; reflexivity). rewrite G25, (OLD2 25%nat ltac:(lia)). exact (EE 25%nat 25%bv eq_refl).
      - replace r with (26%bv : bv 5) by (apply bv_eq; rewrite Hk; reflexivity). rewrite G26, (OLD2 26%nat ltac:(lia)). exact (EE 26%nat 26%bv eq_refl).
      - replace r with (27%bv : bv 5) by (apply bv_eq; rewrite Hk; reflexivity). rewrite G27, (OLD2 27%nat ltac:(lia)). exact (EE 27%nat 27%bv eq_refl). }
    (* the recorder's blocks: record.spill's argument blocks are freed, the rest stay *)
    assert (HPERM' : Permutation (ablocks B ly S) (ablocks B ly2 S2 ++ l_spill Q)).
    { cbn [concat] in Hperm2. rewrite app_nil_r in Hperm2. exact Hperm2. }
    assert (LQ : forall pn, In pn (lay_blocks Q) <-> In pn (concat (l_calls Q) ++ oblk (l_answer Q) ++ oblk (l_reply Q)) \/ In pn (l_spill Q)).
    { intros pn. unfold lay_blocks. rewrite !in_app_iff. tauto. }
    assert (HFO : forall pn, In pn (l_spill Q) -> In pn O) by (intros pn H; apply (proj2 (HOQ pn)); apply LQ; right; exact H).
    assert (HOF : forall pn, In pn O -> In pn (concat (l_calls Q) ++ oblk (l_answer Q) ++ oblk (l_reply Q)) \/ In pn (l_spill Q))
      by (intros pn H; apply LQ; apply (proj1 (HOQ pn)); exact H).
    assert (HObO : forall pn, In pn (concat (l_calls Q) ++ oblk (l_answer Q) ++ oblk (l_reply Q)) -> In pn O)
      by (intros pn H; apply (proj2 (HOQ pn)); apply LQ; left; exact H).
    assert (HFn : forall pn, In pn (l_spill Q) -> ~ In pn (ablocks B ly2 S2)).
    { intros pn Hin. pose proof (recb_ablocks_nodup_m B ly S W mem md HAR0) as ND.
      exact (lrf_nodup_app_disj _ _ _ (Permutation_NoDup HPERM' ND) pn Hin). }
    assert (MLE1 : mo_le MT S S2 (rec_spill_frees R * mo_free MT)).
    { rewrite Hsf. unfold XM_REC_CALLS_FREE in MLE2. cbn [concat] in MLE2. rewrite app_nil_r in MLE2. exact MLE2. }
    assert (HJ3 : ajournal SEGS B LV2_REFUSALS_FORGET_STK sp0 (lrf_FP O) ly S W mem md [] ly2 S2 W2 (ms_mem ms1) mdv3
      (rec_spill_frees R)).
    { replace (rec_spill_frees R) with (0 + EV_REC_CALLS_FREE [l_spill Q]); [exact HJ2|].
      rewrite Hsf. unfold EV_REC_CALLS_FREE. cbn [concat]. rewrite app_nil_r. lia. }
    assert (HMOD : rec_mix (rec_record (set_spill R (fst (r_spill R), [])) REC_LV2_REFUSALS_FORGET [lrf_x uri])
      (REC_LV2_REFUSALS_FORGET, [lrf_x uri]) = lv2_refusals_forget_m R uri).
    { unfold lv2_refusals_forget_m, rec_stub_mix, rec_record. cbn [set_spill r_calls].
      rewrite (proj2 (Nat.ltb_ge _ _) Hge). reflexivity. }
    apply (lrf_cont1 ly S W regs mem md ch pu uri R O ly2 S2 W2 (ms_regs ms1) (ms_mem ms1) mdv3
      (set_spill R (fst (r_spill R), [])) Qb (concat (l_calls Q) ++ oblk (l_answer Q) ++ oblk (l_reply Q)) (l_spill Q)
      (rdW W2 mem2) HPRE HROD H10 HSTR HTAIL HREP HEV HLIVE HMOK HABq HOBq eq_refl eq_refl HMOD
      (fun _ => eq_refl) HPERM' HFO HOF HObO HFn MLE1 HJ3 HspJ R8 R9 R19 R20 Hcs HFR HST).
    * intros a Ha _ _ _ _. exact (KJ a Ha).
    * intros Hlt'. exfalso. lia.
Qed.
(* the statement, exactly as lib/A/Prog/lv2_refusals_forget_c.v states it *)
Theorem tlv2_refusals_forget_holds : tlv2_refusals_forget_spec B MT.
Proof. exact lrf_walk. Qed.
Print Assumptions tlv2_refusals_forget_holds.
End e.
End f.
End d.
Print Assumptions tlv2_refusals_forget_holds.
