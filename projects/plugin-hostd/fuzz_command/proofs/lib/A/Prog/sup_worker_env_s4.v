(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the facts sup_worker_env's ASan walk (plugin-hostd/fuzz_command) reads at its
   calls, carried from the entry along the walk's journal, after proofs/cgif/cgif_file_fuzzer/lib/A/ACh1.v (the
   read-only data and the caller's blocks kept across a segment) and answer_code's walk in an earlier version of
   lib/A/Prog/answer_code.v (:124-132, not_in_ranges). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YI16 YM05 YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs RtAPI.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdSyms CmdAddr CmdList CmdPa CmdPaLib.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaCall PaCallRun PaLibF PaLibG PaLibH PaSB PaDenot PaNoChain PaFx RecBLemmas.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob CmdBase CmdRep CmdObj CmdRo CmdZsh.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import rec_calls_free_c xstrdup_c rec_shape_of_c answer_c hand_back_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import sup_worker_env_c sup_worker_env_m sup_worker_env_s1 sup_worker_env_s2 sup_worker_env_s3.
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
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation SIG s := (@pa_sigma _ cmd_listing PI s).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Context {B : asyms} {MT : ameter_ops}.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
(* the statement's Section hypotheses (sup_worker_env_c.v), at every FP state *)
Hypothesis TRCF : forall fx0 : YK11.FPState, @trec_calls_free_spec fx0 rc SK PI B MT.
Hypothesis TXSTRDUP : forall fx0 : YK11.FPState, @txstrdup_spec fx0 rc SK PI B MT.
Hypothesis TREC_SHAPE_OF : forall fx0 : YK11.FPState, @trec_shape_of_spec fx0 rc SK PI B MT.
Hypothesis TANSWER : forall fx0 : YK11.FPState, @tanswer_spec fx0 rc SK PI B MT.
Hypothesis VOBJS : cmd_val_objs.
(* the walk hypotheses, with cgif's names *)
Hypothesis TL : PALib B.
Hypothesis HB : CmdBSyms B.
Hypothesis MTL : ameter_laws MT.
Hypothesis SIGP : cmd_sig_prog.
(* the named per-binary facts of the recorder walks that the statement does not carry yet (CmdRecFacts) *)
Hypothesis cmd_prog_img : forall a, Exists (in_zr a) recb_PG -> in_img SEGS a.
Hypothesis cmd_prog_writable : forall ly S (W : world SEGS) mem md a,
AR SEGS B ly S W mem md -> Exists (in_zr a) recb_PG -> writable_at SEGS (mrestrict (w_H W) mem) a.
Hypothesis cmd_ro_prog_apart : forall a, in_roP SEGS RLO RHI a -> in_img SEGS a /\ ~ Exists (in_zr a) recb_PG.
Hypothesis cmd_ro_ok_of_aro : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md ->
arodata_okP SEGS RLO RHI B (rdW W mem) -> cmd_ro_ok (rdW W mem).
Hypothesis cmd_heap_tail_vis : forall ly S W mem md p n e, AR SEGS B ly S W mem md -> In (p, n) (ablocks B ly S) ->
p <= e < p + n -> atail_vis SEGS W mem e.
Hypothesis CMD_RO_IN : cmd_ro_in (in_roP SEGS CMD_RLO CMD_RHI).
Let LAWS : AR_laws SEGS B := AR_laws_ok SEGS B.

Section w.
(* the entry of the call: the statement's quantified variables and premises (sup_worker_env_c.v) *)
Context {ly : alayout} {S : astate} {W : world SEGS} {regs : bvmap 5 word} {mem : word -> option byte} {md : Model}
  {ch : list (Z * Z * Z)} {pf pcs pnn : Z} {format cpus nice : option (list byte)} {R : rstate} {O : list (Z * Z)}.
Hypothesis HPRE : afn_pre SEGS B SUP_WORKER_ENV_STK ly S W regs mem md ch.
Hypothesis HFRM : Z.land (Z.shiftr (bv_unsigned (@fp_csr fx)) 5) 7 = 0.
Hypothesis HROD : arodata_okP SEGS RLO RHI B (rdW W mem).
Hypothesis HRO : cmd_ro_ok (rdW W mem).
Hypothesis H10 : getr regs 10 = w64 pf.
Hypothesis HB10 : 0 <= pf < 2 ^ 64.
Hypothesis H11 : getr regs 11 = w64 pcs.
Hypothesis HB11 : 0 <= pcs < 2 ^ 64.
Hypothesis H12 : getr regs 12 = w64 pnn.
Hypothesis HB12 : 0 <= pnn < 2 ^ 64.
Hypothesis HAFx : exists x, format = Some x /\
 in_blockA (ablocks B ly S) pf (Z.of_nat (length x) + 1) /\ astr_atR (rdW W mem) pf x /\
 Z.of_nat (length x) + 1 <= LMAX + 1 /\
 Forall (fun qk => iv_apart pf (Z.of_nat (length x) + 1) (fst qk) (snd qk)) O.
Hypothesis HACx : exists x, cpus = Some x /\
 in_blockA (ablocks B ly S) pcs (Z.of_nat (length x) + 1) /\ astr_atR (rdW W mem) pcs x /\
 Z.of_nat (length x) + 1 <= LMAX + 1 /\
 Forall (fun qk => iv_apart pcs (Z.of_nat (length x) + 1) (fst qk) (snd qk)) O.
Hypothesis HANx : exists x, nice = Some x /\
 in_blockA (ablocks B ly S) pnn (Z.of_nat (length x) + 1) /\ astr_atR (rdW W mem) pnn x /\
 Z.of_nat (length x) + 1 <= LMAX + 1 /\
 Forall (fun qk => iv_apart pnn (Z.of_nat (length x) + 1) (fst qk) (snd qk)) O.
Hypothesis HREP : rec_repA B ly S (rdW W mem) R O.
Hypothesis HFR8 : Z.of_nat (length (frames S)) <= 8.
Hypothesis HEV : st_nev S + EV_SUP_WORKER_ENV R <= EV_MAX.
Hypothesis HLIVE : blocks_bytes S + LIVE_SUP_WORKER_ENV R format cpus nice <= LIVE_MAX.
Hypothesis HMOK : mo_ok MT S (XM_SUP_WORKER_ENV MT R format cpus nice).

#[local] Notation CORE := (swe_core (B:=B) (MT:=MT) (ly:=ly) (S:=S) (W:=W) (regs:=regs) (mem:=mem) (md:=md)
  (format:=format) (cpus:=cpus) (nice:=nice) (R:=R) (O:=O)).
#[local] Notation FPw := (swe_FP (O:=O)).
#[local] Notation FRAME := (swe_frame (regs:=regs)).
#[local] Notation XMs := (swe_xm (MT:=MT) (format:=format) (cpus:=cpus) (nice:=nice) (R:=R)).
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
#[local] Notation A3 := (swe_A3 (format:=format) (cpus:=cpus) (nice:=nice)).

Lemma swe_not_in_ranges : forall (L : list (Z * Z)) lo hi,
forallb (fun r => (hi <=? fst r) || (fst r + snd r <=? lo)) L = true ->
forall a, lo <= a < hi -> ~ Exists (in_zr a) L.
Proof.
intros L lo hi HL a Ha HE. apply Exists_exists in HE as (r & Hr & Hin).
pose proof (proj1 (forallb_forall _ _) HL r Hr) as Hb. cbn beta in Hb.
apply Bool.orb_true_iff in Hb. unfold in_zr in Hin.
destruct Hb as [Hb|Hb]; apply Z.leb_le in Hb; lia.
Qed.

(* g_rec and record.spill are none of the runtime's statics and not the errno cell (CmdB's tables) *)
Lemma swe_recg_unowned : forall a, in_recg a ->
~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).
Proof.
intros a Ha. rewrite (ts_owned B HB), (ts_errno B HB). unfold TFIB_ERRNO.
destruct Ha as [Ha|Ha]; split.
- apply (swe_not_in_ranges _ A_G_REC (A_G_REC + REC_SIZE)); [vm_compute; reflexivity | exact Ha].
- unfold A_G_REC, REC_SIZE in Ha. lia.
- apply (swe_not_in_ranges _ A_REC_SPILL (A_REC_SPILL + SC_SIZE)); [vm_compute; reflexivity | exact Ha].
- unfold A_REC_SPILL, SC_SIZE in Ha. lia.
Qed.

Lemma swe_O_entry : forall pn, In pn O -> In pn (ablocks B ly S).
Proof. exact (rec_repA_in B ly S (rdW W mem) R O HREP). Qed.

Lemma swe_AR0 : AR SEGS B ly S W mem md.
Proof. exact (proj1 HPRE). Qed.

Lemma swe_FP_closed : ~ YI16.sink_open_fp FPw.
Proof.
unfold swe_FP. apply sink_closed_cons; [cbn; unfold A_G_REC; lia|].
apply sink_closed_cons; [cbn; unfold A_REC_SPILL; lia|].
apply sink_closed_ablocks_fp. apply Forall_forall. intros [p n] Hin.
destruct (al_blocks _ _ LAWS ly S W mem md p n swe_AR0 (swe_O_entry _ Hin)) as (_ & H4096 & _). cbn. lia.
Qed.

(* the footprint's image bytes are g_rec's and record.spill's: the recorder's blocks lie off the image *)
Lemma swe_inFP_img : forall a, in_img SEGS a -> inFP FPw a -> in_recg a.
Proof.
intros a Hi Ha. unfold swe_FP in Ha. apply inFP_cons in Ha as [Ha|Ha]; [left; exact Ha|].
apply inFP_cons in Ha as [Ha|Ha]; [right; exact Ha|].
destruct (inFP_ablocks_fp_inv _ _ Ha) as (q & m & Hin & Hr).
pose proof (blk_off_imgP B ly S W mem md q m swe_AR0 (swe_O_entry _ Hin)) as Hoff.
pose proof (pa_img_range a Hi) as Hai. unfold off_img in Hoff. lia.
Qed.

(* a read-only byte is no byte of the footprint *)
Lemma swe_ro_notFP : forall a, in_roP SEGS RLO RHI a -> ~ inFP FPw a.
Proof.
intros a Hro HF. destruct (cmd_ro_prog_apart a Hro) as [Hi Hn].
destruct (swe_inFP_img a Hi HF) as [H|H]; apply Hn; [apply recb_grec_in | apply recb_spill_in]; exact H.
Qed.

Lemma swe_rodata_now : forall m lyc Sc Wc memc mdc k O0 D Fr NB,
CORE m lyc Sc Wc memc mdc k O0 D Fr NB -> arodata_okP SEGS RLO RHI B (rdW Wc memc).
Proof.
intros m lyc Sc Wc memc mdc k O0 D Fr NB HC a Hro Ho He.
destruct HC as (HJ & _). pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _).
rewrite (F3 a); [exact (HROD a Hro Ho He) | exact (proj1 (cmd_ro_prog_apart a Hro)) | exact Ho | exact He |].
apply fp_spares_closed; [exact swe_FP_closed | exact (swe_ro_notFP a Hro)].
Qed.

Lemma swe_ro_now : forall m lyc Sc Wc memc mdc k O0 D Fr NB,
CORE m lyc Sc Wc memc mdc k O0 D Fr NB -> cmd_ro_ok (rdW Wc memc).
Proof.
intros m lyc Sc Wc memc mdc k O0 D Fr NB HC.
pose proof (swe_rodata_now m lyc Sc Wc memc mdc k O0 D Fr NB HC) as HR.
destruct HC as (HJ & _).
exact (cmd_ro_ok_of_aro lyc Sc Wc memc mdc (proj1 HJ) HR).
Qed.

(* the string arguments in the entry's heap-block form (sup_worker_env_c.v:92-103) *)
Definition swe_harg (p : Z) (v : option (list byte)) : Prop :=
exists x, v = Some x /\ in_blockA (ablocks B ly S) p (Z.of_nat (length x) + 1) /\ astr_atR (rdW W mem) p x /\
 Z.of_nat (length x) + 1 <= LMAX + 1 /\ Forall (fun qk => iv_apart p (Z.of_nat (length x) + 1) (fst qk) (snd qk)) O.

(* the same, in astr_argA's heap arm *)
Lemma swe_harg_arg : forall p v, swe_harg p v -> astr_argA B ly S (rdW W mem) (in_roP SEGS RLO RHI) O p v.
Proof.
intros p v (x & -> & (b & kk & Hbk & Hbp & Hpb) & Hs & Hn & Hap). cbn [astr_argA].
destruct (al_blocks _ _ LAWS ly S W mem md b kk swe_AR0 Hbk) as (_ & H4096 & _).
split; [lia|]. split; [exact Hs|]. split; [exact Hn|]. left. split; [exists b, kk; auto | exact Hap].
Qed.
Lemma HAF : astr_argA B ly S (rdW W mem) (in_roP SEGS RLO RHI) O pf format.
Proof. exact (swe_harg_arg pf format HAFx). Qed.
Lemma HAC : astr_argA B ly S (rdW W mem) (in_roP SEGS RLO RHI) O pcs cpus.
Proof. exact (swe_harg_arg pcs cpus HACx). Qed.
Lemma HAN : astr_argA B ly S (rdW W mem) (in_roP SEGS RLO RHI) O pnn nice.
Proof. exact (swe_harg_arg pnn nice HANx). Qed.

(* the m-th argument's string as xstrdup receives it, at a later point of the walk: still in its block (a block of
   the entry that is none of the recorder's), so still live and holding the string, its tail visible *)
Lemma swe_sel_now : forall (p : Z) (v : option (list byte)) m lyc Sc Wc memc mdc k O0 D Fr NB,
swe_harg p v ->
CORE m lyc Sc Wc memc mdc k O0 D Fr NB ->
astr_argA B lyc Sc (rdW Wc memc) (in_roP SEGS RLO RHI) [] (swe_sel p) (Some (sarg v)) /\
atail_vis SEGS Wc memc (swe_sel p + Z.of_nat (length (sarg v))) /\
Z.of_nat (length (sarg v)) <= LMAX.
Proof.
intros p v m lyc Sc Wc memc mdc k O0 D Fr NB (x & -> & (b & kk & Hbk & Hbp & Hpb) & HS & Hn & HAP) HC.
destruct (al_blocks _ _ LAWS ly S W mem md b kk swe_AR0 Hbk) as (_ & H4096 & _).
assert (Hp0 : p <> 0) by lia.
unfold swe_sel. replace (p =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hp0). cbn [sarg].
destruct HC as (HJ & _ & _ & HP0 & HP1 & HFr & _ & _ & _ & _ & _ & _).
pose proof HJ as (HAR1 & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _).
assert (HbO : ~ In (b, kk) O).
{ intros HO. rewrite Forall_forall in HAP. specialize (HAP (b, kk) HO). cbn [fst snd] in HAP. unfold iv_apart in HAP. lia. }
assert (HbD : In (b, kk) D).
{ apply (Permutation_in _ HP0) in Hbk. apply in_app_iff in Hbk as [H|H]; [exact H | exfalso; exact (HbO (HFr _ H))]. }
assert (Hbc : In (b, kk) (ablocks B lyc Sc)) by (apply (Permutation_in _ (Permutation_sym HP1)); apply in_or_app; left; exact HbD).
assert (Hreq : kk <= req_size kk) by (destruct (req_size_pos kk ltac:(lia)) as [_ H]; lia).
assert (KEEP : forall i, 0 <= i < Z.of_nat (length x) + 1 -> rdW Wc memc (p + i) = rdW W mem (p + i)).
{ intros i Hi. replace (p + i) with (b + (p + i - b)) by lia.
  apply (F2 b kk (p + i - b) Hbk Hbc); [lia|].
  intros HF. unfold swe_FP in HF. apply inFP_cons in HF as [HF|HF].
  - pose proof (blk_off_imgP B ly S W mem md b kk swe_AR0 Hbk) as Hoff. unfold off_img, A_G_REC, REC_SIZE in *. lia.
  - apply inFP_cons in HF as [HF|HF].
    + pose proof (blk_off_imgP B ly S W mem md b kk swe_AR0 Hbk) as Hoff. unfold off_img, A_REC_SPILL, SC_SIZE in *. lia.
    + destruct (inFP_ablocks_fp_inv _ _ HF) as (q & mm & Hqm & Hr).
      assert (Hne : (b, kk) <> (q, mm)) by (intros E; rewrite E in HbO; exact (HbO Hqm)).
      pose proof (sep_blocks SEGS B LAWS ly S W mem md b kk q mm swe_AR0 Hbk (swe_O_entry _ Hqm) Hne) as Hd.
      unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia. }
split; [|split].
- cbn [astr_argA]. split; [exact Hp0|]. split; [exact (rastr_kept (rdW W mem) (rdW Wc memc) p x HS KEEP)|].
  split; [exact Hn|]. left. split; [exists b, kk; auto | constructor].
- exact (cmd_heap_tail_vis lyc Sc Wc memc mdc b kk (p + Z.of_nat (length x)) HAR1 Hbc ltac:(lia)).
- unfold LMAX in *. lia.
Qed.



(* the frame's sp and the entry sp lie in the stack window, above the heap *)
Lemma swe_sp_bounds : 2 ^ 46 <= spZ regs - 64 /\ spZ regs <= 2 ^ 47 /\ (spZ regs - 64) mod 16 = 0 /\
alloc_ceiling <= spZ regs - SUP_WORKER_ENV_STK /\ 16560 <= SUP_WORKER_ENV_STK.
Proof.
pose proof HPRE as (_ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & _).
assert (HWS : 16560 <= SUP_WORKER_ENV_STK) by (unfold Z.le; vm_compute; discriminate).
split; [lia|]. split; [lia|]. split; [rewrite Zminus_mod, Hal16; reflexivity|]. split; lia.
Qed.

Lemma swe_frame_kept : forall (Wc Wd : world SEGS) memc memd,
FRAME Wc memc ->
(forall a, spZ regs - 64 <= a < spZ regs -> rdW Wd memd a = rdW Wc memc a) -> FRAME Wd memd.
Proof.
intros Wc Wd memc memd HF HK j r Hj. pose proof (nth_error_Some swe_saved j) as Hl.
rewrite Hj in Hl. assert (Hj8 : (j < 8)%nat) by (apply Hl; discriminate).
apply (aval_mem_kept (rdW Wc memc)); [exact (HF j r Hj)|]. intros kk Hkk. apply HK. lia.
Qed.

Lemma swe_core_mem : forall m lyc Sc Wc memc mdc k O0 D Fr NB memT mdcT,
CORE m lyc Sc Wc memc mdc k O0 D Fr NB ->
ajournal SEGS B SUP_WORKER_ENV_STK (spZ regs) FPw ly S W mem md [] lyc Sc Wc memT mdcT k ->
(forall a, 0 <= a < 2 ^ 64 -> rdW Wc memT a = rdW Wc memc a) ->
CORE m lyc Sc Wc memT mdcT k O0 D Fr NB.
Proof.
intros m lyc Sc Wc memc mdc k O0 D Fr NB memT mdcT HC HJT KR.
destruct swe_sp_bounds as (Hsp & Hsp47 & _).
destruct HC as (_ & Hk & HFR & REST). split; [exact HJT|]. split; [exact Hk|]. split; [|exact REST].
apply (swe_frame_kept Wc Wc memc memT HFR). intros a Ha. apply KR. lia.
Qed.

Lemma swe_bsum_nonneg : forall ly1 S1 (W1 : world SEGS) mem1 md1 l, AR SEGS B ly1 S1 W1 mem1 md1 ->
(forall pn, In pn l -> In pn (ablocks B ly1 S1)) -> 0 <= bsum l.
Proof.
intros ly1 S1 W1 mem1 md1 l HAR Hl. induction l as [|[p n] l IH]; [cbn; lia|]. rewrite bsum_cons. cbn [snd].
destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR (Hl _ (or_introl eq_refl))) as (_ & _ & _ & _ & _ & _ & Hn).
assert (0 <= bsum l) by (apply IH; intros pn Hpn; apply Hl; right; exact Hpn). lia.
Qed.

Lemma swe_sum_nonneg : forall (f : list byte -> Z) l, (forall x, 0 <= f x) -> 0 <= swe_sum f l.
Proof. intros f l Hf. induction l as [|x l IH]; cbn [swe_sum]; [lia | pose proof (Hf x); lia]. Qed.

(* the event, live-byte and meter budget of the (m+1)-th xstrdup *)
Lemma swe_budget_x : forall m lyc Sc Wc memc mdc k O0 D Fr NB, (m < 3)%nat ->
CORE m lyc Sc Wc memc mdc k O0 D Fr NB ->
st_nev Sc + EV_XSTRDUP <= EV_MAX /\
blocks_bytes Sc + LIVE_XSTRDUP (nth m A3 []) <= LIVE_MAX /\
mo_ok MT Sc (XM_XSTRDUP MT (nth m A3 [])).
Proof.
intros m lyc Sc Wc memc mdc k O0 D Fr NB Hm HC.
destruct HC as (HJ & Hk & _ & HP0 & HP1 & _ & _ & _ & _ & HNBl & HNBb & HMLE & _).
pose proof HJ as (HAR1 & _ & _ & _ & _ & _ & Hnev & _).
assert (HbD : 0 <= bsum Fr).
{ apply (swe_bsum_nonneg ly S W mem md Fr swe_AR0). intros pn Hpn.
  apply (Permutation_in _ (Permutation_sym HP0)). apply in_or_app. right. exact Hpn. }
assert (Hbb : blocks_bytes Sc + bsum Fr = blocks_bytes S + bsum NB).
{ rewrite (blocks_bytes_bsum B lyc Sc), (blocks_bytes_bsum B ly S), (bsum_perm _ _ HP0), (bsum_perm _ _ HP1), !bsum_app. lia. }
pose proof (mo_malloc_nonneg MT MTL) as Hmn. pose proof (mo_free_nonneg MT MTL) as Hfn.
assert (HXN : forall x, 0 <= XM_XSTRDUP MT x) by (intros x; unfold XM_XSTRDUP; apply Hmn; lia).
assert (HXA : forall t, 0 <= XM_ANSWER MT t) by (intros t; unfold XM_ANSWER, XM_HAND_BACK; pose proof (HXN t); lia).
assert (HLN : forall t, 0 <= LIVE_ANSWER t) by (intros t; unfold LIVE_ANSWER, LIVE_HAND_BACK, LIVE_XSTRDUP; lia).
assert (HSF : 0 <= rec_spill_frees R) by (unfold rec_spill_frees; destruct (Nat.ltb _ _); lia).
unfold EV_SUP_WORKER_ENV, EV_ANSWER, EV_HAND_BACK, EV_XSTRDUP in HEV.
unfold LIVE_SUP_WORKER_ENV in HLIVE. unfold XM_SUP_WORKER_ENV in HMOK.
pose proof (HXA (snd (sup_worker_env_m R format cpus nice))) as HA1.
pose proof (HLN (snd (sup_worker_env_m R format cpus nice))) as HL1.
rewrite HNBb in Hbb. unfold swe_live, swe_xm, swe_A3 in *.
destruct m as [|[|[|m]]]; [| | | lia]; cbn [firstn swe_sum nth] in *.
- split; [unfold EV_XSTRDUP; lia|]. split; [unfold LIVE_XSTRDUP in *; lia|].
  apply (mok_station MT S Sc _ _ _ MTL HMOK HMLE (HXN _)). pose proof (HXN (sarg cpus)). pose proof (HXN (sarg nice)). lia.
- split; [unfold EV_XSTRDUP; lia|]. split; [unfold LIVE_XSTRDUP in *; lia|].
  apply (mok_station MT S Sc _ _ _ MTL HMOK HMLE (HXN _)). pose proof (HXN (sarg nice)). lia.
- split; [unfold EV_XSTRDUP; lia|]. split; [unfold LIVE_XSTRDUP in *; lia|].
  apply (mok_station MT S Sc _ _ _ MTL HMOK HMLE (HXN _)). lia.
Qed.

Lemma swe_rec_unowned_fp : forall a, in_recg a ->
in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).
Proof.
intros a Ha. split; [apply cmd_prog_img; destruct Ha; [apply recb_grec_in | apply recb_spill_in]; exact H|].
exact (swe_recg_unowned a Ha).
Qed.

(* after the (m)-th xstrdup: the carried facts at the callee's return *)
Lemma swe_after_x : forall m lyc Sc Wc memT mdcT k O0 D Fr NB ly2 S2 W2 mem2 md2 p,
(1 <= m <= 3)%nat ->
CORE (m - 1) lyc Sc Wc memT mdcT k O0 D Fr NB ->
rec_repA B lyc Sc (rdW Wc memT) (rec_record R REC_WORKER_ENV (firstn (m - 1) A3)) (O0 ++ NB) ->
ajournal SEGS B SUP_WORKER_ENV_STK (spZ regs) FPw ly S W mem md [] ly2 S2 W2 mem2 md2 (k + EV_XSTRDUP) ->
ajournal SEGS B XSTRDUP_STK (spZ regs + -64) [] lyc Sc Wc memT mdcT [] ly2 S2 W2 mem2 md2 EV_XSTRDUP ->
Permutation (ablocks B ly2 S2) ((p, LIVE_XSTRDUP (nth (m - 1) A3 [])) :: ablocks B lyc Sc) ->
Forall (fun qk => iv_apart p (LIVE_XSTRDUP (nth (m - 1) A3 [])) (fst qk) (snd qk)) (ablocks B lyc Sc) ->
mo_le MT Sc S2 (XM_XSTRDUP MT (nth (m - 1) A3 [])) ->
CORE m ly2 S2 W2 mem2 md2 (k + EV_XSTRDUP) O0 D Fr (NB ++ [(p, Z.of_nat (length (nth (m - 1) A3 [])) + 1)]) /\
rec_repA B ly2 S2 (rdW W2 mem2) (rec_record R REC_WORKER_ENV (firstn (m - 1) A3)) (O0 ++ NB) /\
Forall (fun qk => iv_apart p (Z.of_nat (length (nth (m - 1) A3 [])) + 1) (fst qk) (snd qk)) (D ++ NB).
Proof.
intros m lyc Sc Wc memT mdcT k O0 D Fr NB ly2 S2 W2 mem2 md2 p Hm HC HREPc HJ2 HJc Hperm Hfresh MLE.
set (x := nth (m - 1) A3 []) in *. unfold LIVE_XSTRDUP in *.
destruct swe_sp_bounds as (Hsp & Hsp47 & _ & Hceil & HWS).
destruct HC as (HJ & Hk & HFR & HP0 & HP1 & HFr & HDO & HO0 & HNBD & HNBl & HNBb & HMLE & HO0D).
pose proof (proj1 HJ) as HAR1. pose proof (proj1 HJ2) as HAR2.
pose proof HJc as (_ & _ & _ & _ & _ & _ & _ & _ & G1 & G2 & G3 & _).
assert (Hsc : ~ YI16.sink_open_fp []) by (apply sink_closed_pos; constructor).
assert (Hin2 : forall pn, In pn (ablocks B lyc Sc) -> In pn (ablocks B ly2 S2))
  by (intros pn Hpn; apply (Permutation_in _ (Permutation_sym Hperm)); right; exact Hpn).
assert (HPn : Permutation (ablocks B ly2 S2) (D ++ NB ++ [(p, Z.of_nat (length x) + 1)])).
{ eapply Permutation_trans; [exact Hperm|]. rewrite app_assoc. eapply Permutation_trans; [|apply Permutation_cons_append].
  apply Permutation_cons; [reflexivity | exact HP1]. }
assert (Hfresh' : Forall (fun qk => iv_apart p (Z.of_nat (length x) + 1) (fst qk) (snd qk)) (D ++ NB)).
{ apply Forall_forall. intros q Hq. rewrite Forall_forall in Hfresh. apply Hfresh.
  apply (Permutation_in _ (Permutation_sym HP1)). exact Hq. }
assert (KB : forall q n i, In (q, n) (ablocks B lyc Sc) -> 0 <= i < n -> rdW W2 mem2 (q + i) = rdW Wc memT (q + i)).
{ intros q n i Hq Hi. destruct (al_blocks _ _ LAWS _ _ _ _ _ q n HAR1 Hq) as (_ & _ & _ & _ & _ & _ & Hn).
  pose proof (req_size_pos n ltac:(lia)) as [_ Hr].
  apply (G2 q n i Hq (Hin2 _ Hq) ltac:(lia)). intros HF. exact (inFP_nil _ HF). }
assert (KG : forall a, in_recg a -> rdW W2 mem2 a = rdW Wc memT a).
{ intros a Ha. destruct (swe_rec_unowned_fp a Ha) as (Hi & Ho & He).
  apply (G3 a Hi Ho He). apply fp_spares_closed; [exact Hsc | intros HF; exact (inFP_nil _ HF)]. }
split; [|split].
- split; [exact HJ2|]. split; [unfold EV_XSTRDUP; lia|].
  split.
  { apply (swe_frame_kept Wc W2 memT mem2 HFR). intros a Ha. apply G1; [lia | lia | intros HF; exact (inFP_nil _ HF)]. }
  split; [exact HP0|]. split; [exact HPn|]. split; [exact HFr|]. split; [exact HDO|]. split; [exact HO0|].
  split.
  { intros pn Hpn Hd. apply in_app_iff in Hpn as [Hpn | [<- | []]]; [exact (HNBD pn Hpn Hd)|].
    rewrite Forall_forall in Hfresh'. specialize (Hfresh' _ (in_or_app _ _ _ (or_introl Hd))).
    cbn [fst snd] in Hfresh'. unfold iv_apart in Hfresh'. lia. }
  split; [rewrite length_app, HNBl; cbn; lia|].
  split; [rewrite bsum_app, HNBb; cbn [bsum fold_right fst snd];
    unfold swe_live; destruct m as [|[|[|[|m]]]]; try lia; cbn [Nat.sub firstn swe_sum nth swe_A3] in *;
    unfold LIVE_XSTRDUP, x; cbn; lia|].
  split; [|exact HO0D].
  replace (XMs m) with (XMs (m - 1) + XM_XSTRDUP MT x).
  { exact (mle_station MT S Sc S2 _ _ MTL HMLE MLE). }
  unfold swe_xm, x. destruct m as [|[|[|[|m]]]]; try lia; cbn [Nat.sub firstn swe_sum nth swe_A3]; lia.
- apply (rec_repA_kept B lyc Sc (rdW Wc memT) ly2 S2 (rdW W2 mem2) _ _ HREPc).
  + intros pn Hpn. apply Hin2. exact (rec_repA_in B lyc Sc _ _ _ HREPc pn Hpn).
  + intros a Ha. apply KG. left. unfold REC_SIZE. exact Ha.
  + intros a Ha. apply KG. right. unfold SC_SIZE. exact Ha.
  + intros q n i Hq Hi. apply (KB q n i); [exact (rec_repA_in B lyc Sc _ _ _ HREPc _ Hq) | exact Hi].
- exact Hfresh'.
Qed.



#[local] Notation XS := (swe_X_stmt (B:=B) (MT:=MT) (ly:=ly) (S:=S) (W:=W) (regs:=regs) (mem:=mem) (md:=md)
  (pf:=pf) (pcs:=pcs) (pnn:=pnn) (format:=format) (cpus:=cpus) (nice:=nice) (R:=R) (O:=O)).
#[local] Notation RS := (swe_R_stmt (B:=B) (MT:=MT) (ly:=ly) (S:=S) (W:=W) (regs:=regs) (mem:=mem) (md:=md)
  (pcs:=pcs) (pnn:=pnn) (format:=format) (cpus:=cpus) (nice:=nice) (R:=R) (O:=O)).
(* a register's value at a stop of the run: the symbolic value, computed, then its denotation *)
Ltac sreg HS r Q :=
lazymatch type of HS with
| st_ok ?sg ?E ?ss (restrict ?H ?ms) => pose proof (st_ok_restrict_reg sg H E ss ms r HS) as Q
| st_ok_pi ?sg ?vl ?E ?ss (restrict ?H ?ms) => pose proof (st_ok_pi_restrict_reg H E ss ms r HS) as Q
end;
cbn [setpc ss_regs abs_ss] in Q;
lazymatch type of Q with _ = sv_denot _ (sr_get ?l ?rr) =>
  let e := eval vm_compute in (sr_get l rr) in change (sr_get l rr) with e in Q end;
cbn [sv_denot] in Q; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned in Q.

(* the seed of a segment that touches no memory: every register its own atom *)
Lemma swe_x_seed : forall ly1 S1 (W1 : world SEGS) mem1 md1 (regs1 : bvmap 5 word) E sp n c pc,
AR SEGS B ly1 S1 W1 mem1 md1 ->
swe_env_ok E sp n c -> 2 ^ 46 <= sp <= 2 ^ 47 -> sp mod 16 = 0 -> 0 <= n <= 16 -> swe_slot_ok c ->
regs_ok E sr_atoms regs1 ->
st_ok_pi SEGS VAL E (mkSS pc sr_atoms [] None swe_facts)
  (restrict (w_H W1) (mkst regs1 (Z_to_bv 64 (BASE + pc)) mem1 (seg_rom SEGS)))
/\ sh_ok SEGS swe_Bx swe_SH E (mrestrict (w_H W1) mem1).
Proof.
intros ly1 S1 W1 mem1 md1 regs1 E sp n c pc HAR HE Hsp Hsp16 Hn Hc HREG.
split; [| exact (swe_sh_ok B HB ly1 S1 W1 mem1 md1 E sp n c HAR HE Hc)].
rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
- exact HREG.
- reflexivity.
- apply Forall_nil.
- exact I.
- exact (swe_facts_ok VOBJS E sp n c HE Hsp Hsp16 Hn Hc).
Qed.

(* the environment of a mid segment: the current registers, then the shadow base, the call count, the slot and the
   entry's saved registers *)
Lemma swe_env_mid : forall (regs1 : bvmap 5 word),
swe_env_ok (Eimg (Ereg regs1 (swe_extra regs (Z.of_nat (swe_n (R:=R))) (swe_c (R:=R))))) (spZ regs1)
  (Z.of_nat (swe_n (R:=R))) (swe_c (R:=R)).
Proof.
intros regs1. split; [apply Eimg_env|].
rewrite !Eimg_low by (unfold SW_SB, SW_N, SW_C, A_TEXT; lia).
split; [rewrite (ew_Ereg_nat regs1 _ 2 2%bv eq_refl); unfold spZ; rewrite Z_to_bv_bv_unsigned; reflexivity|].
split; [exact (ew_Ereg_extra regs1 _ 0)|]. split; [exact (ew_Ereg_extra regs1 _ 1) | exact (ew_Ereg_extra regs1 _ 2)].
Qed.

Lemma swe_n_le : (swe_n (R:=R) <= 16)%nat.
Proof. destruct HREP as (Q & HA & _). destruct HA as (_ & _ & _ & (H & _) & _). exact H. Qed.

Lemma swe_c_ok : swe_slot_ok (swe_c (R:=R)).
Proof. unfold swe_c. apply swe_slot_of_ok. pose proof swe_n_le. lia. Qed.

(* the frame's sp: below the entry sp by 64, above the stack's floor *)
Lemma swe_sp_mid : 2 ^ 46 <= spZ regs - 64 <= 2 ^ 47 /\ (spZ regs - 64) mod 16 = 0 /\
alloc_ceiling <= spZ regs - SUP_WORKER_ENV_STK.
Proof.
pose proof HPRE as (_ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & _).
assert (HWS : 64 <= SUP_WORKER_ENV_STK) by (unfold Z.le; vm_compute; discriminate).
split; [lia|]. split; [|lia]. rewrite Zminus_mod, Hal16. reflexivity.
Qed.

Lemma swe_bv5 : forall r, 0 <= r < 32 -> bv_unsigned (Z_to_bv 5 r) = r.
Proof. intros r Hr. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32. apply Z.mod_small. exact Hr. Qed.

Lemma swe_lits :
(1%bv : bv 5) = Z_to_bv 5 1 /\
(2%bv : bv 5) = Z_to_bv 5 2 /\
(3%bv : bv 5) = Z_to_bv 5 3 /\
(4%bv : bv 5) = Z_to_bv 5 4 /\
(8%bv : bv 5) = Z_to_bv 5 8 /\
(9%bv : bv 5) = Z_to_bv 5 9 /\
(10%bv : bv 5) = Z_to_bv 5 10 /\
(11%bv : bv 5) = Z_to_bv 5 11 /\
(12%bv : bv 5) = Z_to_bv 5 12 /\
(18%bv : bv 5) = Z_to_bv 5 18 /\
(19%bv : bv 5) = Z_to_bv 5 19 /\
(20%bv : bv 5) = Z_to_bv 5 20 /\
(21%bv : bv 5) = Z_to_bv 5 21 /\
(22%bv : bv 5) = Z_to_bv 5 22 /\
(23%bv : bv 5) = Z_to_bv 5 23 /\
(24%bv : bv 5) = Z_to_bv 5 24 /\
(25%bv : bv 5) = Z_to_bv 5 25 /\
(26%bv : bv 5) = Z_to_bv 5 26 /\
(27%bv : bv 5) = Z_to_bv 5 27.
Proof. repeat split; apply bv_eq; reflexivity. Qed.
Ltac swe_z5 := let L := fresh "L" in pose proof swe_lits as L; destruct L as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9 & L10 & L11 & L12 & L13 & L14 & L15 & L16 & L17 & L18 & L19);
 rewrite ?L1, ?L2, ?L3, ?L4, ?L5, ?L6, ?L7, ?L8, ?L9, ?L10, ?L11, ?L12, ?L13, ?L14, ?L15, ?L16, ?L17, ?L18, ?L19 in *; clear L1 L2 L3 L4 L5 L6 L7 L8 L9 L10 L11 L12 L13 L14 L15 L16 L17 L18 L19.

(* the registers a call keeps: the callee-saved ones it preserves, the run before it kept from the segment's start *)
Definition swe_kept_regs : list (bv 5) := map (Z_to_bv 5) [2;3;4;8;9;18;19;20;21;22;23;24;25;26;27].
Lemma swe_kept_in : forall r, In r [2;3;4;8;9;18;19;20;21;22;23;24;25;26;27] -> In (Z_to_bv 5 r) swe_kept_regs.
Proof. intros r Hr. unfold swe_kept_regs. apply in_map. exact Hr. Qed.
Lemma swe_regs_through : forall (regs1 regsT regs2 : bvmap 5 word) r,
(forall rr, In rr swe_kept_regs -> getr regsT rr = getr regs1 rr) -> aregs_preserved regsT regs2 ->
In r [2;3;4;8;9;18;19;20;21;22;23;24;25;26;27] -> getr regs2 (Z_to_bv 5 r) = getr regs1 (Z_to_bv 5 r).
Proof.
intros regs1 regsT regs2 r KR HP Hin. rewrite (HP r); [exact (KR _ (swe_kept_in r Hin))|].
unfold acallee_saved. cbn in Hin. lia.
Qed.

Lemma swe_base_after : forall (regs1 regsT regs2 : bvmap 5 word),
swe_regs_base (B:=B) (regs:=regs) (R:=R) regs1 ->
(forall rr, In rr swe_kept_regs -> getr regsT rr = getr regs1 rr) -> aregs_preserved regsT regs2 ->
swe_regs_base (B:=B) (regs:=regs) (R:=R) regs2.
Proof.
intros regs1 regsT regs2 HRB KR HP. unfold swe_regs_base in *. swe_z5.
destruct HRB as (R2 & R3 & R4 & R8 & R21 & R23).
assert (T : forall r, In r [2;3;4;8;9;18;19;20;21;22;23;24;25;26;27] -> getr regs2 (Z_to_bv 5 r) = getr regs1 (Z_to_bv 5 r))
  by (intros r; apply (swe_regs_through regs1 regsT regs2 r KR HP)).
split; [rewrite <- R2; apply T; cbn; tauto|].
split; [rewrite <- R3; apply T; cbn; tauto|].
split; [rewrite <- R4; apply T; cbn; tauto|].
split; [rewrite <- R8; apply T; cbn; tauto|].
split; [rewrite <- R21; apply T; cbn; tauto|].
intros r Hr. rewrite <- (R23 r Hr). apply T.
assert (r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) as Hc by lia.
destruct Hc as [->|[->|[->|[->| ->]]]]; cbn; tauto.
Qed.

Lemma swe_chk_after : forall (regs1 regsT regs2 : bvmap 5 word),
swe_regs_chk (R:=R) regs1 ->
(forall rr, In rr swe_kept_regs -> getr regsT rr = getr regs1 rr) -> aregs_preserved regsT regs2 ->
swe_regs_chk (R:=R) regs2.
Proof.
intros regs1 regsT regs2 HRC KR HP. unfold swe_regs_chk in *. swe_z5. destruct HRC as (R18 & R22).
split; [rewrite <- R18 | rewrite <- R22]; apply (swe_regs_through regs1 regsT regs2 _ KR HP); cbn; tauto.
Qed.

Lemma swe_reg_after : forall (regs1 regsT regs2 : bvmap 5 word) r v,
(forall rr, In rr swe_kept_regs -> getr regsT rr = getr regs1 rr) -> aregs_preserved regsT regs2 ->
In r [2;3;4;8;9;18;19;20;21;22;23;24;25;26;27] -> getr regs1 (Z_to_bv 5 r) = v -> getr regs2 (Z_to_bv 5 r) = v.
Proof. intros regs1 regsT regs2 r v KR HP Hin Hv. rewrite <- Hv. exact (swe_regs_through regs1 regsT regs2 r KR HP Hin). Qed.

Lemma swe_sig_xstrdup : SIG CS_xstrdup = BASE + AF_xstrdup.
Proof. rewrite (SIGP CS_xstrdup ltac:(cbn [In cmd_prog_syms]; tauto)). reflexivity. Qed.

Lemma swe_X1_ok : RS 1 SWE_R1 -> XS 1 SWE_X1.
Proof.
intros HR1 lyc Sc Wc regs1 memc mdc k O0 D Fr NB HC HRB HRC HXR HREPc.
unfold swe_at.
pose proof HC as (HJ & Hk & HFR & HP0 & HP1 & HFrO & HDO & HO0 & HNBD & HNBl & HNBb & HMLE & HO0D).
pose proof HRB as (R2 & R3 & R4 & R8 & R21 & R23).
pose proof (proj1 HJ) as HAR.
destruct swe_sp_mid as (Hsp & Hsp16 & Hceil).
assert (Esp : spZ regs1 = spZ regs - 64) by (unfold spZ; rewrite R2; unfold w64; rewrite unsigned_lit_small by lia; reflexivity).
pose proof (proj1 (swe_env_mid regs1)) as HEI.
destruct (swe_x_seed lyc Sc Wc memc mdc regs1 _ (spZ regs1) _ _ SWE_X1 HAR (swe_env_mid regs1)
  ltac:(rewrite Esp; exact Hsp) ltac:(rewrite Esp; exact Hsp16) ltac:(pose proof swe_n_le; lia) swe_c_ok
  (regs_ok_Eimg_Ereg regs1 _)) as [HS SHOK].
paj_run_tok RUN HS HJ SHOK swe_Bspan.
{ apply awr_ok_nil. }
pmkst HS.
set (Ex := swe_extra regs (Z.of_nat (swe_n (R:=R))) (swe_c (R:=R))) in *.
assert (HAE : env_agree 32 (Ereg regs1 Ex) (Eimg (Ereg regs1 Ex)))
  by (split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
pose proof (regs_kept_of_st_ok SEGS _ _ _ regs1 Ex swe_kept_regs HS HAE
  ltac:(vm_compute; reflexivity)) as KR. cbn [ms_regs restrict] in KR.
sreg HS (10%bv : bv 5) Q10. sreg HS (1%bv : bv 5) Q1.
rewrite (ew_Eimg_Ereg_nat regs1 Ex 20 20%bv eq_refl) in Q10.
rewrite (img_env_codeptr _ HEI) in Q1.
rewrite swe_sig_xstrdup.
set (regsT := ms_regs ms) in *. set (memT := ms_mem ms) in *.
assert (KM : forall a, 0 <= a < 2 ^ 64 -> rdW Wc memT a = rdW Wc memc a).
{ intros a Ha. apply (kept_of_frame _ _ (w_H Wc) memc memT (fun _ => False) HFr); [|exact Ha|intros H; exact H].
  intros b wlo whi a' Hin _. cbn in Hin. destruct Hin. }
pose proof (swe_core_mem 0 lyc Sc Wc memc mdc k O0 D Fr NB memT _ HC HJ KM) as HCT.
assert (HREPT : rec_repA B lyc Sc (rdW Wc memT) (rec_record R REC_WORKER_ENV (firstn 0 (swe_A3 (format:=format) (cpus:=cpus) (nice:=nice)))) (O0 ++ NB)).
{ apply (rec_repA_kept B lyc Sc (rdW Wc memc) lyc Sc (rdW Wc memT) _ _ HREPc).
  - exact (rec_repA_in B lyc Sc _ _ _ HREPc).
  - intros a Ha. apply KM. unfold A_G_REC in Ha. lia.
  - intros a Ha. apply KM. unfold A_REC_SPILL in Ha. lia.
  - intros q n i Hq Hi. apply KM.
    pose proof (rec_repA_in B lyc Sc _ _ _ HREPc _ Hq) as Hq2.
    destruct (al_blocks _ _ LAWS _ _ _ _ _ q n HAR Hq2) as (_ & Hq4096 & Hqc & _).
    pose proof (req_size_pos n ltac:(lia)) as [_ Hr]. pose proof asan_consts as (C1 & _). lia. }
destruct (swe_sel_now pf format 0 lyc Sc Wc memT _ k O0 D Fr NB HAFx HCT) as (HARG & HTAIL & HLMAX).
destruct (swe_budget_x 0 lyc Sc Wc memT _ k O0 D Fr NB ltac:(lia) HCT) as (HEV1 & HLIVE1 & HMOK1).
pose proof (swe_rodata_now 0 lyc Sc Wc memT _ k O0 D Fr NB HCT) as HRODT.
assert (KRZ : forall rr, In rr swe_kept_regs -> getr regsT rr = getr regs1 rr) by exact KR.
swe_z5.
destruct swe_sp_bounds as (Hsp1 & Hsp47 & _ & Hceil1 & HWS).
assert (HspT : spZ regsT = spZ regs + -64).
{ unfold spZ at 1. swe_z5. rewrite (KR (Z_to_bv 5 2) (swe_kept_in 2 ltac:(cbn; tauto))), R2. unfold w64.
  rewrite unsigned_lit_small by lia. lia. }
pose proof pa_base_lo as HBLO. pose proof pa_B_ok as HBOK.
eapply SRr_bind.
{ eapply (cl_callS B LAWS Wc regsT memT _ SUP_WORKER_ENV_STK (spZ regs) (swe_FP (O:=O)) ly S W mem md [] lyc Sc _ k
     XSTRDUP_STK [] EV_XSTRDUP (-64) (Z_to_bv 64 (BASE + 23620)) []
     (fun ly2 S2 W2 regs2 mem2 md2 => exists p : Z,
       getr regs2 10 = w64 p /\ 4096 <= p < 2 ^ 64 /\
       Permutation (ablocks B ly2 S2) ((p, LIVE_XSTRDUP (sarg format)) :: ablocks B lyc Sc) /\
       Forall (fun qk => iv_apart p (LIVE_XSTRDUP (sarg format)) (fst qk) (snd qk)) (ablocks B lyc Sc) /\
       in_blockA (ablocks B ly2 S2) p (LIVE_XSTRDUP (sarg format)) /\
       astr_atR (rdW W2 mem2) p (sarg format) /\ astr_atR (rdW W2 mem2) (swe_sel pf) (sarg format) /\
       blocks_bytes S2 <= blocks_bytes Sc + LIVE_XSTRDUP (sarg format) /\
       mo_le MT Sc S2 (XM_XSTRDUP MT (sarg format))) HJ HspT).
  - reflexivity.
  - lia.
  - unfold XSTRDUP_STK, ASTACK. lia.
  - unfold XSTRDUP_STK, ASTACK. lia.
  - swe_z5. rewrite (KR (Z_to_bv 5 3) (swe_kept_in 3 ltac:(cbn; tauto))). exact R3.
  - swe_z5. rewrite (KR (Z_to_bv 5 4) (swe_kept_in 4 ltac:(cbn; tauto))). exact R4.
  - swe_z5. exact Q1.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - rewrite unsigned_lit_small by lia. lia.
  - apply achain_low. unfold s0Z. swe_z5. rewrite (KR (Z_to_bv 5 8) (swe_kept_in 8 ltac:(cbn; tauto))), R8. unfold w64.
    destruct (swe_slot_bounds _ swe_c_ok) as [Hcb _]. pose proof asan_consts as (C1 & _).
    rewrite unsigned_lit_small; unfold A_G_REC, A_REC_SPILL, OFF_CALLS in *; lia.
  - intros HPRE1. eapply SRr_mono.
    { apply (TXSTRDUP fx lyc Sc Wc regsT memT _ [] (swe_sel pf) (sarg format) HPRE1 HRODT).
      - swe_z5. rewrite Q10. exact (proj1 HXR).
      - left. exact HARG.
      - exact HTAIL.
      - exact HEV1.
      - exact HLIVE1.
      - exact HMOK1. }
    cbv beta. intros W2 c2 _ (ly' & S' & regs' & mem' & md' & -> & HJ' & HP' & HK').
    exists ly', S', regs', mem', md'. swe_z5. rewrite Q1. split; [reflexivity|]. split; [exact HJ'|]. split; [exact HP' | exact HK'].
  - intros a Ha. exfalso. exact (inFP_nil a Ha). }
cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HJc & HP2 & (p & Hp10 & [Hp4096 Hp64] & Hperm & Hfresh & _ & Hstrp & _ & _ & MLE)).
destruct (swe_after_x 1 lyc Sc Wc memT _ k O0 D Fr NB ly2 S2 W2 mem2 md2 p ltac:(lia) HCT HREPT HJ2 HJc Hperm Hfresh MLE)
  as (HC2 & HREP2 & HFR2).
apply (HR1 ly2 S2 W2 regs2 mem2 md2 (k + EV_XSTRDUP) O0 D Fr NB p HC2).
- exact (swe_base_after regs1 regsT regs2 HRB KRZ HP2).
- exact (swe_chk_after regs1 regsT regs2 HRC KRZ HP2).
- destruct HXR as (_ & X19 & X9). cbn [swe_R_regs]. swe_z5.
  split; [apply (swe_reg_after regs1 regsT regs2 19 _ KRZ HP2); [cbn; tauto | exact X19]
        | apply (swe_reg_after regs1 regsT regs2 9 _ KRZ HP2); [cbn; tauto | exact X9]].
- exact Hp10.
- exact HREP2.
- exact Hp4096.
- exact Hstrp.
- exact HFR2.
Qed.

Lemma swe_X2_ok : RS 2 SWE_R2 -> XS 2 SWE_X2.
Proof.
intros HR2 lyc Sc Wc regs1 memc mdc k O0 D Fr NB HC HRB HRC HXR HREPc.
unfold swe_at.
pose proof HC as (HJ & Hk & HFR & HP0 & HP1 & HFrO & HDO & HO0 & HNBD & HNBl & HNBb & HMLE & HO0D).
pose proof HRB as (R2 & R3 & R4 & R8 & R21 & R23).
pose proof (proj1 HJ) as HAR.
destruct swe_sp_mid as (Hsp & Hsp16 & Hceil).
assert (Esp : spZ regs1 = spZ regs - 64) by (unfold spZ; rewrite R2; unfold w64; rewrite unsigned_lit_small by lia; reflexivity).
pose proof (proj1 (swe_env_mid regs1)) as HEI.
destruct (swe_x_seed lyc Sc Wc memc mdc regs1 _ (spZ regs1) _ _ SWE_X2 HAR (swe_env_mid regs1)
  ltac:(rewrite Esp; exact Hsp) ltac:(rewrite Esp; exact Hsp16) ltac:(pose proof swe_n_le; lia) swe_c_ok
  (regs_ok_Eimg_Ereg regs1 _)) as [HS SHOK].
paj_run_tok RUN HS HJ SHOK swe_Bspan.
{ apply awr_ok_nil. }
pmkst HS.
set (Ex := swe_extra regs (Z.of_nat (swe_n (R:=R))) (swe_c (R:=R))) in *.
assert (HAE : env_agree 32 (Ereg regs1 Ex) (Eimg (Ereg regs1 Ex)))
  by (split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
pose proof (regs_kept_of_st_ok SEGS _ _ _ regs1 Ex swe_kept_regs HS HAE
  ltac:(vm_compute; reflexivity)) as KR. cbn [ms_regs restrict] in KR.
sreg HS (10%bv : bv 5) Q10. sreg HS (1%bv : bv 5) Q1.
rewrite (ew_Eimg_Ereg_nat regs1 Ex 19 19%bv eq_refl) in Q10.
rewrite (img_env_codeptr _ HEI) in Q1.
rewrite swe_sig_xstrdup.
set (regsT := ms_regs ms) in *. set (memT := ms_mem ms) in *.
assert (KM : forall a, 0 <= a < 2 ^ 64 -> rdW Wc memT a = rdW Wc memc a).
{ intros a Ha. apply (kept_of_frame _ _ (w_H Wc) memc memT (fun _ => False) HFr); [|exact Ha|intros H; exact H].
  intros b wlo whi a' Hin _. cbn in Hin. destruct Hin. }
pose proof (swe_core_mem 1 lyc Sc Wc memc mdc k O0 D Fr NB memT _ HC HJ KM) as HCT.
assert (HREPT : rec_repA B lyc Sc (rdW Wc memT) (rec_record R REC_WORKER_ENV (firstn 1 (swe_A3 (format:=format) (cpus:=cpus) (nice:=nice)))) (O0 ++ NB)).
{ apply (rec_repA_kept B lyc Sc (rdW Wc memc) lyc Sc (rdW Wc memT) _ _ HREPc).
  - exact (rec_repA_in B lyc Sc _ _ _ HREPc).
  - intros a Ha. apply KM. unfold A_G_REC in Ha. lia.
  - intros a Ha. apply KM. unfold A_REC_SPILL in Ha. lia.
  - intros q n i Hq Hi. apply KM.
    pose proof (rec_repA_in B lyc Sc _ _ _ HREPc _ Hq) as Hq2.
    destruct (al_blocks _ _ LAWS _ _ _ _ _ q n HAR Hq2) as (_ & Hq4096 & Hqc & _).
    pose proof (req_size_pos n ltac:(lia)) as [_ Hr]. pose proof asan_consts as (C1 & _). lia. }
destruct (swe_sel_now pcs cpus 1 lyc Sc Wc memT _ k O0 D Fr NB HACx HCT) as (HARG & HTAIL & HLMAX).
destruct (swe_budget_x 1 lyc Sc Wc memT _ k O0 D Fr NB ltac:(lia) HCT) as (HEV1 & HLIVE1 & HMOK1).
pose proof (swe_rodata_now 1 lyc Sc Wc memT _ k O0 D Fr NB HCT) as HRODT.
assert (KRZ : forall rr, In rr swe_kept_regs -> getr regsT rr = getr regs1 rr) by exact KR.
swe_z5.
destruct swe_sp_bounds as (Hsp1 & Hsp47 & _ & Hceil1 & HWS).
assert (HspT : spZ regsT = spZ regs + -64).
{ unfold spZ at 1. swe_z5. rewrite (KR (Z_to_bv 5 2) (swe_kept_in 2 ltac:(cbn; tauto))), R2. unfold w64.
  rewrite unsigned_lit_small by lia. lia. }
pose proof pa_base_lo as HBLO. pose proof pa_B_ok as HBOK.
eapply SRr_bind.
{ eapply (cl_callS B LAWS Wc regsT memT _ SUP_WORKER_ENV_STK (spZ regs) (swe_FP (O:=O)) ly S W mem md [] lyc Sc _ k
     XSTRDUP_STK [] EV_XSTRDUP (-64) (Z_to_bv 64 (BASE + 23700)) []
     (fun ly2 S2 W2 regs2 mem2 md2 => exists p : Z,
       getr regs2 10 = w64 p /\ 4096 <= p < 2 ^ 64 /\
       Permutation (ablocks B ly2 S2) ((p, LIVE_XSTRDUP (sarg cpus)) :: ablocks B lyc Sc) /\
       Forall (fun qk => iv_apart p (LIVE_XSTRDUP (sarg cpus)) (fst qk) (snd qk)) (ablocks B lyc Sc) /\
       in_blockA (ablocks B ly2 S2) p (LIVE_XSTRDUP (sarg cpus)) /\
       astr_atR (rdW W2 mem2) p (sarg cpus) /\ astr_atR (rdW W2 mem2) (swe_sel pcs) (sarg cpus) /\
       blocks_bytes S2 <= blocks_bytes Sc + LIVE_XSTRDUP (sarg cpus) /\
       mo_le MT Sc S2 (XM_XSTRDUP MT (sarg cpus))) HJ HspT).
  - reflexivity.
  - lia.
  - unfold XSTRDUP_STK, ASTACK. lia.
  - unfold XSTRDUP_STK, ASTACK. lia.
  - swe_z5. rewrite (KR (Z_to_bv 5 3) (swe_kept_in 3 ltac:(cbn; tauto))). exact R3.
  - swe_z5. rewrite (KR (Z_to_bv 5 4) (swe_kept_in 4 ltac:(cbn; tauto))). exact R4.
  - swe_z5. exact Q1.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - rewrite unsigned_lit_small by lia. lia.
  - apply achain_low. unfold s0Z. swe_z5. rewrite (KR (Z_to_bv 5 8) (swe_kept_in 8 ltac:(cbn; tauto))), R8. unfold w64.
    destruct (swe_slot_bounds _ swe_c_ok) as [Hcb _]. pose proof asan_consts as (C1 & _).
    rewrite unsigned_lit_small; unfold A_G_REC, A_REC_SPILL, OFF_CALLS in *; lia.
  - intros HPRE1. eapply SRr_mono.
    { apply (TXSTRDUP fx lyc Sc Wc regsT memT _ [] (swe_sel pcs) (sarg cpus) HPRE1 HRODT).
      - swe_z5. rewrite Q10. exact (proj1 (proj2 HXR)).
      - left. exact HARG.
      - exact HTAIL.
      - exact HEV1.
      - exact HLIVE1.
      - exact HMOK1. }
    cbv beta. intros W2 c2 _ (ly' & S' & regs' & mem' & md' & -> & HJ' & HP' & HK').
    exists ly', S', regs', mem', md'. swe_z5. rewrite Q1. split; [reflexivity|]. split; [exact HJ'|]. split; [exact HP' | exact HK'].
  - intros a Ha. exfalso. exact (inFP_nil a Ha). }
cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HJc & HP2 & (p & Hp10 & [Hp4096 Hp64] & Hperm & Hfresh & _ & Hstrp & _ & _ & MLE)).
destruct (swe_after_x 2 lyc Sc Wc memT _ k O0 D Fr NB ly2 S2 W2 mem2 md2 p ltac:(lia) HCT HREPT HJ2 HJc Hperm Hfresh MLE)
  as (HC2 & HREP2 & HFR2).
apply (HR2 ly2 S2 W2 regs2 mem2 md2 (k + EV_XSTRDUP) O0 D Fr NB p HC2).
- exact (swe_base_after regs1 regsT regs2 HRB KRZ HP2).
- exact (swe_chk_after regs1 regsT regs2 HRC KRZ HP2).
- destruct HXR as (X20 & _ & X9). cbn [swe_R_regs]. swe_z5.
  split; [apply (swe_reg_after regs1 regsT regs2 20 _ KRZ HP2); [cbn; tauto | exact X20]
        | apply (swe_reg_after regs1 regsT regs2 9 _ KRZ HP2); [cbn; tauto | exact X9]].
- exact Hp10.
- exact HREP2.
- exact Hp4096.
- exact Hstrp.
- exact HFR2.
Qed.

Lemma swe_X3_ok : RS 3 SWE_R3 -> XS 3 SWE_X3.
Proof.
intros HR3 lyc Sc Wc regs1 memc mdc k O0 D Fr NB HC HRB HRC HXR HREPc.
unfold swe_at.
pose proof HC as (HJ & Hk & HFR & HP0 & HP1 & HFrO & HDO & HO0 & HNBD & HNBl & HNBb & HMLE & HO0D).
pose proof HRB as (R2 & R3 & R4 & R8 & R21 & R23).
pose proof (proj1 HJ) as HAR.
destruct swe_sp_mid as (Hsp & Hsp16 & Hceil).
assert (Esp : spZ regs1 = spZ regs - 64) by (unfold spZ; rewrite R2; unfold w64; rewrite unsigned_lit_small by lia; reflexivity).
pose proof (proj1 (swe_env_mid regs1)) as HEI.
destruct (swe_x_seed lyc Sc Wc memc mdc regs1 _ (spZ regs1) _ _ SWE_X3 HAR (swe_env_mid regs1)
  ltac:(rewrite Esp; exact Hsp) ltac:(rewrite Esp; exact Hsp16) ltac:(pose proof swe_n_le; lia) swe_c_ok
  (regs_ok_Eimg_Ereg regs1 _)) as [HS SHOK].
paj_run_tok RUN HS HJ SHOK swe_Bspan.
{ apply awr_ok_nil. }
pmkst HS.
set (Ex := swe_extra regs (Z.of_nat (swe_n (R:=R))) (swe_c (R:=R))) in *.
assert (HAE : env_agree 32 (Ereg regs1 Ex) (Eimg (Ereg regs1 Ex)))
  by (split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
pose proof (regs_kept_of_st_ok SEGS _ _ _ regs1 Ex swe_kept_regs HS HAE
  ltac:(vm_compute; reflexivity)) as KR. cbn [ms_regs restrict] in KR.
sreg HS (10%bv : bv 5) Q10. sreg HS (1%bv : bv 5) Q1.
rewrite (ew_Eimg_Ereg_nat regs1 Ex 9 9%bv eq_refl) in Q10.
rewrite (img_env_codeptr _ HEI) in Q1.
rewrite swe_sig_xstrdup.
set (regsT := ms_regs ms) in *. set (memT := ms_mem ms) in *.
assert (KM : forall a, 0 <= a < 2 ^ 64 -> rdW Wc memT a = rdW Wc memc a).
{ intros a Ha. apply (kept_of_frame _ _ (w_H Wc) memc memT (fun _ => False) HFr); [|exact Ha|intros H; exact H].
  intros b wlo whi a' Hin _. cbn in Hin. destruct Hin. }
pose proof (swe_core_mem 2 lyc Sc Wc memc mdc k O0 D Fr NB memT _ HC HJ KM) as HCT.
assert (HREPT : rec_repA B lyc Sc (rdW Wc memT) (rec_record R REC_WORKER_ENV (firstn 2 (swe_A3 (format:=format) (cpus:=cpus) (nice:=nice)))) (O0 ++ NB)).
{ apply (rec_repA_kept B lyc Sc (rdW Wc memc) lyc Sc (rdW Wc memT) _ _ HREPc).
  - exact (rec_repA_in B lyc Sc _ _ _ HREPc).
  - intros a Ha. apply KM. unfold A_G_REC in Ha. lia.
  - intros a Ha. apply KM. unfold A_REC_SPILL in Ha. lia.
  - intros q n i Hq Hi. apply KM.
    pose proof (rec_repA_in B lyc Sc _ _ _ HREPc _ Hq) as Hq2.
    destruct (al_blocks _ _ LAWS _ _ _ _ _ q n HAR Hq2) as (_ & Hq4096 & Hqc & _).
    pose proof (req_size_pos n ltac:(lia)) as [_ Hr]. pose proof asan_consts as (C1 & _). lia. }
destruct (swe_sel_now pnn nice 2 lyc Sc Wc memT _ k O0 D Fr NB HANx HCT) as (HARG & HTAIL & HLMAX).
destruct (swe_budget_x 2 lyc Sc Wc memT _ k O0 D Fr NB ltac:(lia) HCT) as (HEV1 & HLIVE1 & HMOK1).
pose proof (swe_rodata_now 2 lyc Sc Wc memT _ k O0 D Fr NB HCT) as HRODT.
assert (KRZ : forall rr, In rr swe_kept_regs -> getr regsT rr = getr regs1 rr) by exact KR.
swe_z5.
destruct swe_sp_bounds as (Hsp1 & Hsp47 & _ & Hceil1 & HWS).
assert (HspT : spZ regsT = spZ regs + -64).
{ unfold spZ at 1. swe_z5. rewrite (KR (Z_to_bv 5 2) (swe_kept_in 2 ltac:(cbn; tauto))), R2. unfold w64.
  rewrite unsigned_lit_small by lia. lia. }
pose proof pa_base_lo as HBLO. pose proof pa_B_ok as HBOK.
eapply SRr_bind.
{ eapply (cl_callS B LAWS Wc regsT memT _ SUP_WORKER_ENV_STK (spZ regs) (swe_FP (O:=O)) ly S W mem md [] lyc Sc _ k
     XSTRDUP_STK [] EV_XSTRDUP (-64) (Z_to_bv 64 (BASE + 23776)) []
     (fun ly2 S2 W2 regs2 mem2 md2 => exists p : Z,
       getr regs2 10 = w64 p /\ 4096 <= p < 2 ^ 64 /\
       Permutation (ablocks B ly2 S2) ((p, LIVE_XSTRDUP (sarg nice)) :: ablocks B lyc Sc) /\
       Forall (fun qk => iv_apart p (LIVE_XSTRDUP (sarg nice)) (fst qk) (snd qk)) (ablocks B lyc Sc) /\
       in_blockA (ablocks B ly2 S2) p (LIVE_XSTRDUP (sarg nice)) /\
       astr_atR (rdW W2 mem2) p (sarg nice) /\ astr_atR (rdW W2 mem2) (swe_sel pnn) (sarg nice) /\
       blocks_bytes S2 <= blocks_bytes Sc + LIVE_XSTRDUP (sarg nice) /\
       mo_le MT Sc S2 (XM_XSTRDUP MT (sarg nice))) HJ HspT).
  - reflexivity.
  - lia.
  - unfold XSTRDUP_STK, ASTACK. lia.
  - unfold XSTRDUP_STK, ASTACK. lia.
  - swe_z5. rewrite (KR (Z_to_bv 5 3) (swe_kept_in 3 ltac:(cbn; tauto))). exact R3.
  - swe_z5. rewrite (KR (Z_to_bv 5 4) (swe_kept_in 4 ltac:(cbn; tauto))). exact R4.
  - swe_z5. exact Q1.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - rewrite unsigned_lit_small by lia. lia.
  - apply achain_low. unfold s0Z. swe_z5. rewrite (KR (Z_to_bv 5 8) (swe_kept_in 8 ltac:(cbn; tauto))), R8. unfold w64.
    destruct (swe_slot_bounds _ swe_c_ok) as [Hcb _]. pose proof asan_consts as (C1 & _).
    rewrite unsigned_lit_small; unfold A_G_REC, A_REC_SPILL, OFF_CALLS in *; lia.
  - intros HPRE1. eapply SRr_mono.
    { apply (TXSTRDUP fx lyc Sc Wc regsT memT _ [] (swe_sel pnn) (sarg nice) HPRE1 HRODT).
      - swe_z5. rewrite Q10. exact (proj2 HXR).
      - left. exact HARG.
      - exact HTAIL.
      - exact HEV1.
      - exact HLIVE1.
      - exact HMOK1. }
    cbv beta. intros W2 c2 _ (ly' & S' & regs' & mem' & md' & -> & HJ' & HP' & HK').
    exists ly', S', regs', mem', md'. swe_z5. rewrite Q1. split; [reflexivity|]. split; [exact HJ'|]. split; [exact HP' | exact HK'].
  - intros a Ha. exfalso. exact (inFP_nil a Ha). }
cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HJc & HP2 & (p & Hp10 & [Hp4096 Hp64] & Hperm & Hfresh & _ & Hstrp & _ & _ & MLE)).
destruct (swe_after_x 3 lyc Sc Wc memT _ k O0 D Fr NB ly2 S2 W2 mem2 md2 p ltac:(lia) HCT HREPT HJ2 HJc Hperm Hfresh MLE)
  as (HC2 & HREP2 & HFR2).
apply (HR3 ly2 S2 W2 regs2 mem2 md2 (k + EV_XSTRDUP) O0 D Fr NB p HC2).
- exact (swe_base_after regs1 regsT regs2 HRB KRZ HP2).
- exact (swe_chk_after regs1 regsT regs2 HRC KRZ HP2).
- destruct HXR as (X20 & _). cbn [swe_R_regs]. swe_z5.
  apply (swe_reg_after regs1 regsT regs2 20 _ KRZ HP2); [cbn; tauto | exact X20].
- exact Hp10.
- exact HREP2.
- exact Hp4096.
- exact Hstrp.
- exact HFR2.
Qed.

(* the recorded call's nargs field, from the recorder's state *)
Lemma swe_rep_nargs : forall ly1 S1 rd A O1,
rec_repA B ly1 S1 rd (rec_record R REC_WORKER_ENV A) O1 ->
aval_mem rd (swe_c (R:=R) + 4) 4 (Z.of_nat (length A)).
Proof.
intros ly1 S1 rd A O1 (Q & HA & _).
destruct HA as (_ & _ & _ & (C1 & C2 & C3 & C4 & C5 & C6) & _).
unfold swe_c, swe_slot_of, swe_n. destruct (Nat.ltb_spec (length (r_calls R)) 16) as [Hl|Hl].
- rewrite (rec_record_calls R _ _ Hl) in C2, C4. cbn [r_calls set_calls] in C2, C4.
  replace (Z.of_nat (length (r_calls R)) <? 16) with true by (symmetry; apply Z.ltb_lt; lia).
  rewrite length_app in C2. cbn [length] in C2.
  destruct (nth_error (l_calls Q) (length (r_calls R))) as [P|] eqn:EP.
  + assert (Ec : nth_error (r_calls R ++ [(REC_WORKER_ENV, A)]) (length (r_calls R)) = Some (REC_WORKER_ENV, A))
      by (rewrite nth_error_app2 by lia; rewrite Nat.sub_diag; reflexivity).
    destruct (C4 _ _ _ Ec EP) as ((_ & _ & _ & _ & H5 & _) & _). cbn [snd] in H5.
    unfold CALL_OFF_NARGS in H5. exact H5.
  + exfalso. apply nth_error_None in EP. lia.
- pose proof (rec_record_length R REC_WORKER_ENV [] ltac:(destruct HREP as (Q0 & (_ & _ & _ & (H & _) & _) & _); exact H)) as _.
  assert (Hn16 : length (r_calls R) = 16%nat)
    by (destruct HREP as (Q0 & (_ & _ & _ & (H & _) & _) & _); lia).
  rewrite (rec_record_spill R _ _ Hn16) in C5. cbn [r_spill set_spill] in C5.
  replace (Z.of_nat (length (r_calls R)) <? 16) with false by (symmetry; apply Z.ltb_ge; lia).
  destruct C5 as (_ & _ & _ & _ & H5 & _). cbn [snd] in H5. unfold CALL_OFF_NARGS in H5. exact H5.
Qed.

(* every write of a mid segment lies in the slot: a program static of the footprint *)
Lemma swe_awr_slot : forall E cs bl0 blc fr0 ly1 own,
ew E SW_C = Z_to_bv 64 (swe_c (R:=R)) ->
awr_ok SEGS B E [swe_slot cs] SUP_WORKER_ENV_STK (spZ regs) FPw bl0 blc fr0 ly1 own.
Proof.
intros E cs bl0 blc fr0 ly1 own EC.
destruct (swe_slot_bounds _ swe_c_ok) as [Hcb _].
apply (YCbq.awr_ok_cons_gen SEGS B) with (k := SW_C) (b := swe_c (R:=R)); [reflexivity | rewrite EC; apply unsigned_lit_small; unfold A_G_REC, A_REC_SPILL, OFF_CALLS in *; lia | | apply (YCbq.awr_ok_nil SEGS B)].
intros a Ha. cbn [YP09.r_wlo YP09.r_whi swe_slot] in Ha.
assert (Hr : in_recg a).
{ destruct swe_c_ok as [(H1 & H2 & _) | E1]; [left | right]; [unfold A_G_REC, REC_SIZE, CALL_SIZE, OFF_CALLS in *; lia|].
  rewrite E1 in Ha. unfold A_REC_SPILL, SC_SIZE, CALL_SIZE in *; lia. }
right; right; right; right; left. split; [|split].
- unfold swe_FP. destruct Hr as [Hr|Hr]; [exists (A_G_REC, A_G_REC + REC_SIZE); split; [left; reflexivity | exact Hr]
  | exists (A_REC_SPILL, A_REC_SPILL + SC_SIZE); split; [right; left; reflexivity | exact Hr]].
- rewrite (recb_ts_prog_m B HB). destruct Hr; [apply recb_grec_in | apply recb_spill_in]; assumption.
- apply cmd_prog_img. destruct Hr; [apply recb_grec_in | apply recb_spill_in]; assumption.
Qed.

(* the slot's fields a segment writes, each a region of its own, so that the run's frame names exactly the bytes
   written: J writes fn and nargs, the m-th arg_s writes nargs and args[m-1] *)
Definition swe_regJ : YP09.region := YP09.mkRegion (Some SW_C) 0 8 0 8 [].
Definition swe_regN (v : Z) : YP09.region := YP09.mkRegion (Some SW_C) 4 8 4 8 [YP09.mkChunk 4 (CVal 4 (SLit v))].
Definition swe_regA (j : Z) : YP09.region := YP09.mkRegion (Some SW_C) (8 + 8 * j) (16 + 8 * j) (8 + 8 * j) (16 + 8 * j) [].

Lemma swe_slot_rok : forall ly1 S1 (W1 : world SEGS) mem1 md1 E sp n lo hi wlo whi cs,
AR SEGS B ly1 S1 W1 mem1 md1 -> swe_env_ok E sp n (swe_c (R:=R)) ->
0 <= lo -> hi <= CALL_SIZE -> 0 <= wlo -> whi <= CALL_SIZE ->
Forall (YP09.chunk_ok SEGS E (mrestrict (w_H W1) mem1) (swe_c (R:=R))) cs ->
YP09.region_ok SEGS E (mrestrict (w_H W1) mem1) (YP09.mkRegion (Some SW_C) lo hi wlo whi cs).
Proof.
intros ly1 S1 W1 mem1 md1 E sp n lo hi wlo whi cs HAR HE Hlo Hhi Hwlo Hwhi Hcs.
pose proof HE as (_ & _ & _ & _ & EC). destruct (swe_slot_bounds _ swe_c_ok) as [Hcb _].
unfold YP09.region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
rewrite EC, unsigned_lit_small by (unfold A_G_REC, A_REC_SPILL, OFF_CALLS in *; lia).
split; [unfold A_G_REC, OFF_CALLS in *; lia|]. split; [unfold CALL_SIZE, A_REC_SPILL in *; lia|].
split; [|exact Hcs].
intros o Ho. apply (cmd_prog_writable ly1 S1 W1 mem1 md1); [exact HAR|].
destruct swe_c_ok as [(H1 & H2 & H3) | E1]; [apply recb_grec_in | rewrite E1; apply recb_spill_in];
unfold A_G_REC, REC_SIZE, A_REC_SPILL, SC_SIZE, CALL_SIZE, OFF_CALLS in *; lia.
Qed.

Lemma swe_seed_rs : forall ly1 S1 (W1 : world SEGS) mem1 md1 (regs1 : bvmap 5 word) E sp n pc rs,
AR SEGS B ly1 S1 W1 mem1 md1 ->
swe_env_ok E sp n (swe_c (R:=R)) -> 2 ^ 46 <= sp <= 2 ^ 47 -> sp mod 16 = 0 -> 0 <= n <= 16 ->
regs_ok E sr_atoms regs1 ->
regions_wf rs = true -> Forall (YP09.region_ok SEGS E (mrestrict (w_H W1) mem1)) rs -> pairwise_disjoint E rs ->
st_ok_pi SEGS VAL E (mkSS pc sr_atoms rs None swe_facts)
  (restrict (w_H W1) (mkst regs1 (Z_to_bv 64 (BASE + pc)) mem1 (seg_rom SEGS)))
/\ sh_ok SEGS swe_Bx swe_SH E (mrestrict (w_H W1) mem1).
Proof.
intros ly1 S1 W1 mem1 md1 regs1 E sp n pc rs HAR HE Hsp Hsp16 Hn HREG Hwf Hrs Hpd.
split; [| exact (swe_sh_ok B HB ly1 S1 W1 mem1 md1 E sp n _ HAR HE swe_c_ok)].
rewrite restrict_mkst_fx. apply pa_entry_st_ok_full; [exact HREG | exact Hwf | exact Hrs | exact Hpd |].
exact (swe_facts_ok VOBJS E sp n _ HE Hsp Hsp16 Hn swe_c_ok).
Qed.

(* every region of a mid segment that writes lies in the slot: a program static of the footprint *)
Lemma swe_awr_slots : forall E rs bl0 blc fr0 ly1 own,
ew E SW_C = Z_to_bv 64 (swe_c (R:=R)) ->
Forall (fun r => YP09.r_base r = Some SW_C /\ 0 <= YP09.r_wlo r /\ YP09.r_whi r <= CALL_SIZE) rs ->
awr_ok SEGS B E rs SUP_WORKER_ENV_STK (spZ regs) FPw bl0 blc fr0 ly1 own.
Proof.
intros E rs bl0 blc fr0 ly1 own EC Hrs.
destruct (swe_slot_bounds _ swe_c_ok) as [Hcb _].
induction Hrs as [|r rs (Hb & Hwlo & Hwhi) Hrs IH]; [apply (YCbq.awr_ok_nil SEGS B)|].
apply (YCbq.awr_ok_cons_gen SEGS B) with (k := SW_C) (b := swe_c (R:=R));
  [exact Hb | rewrite EC; apply unsigned_lit_small; unfold A_G_REC, A_REC_SPILL, OFF_CALLS in *; lia | | exact IH].
intros a Ha.
assert (Hr : in_recg a).
{ destruct swe_c_ok as [(H1 & H2 & _) | E1]; [left | right]; [unfold A_G_REC, REC_SIZE, CALL_SIZE, OFF_CALLS in *; lia|].
  rewrite E1 in Ha. unfold A_REC_SPILL, SC_SIZE, CALL_SIZE in *; lia. }
right; right; right; right; left. split; [|split].
- unfold swe_FP. destruct Hr as [Hr|Hr]; [exists (A_G_REC, A_G_REC + REC_SIZE); split; [left; reflexivity | exact Hr]
  | exists (A_REC_SPILL, A_REC_SPILL + SC_SIZE); split; [right; left; reflexivity | exact Hr]].
- rewrite (recb_ts_prog_m B HB). destruct Hr; [apply recb_grec_in | apply recb_spill_in]; assumption.
- apply cmd_prog_img. destruct Hr; [apply recb_grec_in | apply recb_spill_in]; assumption.
Qed.


Lemma swe_core_mem2 : forall m lyc Sc Wc memc mdc k O0 D Fr NB memT mdT,
CORE m lyc Sc Wc memc mdc k O0 D Fr NB ->
ajournal SEGS B SUP_WORKER_ENV_STK (spZ regs) FPw ly S W mem md [] lyc Sc Wc memT mdT k ->
(forall a, spZ regs - 64 <= a < spZ regs -> rdW Wc memT a = rdW Wc memc a) ->
CORE m lyc Sc Wc memT mdT k O0 D Fr NB.
Proof.
intros m lyc Sc Wc memc mdc k O0 D Fr NB memT mdT HC HJT KR.
destruct HC as (_ & Hk & HFR & REST). split; [exact HJT|]. split; [exact Hk|]. split; [|exact REST].
exact (swe_frame_kept Wc Wc memc memT HFR KR).
Qed.

(* each recorded string is at most LMAX bytes *)
Lemma swe_A3_lmax : forall j, Z.of_nat (length (nth j (swe_A3 (format:=format) (cpus:=cpus) (nice:=nice)) [])) <= LMAX.
Proof.
assert (G : forall (p : Z) (v : option (list byte)), astr_argA B ly S (rdW W mem) (in_roP SEGS RLO RHI) O p v ->
  Z.of_nat (length (sarg v)) <= LMAX).
{ intros p [x|] HA; [cbn [astr_argA] in HA; destruct HA as (_ & _ & Hn & _); cbn [sarg]; unfold LMAX in *; lia
  | vm_compute; discriminate]. }
intros [|[|[|j]]]; cbn [nth swe_A3]; [exact (G _ _ HAF) | exact (G _ _ HAC) | exact (G _ _ HAN) | destruct j; vm_compute; discriminate].
Qed.

(* a heap block is apart from g_rec and from record.spill: those lie in the image *)
Lemma swe_blk_apart_rec : forall ly1 S1 (W1 : world SEGS) mem1 md1 p n, AR SEGS B ly1 S1 W1 mem1 md1 ->
In (p, n) (ablocks B ly1 S1) -> iv_apart p n A_G_REC REC_SIZE /\ iv_apart p n A_REC_SPILL SC_SIZE.
Proof.
intros ly1 S1 W1 mem1 md1 p n HAR Hin.
pose proof (blk_off_imgP B ly1 S1 W1 mem1 md1 p n HAR Hin) as Hoff.
destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR Hin) as (_ & _ & _ & _ & _ & _ & Hn).
pose proof (req_size_pos n ltac:(lia)) as [_ Hr]. unfold off_img in Hoff.
unfold iv_apart, A_G_REC, REC_SIZE, A_REC_SPILL, SC_SIZE. lia.
Qed.

(* the m-th arg_s: after the stores of nargs and args[m-1], the carried facts hold at the new memory *)
Lemma swe_R_to_X : forall m lyc Sc Wc memc mdc k O0 D Fr NB p memT mdT,
let x := nth (m - 1) (swe_A3 (format:=format) (cpus:=cpus) (nice:=nice)) [] in
let c := swe_c (R:=R) in
(1 <= m <= 3)%nat ->
CORE m lyc Sc Wc memc mdc k O0 D Fr (NB ++ [(p, Z.of_nat (length x) + 1)]) ->
rec_repA B lyc Sc (rdW Wc memc) (rec_record R REC_WORKER_ENV (firstn (m - 1) (swe_A3 (format:=format) (cpus:=cpus) (nice:=nice)))) (O0 ++ NB) ->
4096 <= p -> Forall (fun qk => iv_apart p (Z.of_nat (length x) + 1) (fst qk) (snd qk)) (D ++ NB) ->
astr_atR (rdW Wc memc) p x ->
ajournal SEGS B SUP_WORKER_ENV_STK (spZ regs) FPw ly S W mem md [] lyc Sc Wc memT mdT k ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (c + 4 <= a < c + 8) -> ~ (c + 8 + 8 * Z.of_nat (m - 1) <= a < c + 16 + 8 * Z.of_nat (m - 1)) ->
  rdW Wc memT a = rdW Wc memc a) ->
aval_mem (rdW Wc memT) (c + 4) 4 (Z.of_nat m) -> aval_mem (rdW Wc memT) (c + 8 + 8 * Z.of_nat (m - 1)) 8 p ->
CORE m lyc Sc Wc memT mdT k O0 D Fr (NB ++ [(p, Z.of_nat (length x) + 1)]) /\
rec_repA B lyc Sc (rdW Wc memT) (rec_record R REC_WORKER_ENV (firstn m (swe_A3 (format:=format) (cpus:=cpus) (nice:=nice))))
  (O0 ++ NB ++ [(p, Z.of_nat (length x) + 1)]).
Proof.
intros m lyc Sc Wc memc mdc k O0 D Fr NB p memT mdT x c Hm HC HREPc Hp4096 Hfresh Hstr HJT KM HNA HAR0.
destruct swe_sp_bounds as (Hsp & Hsp47 & _ & Hceil & HWS).
destruct (swe_slot_bounds _ swe_c_ok) as [Hcb _].
pose proof asan_consts as (C1 & _).
pose proof HC as (HJ & Hk & HFR & HP0 & HP1 & HFrO & HDO & HO0 & HNBD & HNBl & HNBb & HMLE & HO0D).
pose proof (proj1 HJ) as HAR.
assert (Hpin : In (p, Z.of_nat (length x) + 1) (ablocks B lyc Sc))
  by (apply (Permutation_in _ (Permutation_sym HP1)); apply in_or_app; right; apply in_or_app; right; left; reflexivity).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hpin) as (_ & _ & Hpceil & _).
pose proof (req_size_pos (Z.of_nat (length x) + 1) ltac:(lia)) as [_ Hpr].
assert (HBLK : forall q n i, In (q, n) (ablocks B lyc Sc) -> 0 <= i < n -> rdW Wc memT (q + i) = rdW Wc memc (q + i)).
{ intros q n i Hq Hi. pose proof (blk_off_imgP B lyc Sc Wc memc mdc q n HAR Hq) as Hoff.
  destruct (al_blocks _ _ LAWS _ _ _ _ _ q n HAR Hq) as (_ & Hq4096 & Hqc & _).
  pose proof (req_size_pos n ltac:(lia)) as [_ Hr]. unfold off_img in Hoff.
  apply KM; [lia | | ]; destruct swe_c_ok as [(H1 & H2 & _) | E1]; unfold c in *; try rewrite E1 in *;
  unfold A_G_REC, REC_SIZE, A_REC_SPILL, CALL_SIZE, OFF_CALLS in *; nia. }
split.
- apply (swe_core_mem2 m lyc Sc Wc memc mdc k O0 D Fr _ memT mdT HC HJT).
  intros a Ha. apply KM; [lia | |]; destruct swe_c_ok as [(H1 & H2 & _) | E1]; unfold c in *; try rewrite E1 in *;
  unfold A_G_REC, REC_SIZE, A_REC_SPILL, CALL_SIZE, OFF_CALLS in *; lia.
- assert (HLA : length (firstn (m - 1) (swe_A3 (format:=format) (cpus:=cpus) (nice:=nice))) = (m - 1)%nat)
    by (rewrite length_firstn; cbn [length swe_A3]; lia).
  assert (Ex : firstn (m - 1) (swe_A3 (format:=format) (cpus:=cpus) (nice:=nice)) ++ [x] = firstn m (swe_A3 (format:=format) (cpus:=cpus) (nice:=nice))).
  { unfold x. destruct m as [|[|[|[|m]]]]; try lia; reflexivity. }
  rewrite <- Ex, app_assoc.
  destruct (swe_blk_apart_rec lyc Sc Wc memc mdc _ _ HAR Hpin) as [Hag Has].
  apply (swe_rec_arg B lyc Sc (rdW Wc memc) (rdW Wc memT) R (O0 ++ NB) _ x p HREPc swe_n_le).
  + rewrite HLA. lia.
  + exact Hpin.
  + lia.
  + apply Forall_forall. intros q Hq. rewrite Forall_forall in Hfresh. apply Hfresh.
    apply in_app_iff in Hq as [Hq|Hq]; apply in_or_app; [left; exact (HO0D q Hq) | right; exact Hq].
  + exact Hag.
  + exact Has.
  + exact (swe_A3_lmax (m - 1)).
  + apply (rastr_kept (rdW Wc memc) (rdW Wc memT) p x Hstr). intros i Hi. apply (HBLK p _ i Hpin Hi).
  + rewrite HLA. replace (Z.of_nat (m - 1) + 1) with (Z.of_nat m) by lia. exact HNA.
  + rewrite HLA. exact HAR0.
  + intros a Ha H1 H2. rewrite HLA in H2. apply KM; [destruct Ha; unfold A_G_REC, REC_SIZE, A_REC_SPILL, SC_SIZE in *; lia | exact H1 | exact H2].
  + intros q n i Hq Hi. apply (HBLK q n i); [exact (rec_repA_in B lyc Sc _ _ _ HREPc _ Hq) | exact Hi].
Qed.


#[local] Notation XS6 := (swe_X_stmt (B:=B) (MT:=MT) (ly:=ly) (S:=S) (W:=W) (regs:=regs) (mem:=mem) (md:=md)
  (pf:=pf) (pcs:=pcs) (pnn:=pnn) (format:=format) (cpus:=cpus) (nice:=nice) (R:=R) (O:=O)).
#[local] Notation RS6 := (swe_R_stmt (B:=B) (MT:=MT) (ly:=ly) (S:=S) (W:=W) (regs:=regs) (mem:=mem) (md:=md)
  (pcs:=pcs) (pnn:=pnn) (format:=format) (cpus:=cpus) (nice:=nice) (R:=R) (O:=O)).

(* the end of the m-th arg_s segment: the facts at the next xstrdup's argument register give the next statement *)
Lemma swe_RX_apply : forall m pcX lyc Sc Wc memc mdc k O0 D Fr NB p (regsT : bvmap 5 word) memT mdT,
let x := nth (m - 1) (swe_A3 (format:=format) (cpus:=cpus) (nice:=nice)) [] in
let c := swe_c (R:=R) in
(1 <= m <= 2)%nat ->
XS6 (m + 1) pcX ->
CORE m lyc Sc Wc memc mdc k O0 D Fr (NB ++ [(p, Z.of_nat (length x) + 1)]) ->
rec_repA B lyc Sc (rdW Wc memc) (rec_record R REC_WORKER_ENV (firstn (m - 1) (swe_A3 (format:=format) (cpus:=cpus) (nice:=nice)))) (O0 ++ NB) ->
4096 <= p -> Forall (fun qk => iv_apart p (Z.of_nat (length x) + 1) (fst qk) (snd qk)) (D ++ NB) ->
astr_atR (rdW Wc memc) p x ->
ajournal SEGS B SUP_WORKER_ENV_STK (spZ regs) FPw ly S W mem md [] lyc Sc Wc memT mdT k ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (c + 4 <= a < c + 8) -> ~ (c + 8 + 8 * Z.of_nat (m - 1) <= a < c + 16 + 8 * Z.of_nat (m - 1)) ->
  rdW Wc memT a = rdW Wc memc a) ->
aval_mem (rdW Wc memT) (c + 4) 4 (Z.of_nat m) -> aval_mem (rdW Wc memT) (c + 8 + 8 * Z.of_nat (m - 1)) 8 p ->
swe_regs_base (B:=B) (regs:=regs) (R:=R) regsT -> swe_regs_chk (R:=R) regsT ->
swe_X_regs (pf:=pf) (pcs:=pcs) (pnn:=pnn) (R:=R) (m + 1) regsT ->
swe_at (B:=B) (MT:=MT) (ly:=ly) (S:=S) (W:=W) (regs:=regs) (mem:=mem) (md:=md) (format:=format) (cpus:=cpus)
  (nice:=nice) (R:=R) (O:=O) pcX Wc regsT memT mdT.
Proof.
intros m pcX lyc Sc Wc memc mdc k O0 D Fr NB p regsT memT mdT x c Hm HX HC HREPc Hp Hfresh Hstr HJT KM HNA HAR0 HRB HRC HXR.
destruct (swe_R_to_X m lyc Sc Wc memc mdc k O0 D Fr NB p memT mdT ltac:(lia) HC HREPc Hp Hfresh Hstr HJT KM HNA HAR0)
  as [HC2 HREP2].
apply (HX lyc Sc Wc regsT memT mdT k O0 D Fr (NB ++ [(p, Z.of_nat (length x) + 1)])).
- replace (m + 1 - 1)%nat with m by lia. exact HC2.
- exact HRB.
- exact HRC.
- exact HXR.
- replace (m + 1 - 1)%nat with m by lia. exact HREP2.
Qed.

(* an argument pointer: 0 exactly for a NULL argument, else an address of a live block or of the image *)
Lemma swe_ptr_range : forall (p : Z) (v : option (list byte)),
astr_argA B ly S (rdW W mem) (in_roP SEGS RLO RHI) O p v -> 0 <= p < 2 ^ 64 /\ (p = 0 <-> v = None).
Proof.
intros p [x|] HA; cbn [astr_argA] in HA; [|subst p; split; [lia | split; reflexivity]].
destruct HA as (Hp0 & _ & Hn & [((b & kk & Hbk & Hbp & Hpb) & _) | (HRO' & _)]).
- destruct (al_blocks _ _ LAWS _ _ _ _ _ b kk swe_AR0 Hbk) as (_ & H4096 & Hc & _ & _ & _ & Hk).
  pose proof (req_size_pos kk ltac:(lia)) as [_ Hr]. pose proof asan_consts as (C1 & _).
  split; [lia | split; [intros E; exfalso; exact (Hp0 E) | discriminate]].
- destruct (HRO' 0 ltac:(lia)) as (Hro & _). rewrite Z.add_0_r in Hro.
  pose proof (pa_img_range p (proj1 (cmd_ro_prog_apart p Hro))) as Hi.
  split; [lia | split; [intros E; exfalso; exact (Hp0 E) | discriminate]].
Qed.

(* the frame of an arg_s run: only nargs and args[j] change *)
Lemma swe_frame_NA : forall (Wc : world SEGS) E1 (m0 m1 : word -> option byte) v j cs,
bv_unsigned (ew E1 SW_C) = swe_c (R:=R) ->
frame_of E1 [YP09.mkRegion (Some SW_C) 4 8 4 8 [YP09.mkChunk 4 (CVal 4 (SLit v))];
             YP09.mkRegion (Some SW_C) (8 + 8 * j) (16 + 8 * j) (8 + 8 * j) (16 + 8 * j) cs]
  (mrestrict (w_H Wc) m0) (mrestrict (w_H Wc) m1) ->
forall a, 0 <= a < 2 ^ 64 -> ~ (swe_c (R:=R) + 4 <= a < swe_c (R:=R) + 8) ->
~ (swe_c (R:=R) + 8 + 8 * j <= a < swe_c (R:=R) + 16 + 8 * j) ->
rdW Wc m1 a = rdW Wc m0 a.
Proof.
intros Wc E1 m0 m1 v j cs U Hfr a Ha H1 H2.
apply (kept_of_frame E1 _ (w_H Wc) _ _ (fun a => (swe_c (R:=R) + 4 <= a < swe_c (R:=R) + 8) \/
  (swe_c (R:=R) + 8 + 8 * j <= a < swe_c (R:=R) + 16 + 8 * j)) Hfr); [| exact Ha | intros [H|H]; [exact (H1 H) | exact (H2 H)]].
intros b wlo whi a' Hin Hr. cbn in Hin.
destruct Hin as [Hq | [Hq | []]]; injection Hq as <- <- <-; cbn [base_val] in Hr; rewrite U in Hr; lia.
Qed.

(* the registers at the end of an arg_s segment: the frame's base registers and the two nargs registers *)
Lemma swe_end_regs : forall (regs1 : bvmap 5 word) ss H (ms0 : machine_state),
st_ok_pi SEGS VAL (Eimg (Ereg regs1 (swe_extra regs (Z.of_nat (swe_n (R:=R))) (swe_c (R:=R))))) ss (restrict H ms0) ->
swe_regs_base (B:=B) (regs:=regs) (R:=R) regs1 ->
forallb (fun r : bv 5 => sv_eqb (sr_get (ss_regs ss) r) (SOff (Z.to_nat (bv_unsigned r)) 0))
  (map (Z_to_bv 5) [2;3;4;23;24;25;26;27]) = true ->
sr_get (ss_regs ss) (Z_to_bv 5 8) = SOff SW_C 0 -> sr_get (ss_regs ss) (Z_to_bv 5 21) = SOff SW_SB 0 ->
sr_get (ss_regs ss) (Z_to_bv 5 18) = SOff SW_C 4 ->
sr_get (ss_regs ss) (Z_to_bv 5 22) = SAlu ALU_ADD (SAlu ALU_SRL (SOff SW_C 4) (SLit 3)) (SOff SW_SB 0) ->
swe_regs_base (B:=B) (regs:=regs) (R:=R) (ms_regs ms0) /\ swe_regs_chk (R:=R) (ms_regs ms0).
Proof.
intros regs1 ss H ms0 HS HRB Hfb G8 G21 G18 G22.
set (Ex := swe_extra regs (Z.of_nat (swe_n (R:=R))) (swe_c (R:=R))) in *.
pose proof (swe_env_mid regs1) as HE. fold Ex in HE. pose proof HE as (HEI & E2 & ESB & EN & EC).
destruct (swe_slot_bounds _ swe_c_ok) as [Hcb Hc8].
assert (HAE : env_agree 32 (Ereg regs1 Ex) (Eimg (Ereg regs1 Ex)))
  by (split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
pose proof (regs_kept_of_st_ok SEGS _ _ _ regs1 Ex _ HS HAE Hfb) as KR. cbn [ms_regs restrict] in KR.
assert (V : forall r, getr (ms_regs ms0) r = sv_denot (Eimg (Ereg regs1 Ex)) (sr_get (ss_regs ss) r))
  by (intros r; exact (st_ok_pi_restrict_reg H _ ss ms0 r HS)).
assert (V8 : getr (ms_regs ms0) (Z_to_bv 5 8) = w64 (swe_c (R:=R))).
{ rewrite V, G8. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned, EC. reflexivity. }
assert (V21 : getr (ms_regs ms0) (Z_to_bv 5 21) = w64 SB).
{ rewrite V, G21. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned, ESB. reflexivity. }
assert (V18 : getr (ms_regs ms0) (Z_to_bv 5 18) = w64 (swe_c (R:=R) + 4)).
{ rewrite V, G18. cbn [sv_denot]. rewrite EC, unsigned_lit_small by (unfold A_G_REC, A_REC_SPILL, OFF_CALLS in *; lia). reflexivity. }
assert (V22 : getr (ms_regs ms0) (Z_to_bv 5 22) = w64 (SB + (swe_c (R:=R) + 4) / 8)).
{ rewrite V, G22. rewrite (denot_shx _ SW_C SW_SB 4 (swe_c (R:=R)) SB EC ESB) by (unfold SB, A_G_REC, A_REC_SPILL, OFF_CALLS in *; lia).
  reflexivity. }
assert (T : forall r, In r [2;3;4;23;24;25;26;27] -> getr (ms_regs ms0) (Z_to_bv 5 r) = getr regs1 (Z_to_bv 5 r))
  by (intros r Hr; apply KR; apply in_map; exact Hr).
unfold swe_regs_base, swe_regs_chk in *. swe_z5.
destruct HRB as (R2 & R3 & R4 & R8 & R21 & R23).
split; [|split; [exact V18 | exact V22]].
split; [rewrite <- R2; apply T; cbn; tauto|].
split; [rewrite <- R3; apply T; cbn; tauto|].
split; [rewrite <- R4; apply T; cbn; tauto|].
split; [exact V8|]. split; [exact V21|].
intros r Hr. rewrite <- (R23 r Hr). apply T.
assert (r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) as Hc by lia.
destruct Hc as [->|[->|[->|[->| ->]]]]; cbn; tauto.
Qed.

(* the two slot fields after an arg_s segment, from the symbolic state's regions *)
Lemma swe_end_fields : forall E ss H (ms0 : machine_state) v j e p,
st_ok_pi SEGS VAL E ss (restrict H ms0) ->
ss_mem ss = [YP09.mkRegion (Some SW_C) 4 8 4 8 [YP09.mkChunk 4 (CVal 4 (SLit v))];
             YP09.mkRegion (Some SW_C) (8 + 8 * j) (16 + 8 * j) (8 + 8 * j) (16 + 8 * j) [YP09.mkChunk (8 + 8 * j) (CVal 8 e)]] ->
bv_unsigned (ew E SW_C) = swe_c (R:=R) -> 0 <= v < 2 ^ 32 ->
sv_denot E e = Z_to_bv 64 p -> 0 <= p < 2 ^ 64 ->
aval_mem (aview SEGS H (ms_mem ms0)) (swe_c (R:=R) + 4) 4 v /\
aval_mem (aview SEGS H (ms_mem ms0)) (swe_c (R:=R) + 8 + 8 * j) 8 p.
Proof.
intros E ss H ms0 v j e p HS Hm U Hv He Hp.
pose proof (st_ok_pi_region_nth _ ss _ 0 _ HS ltac:(rewrite Hm; reflexivity)) as RG0.
pose proof (st_ok_pi_region_nth _ ss _ 1 _ HS ltac:(rewrite Hm; reflexivity)) as RG1.
cbn [ms_mem restrict] in RG0, RG1.
split.
- apply (aval_mem_view SEGS).
  exact (field_of_region E _ SW_C (swe_c (R:=R)) _ 4 8 4 8 4 4%N (SLit v) v RG0 U (or_introl eq_refl) eq_refl
    ltac:(change (8 * Z.of_N 4) with 32; lia) ltac:(cbn; lia)).
- apply (aval_mem_view SEGS). replace (swe_c (R:=R) + 8 + 8 * j) with (swe_c (R:=R) + (8 + 8 * j)) by lia.
  exact (field_of_region E _ SW_C (swe_c (R:=R)) _ _ _ _ _ (8 + 8 * j) 8%N e p RG1 U (or_introl eq_refl) He
    ltac:(change (8 * Z.of_N 8) with 64; lia) ltac:(cbn; lia)).
Qed.

Lemma swe_R1_ok : XS6 2 SWE_X2 -> RS6 1 SWE_R1.
Proof.
intros HX2 lyc Sc Wc regs1 memc mdc k O0 D Fr NB p x HC HRB HRC HRR Hp10 HREPc Hp4096 Hstrp Hfresh.
unfold swe_at.
pose proof HC as (HJ & Hk & HFR & HP0 & HP1 & HFrO & HDO & HO0 & HNBD & HNBl & HNBb & HMLE & HO0D).
pose proof HRB as (R2 & R3 & R4 & R8 & R21 & R23). pose proof HRC as (R18 & R22).
pose proof (proj1 HJ) as HAR.
destruct swe_sp_mid as (Hsp & Hsp16 & Hceil).
destruct (swe_slot_bounds _ swe_c_ok) as [Hcb Hc8].
assert (Esp : spZ regs1 = spZ regs - 64) by (unfold spZ; rewrite R2; unfold w64; rewrite unsigned_lit_small by lia; reflexivity).
set (Ex := swe_extra regs (Z.of_nat (swe_n (R:=R))) (swe_c (R:=R))) in *.
pose proof (swe_env_mid regs1) as HE. fold Ex in HE. pose proof HE as (HEI & E2 & ESB & EN & EC).
pose proof (swe_rep_nargs lyc Sc (rdW Wc memc) _ _ HREPc) as HNA. cbn [length firstn Nat.sub] in HNA.
assert (HCK : YP09.chunk_ok SEGS (Eimg (Ereg regs1 Ex)) (mrestrict (w_H Wc) memc) (swe_c (R:=R)) (YP09.mkChunk 4 (CVal 4 (SLit 0))))
  by (apply (chunk_ok_val SEGS _ _ _ 4 4%N (SLit 0) 0); [reflexivity | lia | lia | exact (val_mem_view SEGS _ _ _ _ _ HNA)]).
assert (RN : YP09.region_ok SEGS (Eimg (Ereg regs1 Ex)) (mrestrict (w_H Wc) memc) (swe_regN 0)).
{ unfold swe_regN. apply (swe_slot_rok lyc Sc Wc memc mdc (Eimg (Ereg regs1 Ex)) (spZ regs1) (Z.of_nat (swe_n (R:=R)))).
  - exact HAR.
  - exact HE.
  - lia.
  - unfold CALL_SIZE. lia.
  - lia.
  - unfold CALL_SIZE. lia.
  - apply Forall_cons; [exact HCK | apply Forall_nil]. }
assert (RA : YP09.region_ok SEGS (Eimg (Ereg regs1 Ex)) (mrestrict (w_H Wc) memc) (swe_regA 0)).
{ unfold swe_regA. apply (swe_slot_rok lyc Sc Wc memc mdc (Eimg (Ereg regs1 Ex)) (spZ regs1) (Z.of_nat (swe_n (R:=R)))).
  - exact HAR.
  - exact HE.
  - lia.
  - unfold CALL_SIZE. lia.
  - lia.
  - unfold CALL_SIZE. lia.
  - apply Forall_nil. }
destruct (swe_seed_rs lyc Sc Wc memc mdc regs1 (Eimg (Ereg regs1 Ex)) (spZ regs1) (Z.of_nat (swe_n (R:=R))) SWE_R1 [swe_regN 0; swe_regA 0] HAR HE
  ltac:(rewrite Esp; exact Hsp) ltac:(rewrite Esp; exact Hsp16) ltac:(pose proof swe_n_le; lia)
  (regs_ok_Eimg_Ereg regs1 _) ltac:(vm_compute; reflexivity)
  ltac:(apply Forall_cons; [exact RN | apply Forall_cons; [exact RA | apply Forall_nil]])
  ltac:(apply pairwise_disjoint_of_extents; unfold swe_regN, swe_regA, extent_of_region;
        cbn [map YP09.r_base YP09.r_lo YP09.r_hi]; cbn [zpairwise_disjoint zall_disjoint]; unfold zdisj; cbn [fst snd];
        repeat split; lia)) as [HS SHOK].
assert (U34 : bv_unsigned (ew (Eimg (Ereg regs1 Ex)) SW_C) = swe_c (R:=R))
  by (rewrite EC; apply unsigned_lit_small; unfold A_G_REC, A_REC_SPILL, OFF_CALLS in *; lia).
assert (U32 : bv_unsigned (ew (Eimg (Ereg regs1 Ex)) SW_SB) = SB) by (rewrite ESB; apply unsigned_lit_small; unfold SB; lia).
swe_z5.
pose proof (st_ok_pi_set_reg _ _ _ (Z_to_bv 5 8) (SOff SW_C 0) HS ltac:(discriminate)
  ltac:(cbn [ms_regs restrict mkst sv_denot]; rewrite U34, Z.add_0_r; exact R8)) as HS1. clear HS.
pose proof (st_ok_pi_set_reg _ _ _ (Z_to_bv 5 21) (SOff SW_SB 0) HS1 ltac:(discriminate)
  ltac:(cbn [ms_regs restrict mkst sv_denot]; rewrite U32, Z.add_0_r; exact R21)) as HS2. clear HS1.
pose proof (st_ok_pi_set_reg _ _ _ (Z_to_bv 5 18) (SOff SW_C 4) HS2 ltac:(discriminate)
  ltac:(cbn [ms_regs restrict mkst sv_denot]; rewrite U34; exact R18)) as HS3. clear HS2.
pose proof (st_ok_pi_set_reg _ _ _ (Z_to_bv 5 22) (SAlu ALU_ADD (SAlu ALU_SRL (SOff SW_C 4) (SLit 3)) (SOff SW_SB 0)) HS3 ltac:(discriminate)
  ltac:(cbn [ms_regs restrict mkst]; rewrite (denot_shx _ SW_C SW_SB 4 (swe_c (R:=R)) SB EC ESB) by (unfold SB, A_G_REC, A_REC_SPILL, OFF_CALLS in *; lia);
        exact R22)) as HS. clear HS3.
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS.
paj_run_tok RUN HS HJ SHOK swe_Bspan.
{ cbn [ss_mem]. apply swe_awr_slots; [exact EC|].
  apply Forall_cons; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi swe_regN swe_regA]; unfold CALL_SIZE; split; [reflexivity | lia]|].
  apply Forall_cons; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi swe_regN swe_regA]; unfold CALL_SIZE; split; [reflexivity | lia]|]. apply Forall_nil. }
set (E0 := Eimg (Ereg regs1 Ex)) in *.
pose proof (swe_frame_NA Wc E0 _ _ 0 0 _ U34 HFr) as KM1. cbn [Z.mul Z.add] in KM1.
set (mem1 := ms_mem ms) in *.
clear HF HFr HG.
destruct (swe_ptr_range pcs cpus HAC) as (Hpcs0 & Hpcs1).
assert (HAE : env_agree 32 (Ereg regs1 Ex) E0) by (split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
pose proof (swe_c_ok) as Hcok.
assert (Hpin : In (p, Z.of_nat (length x) + 1) (ablocks B lyc Sc))
  by (apply (Permutation_in _ (Permutation_sym HP1)); apply in_or_app; right; apply in_or_app; right; left; reflexivity).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hpin) as (_ & _ & Hpceil & _).
pose proof asan_consts as (C1 & _).
assert (Hp64 : 0 <= p < 2 ^ 64) by (pose proof (req_size_pos (Z.of_nat (length x) + 1) ltac:(lia)) as [_ Hr]; lia).
assert (D10 : sv_denot E0 (SOff 10 0) = Z_to_bv 64 p).
{ unfold E0. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (ew_Eimg_Ereg_nat regs1 Ex 10 (Z_to_bv 5 10) eq_refl), Hp10.
  reflexivity. }
assert (H19 : getr regs1 (Z_to_bv 5 19) = w64 pcs) by (cbn [swe_R_regs] in HRR; swe_z5; exact (proj1 HRR)).
assert (H9 : getr regs1 (Z_to_bv 5 9) = w64 pnn) by (cbn [swe_R_regs] in HRR; swe_z5; exact (proj2 HRR)).
psrr_branch_tok RUN BR HS SHOK swe_Bspan.
- (* cpus is not NULL: s3 stays the argument *)
  assert (Hpc : pcs <> 0).
  { intros E. rewrite branch_ne_U in Hc. unfold U, E0 in Hc. cbn [sv_denot] in Hc.
    rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (ew_Eimg_Ereg_nat regs1 Ex 19 (Z_to_bv 5 19) eq_refl), H19, E in Hc.
    vm_compute in Hc. discriminate Hc. }
  paj_run_to_tok RUNTO HS HJ SHOK swe_Bspan SWE_X2.
  { cbn [ss_mem add_cond]. apply swe_awr_slots; [exact EC|].
    repeat (apply Forall_cons; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi]; unfold CALL_SIZE; split; [reflexivity | lia]|]). apply Forall_nil. }
  pmkst HS.
  pose proof (swe_frame_NA Wc E0 _ _ 1 0 _ U34 HFr) as KM2. cbn [Z.mul Z.add] in KM2.
  destruct (swe_end_fields E0 _ _ _ 1 0 (SOff 10 0) p HS eq_refl U34 ltac:(lia) D10 Hp64) as [FN FA].
  destruct (swe_end_regs regs1 _ _ _ HS HRB eq_refl eq_refl eq_refl eq_refl eq_refl) as [HRB2 HRC2].
  sreg HS (Z_to_bv 5 20) Q20. sreg HS (Z_to_bv 5 19) Q19. sreg HS (Z_to_bv 5 9) Q9.
  assert (X20 : getr (ms_regs ms0) (Z_to_bv 5 20) = w64 (swe_c (R:=R) + 8))
    by (rewrite Q20, (U34 : bv_unsigned (ew E0 34) = _); reflexivity).
  assert (X19 : getr (ms_regs ms0) (Z_to_bv 5 19) = w64 (swe_sel pcs)).
  { rewrite Q19. unfold E0. rewrite (ew_Eimg_Ereg_nat regs1 Ex 19 (Z_to_bv 5 19) eq_refl), H19. unfold swe_sel.
    replace (pcs =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hpc). reflexivity. }
  assert (X9 : getr (ms_regs ms0) (Z_to_bv 5 9) = w64 pnn)
    by (rewrite Q9; unfold E0; rewrite (ew_Eimg_Ereg_nat regs1 Ex 9 (Z_to_bv 5 9) eq_refl), H9; reflexivity).
  apply (swe_RX_apply 1 SWE_X2 lyc Sc Wc memc mdc k O0 D Fr NB p (ms_regs ms0) (ms_mem ms0) _ ltac:(lia) HX2 HC HREPc
    Hp4096 Hfresh Hstrp HJ).
  + intros a Ha H1 H2. rewrite (KM2 a Ha H1 ltac:(intros H; apply H2; cbn in H |- *; lia)).
    apply KM1; [exact Ha | exact H1 | intros H; apply H2; cbn in H |- *; lia].
  + exact FN.
  + rewrite Z.mul_0_r, Z.add_0_r in FA. change (Z.of_nat (1 - 1)) with 0. rewrite Z.mul_0_r, Z.add_0_r. exact FA.
  + exact HRB2.
  + exact HRC2.
  + cbn [swe_X_regs Nat.add]. swe_z5. split; [exact X20 | split; [exact X19 | exact X9]].
- (* cpus is NULL: s3 := "(null)" *)
  assert (Hpc : pcs = 0).
  { rewrite branch_ne_U in Hc. unfold U, E0 in Hc. cbn [sv_denot] in Hc.
    rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (ew_Eimg_Ereg_nat regs1 Ex 19 (Z_to_bv 5 19) eq_refl), H19 in Hc.
    apply negb_false_iff, Z.eqb_eq in Hc. unfold w64 in Hc. rewrite !unsigned_lit_small in Hc by lia. exact Hc. }
  paj_run_to_tok RUNTO HS HJ SHOK swe_Bspan SWE_X2.
  { cbn [ss_mem add_cond]. apply swe_awr_slots; [exact EC|].
    repeat (apply Forall_cons; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi]; unfold CALL_SIZE; split; [reflexivity | lia]|]). apply Forall_nil. }
  pmkst HS.
  pose proof (swe_frame_NA Wc E0 _ _ 1 0 _ U34 HFr) as KM2. cbn [Z.mul Z.add] in KM2.
  destruct (swe_end_fields E0 _ _ _ 1 0 (SOff 10 0) p HS eq_refl U34 ltac:(lia) D10 Hp64) as [FN FA].
  destruct (swe_end_regs regs1 _ _ _ HS HRB eq_refl eq_refl eq_refl eq_refl eq_refl) as [HRB2 HRC2].
  sreg HS (Z_to_bv 5 20) Q20. sreg HS (Z_to_bv 5 19) Q19. sreg HS (Z_to_bv 5 9) Q9.
  assert (X20 : getr (ms_regs ms0) (Z_to_bv 5 20) = w64 (swe_c (R:=R) + 8))
    by (rewrite Q20, (U34 : bv_unsigned (ew E0 34) = _); reflexivity).
  assert (X19 : getr (ms_regs ms0) (Z_to_bv 5 19) = w64 (swe_sel pcs)).
  { rewrite Q19. change 293%nat with SW_NULL.
    rewrite (img_env_atomP E0 SW_NULL HEI ltac:(unfold SW_NULL, A_OBJ, A_TEXT, A_LIM; lia)), (swe_null_val VOBJS), Hpc.
    reflexivity. }
  assert (X9 : getr (ms_regs ms0) (Z_to_bv 5 9) = w64 pnn)
    by (rewrite Q9; unfold E0; rewrite (ew_Eimg_Ereg_nat regs1 Ex 9 (Z_to_bv 5 9) eq_refl), H9; reflexivity).
  apply (swe_RX_apply 1 SWE_X2 lyc Sc Wc memc mdc k O0 D Fr NB p (ms_regs ms0) (ms_mem ms0) _ ltac:(lia) HX2 HC HREPc
    Hp4096 Hfresh Hstrp HJ).
  + intros a Ha H1 H2. rewrite (KM2 a Ha H1 ltac:(intros H; apply H2; cbn in H |- *; lia)).
    apply KM1; [exact Ha | exact H1 | intros H; apply H2; cbn in H |- *; lia].
  + exact FN.
  + rewrite Z.mul_0_r, Z.add_0_r in FA. change (Z.of_nat (1 - 1)) with 0. rewrite Z.mul_0_r, Z.add_0_r. exact FA.
  + exact HRB2.
  + exact HRC2.
  + cbn [swe_X_regs Nat.add]. swe_z5. split; [exact X20 | split; [exact X19 | exact X9]].
Qed.

Lemma swe_R2_ok : XS6 3 SWE_X3 -> RS6 2 SWE_R2.
Proof.
intros HX3 lyc Sc Wc regs1 memc mdc k O0 D Fr NB p x HC HRB HRC HRR Hp10 HREPc Hp4096 Hstrp Hfresh.
unfold swe_at.
pose proof HC as (HJ & Hk & HFR & HP0 & HP1 & HFrO & HDO & HO0 & HNBD & HNBl & HNBb & HMLE & HO0D).
pose proof HRB as (R2 & R3 & R4 & R8 & R21 & R23). pose proof HRC as (R18 & R22).
pose proof (proj1 HJ) as HAR.
destruct swe_sp_mid as (Hsp & Hsp16 & Hceil).
destruct (swe_slot_bounds _ swe_c_ok) as [Hcb Hc8].
assert (Esp : spZ regs1 = spZ regs - 64) by (unfold spZ; rewrite R2; unfold w64; rewrite unsigned_lit_small by lia; reflexivity).
set (Ex := swe_extra regs (Z.of_nat (swe_n (R:=R))) (swe_c (R:=R))) in *.
pose proof (swe_env_mid regs1) as HE. fold Ex in HE. pose proof HE as (HEI & E2 & ESB & EN & EC).
pose proof (swe_rep_nargs lyc Sc (rdW Wc memc) _ _ HREPc) as HNA. cbn [length firstn Nat.sub] in HNA.
assert (HCK : YP09.chunk_ok SEGS (Eimg (Ereg regs1 Ex)) (mrestrict (w_H Wc) memc) (swe_c (R:=R)) (YP09.mkChunk 4 (CVal 4 (SLit 1))))
  by (apply (chunk_ok_val SEGS _ _ _ 4 4%N (SLit 1) 1); [reflexivity | lia | lia | exact (val_mem_view SEGS _ _ _ _ _ HNA)]).
assert (RN : YP09.region_ok SEGS (Eimg (Ereg regs1 Ex)) (mrestrict (w_H Wc) memc) (swe_regN 1)).
{ unfold swe_regN. apply (swe_slot_rok lyc Sc Wc memc mdc (Eimg (Ereg regs1 Ex)) (spZ regs1) (Z.of_nat (swe_n (R:=R)))).
  - exact HAR.
  - exact HE.
  - lia.
  - unfold CALL_SIZE. lia.
  - lia.
  - unfold CALL_SIZE. lia.
  - apply Forall_cons; [exact HCK | apply Forall_nil]. }
assert (RA : YP09.region_ok SEGS (Eimg (Ereg regs1 Ex)) (mrestrict (w_H Wc) memc) (swe_regA 1)).
{ unfold swe_regA. apply (swe_slot_rok lyc Sc Wc memc mdc (Eimg (Ereg regs1 Ex)) (spZ regs1) (Z.of_nat (swe_n (R:=R)))).
  - exact HAR.
  - exact HE.
  - lia.
  - unfold CALL_SIZE. lia.
  - lia.
  - unfold CALL_SIZE. lia.
  - apply Forall_nil. }
destruct (swe_seed_rs lyc Sc Wc memc mdc regs1 (Eimg (Ereg regs1 Ex)) (spZ regs1) (Z.of_nat (swe_n (R:=R))) SWE_R2 [swe_regN 1; swe_regA 1] HAR HE
  ltac:(rewrite Esp; exact Hsp) ltac:(rewrite Esp; exact Hsp16) ltac:(pose proof swe_n_le; lia)
  (regs_ok_Eimg_Ereg regs1 _) ltac:(vm_compute; reflexivity)
  ltac:(apply Forall_cons; [exact RN | apply Forall_cons; [exact RA | apply Forall_nil]])
  ltac:(apply pairwise_disjoint_of_extents; unfold swe_regN, swe_regA, extent_of_region;
        cbn [map YP09.r_base YP09.r_lo YP09.r_hi]; cbn [zpairwise_disjoint zall_disjoint]; unfold zdisj; cbn [fst snd];
        repeat split; lia)) as [HS SHOK].
assert (U34 : bv_unsigned (ew (Eimg (Ereg regs1 Ex)) SW_C) = swe_c (R:=R))
  by (rewrite EC; apply unsigned_lit_small; unfold A_G_REC, A_REC_SPILL, OFF_CALLS in *; lia).
assert (U32 : bv_unsigned (ew (Eimg (Ereg regs1 Ex)) SW_SB) = SB) by (rewrite ESB; apply unsigned_lit_small; unfold SB; lia).
swe_z5.
pose proof (st_ok_pi_set_reg _ _ _ (Z_to_bv 5 8) (SOff SW_C 0) HS ltac:(discriminate)
  ltac:(cbn [ms_regs restrict mkst sv_denot]; rewrite U34, Z.add_0_r; exact R8)) as HS1. clear HS.
pose proof (st_ok_pi_set_reg _ _ _ (Z_to_bv 5 21) (SOff SW_SB 0) HS1 ltac:(discriminate)
  ltac:(cbn [ms_regs restrict mkst sv_denot]; rewrite U32, Z.add_0_r; exact R21)) as HS2. clear HS1.
pose proof (st_ok_pi_set_reg _ _ _ (Z_to_bv 5 18) (SOff SW_C 4) HS2 ltac:(discriminate)
  ltac:(cbn [ms_regs restrict mkst sv_denot]; rewrite U34; exact R18)) as HS3a. clear HS2.
assert (R20 : getr regs1 (Z_to_bv 5 20) = w64 (swe_c (R:=R) + 8)) by (cbn [swe_R_regs] in HRR; swe_z5; exact (proj1 HRR)).
pose proof (st_ok_pi_set_reg _ _ _ (Z_to_bv 5 20) (SOff SW_C 8) HS3a ltac:(discriminate)
  ltac:(cbn [ms_regs restrict mkst sv_denot]; rewrite U34; exact R20)) as HS3. clear HS3a.
pose proof (st_ok_pi_set_reg _ _ _ (Z_to_bv 5 22) (SAlu ALU_ADD (SAlu ALU_SRL (SOff SW_C 4) (SLit 3)) (SOff SW_SB 0)) HS3 ltac:(discriminate)
  ltac:(cbn [ms_regs restrict mkst]; rewrite (denot_shx _ SW_C SW_SB 4 (swe_c (R:=R)) SB EC ESB) by (unfold SB, A_G_REC, A_REC_SPILL, OFF_CALLS in *; lia);
        exact R22)) as HS. clear HS3.
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS.
paj_run_tok RUN HS HJ SHOK swe_Bspan.
{ cbn [ss_mem]. apply swe_awr_slots; [exact EC|].
  apply Forall_cons; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi swe_regN swe_regA]; unfold CALL_SIZE; split; [reflexivity | lia]|].
  apply Forall_cons; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi swe_regN swe_regA]; unfold CALL_SIZE; split; [reflexivity | lia]|]. apply Forall_nil. }
set (E0 := Eimg (Ereg regs1 Ex)) in *.
pose proof (swe_frame_NA Wc E0 _ _ 1 1 _ U34 HFr) as KM1. cbn [Z.mul Z.add] in KM1.
set (mem1 := ms_mem ms) in *.
clear HF HFr HG.
destruct (swe_ptr_range pnn nice HAN) as (Hpcs0 & Hpcs1).
assert (HAE : env_agree 32 (Ereg regs1 Ex) E0) by (split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
pose proof (swe_c_ok) as Hcok.
assert (Hpin : In (p, Z.of_nat (length x) + 1) (ablocks B lyc Sc))
  by (apply (Permutation_in _ (Permutation_sym HP1)); apply in_or_app; right; apply in_or_app; right; left; reflexivity).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hpin) as (_ & _ & Hpceil & _).
pose proof asan_consts as (C1 & _).
assert (Hp64 : 0 <= p < 2 ^ 64) by (pose proof (req_size_pos (Z.of_nat (length x) + 1) ltac:(lia)) as [_ Hr]; lia).
assert (D10 : sv_denot E0 (SOff 10 0) = Z_to_bv 64 p).
{ unfold E0. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (ew_Eimg_Ereg_nat regs1 Ex 10 (Z_to_bv 5 10) eq_refl), Hp10.
  reflexivity. }
assert (H9 : getr regs1 (Z_to_bv 5 9) = w64 pnn) by (cbn [swe_R_regs] in HRR; swe_z5; exact (proj2 HRR)).
psrr_branch_tok RUN BR HS SHOK swe_Bspan.
- (* cpus is not NULL: s3 stays the argument *)
  assert (Hpc : pnn <> 0).
  { intros E. rewrite branch_ne_U in Hc. unfold U, E0 in Hc. cbn [sv_denot] in Hc.
    rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (ew_Eimg_Ereg_nat regs1 Ex 9 (Z_to_bv 5 9) eq_refl), H9, E in Hc.
    vm_compute in Hc. discriminate Hc. }
  paj_run_to_tok RUNTO HS HJ SHOK swe_Bspan SWE_X3.
  { cbn [ss_mem add_cond]. apply swe_awr_slots; [exact EC|].
    repeat (apply Forall_cons; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi]; unfold CALL_SIZE; split; [reflexivity | lia]|]). apply Forall_nil. }
  pmkst HS.
  pose proof (swe_frame_NA Wc E0 _ _ 2 1 _ U34 HFr) as KM2. cbn [Z.mul Z.add] in KM2.
  destruct (swe_end_fields E0 _ _ _ 2 1 (SOff 10 0) p HS eq_refl U34 ltac:(lia) D10 Hp64) as [FN FA].
  destruct (swe_end_regs regs1 _ _ _ HS HRB eq_refl eq_refl eq_refl eq_refl eq_refl) as [HRB2 HRC2].
  sreg HS (Z_to_bv 5 20) Q20. sreg HS (Z_to_bv 5 9) Q9.
  assert (X20 : getr (ms_regs ms0) (Z_to_bv 5 20) = w64 (swe_c (R:=R) + 8))
    by (rewrite Q20, (U34 : bv_unsigned (ew E0 34) = _); reflexivity).
  assert (X9 : getr (ms_regs ms0) (Z_to_bv 5 9) = w64 (swe_sel pnn)).
  { rewrite Q9. unfold E0. rewrite (ew_Eimg_Ereg_nat regs1 Ex 9 (Z_to_bv 5 9) eq_refl), H9. unfold swe_sel.
    replace (pnn =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hpc). reflexivity. }
  apply (swe_RX_apply 2 SWE_X3 lyc Sc Wc memc mdc k O0 D Fr NB p (ms_regs ms0) (ms_mem ms0) _ ltac:(lia) HX3 HC HREPc
    Hp4096 Hfresh Hstrp HJ).
  + intros a Ha H1 H2. rewrite (KM2 a Ha H1 ltac:(intros H; apply H2; cbn in H |- *; lia)).
    apply KM1; [exact Ha | exact H1 | intros H; apply H2; cbn in H |- *; lia].
  + exact FN.
  + change (Z.of_nat (2 - 1)) with 1. exact FA.
  + exact HRB2.
  + exact HRC2.
  + cbn [swe_X_regs Nat.add]. swe_z5. split; [exact X20 | exact X9].
- (* cpus is NULL: s3 := "(null)" *)
  assert (Hpc : pnn = 0).
  { rewrite branch_ne_U in Hc. unfold U, E0 in Hc. cbn [sv_denot] in Hc.
    rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (ew_Eimg_Ereg_nat regs1 Ex 9 (Z_to_bv 5 9) eq_refl), H9 in Hc.
    apply negb_false_iff, Z.eqb_eq in Hc. unfold w64 in Hc. rewrite !unsigned_lit_small in Hc by lia. exact Hc. }
  paj_run_to_tok RUNTO HS HJ SHOK swe_Bspan SWE_X3.
  { cbn [ss_mem add_cond]. apply swe_awr_slots; [exact EC|].
    repeat (apply Forall_cons; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi]; unfold CALL_SIZE; split; [reflexivity | lia]|]). apply Forall_nil. }
  pmkst HS.
  pose proof (swe_frame_NA Wc E0 _ _ 2 1 _ U34 HFr) as KM2. cbn [Z.mul Z.add] in KM2.
  destruct (swe_end_fields E0 _ _ _ 2 1 (SOff 10 0) p HS eq_refl U34 ltac:(lia) D10 Hp64) as [FN FA].
  destruct (swe_end_regs regs1 _ _ _ HS HRB eq_refl eq_refl eq_refl eq_refl eq_refl) as [HRB2 HRC2].
  sreg HS (Z_to_bv 5 20) Q20. sreg HS (Z_to_bv 5 9) Q9.
  assert (X20 : getr (ms_regs ms0) (Z_to_bv 5 20) = w64 (swe_c (R:=R) + 8))
    by (rewrite Q20, (U34 : bv_unsigned (ew E0 34) = _); reflexivity).
  assert (X9 : getr (ms_regs ms0) (Z_to_bv 5 9) = w64 (swe_sel pnn)).
  { rewrite Q9. change 293%nat with SW_NULL.
    rewrite (img_env_atomP E0 SW_NULL HEI ltac:(unfold SW_NULL, A_OBJ, A_TEXT, A_LIM; lia)), (swe_null_val VOBJS), Hpc.
    reflexivity. }
  apply (swe_RX_apply 2 SWE_X3 lyc Sc Wc memc mdc k O0 D Fr NB p (ms_regs ms0) (ms_mem ms0) _ ltac:(lia) HX3 HC HREPc
    Hp4096 Hfresh Hstrp HJ).
  + intros a Ha H1 H2. rewrite (KM2 a Ha H1 ltac:(intros H; apply H2; cbn in H |- *; lia)).
    apply KM1; [exact Ha | exact H1 | intros H; apply H2; cbn in H |- *; lia].
  + exact FN.
  + change (Z.of_nat (2 - 1)) with 1. exact FA.
  + exact HRB2.
  + exact HRC2.
  + cbn [swe_X_regs Nat.add]. swe_z5. split; [exact X20 | exact X9].
Qed.

#[local] Notation JSj := (swe_J_stmt (B:=B) (MT:=MT) (ly:=ly) (S:=S) (W:=W) (regs:=regs) (mem:=mem) (md:=md)
  (pf:=pf) (pcs:=pcs) (pnn:=pnn) (format:=format) (cpus:=cpus) (nice:=nice) (R:=R) (O:=O)).
#[local] Notation POSTj := (swe_POST (B:=B) (MT:=MT) (ly:=ly) (S:=S) (W:=W) (regs:=regs) (mem:=mem) (md:=md)
  (format:=format) (cpus:=cpus) (nice:=nice) (R:=R) (O:=O)).

(* an argument pointer is a 64-bit value: NULL, a heap address or an image address *)
Lemma swe_j_arg_rng : forall (p : Z) (v : option (list byte)),
astr_argA B ly S (rdW W mem) (in_roP SEGS RLO RHI) O p v -> 0 <= p < 2 ^ 64.
Proof.
intros p [x|] HA; cbn [astr_argA] in HA; [|subst p; lia].
destruct HA as (Hp0 & _ & Hn & [((q & kk & Hq & Hqp & Hpq) & _) | (HRO' & _)]).
- destruct (al_blocks _ _ LAWS _ _ _ _ _ q kk swe_AR0 Hq) as (_ & Hq4096 & Hqc & _).
  pose proof (req_size_pos kk ltac:(lia)) as [_ Hr]. pose proof asan_consts as (C1 & _). lia.
- destruct (HRO' 0 ltac:(lia)) as (Hro & _). rewrite Z.add_0_r in Hro.
  pose proof (pa_img_range p (proj1 (cmd_ro_prog_apart p Hro))) as Hr. lia.
Qed.

(* at 0x8c120, both arms: fn and nargs stored, s2/s6 set, s4 = the first argument string; hand over to X1 *)
Lemma swe_j_fin : XS 1 SWE_X1 -> forall lyc Sc Wc regs1 memc mdc k O0 D Fr regsT memT mdT,
CORE 0 lyc Sc Wc memc mdc k O0 D Fr [] ->
swe_regs_base (B:=B) (regs:=regs) (R:=R) regs1 ->
getr regs1 19 = w64 pcs -> getr regs1 9 = w64 pnn ->
(forall rd', (forall a, in_recg a -> ~ (swe_c (R:=R) <= a < swe_c (R:=R) + 8) -> rd' a = rdW Wc memc a) ->
   (forall p k i, In (p, k) O0 -> 0 <= i < k -> rd' (p + i) = rdW Wc memc (p + i)) ->
   aval_mem rd' (swe_c (R:=R)) 4 REC_WORKER_ENV -> aval_mem rd' (swe_c (R:=R) + 4) 4 0 ->
   rec_repA B lyc Sc rd' (rec_record R REC_WORKER_ENV []) O0) ->
ajournal SEGS B SUP_WORKER_ENV_STK (spZ regs) FPw ly S W mem md [] lyc Sc Wc memT mdT k ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (swe_c (R:=R) <= a < swe_c (R:=R) + 8) -> rdW Wc memT a = rdW Wc memc a) ->
aval_mem (rdW Wc memT) (swe_c (R:=R)) 4 16 -> aval_mem (rdW Wc memT) (swe_c (R:=R) + 4) 4 0 ->
(forall r, In r [2;3;4;9;19;23;24;25;26;27] -> getr regsT (Z_to_bv 5 r) = getr regs1 (Z_to_bv 5 r)) ->
getr regsT (Z_to_bv 5 8) = w64 (swe_c (R:=R)) -> getr regsT (Z_to_bv 5 21) = w64 SB ->
getr regsT (Z_to_bv 5 18) = w64 (swe_c (R:=R) + 4) -> getr regsT (Z_to_bv 5 22) = w64 (SB + (swe_c (R:=R) + 4) / 8) ->
getr regsT (Z_to_bv 5 20) = w64 (swe_sel pf) ->
SRr SEGS Wc (mkCfg (mkst regsT (Z_to_bv 64 (BASE + SWE_X1)) memT (seg_rom SEGS)) mdT) POSTj.
Proof.
intros HX1 lyc Sc Wc regs1 memc mdc k O0 D Fr regsT memT mdT HC HRB H19 H9 HCOMP HJT KM F0 F4 KR T8 T21 T18 T22 T20.
destruct swe_sp_bounds as (Hsp & Hsp47 & _).
destruct (swe_slot_bounds _ swe_c_ok) as [Hcb _].
pose proof asan_consts as (C1 & _).
pose proof HC as (HJ & _ & _ & _ & HP1 & _ & _ & _ & _ & _ & _ & _ & HO0D).
pose proof (proj1 HJ) as HAR.
pose proof HRB as (R2 & R3 & R4 & R8 & R21 & R23).
assert (HCT : CORE 0 lyc Sc Wc memT mdT k O0 D Fr []).
{ apply (swe_core_mem2 0 lyc Sc Wc memc mdc k O0 D Fr [] memT mdT HC HJT).
  intros a Ha. apply KM; [lia|]. unfold A_G_REC, A_REC_SPILL, OFF_CALLS in *. lia. }
apply (HX1 lyc Sc Wc regsT memT mdT k O0 D Fr [] HCT).
- unfold swe_regs_base. swe_z5.
  split; [rewrite (KR 2 ltac:(cbn; tauto)); exact R2|].
  split; [rewrite (KR 3 ltac:(cbn; tauto)); exact R3|].
  split; [rewrite (KR 4 ltac:(cbn; tauto)); exact R4|].
  split; [exact T8|]. split; [exact T21|].
  intros r Hr. rewrite <- (R23 r Hr). apply KR.
  assert (r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) as Hc by lia.
  destruct Hc as [->|[->|[->|[->| ->]]]]; cbn; tauto.
- unfold swe_regs_chk. swe_z5. split; [exact T18 | exact T22].
- cbn [swe_X_regs]. swe_z5. split; [exact T20|]. split.
  + rewrite (KR 19 ltac:(cbn; tauto)). exact H19.
  + rewrite (KR 9 ltac:(cbn; tauto)). exact H9.
- cbn [firstn]. rewrite app_nil_r. apply HCOMP.
  + intros a Ha Hn. apply KM; [destruct Ha; unfold A_G_REC, REC_SIZE, A_REC_SPILL, SC_SIZE in *; lia | exact Hn].
  + intros q n i Hq Hi.
    assert (Hq2 : In (q, n) (ablocks B lyc Sc))
      by (apply (Permutation_in _ (Permutation_sym HP1)); rewrite app_nil_r; exact (HO0D _ Hq)).
    pose proof (blk_off_imgP B lyc Sc Wc memc mdc q n HAR Hq2) as Hoff.
    destruct (al_blocks _ _ LAWS _ _ _ _ _ q n HAR Hq2) as (_ & Hq4096 & Hqc & _).
    pose proof (req_size_pos n ltac:(lia)) as [_ Hr]. unfold off_img in Hoff.
    apply KM; [lia|]. destruct swe_c_ok as [(H1 & H2 & _) | E1]; try rewrite E1 in *;
      unfold A_G_REC, REC_SIZE, A_REC_SPILL, CALL_SIZE, OFF_CALLS in *; nia.
  + exact F0.
  + exact F4.
Qed.

(* the write ranges of a run from the J state: the slot's fn and nargs fields *)
Ltac swe_j_awr EC :=
  lazymatch goal with |- awr_ok _ _ _ ?rs _ _ _ _ _ _ _ _ => let v := eval vm_compute in rs in change rs with v end;
  apply swe_awr_slots; [exact EC|];
  apply Forall_cons; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi]; unfold CALL_SIZE; split; [reflexivity | lia] | apply Forall_nil].

Lemma swe_J_ok : XS 1 SWE_X1 -> JSj.
Proof.
intros HX1 lyc Sc Wc regs1 memc mdc k O0 D Fr HC HRB H20 H19 H9 HCOMP.
unfold swe_at.
pose proof (proj1 HC) as HJ.
pose proof HRB as (R2 & R3 & R4 & R8 & R21 & R23).
pose proof (proj1 HJ) as HAR.
destruct swe_sp_mid as (Hsp & Hsp16 & _).
destruct (swe_slot_bounds _ swe_c_ok) as [Hcb _].
assert (Esp : spZ regs1 = spZ regs - 64) by (unfold spZ; rewrite R2; unfold w64; rewrite unsigned_lit_small by lia; reflexivity).
set (Ex := swe_extra regs (Z.of_nat (swe_n (R:=R))) (swe_c (R:=R))) in *.
pose proof (swe_env_mid regs1) as HE. fold Ex in HE. pose proof HE as (HEI & E2 & ESB & EN & EC).
assert (RJ : YP09.region_ok SEGS (Eimg (Ereg regs1 Ex)) (mrestrict (w_H Wc) memc) swe_regJ).
{ unfold swe_regJ. apply (swe_slot_rok lyc Sc Wc memc mdc (Eimg (Ereg regs1 Ex)) (spZ regs1) (Z.of_nat (swe_n (R:=R)))).
  - exact HAR.
  - exact HE.
  - lia.
  - unfold CALL_SIZE. lia.
  - lia.
  - unfold CALL_SIZE. lia.
  - apply Forall_nil. }
destruct (swe_seed_rs lyc Sc Wc memc mdc regs1 (Eimg (Ereg regs1 Ex)) (spZ regs1) (Z.of_nat (swe_n (R:=R))) SWE_J [swe_regJ] HAR HE
  ltac:(rewrite Esp; exact Hsp) ltac:(rewrite Esp; exact Hsp16) ltac:(pose proof swe_n_le; lia)
  (regs_ok_Eimg_Ereg regs1 _) ltac:(vm_compute; reflexivity)
  ltac:(apply Forall_cons; [exact RJ | apply Forall_nil])
  ltac:(apply pairwise_disjoint_of_extents; unfold swe_regJ, extent_of_region;
        cbn [map YP09.r_base YP09.r_lo YP09.r_hi]; cbn [zpairwise_disjoint zall_disjoint]; unfold zdisj; cbn [fst snd];
        repeat split; lia)) as [HS SHOK].
assert (U34 : bv_unsigned (ew (Eimg (Ereg regs1 Ex)) SW_C) = swe_c (R:=R))
  by (rewrite EC; apply unsigned_lit_small; unfold A_G_REC, A_REC_SPILL, OFF_CALLS in *; lia).
assert (U32 : bv_unsigned (ew (Eimg (Ereg regs1 Ex)) SW_SB) = SB) by (rewrite ESB; apply unsigned_lit_small; unfold SB; lia).
assert (U34' : bv_unsigned (ew (Eimg (Ereg regs1 Ex)) 34%nat) = swe_c (R:=R)) by exact U34.
assert (EC' : ew (Eimg (Ereg regs1 Ex)) 34%nat = Z_to_bv 64 (swe_c (R:=R))) by exact EC.
assert (ESB' : ew (Eimg (Ereg regs1 Ex)) 32%nat = Z_to_bv 64 SB) by exact ESB.
assert (HAE : env_agree 32 (Ereg regs1 Ex) (Eimg (Ereg regs1 Ex)))
  by (split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
swe_z5.
assert (EW20 : ew (Eimg (Ereg regs1 Ex)) 20%nat = Z_to_bv 64 pf)
  by (rewrite (ew_Eimg_Ereg_nat regs1 Ex 20 (Z_to_bv 5 20) eq_refl); exact H20).
pose proof (swe_j_arg_rng pf format HAF) as Hpfr.
pose proof (st_ok_pi_set_reg _ _ _ (Z_to_bv 5 8) (SOff SW_C 0) HS ltac:(discriminate)
  ltac:(cbn [ms_regs restrict mkst sv_denot]; rewrite U34, Z.add_0_r; exact R8)) as HS1. clear HS.
pose proof (st_ok_pi_set_reg _ _ _ (Z_to_bv 5 21) (SOff SW_SB 0) HS1 ltac:(discriminate)
  ltac:(cbn [ms_regs restrict mkst sv_denot]; rewrite U32, Z.add_0_r; exact R21)) as HS. clear HS1.
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS.
(* 0x8c0e4 .. 0x8c114: the shadow checks of c and c + 4, fn := 16, nargs := 0, s2 := c + 4, s6 := its shadow byte *)
paj_run_tok RUN HS HJ SHOK swe_Bspan.
{ swe_j_awr EC. }
assert (KM1 : forall a, 0 <= a < 2 ^ 64 -> ~ (swe_c (R:=R) <= a < swe_c (R:=R) + 8) -> rdW Wc (ms_mem ms) a = rdW Wc memc a).
{ intros a Ha Hn. apply (kept_of_frame _ _ (w_H Wc) memc (ms_mem ms) (fun a => swe_c (R:=R) <= a < swe_c (R:=R) + 8) HFr);
    [|exact Ha|exact Hn].
  intros b wlo whi a' Hin Hr. vm_compute in Hin. destruct Hin as [Hq|[]]. injection Hq as <- <- <-.
  cbn [base_val] in Hr. rewrite U34' in Hr. lia. }
clear HF HFr HG.
lazymatch goal with |- SRr _ _ (mkCfg _ ?d) _ => set (mdv := d) in *; clearbody mdv end.
(* 0x8c114: bnez s4. Taken (format is a string): s4 keeps pf, atom 20. Not taken (format is NULL): s4 := .str.47,
   atom 293, the image object "(null)". H20v: s4's atom holds swe_sel pf. *)
pose proof (U_lit (Eimg (Ereg regs1 Ex)) 0 ltac:(lia)) as UL0.
psrr_branch_tok RUN BR HS SHOK swe_Bspan; rewrite branch_ne_U, UL0, (U_atom _ 20 pf EW20 Hpfr) in Hc.
1: assert (H20v : ew (Eimg (Ereg regs1 Ex)) 20%nat = w64 (swe_sel pf))
     by (rewrite EW20; unfold swe_sel; destruct (pf =? 0) eqn:Hz0;
         [rewrite ?Hz0 in Hc; vm_compute in Hc; discriminate Hc | reflexivity]).
2: assert (H20v : ew (Eimg (Ereg regs1 Ex)) 293%nat = w64 (swe_sel pf))
     by (unfold swe_sel; destruct (pf =? 0) eqn:Hz0; [|rewrite ?Hz0 in Hc; vm_compute in Hc; discriminate Hc];
         assert (V293 : bv_unsigned (ew (Eimg (Ereg regs1 Ex)) 293%nat) = 0x22480)
           by (rewrite (HEI 293%nat ltac:(cbv; lia)); exact (swe_null_val VOBJS));
         rewrite <- V293; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity).
all: clear Hc; paj_run_to_tok RUNTO HS HJ SHOK swe_Bspan SWE_X1.
1, 3: swe_j_awr EC.
(* at 0x8c120 in either arm: the registers, fn and nargs from the slot's region, the memory kept outside [c, c + 8),
   then X1 *)
all: pmkst HS;
  pose proof (regs_kept_of_st_ok_pi _ _ _ regs1 Ex (map (Z_to_bv 5) [2;3;4;9;19;23;24;25;26;27]) HS HAE
    ltac:(vm_compute; reflexivity)) as KR; cbn [ms_regs restrict] in KR;
  sreg HS (Z_to_bv 5 8) Q8; sreg HS (Z_to_bv 5 21) Q21; sreg HS (Z_to_bv 5 18) Q18; sreg HS (Z_to_bv 5 20) Q20;
  pose proof (st_ok_pi_restrict_reg _ _ _ _ (Z_to_bv 5 22) HS) as Q22;
  lazymatch type of Q22 with _ = sv_denot _ (sr_get ?l ?rr) =>
    let e := eval vm_compute in (sr_get l rr) in change (sr_get l rr) with e in Q22 end;
  cbn [ms_regs restrict] in Q22;
  rewrite (denot_shx _ 34%nat 32%nat 4 (swe_c (R:=R)) SB EC ESB) in Q22 by (unfold SB, A_G_REC, A_REC_SPILL, OFF_CALLS in *; lia);
  rewrite EC' in Q8; rewrite ESB' in Q21; rewrite U34' in Q18;
  pose proof (st_ok_pi_region_nth _ _ _ 0 _ HS eq_refl) as HRf; cbn [ms_mem restrict] in HRf;
  pose proof (field_of_region _ _ _ _ _ _ _ _ _ 0 4%N (SLit 16) 16 HRf U34' ltac:(cbn; tauto) ltac:(reflexivity)
    ltac:(split; [lia | vm_compute; reflexivity]) ltac:(cbn; lia)) as F0;
  pose proof (field_of_region _ _ _ _ _ _ _ _ _ 4 4%N (SLit 0) 0 HRf U34' ltac:(cbn; tauto) ltac:(reflexivity)
    ltac:(split; [lia | vm_compute; reflexivity]) ltac:(cbn; lia)) as F4;
  apply (aval_mem_view SEGS) in F0, F4; rewrite Z.add_0_r in F0;
  lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msT) =>
  assert (KM : forall a, 0 <= a < 2 ^ 64 -> ~ (swe_c (R:=R) <= a < swe_c (R:=R) + 8) ->
    rdW Wc (ms_mem msT) a = rdW Wc memc a)
  by (intros a Ha Hn; rewrite <- (KM1 a Ha Hn);
      apply (kept_of_frame _ _ _ _ _ (fun a => swe_c (R:=R) <= a < swe_c (R:=R) + 8) HFr); [|exact Ha|exact Hn];
      intros b wlo whi a' Hin Hr; vm_compute in Hin; destruct Hin as [Hq|[]]; injection Hq as <- <- <-;
      cbn [base_val] in Hr; rewrite U34' in Hr; lia) end;
  apply (swe_j_fin HX1 lyc Sc Wc regs1 memc mdc k O0 D Fr _ _ _ HC HRB H19 H9 HCOMP HJ KM F0 F4);
  [ intros r Hr; apply KR; apply in_map; cbn in Hr |- *; tauto
  | exact Q8 | exact Q21 | exact Q18 | exact Q22 | rewrite Q20; exact H20v ].
Qed.

#[local] Notation JSe := (swe_J_stmt (B:=B) (MT:=MT) (ly:=ly) (S:=S) (W:=W) (regs:=regs) (mem:=mem) (md:=md)
  (pf:=pf) (pcs:=pcs) (pnn:=pnn) (format:=format) (cpus:=cpus) (nice:=nice) (R:=R) (O:=O)).
#[local] Notation POSTe := (swe_POST (B:=B) (MT:=MT) (ly:=ly) (S:=S) (W:=W) (regs:=regs) (mem:=mem) (md:=md)
  (format:=format) (cpus:=cpus) (nice:=nice) (R:=R) (O:=O)).

(* the write windows of every run of the entry segment: the frame, two read-only cells, g_rec.ncalls *)
Ltac swe_e_awr Usp EGu :=
lazymatch goal with |- awr_ok ?sg ?bb ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr ?lyx ?own =>
  let rs' := eval vm_compute in rs in change (awr_ok sg bb Ex rs' stk spx fp b0 bc fr lyx own) end;
eapply awr_ok_cons_stack; [reflexivity | exact Usp | cbn; lia | cbn; lia |];
apply awr_ok_cons_ro; [cbn; lia|];
apply awr_ok_cons_ro; [cbn; lia|];
eapply (YCbq.awr_ok_cons_gen SEGS B) with (k := SW_GREC) (b := A_G_REC);
[ reflexivity
| exact EGu
| intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha;
  right; right; right; right; left; (split; [|split]);
  [ unfold swe_FP; exists (A_G_REC, A_G_REC + REC_SIZE); split; [left; reflexivity|];
    cbn [fst snd]; unfold OFF_NCALLS, REC_SIZE in *; lia
  | rewrite (recb_ts_prog_m B HB); apply recb_grec_in; unfold OFF_NCALLS, REC_SIZE in *; lia
  | apply cmd_prog_img; apply recb_grec_in; unfold OFF_NCALLS, REC_SIZE in *; lia ]
| apply (YCbq.awr_ok_nil SEGS B) ].

(* the windows of those runs lie in the frame or in g_rec.ncalls *)
Ltac swe_e_win Usp EGu :=
intros b wlo whi a Hin Hrr; vm_compute in Hin;
repeat (destruct Hin as [Hq | Hin];
  [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?Usp, ?EGu in Hrr;
   unfold OFF_NCALLS, A_G_REC in *; first [left; lia | right; lia]|]); destruct Hin.

(* a register's symbolic value, without normalising its denotation *)
Ltac swe_e_preg HS r Hr :=
lazymatch type of HS with
| st_ok_pi ?segs ?val ?E ?ss (restrict ?H ?ms) =>
  pose proof (st_ok_pi_restrict_reg H E ss ms r HS) as Hr;
  let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
  cbn [ms_regs restrict mkst] in Hr
end.

(* the slot the table arm computes: g_rec + 16 + 56 * ncalls, as the symbolic executor writes it *)
Lemma swe_e_den_slot : forall E m g n,
ew E m = Z_to_bv 64 n -> 0 <= n <= 16 -> ew E g = Z_to_bv 64 A_G_REC ->
sv_denot E (SAlu ALU_ADD (SAlu ALU_ADD (SMd M_MUL (SOff m 0) (SLit 56)) (SLit 16)) (SOff g 0))
= Z_to_bv 64 (A_G_REC + OFF_CALLS + CALL_SIZE * n).
Proof.
intros E m g n Hm Hn Hg.
assert (ZC : forall x, 0 <= x < 2 ^ 64 -> zcanon x = x)
  by (intros x Hx; unfold zcanon, M64; apply Z.mod_small; lia).
assert (Hmul : U E (SMd M_MUL (SOff m 0) (SLit 56)) = 56 * n).
{ change (SMd M_MUL (SOff m 0) (SLit 56)) with (mono m 56).
  rewrite mono_sound, Hm, unsigned_lit_small by lia. unfold M64. apply Z.mod_small. lia. }
rewrite <- (Z_to_bv_bv_unsigned 64 (sv_denot E _)). f_equal.
change (U E (SAlu ALU_ADD (SAlu ALU_ADD (SMd M_MUL (SOff m 0) (SLit 56)) (SLit 16)) (SOff g 0))
        = A_G_REC + OFF_CALLS + CALL_SIZE * n).
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw].
rewrite Hmul, U_SLit, U_SOff, Hg, unsigned_lit_small by (unfold A_G_REC; lia).
assert (Z16 : zcanon 16 = 16) by (apply ZC; lia).
assert (ZG : zcanon (A_G_REC + 0) = A_G_REC) by (apply ZC; unfold A_G_REC; lia).
rewrite Z16, ZG.
assert (Z1 : zcanon (56 * n + 16) = 56 * n + 16) by (apply ZC; lia).
rewrite Z1.
assert (Z2 : zcanon (56 * n + 16 + A_G_REC) = 56 * n + 16 + A_G_REC) by (apply ZC; unfold A_G_REC; lia).
rewrite Z2. unfold A_G_REC, OFF_CALLS, CALL_SIZE. lia.
Qed.

Lemma swe_e_concat1 : forall (x : list (Z * Z)), concat [x] = x.
Proof. intros x. change (concat [x]) with (x ++ (@nil (Z * Z))). apply app_nil_r. Qed.

(* the read-only data along the journal of this call *)
Lemma swe_e_rodata : forall lyc Sc Wc memc mdc k,
ajournal SEGS B SUP_WORKER_ENV_STK (spZ regs) FPw ly S W mem md [] lyc Sc Wc memc mdc k ->
arodata_okP SEGS RLO RHI B (rdW Wc memc).
Proof.
intros lyc Sc Wc memc mdc k HJ a Hro Ho He.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _).
rewrite (F3 a); [exact (HROD a Hro Ho He) | exact (proj1 (cmd_ro_prog_apart a Hro)) | exact Ho | exact He |].
apply fp_spares_closed; [exact swe_FP_closed | exact (swe_ro_notFP a Hro)].
Qed.

(* the frame the prologue wrote, read off the stack region of a symbolic state *)
Lemma swe_e_frame_of_region : forall E (Wc : world SEGS) memc cs,
YP09.region_ok SEGS E (mrestrict (w_H Wc) memc) (YP09.mkRegion (Some 2%nat) (-64) 0 (-64) 0 cs) ->
bv_unsigned (ew E 2) = spZ regs ->
(forall nn (rr : bv 5), Z.of_nat nn = bv_unsigned rr -> ew E nn = getr regs rr) ->
(forall j r, nth_error swe_saved j = Some r ->
   In (YP09.mkChunk (- 8 - 8 * Z.of_nat j) (CVal 8 (SOff (Z.to_nat r) 0))) cs) ->
FRAME Wc memc.
Proof.
intros E Wc memc cs HR Hsp2 HE HIn j r Hj.
assert (Hr32 : 0 <= r < 32).
{ assert (H32 : Forall (fun x => 0 <= x < 32) swe_saved) by (unfold swe_saved; repeat constructor; lia).
  rewrite Forall_forall in H32. apply H32. eapply nth_error_In. exact Hj. }
assert (Hr5 : Z.of_nat (Z.to_nat r) = bv_unsigned (Z_to_bv 5 r)).
{ rewrite Z2Nat.id by lia. rewrite Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 5) with 32. symmetry. apply Z.mod_small. lia. }
apply (aval_mem_view SEGS).
replace (spZ regs - 8 - 8 * Z.of_nat j) with (spZ regs + (- 8 - 8 * Z.of_nat j)) by lia.
change 8%nat with (N.to_nat 8).
apply (field_of_region E _ 2%nat (spZ regs) cs (-64) 0 (-64) 0 (- 8 - 8 * Z.of_nat j) 8
  (SOff (Z.to_nat r) 0) _ HR Hsp2 (HIn j r Hj)).
- cbn [sv_denot]. rewrite (HE (Z.to_nat r) (Z_to_bv 5 r) Hr5), Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
- pose proof (bv_unsigned_in_range 64 (getr regs (Z_to_bv 5 r))) as Hb.
  change (bv_modulus 64) with (2 ^ 64) in Hb. cbn. lia.
- cbn. lia.
Qed.

Lemma swe_e_sig_rcf : SIG CS_rec_calls_free = BASE + AF_rec_calls_free.
Proof. rewrite (SIGP CS_rec_calls_free ltac:(cbn [In cmd_prog_syms]; tauto)). reflexivity. Qed.

(* 0x8c060 .. 0x8c0e4: the prologue and the inlined record()'s choice of slot, both arms, up to the join *)
Lemma swe_entry_ok : JSe -> SRr SEGS W (cfg_at SEGS (BASE + AF_sup_worker_env) regs mem md) POSTe.
Proof.
intros HJS.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
destruct swe_sp_bounds as (Hsp & Hsp47 & Hsp16 & Hceil1 & HWS).
pose proof swe_n_le as Hn16.
assert (Hn : 0 <= Z.of_nat (swe_n (R:=R)) <= 16) by lia.
pose proof asan_consts as (AC1 & _).
pose proof pa_base_lo as HBLO. pose proof pa_B_ok as HBOK.
pose proof HREP as (Qr & HAr & HOr).
pose proof HAr as (Hg8 & Hs8 & Hap & (C1 & C2 & C3 & C4 & C5 & C6) & HANS & HRPL & HSCAL & HOWN).
set (Ex := swe_extra regs (Z.of_nat (swe_n (R:=R))) (swe_c (R:=R))) in *.
pose proof (swe_env_mid regs) as HE. fold Ex in HE.
set (E := Eimg (Ereg regs Ex)) in *.
pose proof HE as (HEI & E2 & ESB & EN & EC).
destruct (swe_entry_seed B TL HB VOBJS cmd_prog_writable ly S W mem md regs E (spZ regs) (Z.of_nat (swe_n (R:=R))) (swe_c (R:=R))
  HAR HE ltac:(lia) Hal16 ltac:(lia) swe_c_ok
  ltac:(intros a Ha; apply Hpres; unfold SWE_FRAME in Ha; lia) C3 (regs_ok_Eimg_Ereg regs Ex)) as [HS SHOK].
pose proof (ajournal_init SEGS B SUP_WORKER_ENV_STK FPw ly S W regs mem md ch HPRE) as HJ.
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; apply unsigned_lit_small; lia).
assert (EGu : bv_unsigned (ew E 285%nat) = A_G_REC)
  by (change 285%nat with SW_GREC; rewrite (img_env_atomP E SW_GREC HEI ltac:(unfold SW_GREC, A_OBJ, A_TEXT, A_LIM; lia)),
      (swe_grec_val VOBJS); apply unsigned_lit_small; unfold A_G_REC; lia).
assert (EG : ew E 285%nat = Z_to_bv 64 A_G_REC) by (rewrite <- EGu, Z_to_bv_bv_unsigned; reflexivity).
assert (ESP : ew E 292%nat = Z_to_bv 64 A_REC_SPILL)
  by (change 292%nat with SW_SPILL; rewrite (img_env_atomP E SW_SPILL HEI ltac:(unfold SW_SPILL, A_OBJ, A_TEXT, A_LIM; lia)),
      (swe_spill_val VOBJS); reflexivity).
assert (E33 : ew E 33%nat = Z_to_bv 64 (Z.of_nat (swe_n (R:=R)))) by exact EN.
assert (E32 : ew E 32%nat = Z_to_bv 64 SB) by exact ESB.
assert (EEo : forall m (rr : bv 5), Z.of_nat m = bv_unsigned rr -> ew E m = getr regs rr)
  by (intros m rr Hm; exact (ew_Eimg_Ereg_nat regs Ex m rr Hm)).
assert (HAE : env_agree 32 (Ereg regs Ex) (Eimg (Ereg regs Ex)))
  by (split; [intros nn Hnn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
unfold cfg_at, w64.
paj_run_tok RUN HS HJ SHOK swe_Bspan.
{ swe_e_awr Usp EGu. }
pose proof (kept_of_frame (segs:=SEGS) _ _ _ _ _
  (fun a => spZ regs - 64 <= a < spZ regs \/ A_G_REC + OFF_NCALLS <= a < A_G_REC + OFF_NCALLS + 4) HFr
  ltac:(swe_e_win Usp EGu)) as UN1.
clear HF HFr HG.
psrr_branch_tok RUN BR HS SHOK swe_Bspan.
- (* the table arm: g_rec.ncalls < 16 *)
  assert (Hlt : (length (r_calls R) < 16)%nat).
  { rewrite branch_ne_U in Hc. apply negb_true_iff, Z.eqb_neq in Hc.
    rewrite U_SOff, E33, unsigned_lit_small in Hc by lia. rewrite U_SLit in Hc.
    rewrite !zcanon_small in Hc by lia. unfold swe_n in Hc. lia. }
  paj_run_to_tok RUNTO HS HJ SHOK swe_Bspan SWE_J.
  { swe_e_awr Usp EGu. }
  pose proof (kept_of_frame (segs:=SEGS) _ _ _ _ _
    (fun a => spZ regs - 64 <= a < spZ regs \/ A_G_REC + OFF_NCALLS <= a < A_G_REC + OFF_NCALLS + 4) HFr
    ltac:(swe_e_win Usp EGu)) as UN2.
  clear HF HFr HG.
  lazymatch type of UN2 with forall a, _ -> _ -> aview _ _ ?m2 a = _ =>
    assert (UN : forall a, 0 <= a < 2 ^ 64 ->
      ~ (spZ regs - 64 <= a < spZ regs \/ A_G_REC + OFF_NCALLS <= a < A_G_REC + OFF_NCALLS + 4) ->
      aview SEGS (w_H W) m2 a = aview SEGS (w_H W) mem a)
      by (intros a Ha Hna; rewrite (UN2 a Ha Hna); exact (UN1 a Ha Hna)) end.
  pmkst HS.
  lazymatch type of HS with st_ok_pi _ _ _ ?ssx (restrict _ ?msx) =>
    let r0 := eval vm_compute in (nth 0 (ss_mem ssx) got_regionP) in
    let r3 := eval vm_compute in (nth 3 (ss_mem ssx) got_regionP) in
    pose proof (st_ok_pi_region_nth E ssx (restrict _ msx) 0 r0 HS ltac:(vm_compute; reflexivity)) as HR0;
    pose proof (st_ok_pi_region_nth E ssx (restrict _ msx) 3 r3 HS ltac:(vm_compute; reflexivity)) as HR3 end.
  cbn [ms_mem restrict mkst] in HR0, HR3.
  sreg HS (2%bv : bv 5) Q2. sreg HS (3%bv : bv 5) Q3. sreg HS (4%bv : bv 5) Q4.
  sreg HS (9%bv : bv 5) Q9. sreg HS (19%bv : bv 5) Q19. sreg HS (20%bv : bv 5) Q20. sreg HS (21%bv : bv 5) Q21.
  swe_e_preg HS (8%bv : bv 5) P8.
  pose proof (regs_kept_of_st_ok SEGS _ _ _ regs Ex (map (Z_to_bv 5) [23;24;25;26;27]) HS HAE
    ltac:(vm_compute; reflexivity)) as KR.
  cbn [ms_regs restrict] in KR.
  rewrite Usp in Q2.
  rewrite (EEo 3%nat 3%bv eq_refl), Hgp in Q3. rewrite (EEo 4%nat 4%bv eq_refl), Htp in Q4.
  rewrite (EEo 12%nat 12%bv eq_refl), H12 in Q9. rewrite (EEo 11%nat 11%bv eq_refl), H11 in Q19.
  rewrite (EEo 10%nat 10%bv eq_refl), H10 in Q20. rewrite E32 in Q21.
  rewrite (swe_e_den_slot E 33%nat 285%nat _ E33 Hn EG) in P8.
  pose proof (field_of_region E _ 285%nat A_G_REC _ _ _ _ _ 8 4 (SOff 33%nat 1) (Z.of_nat (swe_n (R:=R)) + 1) HR3 EGu
    ltac:(cbn; tauto) ltac:(cbn [sv_denot]; rewrite E33, unsigned_lit_small by lia; reflexivity)
    ltac:(cbn; lia) ltac:(cbn; lia)) as VncJ.
  change (N.to_nat 4) with 4%nat in VncJ. apply (aval_mem_view SEGS) in VncJ.
  lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msx) =>
    set (regsJ := ms_regs msx) in *; set (memJ := ms_mem msx) in * end.
  assert (Hcv : swe_c (R:=R) = A_G_REC + OFF_CALLS + CALL_SIZE * Z.of_nat (length (r_calls R)))
    by (unfold swe_c, swe_n; exact (swe_m_slot_lt _ Hlt)).
  assert (Hsf0 : rec_spill_frees R = 0)
    by (unfold rec_spill_frees; replace (Nat.ltb (length (r_calls R)) 16) with true
        by (symmetry; apply Nat.ltb_lt; exact Hlt); reflexivity).
  apply (HJS ly S W regsJ memJ _ 0 O (ablocks B ly S) []).
  + split; [exact HJ|].
    split; [rewrite Hsf0; lia|].
    split.
    { apply (swe_e_frame_of_region E W memJ _ HR0 Usp EEo).
      intros j r Hj. unfold swe_saved in Hj.
      do 8 (destruct j as [|j]; [cbn in Hj; injection Hj as <-; cbn; tauto|]); destruct j; cbn in Hj; discriminate Hj. }
    split; [rewrite app_nil_r; reflexivity|].
    split; [rewrite app_nil_r; reflexivity|].
    split; [intros pn []|].
    split; [intros pn _ H; exact H|].
    split; [intros pn H; exact H|].
    split; [intros pn []|].
    split; [reflexivity|].
    split; [reflexivity|].
    split; [|exact swe_O_entry].
    unfold swe_xm. rewrite Hsf0.
    change (swe_sum (XM_XSTRDUP MT) (firstn 0 A3)) with 0.
    apply (mle_weaken MT S S 0 _ MTL (mle_start MT S MTL)). lia.
  + unfold swe_regs_base.
    split; [rewrite Q2; unfold w64; f_equal; lia|].
    split; [exact Q3|].
    split; [exact Q4|].
    split; [rewrite P8, Hcv; reflexivity|].
    split; [exact Q21|].
    intros r Hr. apply KR. apply in_map.
    assert (r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) as Hc5 by lia.
    destruct Hc5 as [->|[->|[->|[->| ->]]]]; cbn; tauto.
  + exact Q20.
  + exact Q19.
  + exact Q9.
  + intros rd' K1 K2 HFN HNA.
    apply (swe_rec_slot B ly S (rdW W mem) rd' R O HREP Hlt).
    * apply (aval_mem_kept (rdW W memJ)); [exact VncJ|].
      intros kk Hkk. apply K1; [left; unfold A_G_REC, OFF_NCALLS, REC_SIZE; lia|].
      rewrite Hcv. unfold A_G_REC, OFF_NCALLS, OFF_CALLS, CALL_SIZE. lia.
    * exact HFN.
    * exact HNA.
    * intros a Ha Hnc Hsl. rewrite (K1 a Ha Hsl). apply UN.
      { destruct Ha; unfold A_G_REC, REC_SIZE, A_REC_SPILL, SC_SIZE in *; lia. }
      intros [Hx|Hx]; [destruct Ha; unfold A_G_REC, REC_SIZE, A_REC_SPILL, SC_SIZE in *; lia | exact (Hnc Hx)].
    * intros p k i Hpk Hi. rewrite (K2 p k i Hpk Hi).
      pose proof (swe_O_entry _ Hpk) as Hpk2.
      destruct (al_blocks _ _ LAWS _ _ _ _ _ p k HAR Hpk2) as (_ & Hp4096 & Hpc & _).
      pose proof (req_size_pos k ltac:(lia)) as [_ Hrq].
      pose proof (blk_off_imgP B ly S W mem md p k HAR Hpk2) as Hoff. unfold off_img in Hoff.
      apply UN; [lia|]. unfold A_G_REC, OFF_NCALLS. lia.
- (* the spill arm: g_rec.ncalls = 16 *)
  assert (Hn16e : length (r_calls R) = 16%nat).
  { rewrite branch_ne_U in Hc. apply negb_false_iff, Z.eqb_eq in Hc.
    rewrite U_SOff, E33, unsigned_lit_small in Hc by lia. rewrite U_SLit in Hc.
    rewrite !zcanon_small in Hc by lia. unfold swe_n in Hc. lia. }
  assert (Hc16 : swe_c (R:=R) = A_REC_SPILL) by (unfold swe_c, swe_n; rewrite Hn16e; reflexivity).
  paj_run_tok RUN HS HJ SHOK swe_Bspan.
  { swe_e_awr Usp EGu. }
  pose proof (kept_of_frame (segs:=SEGS) _ _ _ _ _
    (fun a => spZ regs - 64 <= a < spZ regs \/ A_G_REC + OFF_NCALLS <= a < A_G_REC + OFF_NCALLS + 4) HFr
    ltac:(swe_e_win Usp EGu)) as UN2.
  clear HF HFr HG.
  lazymatch type of UN2 with forall a, _ -> _ -> aview _ _ ?m2 a = _ =>
    assert (UN : forall a, 0 <= a < 2 ^ 64 ->
      ~ (spZ regs - 64 <= a < spZ regs \/ A_G_REC + OFF_NCALLS <= a < A_G_REC + OFF_NCALLS + 4) ->
      aview SEGS (w_H W) m2 a = aview SEGS (w_H W) mem a)
      by (intros a Ha Hna; rewrite (UN2 a Ha Hna); exact (UN1 a Ha Hna)) end.
  pmkst HS.
  lazymatch type of HS with st_ok _ _ (setpc ?ssx ?pcx) (restrict _ ?msx) =>
    let r0 := eval vm_compute in (nth 0 (ss_mem ssx) got_regionP) in
    let r3 := eval vm_compute in (nth 3 (ss_mem ssx) got_regionP) in
    pose proof (st_ok_region_nth E (setpc ssx pcx) (restrict _ msx) 0 r0 HS ltac:(vm_compute; reflexivity)) as HR0;
    pose proof (st_ok_region_nth E (setpc ssx pcx) (restrict _ msx) 3 r3 HS ltac:(vm_compute; reflexivity)) as HR3 end.
  cbn [ms_mem restrict mkst] in HR0, HR3.
  sreg HS (1%bv : bv 5) Q1. sreg HS (2%bv : bv 5) Q2. sreg HS (3%bv : bv 5) Q3. sreg HS (4%bv : bv 5) Q4.
  sreg HS (8%bv : bv 5) Q8. sreg HS (9%bv : bv 5) Q9. sreg HS (10%bv : bv 5) Q10. sreg HS (11%bv : bv 5) Q11.
  sreg HS (19%bv : bv 5) Q19. sreg HS (20%bv : bv 5) Q20. sreg HS (21%bv : bv 5) Q21.
  pose proof (regs_kept_of_st_ok SEGS _ _ _ regs Ex (map (Z_to_bv 5) [23;24;25;26;27]) HS HAE
    ltac:(vm_compute; reflexivity)) as KR.
  cbn [ms_regs restrict] in KR.
  rewrite (img_env_codeptr _ HEI) in Q1. rewrite Usp in Q2.
  rewrite (EEo 3%nat 3%bv eq_refl), Hgp in Q3. rewrite (EEo 4%nat 4%bv eq_refl), Htp in Q4.
  rewrite ESP in Q8, Q10.
  rewrite (EEo 12%nat 12%bv eq_refl), H12 in Q9. rewrite (EEo 11%nat 11%bv eq_refl), H11 in Q19.
  rewrite (EEo 10%nat 10%bv eq_refl), H10 in Q20. rewrite E32 in Q21.
  pose proof (field_of_region E _ 285%nat A_G_REC _ _ _ _ _ 8 4 (SOff 33%nat 0) (Z.of_nat (swe_n (R:=R))) HR3 EGu
    ltac:(cbn; tauto) ltac:(cbn [sv_denot]; rewrite E33, unsigned_lit_small by lia; rewrite Z.add_0_r; reflexivity)
    ltac:(cbn; lia) ltac:(cbn; lia)) as VncT.
  change (N.to_nat 4) with 4%nat in VncT. apply (aval_mem_view SEGS) in VncT.
  lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) =>
    set (regsT := ms_regs msx) in *; set (memT := ms_mem msx) in * end.
  pose proof (swe_e_frame_of_region E W memT _ HR0 Usp EEo ltac:(
    intros j r Hj; unfold swe_saved in Hj;
    do 8 (destruct j as [|j]; [cbn in Hj; injection Hj as <-; cbn; tauto|]); destruct j; cbn in Hj; discriminate Hj)) as HFRT.
  (* every byte but the frame's is the entry's: g_rec.ncalls holds the same count *)
  assert (UNs : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 64 <= a < spZ regs) -> rdW W memT a = rdW W mem a).
  { intros a Ha Hf.
    destruct (Z.leb_spec (A_G_REC + OFF_NCALLS) a) as [Hd1|Hd1];
    [destruct (Z.ltb_spec a (A_G_REC + OFF_NCALLS + 4)) as [Hd2|Hd2]|].
    - assert (Hk4 : (Z.to_nat (a - (A_G_REC + OFF_NCALLS)) < 4)%nat) by lia.
      pose proof (VncT _ Hk4) as V1. pose proof (C3 _ Hk4) as V2.
      change (A_G_REC + 8) with (A_G_REC + OFF_NCALLS) in V1.
      replace (A_G_REC + OFF_NCALLS + Z.of_nat (Z.to_nat (a - (A_G_REC + OFF_NCALLS)))) with a in V1, V2 by lia.
      rewrite V1, V2. reflexivity.
    - apply UN; [exact Ha | lia].
    - apply UN; [exact Ha | lia]. }
  assert (HREPT : rec_repA B ly S (rdW W memT) R O).
  { apply (rec_repA_kept B ly S (rdW W mem) ly S (rdW W memT) R O HREP).
    - exact swe_O_entry.
    - intros a Ha. apply UNs; unfold A_G_REC in *; lia.
    - intros a Ha. apply UNs; unfold A_REC_SPILL in *; lia.
    - intros p k i Hpk Hi. pose proof (swe_O_entry _ Hpk) as Hpk2.
      destruct (al_blocks _ _ LAWS _ _ _ _ _ p k HAR Hpk2) as (_ & Hp4096 & Hpc & _).
      pose proof (req_size_pos k ltac:(lia)) as [_ Hrq].
      apply UNs; lia. }
  destruct HREPT as (Q & HAQ & HOQ).
  pose proof HAQ as (_ & _ & _ & (D1 & D2 & D3 & D4 & D5 & D6) & _).
  pose proof D5 as (F0 & F1 & F2 & F3 & F4 & F5 & F6).
  assert (HspO : forall pn, In pn (l_spill Q) -> In pn O)
    by (intros pn Hpn; apply HOQ; unfold lay_blocks; apply in_app_iff; right; apply in_app_iff; left; exact Hpn).
  assert (HFP1c : forall a, inFP (rcf_fp A_REC_SPILL [l_spill Q]) a ->
    (A_REC_SPILL + 4 <= a < A_REC_SPILL + 8) \/ exists p k, In (p, k) (l_spill Q) /\ p <= a < p + req_size k).
  { intros a Ha. unfold rcf_fp in Ha. apply inFP_app in Ha as [Ha | Ha].
    - left. cbn in Ha. apply inFP_cons in Ha as [Ha | Ha]; [|destruct (inFP_nil a Ha)].
      unfold A_REC_SPILL, CALL_SIZE, CALL_OFF_NARGS in *. lia.
    - right. apply inFP_ablocks_fp_inv in Ha as (p & k & Hpk & Hr). rewrite swe_e_concat1 in Hpk.
      exists p, k. split; [exact Hpk | exact Hr]. }
  assert (HFP1lo : forall a, inFP (rcf_fp A_REC_SPILL [l_spill Q]) a -> a < alloc_ceiling).
  { intros a Ha. destruct (HFP1c a Ha) as [Hn1 | (p & k & Hpk & Hr)]; [unfold A_REC_SPILL in Hn1; lia|].
    destruct (al_blocks _ _ LAWS _ _ _ _ _ p k HAR (swe_O_entry _ (HspO _ Hpk))) as (_ & _ & Hpc & _). lia. }
  assert (Hsf : rec_spill_frees R = Z.of_nat (length (snd (r_spill R))))
    by (unfold rec_spill_frees; replace (Nat.ltb (length (r_calls R)) 16) with false
        by (symmetry; apply Nat.ltb_ge; lia); reflexivity).
  pose proof (swe_e_rodata _ _ _ _ _ _ HJ) as HRODT.
  assert (HspT : spZ regsT = spZ regs + -64).
  { unfold spZ at 1. swe_z5. rewrite Q2. rewrite unsigned_lit_small by lia. lia. }
  swe_z5.
  rewrite swe_e_sig_rcf.
  eapply SRr_bind.
  { eapply (cl_callS_wide B LAWS W regsT memT _ SUP_WORKER_ENV_STK (spZ regs) FPw ly S W mem md [] ly S _ 0
       REC_CALLS_FREE_STK (rcf_fp A_REC_SPILL [l_spill Q]) (EV_REC_CALLS_FREE [l_spill Q]) (-64)
       (Z_to_bv 64 (BASE + 23520)) [] _ HJ HspT).
    - reflexivity.
    - lia.
    - unfold REC_CALLS_FREE_STK, ASTACK. lia.
    - unfold SUP_WORKER_ENV_STK. lia.
    - swe_z5. exact Q3.
    - swe_z5. exact Q4.
    - swe_z5. exact Q1.
    - apply ret_ok_codeptr_v; [lia | reflexivity].
    - rewrite unsigned_lit_small by lia. lia.
    - apply achain_low. unfold s0Z. swe_z5. rewrite Q8. rewrite unsigned_lit_small by (unfold A_REC_SPILL; lia).
      unfold A_REC_SPILL. lia.
    - intros HPRE1. eapply SRr_mono.
      { apply (TRCF fx ly S W regsT memT _ [] A_REC_SPILL [l_spill Q] HPRE1 HRODT).
        + swe_z5. exact Q10.
        + swe_z5. exact Q11.
        + cbn. lia.
        + right. left. unfold CALL_SIZE, SC_SIZE. cbn. lia.
        + unfold A_REC_SPILL. reflexivity.
        + intros i P0 Hi. destruct i as [|[|i]]; [|discriminate Hi|discriminate Hi].
          cbn in Hi. injection Hi as <-.
          split; [rewrite F2; exact F1|].
          split; [rewrite F2; replace (A_REC_SPILL + CALL_SIZE * Z.of_nat 0 + CALL_OFF_NARGS) with (A_REC_SPILL + CALL_OFF_NARGS) by lia;
                  exact F4|].
          intros j pn Hj.
          assert (Hjl : (j < length (snd (r_spill R)))%nat) by (rewrite <- F2; apply nth_error_Some; rewrite Hj; discriminate).
          destruct (nth_error (snd (r_spill R)) j) as [s|] eqn:Es; [|apply nth_error_None in Es; lia].
          destruct (F6 j s pn Es Hj) as (A1 & _ & A3 & _).
          split; [|exact A3].
          replace (A_REC_SPILL + CALL_SIZE * Z.of_nat 0 + CALL_OFF_ARGS + 8 * Z.of_nat j)
            with (A_REC_SPILL + CALL_OFF_ARGS + 8 * Z.of_nat j) by lia. exact A1.
        + rewrite swe_e_concat1. exact F5.
        + unfold EV_REC_CALLS_FREE. rewrite swe_e_concat1, F2.
          pose proof HEV as HEV'. unfold EV_SUP_WORKER_ENV, EV_ANSWER, EV_HAND_BACK, EV_XSTRDUP in HEV'.
          rewrite Hsf in HEV'. lia.
        + pose proof (mo_malloc_nonneg MT MTL) as Hmn. pose proof (mo_free_nonneg MT MTL) as Hfn.
          assert (HXN : forall x, 0 <= XM_XSTRDUP MT x) by (intros x; unfold XM_XSTRDUP; apply Hmn; lia).
          assert (HXA : forall t, 0 <= XM_ANSWER MT t) by (intros t; unfold XM_ANSWER, XM_HAND_BACK; pose proof (HXN t); lia).
          apply (mok_station MT S S _ 0 _ MTL HMOK (mle_start MT S MTL)).
          * unfold XM_REC_CALLS_FREE. apply Z.mul_nonneg_nonneg; lia.
          * unfold XM_REC_CALLS_FREE, XM_SUP_WORKER_ENV. rewrite swe_e_concat1, F2, Hsf.
            pose proof (HXN (sarg format)). pose proof (HXN (sarg cpus)). pose proof (HXN (sarg nice)).
            pose proof (HXA (snd (sup_worker_env_m R format cpus nice))). lia. }
      cbv beta. intros W2 c2 _ (ly' & S' & regs' & mem' & md' & -> & HJ' & HP' & HK').
      exists ly', S', regs', mem', md'. split; [|split; [exact HJ' | split; [exact HP' | exact HK']]].
      swe_z5. rewrite Q1. reflexivity.
    - intros a Ha. destruct (HFP1c a Ha) as [Hn1 | (p & k & Hpk & Hr)].
      + right; right; right; right; left. split; [|split].
        * unfold swe_FP. exists (A_REC_SPILL, A_REC_SPILL + SC_SIZE). split; [right; left; reflexivity|].
          cbn [fst snd]. unfold SC_SIZE. lia.
        * rewrite (recb_ts_prog_m B HB). apply recb_spill_in. unfold SC_SIZE. lia.
        * apply cmd_prog_img. apply recb_spill_in. unfold SC_SIZE. lia.
      + right; left. split.
        * unfold swe_FP. apply inFP_cons. right. apply inFP_cons. right.
          replace a with (p + (a - p)) by lia. apply (inFP_ablocks_fp O p k (a - p)); [exact (HspO _ Hpk) | lia].
        * exists p, k. split; [exact (swe_O_entry _ (HspO _ Hpk)) | lia].
    - intros ly0 S0 W0 regs0 mem0 md0 _ a Ha Hw _. exfalso. pose proof (HFP1lo a Ha). lia. }
  cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HJc & HP2 & HK2).
  destruct HK2 as (HPERM & _ & _ & _ & _ & HSP & _ & _ & HMLE2).
  pose proof (HSP R Q HAQ eq_refl eq_refl) as HREP2.
  rewrite swe_e_concat1 in HPERM.
  pose proof (proj1 HJc) as HAR2.
  assert (G : forall r, In r [2;3;4;8;9;18;19;20;21;22;23;24;25;26;27] -> getr regs2 (Z_to_bv 5 r) = getr regsT (Z_to_bv 5 r)).
  { intros r Hr. apply HP2. unfold acallee_saved. cbn in Hr. lia. }
  assert (Esp2 : spZ regs2 = spZ regs - 64).
  { unfold spZ at 1. swe_z5. rewrite (G 2 ltac:(cbn; tauto)), Q2. rewrite unsigned_lit_small by lia. lia. }
  pose proof (proj1 (swe_env_mid regs2)) as HEI2.
  destruct (swe_x_seed ly2 S2 W2 mem2 md2 regs2 _ (spZ regs2) _ _ 23520 HAR2 (swe_env_mid regs2)
    ltac:(rewrite Esp2; lia) ltac:(rewrite Esp2; exact Hsp16) ltac:(lia) swe_c_ok (regs_ok_Eimg_Ereg regs2 _)) as [HS2 SHOK2].
  assert (HAE2 : env_agree 32 (Ereg regs2 Ex) (Eimg (Ereg regs2 Ex)))
    by (split; [intros nn Hnn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  paj_run_to_tok RUNTO HS2 HJ2 SHOK2 swe_Bspan SWE_J.
  { apply (YCbq.awr_ok_nil SEGS B). }
  pmkst HS2.
  pose proof (regs_kept_of_st_ok SEGS _ _ _ regs2 Ex swe_kept_regs HS2 HAE2 ltac:(vm_compute; reflexivity)) as KRJ.
  cbn [ms_regs restrict] in KRJ.
  lazymatch type of HS2 with st_ok_pi _ _ _ _ (restrict _ ?msx) =>
    assert (KMJ : forall a, 0 <= a < 2 ^ 64 -> rdW W2 (ms_mem msx) a = rdW W2 mem2 a)
      by (intros a Ha; apply (kept_of_frame _ _ (w_H W2) mem2 _ (fun _ => False) HFr); [|exact Ha|intros H; exact H];
          intros b wlo whi a' Hin _; cbn in Hin; destruct Hin);
    set (regsJ := ms_regs msx) in *; set (memJ := ms_mem msx) in * end.
  clear HF HFr HG.
  set (O0 := concat (l_calls Q) ++ oblk (l_answer Q) ++ oblk (l_reply Q)) in *.
  assert (GJ : forall r, In r [2;3;4;8;9;18;19;20;21;22;23;24;25;26;27] -> getr regsJ (Z_to_bv 5 r) = getr regsT (Z_to_bv 5 r))
    by (intros r Hr; rewrite (KRJ _ (swe_kept_in r Hr)); exact (G r Hr)).
  apply (HJS ly2 S2 W2 regsJ memJ _ (0 + EV_REC_CALLS_FREE [l_spill Q]) O0 (ablocks B ly2 S2) (l_spill Q)).
  + split; [exact HJ2|].
    split.
    { unfold EV_REC_CALLS_FREE. rewrite Hsf, swe_e_concat1, F2. lia. }
    split.
    { apply (swe_frame_kept W2 W2 mem2 memJ); [|intros a Ha; apply KMJ; lia].
      apply (swe_frame_kept W W2 memT mem2 HFRT). intros a Ha.
      pose proof HJc as (_ & _ & _ & _ & _ & _ & _ & _ & G1 & _).
      apply G1; [lia | lia | intros HFa; pose proof (HFP1lo a HFa); lia]. }
    split; [exact HPERM|].
    split; [rewrite app_nil_r; reflexivity|].
    split; [exact HspO|].
    split.
    { intros pn HD HO. apply HOQ in HO. unfold lay_blocks in HO. unfold O0.
      apply in_app_iff in HO as [H|H]; [apply in_app_iff; left; exact H|].
      apply in_app_iff in H as [H|H]; [|apply in_app_iff; right; exact H].
      exfalso. pose proof (Permutation_NoDup HPERM (recb_ablocks_nodup_m B ly S W mem md HAR)) as HND.
      exact (list_nodup_app_disj _ _ pn HND HD H). }
    split.
    { intros pn Hpn. apply HOQ. unfold lay_blocks. unfold O0 in Hpn.
      apply in_app_iff in Hpn as [H|H]; [apply in_app_iff; left; exact H|].
      apply in_app_iff; right; apply in_app_iff; right; exact H. }
    split; [intros pn []|].
    split; [reflexivity|].
    split; [reflexivity|].
    split; [|exact (rec_repA_in B ly2 S2 _ _ _ HREP2)].
    unfold swe_xm. rewrite Hsf.
    change (swe_sum (XM_XSTRDUP MT) (firstn 0 A3)) with 0.
    apply (mle_weaken MT S S2 _ _ MTL HMLE2).
    unfold XM_REC_CALLS_FREE. rewrite swe_e_concat1, F2. lia.
  + unfold swe_regs_base. swe_z5.
    split; [rewrite (GJ 2 ltac:(cbn; tauto)), Q2; unfold w64; f_equal; lia|].
    split; [rewrite (GJ 3 ltac:(cbn; tauto)); exact Q3|].
    split; [rewrite (GJ 4 ltac:(cbn; tauto)); exact Q4|].
    split; [rewrite (GJ 8 ltac:(cbn; tauto)), Q8, Hc16; reflexivity|].
    split; [rewrite (GJ 21 ltac:(cbn; tauto)); exact Q21|].
    intros r Hr.
    assert (r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) as Hc5 by lia.
    rewrite (GJ r ltac:(destruct Hc5 as [->|[->|[->|[->| ->]]]]; cbn; tauto)).
    apply KR. apply in_map. destruct Hc5 as [->|[->|[->|[->| ->]]]]; cbn; tauto.
  + swe_z5. rewrite (GJ 20 ltac:(cbn; tauto)). exact Q20.
  + swe_z5. rewrite (GJ 19 ltac:(cbn; tauto)). exact Q19.
  + swe_z5. rewrite (GJ 9 ltac:(cbn; tauto)). exact Q9.
  + intros rd' K1 K2 HFN HNA.
    rewrite (rec_record_spill R REC_WORKER_ENV [] Hn16e).
    assert (HREPJ : rec_repA B ly2 S2 (rdW W2 memJ) (set_spill R (fst (r_spill R), [])) O0).
    { apply (rec_repA_kept B ly2 S2 (rdW W2 mem2) ly2 S2 (rdW W2 memJ) _ _ HREP2).
      - exact (rec_repA_in B ly2 S2 _ _ _ HREP2).
      - intros a Ha. apply KMJ. unfold A_G_REC in Ha. lia.
      - intros a Ha. apply KMJ. unfold A_REC_SPILL in Ha. lia.
      - intros p k i Hpk Hi. apply KMJ.
        pose proof (rec_repA_in B ly2 S2 _ _ _ HREP2 _ Hpk) as Hpk2.
        destruct (al_blocks _ _ LAWS _ _ _ _ _ p k HAR2 Hpk2) as (_ & Hp4096 & Hpc & _).
        pose proof (req_size_pos k ltac:(lia)) as [_ Hrq]. lia. }
    rewrite Hc16 in K1, HFN, HNA.
    exact (swe_rec_spill B ly2 S2 (rdW W2 memJ) rd' (set_spill R (fst (r_spill R), [])) O0 HREPJ eq_refl HFN HNA K1 K2).
Qed.

#[local] Notation RSr3 := (swe_R_stmt (B:=B) (MT:=MT) (ly:=ly) (S:=S) (W:=W) (regs:=regs) (mem:=mem) (md:=md)
  (pcs:=pcs) (pnn:=pnn) (format:=format) (cpus:=cpus) (nice:=nice) (R:=R) (O:=O)).
#[local] Notation POSTr3 := (swe_POST (B:=B) (MT:=MT) (ly:=ly) (S:=S) (W:=W) (regs:=regs) (mem:=mem) (md:=md)
  (format:=format) (cpus:=cpus) (nice:=nice) (R:=R) (O:=O)).
#[local] Notation QQr3 := (swe_Q (B:=B) (MT:=MT) (ly:=ly) (S:=S) (format:=format) (cpus:=cpus) (nice:=nice) (R:=R) (O:=O)).
#[local] Notation EXr3 := (swe_extra regs (Z.of_nat (swe_n (R:=R))) (swe_c (R:=R))).
(* the verb rec_shape_of looks up: "worker_env", the first 10 bytes of .str.14 (RO_lit_21ec0) *)
Definition swe_r3_v : list byte := map (Z_to_bv 8) [119; 111; 114; 107; 101; 114; 95; 101; 110; 118].
#[local] Notation SHPr3 := (shape_of swe_r3_v).
#[local] Notation RAr3 := (rec_record R REC_WORKER_ENV A3).
#[local] Notation TTr3 := (snd (rec_answer RAr3 (REC_WORKER_ENV, A3) SHPr3 true)).
#[local] Notation FP1r3 old Oa := ((A_G_REC + OFF_ANSWER, A_G_REC + OFF_ANSWER + 8) ::
  (A_G_REC + OFF_STATE, A_G_REC + OFF_STATE + 8) :: ablocks_fp (filter (fun pn => fst pn =? old) Oa)).

Definition swe_r3_pdec (x y : Z * Z) : {x = y} + {x <> y}.
Proof. decide equality; apply Z.eq_dec. Defined.

(* the model step of the statement, with the verb's bytes named *)
Lemma swe_r3_vb : sup_worker_env_m R format cpus nice = rec_answer RAr3 (REC_WORKER_ENV, A3) SHPr3 true.
Proof.
unfold sup_worker_env_m, rec_stub, daemon_shape, swe_A3.
lazymatch goal with |- context [bstr ?s] => replace (bstr s) with swe_r3_v by (vm_compute; reflexivity) end.
reflexivity.
Qed.

Lemma swe_r3_fits : fits SHPr3.
Proof. unfold fits. vm_compute. discriminate. Qed.

Lemma swe_r3_sig_rso : SIG CS_rec_shape_of = BASE + AF_rec_shape_of.
Proof. rewrite (SIGP CS_rec_shape_of ltac:(cbn [In cmd_prog_syms]; tauto)). reflexivity. Qed.

Lemma swe_r3_sig_ans : SIG CS_answer = BASE + AF_answer.
Proof. rewrite (SIGP CS_answer ltac:(cbn [In cmd_prog_syms]; tauto)). reflexivity. Qed.

(* the saved registers as the atoms 35 + j of a mid segment's environment *)
Lemma swe_r3_atom : forall (regs2 : bvmap 5 word) n j r, n = (35 + j)%nat -> nth_error swe_saved j = Some r ->
ew (Eimg (Ereg regs2 EXr3)) n = getr regs (Z_to_bv 5 r).
Proof.
intros regs2 n j r -> Ej.
assert (Hj : (j < 8)%nat) by (pose proof (nth_error_Some swe_saved j) as Hl; rewrite Ej in Hl; cbn [length swe_saved] in Hl; apply Hl; discriminate).
rewrite Eimg_low by (unfold A_TEXT; lia).
replace (35 + j)%nat with (32 + (3 + j))%nat by lia. rewrite ew_Ereg_extra.
unfold swe_extra. rewrite app_nth2 by (cbn [length map]; lia). cbn [length map]. replace (3 + j - 3)%nat with j by lia.
apply nth_error_nth. rewrite nth_error_map, Ej. reflexivity.
Qed.

(* the frame's saved registers as the chunks of the mid-segment frame region *)
Lemma swe_r3_frame_ok : forall (W2 : world SEGS) mem2 (regs2 : bvmap 5 word),
FRAME W2 mem2 -> spZ regs2 = spZ regs - 64 ->
Forall (YP09.chunk_ok SEGS (Eimg (Ereg regs2 EXr3)) (mrestrict (w_H W2) mem2) (spZ regs2)) swe_frame_chunks.
Proof.
intros W2 mem2 regs2 HF Esp.
unfold swe_frame_chunks. apply Forall_forall. intros chk Hch. apply in_map_iff in Hch as (j & <- & Hj). apply in_seq in Hj.
destruct (nth_error swe_saved j) as [r|] eqn:Ej; [| exfalso; apply nth_error_None in Ej; cbn [length swe_saved] in Ej; lia].
pose proof (HF j r Ej) as Hv.
pose proof (bv_unsigned_in_range 64 (getr regs (Z_to_bv 5 r))) as Hr. change (bv_modulus 64) with (2 ^ 64) in Hr.
apply (chunk_ok_val SEGS _ _ _ _ 8 (SOff (35 + j) 0) (bv_unsigned (getr regs (Z_to_bv 5 r)))).
- cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned.
  rewrite (swe_r3_atom regs2 (35 + j) j r eq_refl Ej). first [reflexivity | symmetry; apply Z_to_bv_bv_unsigned].
- rewrite swe_pow8. lia.
- cbn. lia.
- rewrite Esp. replace (spZ regs - 64 + (56 - 8 * Z.of_nat j)) with (spZ regs - 8 - 8 * Z.of_nat j) by lia.
  exact (val_mem_view SEGS _ _ _ _ _ Hv).
Qed.

Lemma swe_r3_In_Z : forall (x : Z) l, existsb (Z.eqb x) l = true -> In x l.
Proof. intros x l H. apply existsb_exists in H as (y & Hy & E). apply Z.eqb_eq in E. subst. exact Hy. Qed.

(* the verb as rec_shape_of takes it: its bytes, and the read-only arm of astr_argA (.str.14, 0x21ec0, 11 bytes
   with its NUL; its shadow and its end decided on the image's constants) *)
Lemma swe_r3_verb : forall lyc Sc (Wc : world SEGS) memc, cmd_ro_ok (rdW Wc memc) ->
abytes_atR (rdW Wc memc) 0x21ec0 swe_r3_v /\
astr_argA B lyc Sc (rdW Wc memc) (in_roP SEGS RLO RHI) [] 0x21ec0 (Some swe_r3_v).
Proof.
intros lyc Sc Wc memc HRO1.
assert (HLIT : abytes_atR (rdW Wc memc) 0x21ec0 RO_lit_21ec0).
{ clear - HRO1. destruct HRO1 as [HRO1 _]. unfold cmd_ro_bytes in HRO1.
  repeat match type of HRO1 with
  | abytes_atR _ 0x21ec0 _ /\ _ => exact (proj1 HRO1)
  | _ /\ _ => apply proj2 in HRO1
  end. }
assert (HIN : forall i, 0 <= i < 11 -> in_roP SEGS RLO RHI (0x21ec0 + i)).
{ pose proof CMD_RO_IN as HI. clear - HI. unfold cmd_ro_in in HI.
  repeat match type of HI with
  | (forall i, 0 <= i < 11 -> _ (0x21ec0 + i)) /\ _ => exact (proj1 HI)
  | _ /\ _ => apply proj2 in HI
  end. }
replace RO_lit_21ec0 with (swe_r3_v ++ [Z_to_bv 8 0]) in HLIT by reflexivity.
assert (HBy : abytes_atR (rdW Wc memc) 0x21ec0 swe_r3_v).
{ intros i Hi. specialize (HLIT i ltac:(rewrite length_app; cbn [length] in *; lia)).
  rewrite app_nth1 in HLIT by exact Hi. exact HLIT. }
split; [exact HBy|].
cbn [astr_argA]. change (Z.of_nat (length swe_r3_v)) with 10.
split; [lia|].
split.
{ split; [exact HLIT|]. vm_compute. intros H; repeat (destruct H as [H|H]; [discriminate H|]); exact H. }
split; [unfold LMAX; lia|].
right.
split.
{ intros i Hi. split; [apply HIN; lia|].
  rewrite (ts_owned B HB), (ts_errno B HB). unfold TFIB_ERRNO. split; [|lia].
  apply (swe_not_in_ranges _ 0x21ec0 (0x21ec0 + 11)); [vm_compute; reflexivity | lia]. }
split; [vm_compute; reflexivity|].
split; [vm_compute; reflexivity|].
apply swe_r3_In_Z. vm_compute. reflexivity.
Qed.

(* a string argument stays one at a memory that reads the same at every address *)
Lemma swe_r3_arg_kept : forall ly1 S1 (W1 : world SEGS) mem1 md1 (rd rd' : reader) Oa q x,
AR SEGS B ly1 S1 W1 mem1 md1 -> 0 <= q ->
(forall a, 0 <= a < 2 ^ 64 -> rd' a = rd a) ->
astr_argA B ly1 S1 rd (in_roP SEGS RLO RHI) Oa q (Some x) ->
astr_argA B ly1 S1 rd' (in_roP SEGS RLO RHI) Oa q (Some x).
Proof.
intros ly1 S1 W1 mem1 md1 rd rd' Oa q x HAR Hq0 Hk HA. cbn [astr_argA] in HA |- *.
destruct HA as (Hp0 & Hs & Hn & Harm).
assert (Hbd : forall i, 0 <= i < Z.of_nat (length x) + 1 -> 0 <= q + i < 2 ^ 64).
{ intros i Hi. pose proof asan_consts as (C1 & _).
  destruct Harm as [((b & kk & Hbk & Hbq & Hqb) & _) | (Hro & _)].
  - destruct (al_blocks _ _ LAWS _ _ _ _ _ b kk HAR Hbk) as (_ & _ & Hc & _ & _ & _ & Hkk).
    pose proof (req_size_pos kk ltac:(lia)) as [_ Hr]. lia.
  - destruct (Hro i Hi) as (Hr & _). destruct (cmd_ro_prog_apart _ Hr) as [Himg _].
    pose proof (pa_img_range _ Himg). lia. }
split; [exact Hp0|].
split; [apply (rastr_kept rd rd' q x Hs); intros i Hi; apply Hk; exact (Hbd i Hi)|].
split; [exact Hn | exact Harm].
Qed.

(* the answer g_rec holds: 0, or the start of one of the recorder's blocks *)
Lemma swe_r3_old : forall ly1 S1 rd Ra Oa, rec_repA B ly1 S1 rd Ra Oa ->
exists old, aval_mem rd (A_G_REC + OFF_ANSWER) 8 old /\ (old = 0 \/ exists m, In (old, m) Oa).
Proof.
intros ly1 S1 rd Ra Oa (Q & HA & HO).
destruct HA as (_ & _ & _ & _ & Ha & _). unfold aanswer_at in Ha.
revert Ha. destruct (l_answer Q) as [[q m]|] eqn:EQ; destruct (r_answer Ra) as [x|]; intros Ha; try contradiction.
- exists q. split; [exact (proj1 Ha)|]. right. exists m. apply HO. unfold lay_blocks. rewrite EQ.
  apply in_app_iff. right. apply in_app_iff. right. apply in_app_iff. left. left. reflexivity.
- exists 0. split; [exact Ha | left; reflexivity].
Qed.

(* a live block that starts at the old answer is the old answer's block *)
Lemma swe_r3_old_blk : forall lyc Sc (Wc : world SEGS) memc mdc Oa old, AR SEGS B lyc Sc Wc memc mdc ->
(forall pn, In pn Oa -> In pn (ablocks B lyc Sc)) -> (old = 0 \/ exists m, In (old, m) Oa) ->
forall pn, In pn (ablocks B lyc Sc) -> fst pn = old -> In pn Oa.
Proof.
intros lyc Sc Wc memc mdc Oa old HAR HOa Hold [b mm] Hb Ef. cbn [fst] in Ef. subst b.
destruct (al_blocks _ _ LAWS _ _ _ _ _ old mm HAR Hb) as (_ & H4096 & _ & _ & _ & _ & Hmm).
destruct Hold as [E0 | (m & Hm)]; [lia|].
destruct (swe_r3_pdec (old, mm) (old, m)) as [E|Hne]; [rewrite E; exact Hm|].
exfalso. pose proof (HOa _ Hm) as Hmc.
destruct (al_blocks _ _ LAWS _ _ _ _ _ old m HAR Hmc) as (_ & _ & _ & _ & _ & _ & Hm0).
pose proof (sep_blocks SEGS B LAWS lyc Sc Wc memc mdc old mm old m HAR Hb Hmc Hne) as Hdj.
pose proof (req_size_pos mm ltac:(lia)) as [Hr1 _]. pose proof (req_size_pos m ltac:(lia)) as [Hr2 _].
unfold zdisjoint in Hdj. cbn [fst snd] in Hdj. lia.
Qed.

(* record()'s slot holds the call answer records (answer's premise on c) *)
Lemma swe_r3_slot :
(exists kk, nth_error (r_calls RAr3) kk = Some (REC_WORKER_ENV, A3) /\
   swe_c (R:=R) = A_G_REC + OFF_CALLS + CALL_SIZE * Z.of_nat kk) \/
(swe_c (R:=R) = A_REC_SPILL /\ (REC_WORKER_ENV, A3) = r_spill RAr3).
Proof.
pose proof swe_n_le as Hn16. unfold swe_c, swe_n, swe_slot_of in *.
destruct (Nat.ltb_spec (length (r_calls R)) 16) as [Hl|Hl].
- left. exists (length (r_calls R)). rewrite (rec_record_calls R _ _ Hl). unfold set_calls. cbn [r_calls].
  split; [rewrite nth_error_app2, Nat.sub_diag by lia; reflexivity|].
  replace (Z.of_nat (length (r_calls R)) <? 16) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
- right. assert (Hn : length (r_calls R) = 16%nat) by lia. rewrite (rec_record_spill R _ _ Hn). unfold set_spill. cbn [r_spill].
  rewrite Hn. split; reflexivity.
Qed.

(* membership in answer's filtered block list *)
Lemma swe_r3_filter_in : forall (old : Z) (Oa : list (Z * Z)) x,
In x (filter (fun pn : Z * Z => fst pn =? old) Oa) -> In x Oa.
Proof.
intros old Oa x. induction Oa as [|y Oa IH]; intros H; [cbn in H; contradiction|].
cbn in H. destruct (decide _) in H; [destruct H as [<- | H]; [left; reflexivity | right; apply IH; exact H] | right; apply IH; exact H].
Qed.

(* no footprint byte lies at or above the allocator's ceiling (the stack) *)
Lemma swe_r3_notFP_hi : forall a, alloc_ceiling <= a -> ~ inFP FPw a.
Proof.
intros a Ha HF. pose proof asan_consts as (C1 & _).
unfold swe_FP in HF. apply inFP_cons in HF as [HF|HF]; [unfold A_G_REC, REC_SIZE in HF; lia|].
apply inFP_cons in HF as [HF|HF]; [unfold A_REC_SPILL, SC_SIZE in HF; lia|].
destruct (inFP_ablocks_fp_inv _ _ HF) as (b & n & Hin & Hr).
destruct (al_blocks _ _ LAWS _ _ _ _ _ b n swe_AR0 (swe_O_entry _ Hin)) as (_ & _ & Hc & _). lia.
Qed.

(* answer's footprint lies below the allocator's ceiling *)
Lemma swe_r3_fp_low : forall lyc Sc (Wc : world SEGS) memc mdc Oa old a, AR SEGS B lyc Sc Wc memc mdc ->
(forall pn, In pn Oa -> In pn (ablocks B lyc Sc)) -> inFP (FP1r3 old Oa) a -> a < alloc_ceiling.
Proof.
intros lyc Sc Wc memc mdc Oa old a HAR HOa Ha. pose proof asan_consts as (C1 & _).
apply inFP_cons in Ha as [Ha|Ha]; [unfold A_G_REC, OFF_ANSWER in Ha; lia|].
apply inFP_cons in Ha as [Ha|Ha]; [unfold A_G_REC, OFF_STATE in Ha; lia|].
destruct (inFP_ablocks_fp_inv _ _ Ha) as (b & n & Hin & Hr). apply swe_r3_filter_in in Hin.
destruct (al_blocks _ _ LAWS _ _ _ _ _ b n HAR (HOa _ Hin)) as (_ & _ & Hc & _). lia.
Qed.

(* answer's footprint is bytes this call may write: g_rec's fields, or a block of the recorder (one of the entry's
   footprint blocks, or one made during the call) *)
Lemma swe_r3_fp : forall lyc Sc Wc memc mdc k O0 D Fr NB old a,
CORE 3 lyc Sc Wc memc mdc k O0 D Fr NB ->
rec_repA B lyc Sc (rdW Wc memc) RAr3 (O0 ++ NB) ->
inFP (FP1r3 old (O0 ++ NB)) a ->
awr_byte SEGS B SUP_WORKER_ENV_STK (spZ regs) FPw (ablocks B ly S) (ablocks B lyc Sc) (frames S) lyc [] a.
Proof.
intros lyc Sc Wc memc mdc k O0 D Fr NB old a HC HREPc Ha.
pose proof HC as (HJ & _ & _ & HP0 & HP1 & HFrO & _ & HO0 & HNBD & _).
assert (HG : forall a0, A_G_REC <= a0 < A_G_REC + REC_SIZE ->
  awr_byte SEGS B SUP_WORKER_ENV_STK (spZ regs) FPw (ablocks B ly S) (ablocks B lyc Sc) (frames S) lyc [] a0).
{ intros a0 Ha0. right; right; right; right; left. split; [|split].
  - unfold swe_FP. exists (A_G_REC, A_G_REC + REC_SIZE). split; [left; reflexivity | exact Ha0].
  - rewrite (recb_ts_prog_m B HB). apply recb_grec_in. exact Ha0.
  - apply cmd_prog_img. apply recb_grec_in. exact Ha0. }
apply inFP_cons in Ha as [Ha|Ha]; [apply HG; unfold OFF_ANSWER, REC_SIZE in *; lia|].
apply inFP_cons in Ha as [Ha|Ha]; [apply HG; unfold OFF_STATE, REC_SIZE in *; lia|].
destruct (inFP_ablocks_fp_inv _ _ Ha) as (b & n & Hin & Hr). apply swe_r3_filter_in in Hin.
pose proof (rec_repA_in B lyc Sc _ _ _ HREPc _ Hin) as Hbc.
destruct (in_dec swe_r3_pdec (b, n) (ablocks B ly S)) as [H0|H0].
- right; left. split; [|exists b, n; split; [exact Hbc | exact Hr]].
  assert (HbO : In (b, n) O).
  { apply (Permutation_in _ HP0) in H0. apply in_app_iff in H0 as [Hd|Hf]; [|exact (HFrO _ Hf)].
    apply in_app_iff in Hin as [Ho|Hn]; [exact (HO0 _ Ho) | exfalso; exact (HNBD _ Hn Hd)]. }
  replace a with (b + (a - b)) by lia. unfold swe_FP.
  apply inFP_cons. right. apply inFP_cons. right. exact (inFP_ablocks_fp O b n (a - b) HbO ltac:(lia)).
- right; right; left. exists b, n. split; [exact Hbc|]. split; [exact H0 | exact Hr].
Qed.

(* the event, live-byte and meter budget of answer at the tail call *)
Lemma swe_r3_budget : forall lyc Sc Wc memc mdc k O0 D Fr NB,
CORE 3 lyc Sc Wc memc mdc k O0 D Fr NB ->
st_nev Sc + EV_ANSWER <= EV_MAX /\ blocks_bytes Sc + LIVE_ANSWER TTr3 <= LIVE_MAX /\ mo_ok MT Sc (XM_ANSWER MT TTr3).
Proof.
intros lyc Sc Wc memc mdc k O0 D Fr NB HC.
destruct HC as (HJ & Hk & _ & HP0 & HP1 & _ & _ & _ & _ & HNBl & HNBb & HMLE & _). change (Z.of_nat 3) with 3 in Hk.
pose proof HJ as (HAR1 & _ & _ & _ & _ & _ & Hnev & _).
assert (HbD : 0 <= bsum Fr).
{ apply (swe_bsum_nonneg ly S W mem md Fr swe_AR0). intros pn Hpn.
  apply (Permutation_in _ (Permutation_sym HP0)). apply in_app_iff. right. exact Hpn. }
assert (Hbb : blocks_bytes Sc + bsum Fr = blocks_bytes S + bsum NB).
{ rewrite (blocks_bytes_bsum B lyc Sc), (blocks_bytes_bsum B ly S), (bsum_perm _ _ HP0), (bsum_perm _ _ HP1), !bsum_app. lia. }
pose proof (mo_malloc_nonneg MT MTL) as Hmn. pose proof (mo_free_nonneg MT MTL) as Hfn.
assert (HXN : forall x, 0 <= XM_XSTRDUP MT x) by (intros x; unfold XM_XSTRDUP; apply Hmn; lia).
assert (HXA : forall t, 0 <= XM_ANSWER MT t) by (intros t; unfold XM_ANSWER, XM_HAND_BACK; pose proof (HXN t); lia).
assert (Et : snd (sup_worker_env_m R format cpus nice) = TTr3) by (rewrite swe_r3_vb; reflexivity).
unfold EV_SUP_WORKER_ENV in HEV. unfold LIVE_SUP_WORKER_ENV in HLIVE. unfold XM_SUP_WORKER_ENV in HMOK.
rewrite Et in HLIVE, HMOK.
rewrite HNBb in Hbb. unfold swe_live, swe_xm in *. unfold swe_A3 in HNBb, Hbb, HMLE. cbn [firstn swe_sum] in Hbb, HMLE.
split; [unfold EV_ANSWER, EV_HAND_BACK, EV_XSTRDUP in *; lia|].
split; [lia|].
apply (mok_station MT S Sc _ _ _ MTL HMOK HMLE (HXA _)). lia.
Qed.

(* after rec_shape_of (it keeps the layout and the allocator state): the carried facts at its return *)
Lemma swe_r3_after_rso : forall lyc Sc Wc memT mdT k O0 D Fr NB W2 mem2 md2,
CORE 3 lyc Sc Wc memT mdT k O0 D Fr NB ->
rec_repA B lyc Sc (rdW Wc memT) RAr3 (O0 ++ NB) ->
ajournal SEGS B SUP_WORKER_ENV_STK (spZ regs) FPw ly S W mem md [] lyc Sc W2 mem2 md2 (k + EV_REC_SHAPE_OF) ->
ajournal SEGS B REC_SHAPE_OF_STK (spZ regs + -64) [] lyc Sc Wc memT mdT [] lyc Sc W2 mem2 md2 EV_REC_SHAPE_OF ->
CORE 3 lyc Sc W2 mem2 md2 k O0 D Fr NB /\ rec_repA B lyc Sc (rdW W2 mem2) RAr3 (O0 ++ NB).
Proof.
intros lyc Sc Wc memT mdT k O0 D Fr NB W2 mem2 md2 HC HREPc HJ2 HJc.
unfold EV_REC_SHAPE_OF in HJ2, HJc. rewrite Z.add_0_r in HJ2.
destruct swe_sp_bounds as (Hsp & Hsp47 & _ & Hceil & HWS).
destruct HC as (HJ & Hk & HFR & HP0 & HP1 & HFrO & HDO & HO0 & HNBD & HNBl & HNBb & HMLE & HO0D).
pose proof (proj1 HJ) as HAR1.
pose proof HJc as (_ & _ & _ & _ & _ & _ & _ & _ & G1 & G2 & G3 & _).
assert (Hsc : ~ YI16.sink_open_fp []) by (apply sink_closed_pos; constructor).
assert (KB : forall q n i, In (q, n) (ablocks B lyc Sc) -> 0 <= i < n -> rdW W2 mem2 (q + i) = rdW Wc memT (q + i)).
{ intros q n i Hq Hi. destruct (al_blocks _ _ LAWS _ _ _ _ _ q n HAR1 Hq) as (_ & _ & _ & _ & _ & _ & Hn).
  pose proof (req_size_pos n ltac:(lia)) as [_ Hr].
  apply (G2 q n i Hq Hq ltac:(lia)). intros HF. exact (inFP_nil _ HF). }
assert (KG : forall a, in_recg a -> rdW W2 mem2 a = rdW Wc memT a).
{ intros a Ha. destruct (swe_rec_unowned_fp a Ha) as (Hi & Ho & He).
  apply (G3 a Hi Ho He). apply fp_spares_closed; [exact Hsc | intros HF; exact (inFP_nil _ HF)]. }
split.
- split; [exact HJ2|]. split; [exact Hk|].
  split.
  { apply (swe_frame_kept Wc W2 memT mem2 HFR). intros a Ha. apply G1; [lia | lia | intros HF; exact (inFP_nil _ HF)]. }
  split; [exact HP0|]. split; [exact HP1|].
  split; [exact HFrO|]. split; [exact HDO|]. split; [exact HO0|]. split; [exact HNBD|].
  split; [exact HNBl|]. split; [exact HNBb|]. split; [exact HMLE | exact HO0D].
- apply (rec_repA_kept B lyc Sc (rdW Wc memT) lyc Sc (rdW W2 mem2) _ _ HREPc).
  + exact (rec_repA_in B lyc Sc _ _ _ HREPc).
  + intros a Ha. apply KG. left. unfold REC_SIZE. exact Ha.
  + intros a Ha. apply KG. right. unfold SC_SIZE. exact Ha.
  + intros q n i Hq Hi. apply (KB q n i); [exact (rec_repA_in B lyc Sc _ _ _ HREPc _ Hq) | exact Hi].
Qed.

(* the post of the call from what answer gives: the statement's swe_Q and the journal's event count *)
Lemma swe_r3_post : forall lyc Sc (Wc : world SEGS) memc mdc k O0 D Fr NB old
  ly' S' (W' : world SEGS) (regs' : bvmap 5 word) mem' md' p1 p2 O',
CORE 3 lyc Sc Wc memc mdc k O0 D Fr NB ->
rec_repA B lyc Sc (rdW Wc memc) RAr3 (O0 ++ NB) ->
(old = 0 \/ exists m, In (old, m) (O0 ++ NB)) ->
ajournal SEGS B SUP_WORKER_ENV_STK (spZ regs) FPw ly S W mem md [] ly' S' W' mem' md' (k + EV_ANSWER) ->
getr regs' 10 = w64 p2 -> 4096 <= p2 < 2 ^ 64 -> p1 <> p2 ->
(forall pn, In pn (ablocks B lyc Sc) -> fst pn <> old ->
   pn <> (p1, Z.of_nat (length TTr3) + 1) /\ pn <> (p2, Z.of_nat (length TTr3) + 1)) ->
(forall pn, In pn (ablocks B ly' S') <->
   (In pn (ablocks B lyc Sc) /\ fst pn <> old) \/ pn = (p1, Z.of_nat (length TTr3) + 1) \/
   pn = (p2, Z.of_nat (length TTr3) + 1)) ->
rec_repA B ly' S' (rdW W' mem') (fst (rec_answer RAr3 (REC_WORKER_ENV, A3) SHPr3 true)) O' ->
(forall pn, In pn O' <-> (In pn (O0 ++ NB) /\ fst pn <> old) \/ pn = (p1, Z.of_nat (length TTr3) + 1)) ->
astr_atR (rdW W' mem') p2 TTr3 ->
blocks_bytes S' <= blocks_bytes Sc + LIVE_ANSWER TTr3 ->
mo_le MT Sc S' (XM_ANSWER MT TTr3) ->
ajournal SEGS B SUP_WORKER_ENV_STK (spZ regs) FPw ly S W mem md [] ly' S' W' mem' md' (EV_SUP_WORKER_ENV R) /\
QQr3 ly' S' W' regs' mem' md'.
Proof.
intros lyc Sc Wc memc mdc k O0 D Fr NB old ly' S' W' regs' mem' md' p1 p2 O'
  HC HREPc Hold HJ' Hr10 Hp2 Hp12 HG1 Hbl HREP' HO' Hstr Hbb' MLE.
pose proof HC as (HJ & Hk & HFR & HP0 & HP1 & HFrO & HDO & HO0 & HNBD & HNBl & HNBb & HMLE & HO0D). change (Z.of_nat 3) with 3 in Hk.
pose proof (proj1 HJ) as HAR. pose proof (proj1 HJ') as HAR'.
set (n := Z.of_nat (length TTr3) + 1) in *.
assert (HinD : forall pn, In pn D -> In pn (ablocks B lyc Sc))
  by (intros pn H; apply (Permutation_in _ (Permutation_sym HP1)); apply in_or_app; left; exact H).
assert (HD0 : forall pn, In pn D -> In pn (ablocks B ly S))
  by (intros pn H; apply (Permutation_in _ (Permutation_sym HP0)); apply in_or_app; left; exact H).
assert (Hentry : forall pn, In pn (ablocks B ly S) -> ~ In pn (ablocks B lyc Sc) -> In pn O).
{ intros pn H Hn. apply (Permutation_in _ HP0) in H. apply in_app_iff in H as [Hd|Hf];
  [exfalso; exact (Hn (HinD _ Hd)) | exact (HFrO _ Hf)]. }
assert (HOa : forall pn, In pn (O0 ++ NB) -> In pn O \/ ~ In pn (ablocks B ly S)).
{ intros pn H. apply in_app_iff in H as [Ho|Hn]; [left; exact (HO0 _ Ho)|].
  destruct (in_dec swe_r3_pdec pn (ablocks B ly S)) as [H0|H0]; [left | right; exact H0].
  apply (Permutation_in _ HP0) in H0. apply in_app_iff in H0 as [Hd|Hf]; [exfalso; exact (HNBD _ Hn Hd) | exact (HFrO _ Hf)]. }
assert (Hsz : forall pn, In pn (ablocks B lyc Sc) -> 0 <= snd pn /\ 4096 <= fst pn).
{ intros [b m] H. destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR H) as (_ & H4096 & _ & _ & _ & _ & Hm). cbn [fst snd]. lia. }
assert (Hn0 : 0 <= n) by (unfold n; lia).
assert (Hp2in : In (p2, n) (ablocks B ly' S')) by (apply Hbl; right; right; reflexivity).
assert (HoldB : forall pn, In pn (ablocks B lyc Sc) -> fst pn = old -> In pn (O0 ++ NB))
  by exact (swe_r3_old_blk lyc Sc Wc memc mdc (O0 ++ NB) old HAR (rec_repA_in B lyc Sc _ _ _ HREPc) Hold).
assert (HDold : forall pn, In pn D -> ~ In pn O -> fst pn <> old).
{ intros pn Hd HnO Ef. apply (HoldB pn (HinD _ Hd)) in Ef.
  apply in_app_iff in Ef as [Ho|Hn]; [exact (HnO (HO0 _ Ho)) | exact (HNBD _ Hn Hd)]. }
assert (Hsep' : forall pn, In pn (ablocks B lyc Sc) -> fst pn <> old ->
  In pn (ablocks B ly' S') /\ iv_apart (fst pn) (snd pn) p2 n).
{ intros [b m] H Hne. assert (H' : In (b, m) (ablocks B ly' S')) by (apply Hbl; left; split; assumption).
  split; [exact H'|].
  assert (Hne2 : (b, m) <> (p2, n)) by exact (proj2 (HG1 _ H Hne)).
  pose proof (sep_blocks SEGS B LAWS ly' S' W' mem' md' b m p2 n HAR' H' Hp2in Hne2) as Hd.
  destruct (Hsz _ H) as [Hm _]. cbn [fst snd] in Hm.
  pose proof (req_size_pos m Hm) as [_ Hr1]. pose proof (req_size_pos n Hn0) as [_ Hr2].
  unfold zdisjoint in Hd. cbn [fst snd] in Hd |- *. unfold iv_apart. lia. }
split.
- eapply (ajournal_mono_k SEGS B); [exact HJ'|]. unfold EV_SUP_WORKER_ENV, EV_XSTRDUP. lia.
- exists (fst (rec_answer RAr3 (REC_WORKER_ENV, A3) SHPr3 true)), TTr3, p2, O'.
  split; [rewrite swe_r3_vb; apply surjective_pairing|].
  split; [exact Hr10|]. split; [exact Hp2|]. split; [exact HREP'|].
  split.
  { intros pn Hpn. apply HO' in Hpn as [(Hin & _) | ->]; [exact (HOa _ Hin)|].
    destruct (in_dec swe_r3_pdec (p1, n) (ablocks B lyc Sc)) as [Hc|Hc].
    - destruct (Z.eq_dec p1 old) as [E|Ne].
      + apply HOa. apply HoldB; [exact Hc | exact E].
      + exfalso. exact (proj1 (HG1 _ Hc Ne) eq_refl).
    - destruct (in_dec swe_r3_pdec (p1, n) (ablocks B ly S)) as [H0|H0]; [left; exact (Hentry _ H0 Hc) | right; exact H0]. }
  split; [exact Hp2in|].
  split.
  { intros pn H0 HnO. apply (Permutation_in _ HP0) in H0. apply in_app_iff in H0 as [Hd|Hf]; [|exfalso; exact (HnO (HFrO _ Hf))].
    exact (proj2 (HG1 _ (HinD _ Hd) (HDold _ Hd HnO))). }
  split.
  { intros Hin. apply in_map_iff in Hin as ([b m] & Ef & Hpn). cbn [fst] in Ef. subst b.
    apply HO' in Hpn as [(Hin & Hne) | E].
    - pose proof (rec_repA_in B lyc Sc _ _ _ HREPc _ Hin) as Hc.
      assert (Hc' : In (p2, m) (ablocks B ly' S')) by (apply Hbl; left; split; [exact Hc | exact Hne]).
      assert (Hne2 : (p2, m) <> (p2, n)) by exact (proj2 (HG1 _ Hc Hne)).
      pose proof (sep_blocks SEGS B LAWS ly' S' W' mem' md' p2 m p2 n HAR' Hc' Hp2in Hne2) as Hdj.
      destruct (Hsz _ Hc) as [Hm _]. cbn [snd] in Hm.
      pose proof (req_size_pos m Hm) as [Hr1 _]. pose proof (req_size_pos n Hn0) as [Hr2 _].
      unfold zdisjoint in Hdj. cbn [fst snd] in Hdj. lia.
    - injection E as E1 _. exact (Hp12 (eq_sym E1)). }
  split; [exact Hstr|].
  split.
  { intros pn H0 HnO. apply (Permutation_in _ HP0) in H0. apply in_app_iff in H0 as [Hd|Hf]; [|exfalso; exact (HnO (HFrO _ Hf))].
    exact (Hsep' _ (HinD _ Hd) (HDold _ Hd HnO)). }
  split.
  { intros pn H. apply Hbl in H as [(Hin & Hne) | [-> | ->]].
    - destruct (in_dec swe_r3_pdec pn (O0 ++ NB)) as [HinO|HnO].
      + right; left. apply HO'. left. split; assumption.
      + left. apply (Permutation_in _ HP1) in Hin. apply in_app_iff in Hin as [Hd|Hn].
        * split; [exact (HD0 _ Hd)|]. intros HO. apply HnO. apply in_or_app. left. exact (HDO _ Hd HO).
        * exfalso. apply HnO. apply in_or_app. right. exact Hn.
    - right; left. apply HO'. right. reflexivity.
    - right; right. reflexivity. }
  split.
  { assert (HbD : 0 <= bsum Fr).
    { apply (swe_bsum_nonneg ly S W mem md Fr swe_AR0). intros pn Hpn.
      apply (Permutation_in _ (Permutation_sym HP0)). apply in_or_app. right. exact Hpn. }
    assert (Hbb : blocks_bytes Sc + bsum Fr = blocks_bytes S + bsum NB).
    { rewrite (blocks_bytes_bsum B lyc Sc), (blocks_bytes_bsum B ly S), (bsum_perm _ _ HP0), (bsum_perm _ _ HP1), !bsum_app. lia. }
    rewrite HNBb in Hbb. unfold swe_live, swe_A3 in Hbb. cbn [firstn swe_sum] in Hbb.
    unfold LIVE_SUP_WORKER_ENV. rewrite swe_r3_vb. lia. }
  replace (XM_SUP_WORKER_ENV MT R format cpus nice) with (XMs 3 + XM_ANSWER MT TTr3).
  + exact (mle_station MT S Sc S' _ _ MTL HMLE MLE).
  + unfold XM_SUP_WORKER_ENV. rewrite swe_r3_vb. unfold swe_xm, swe_A3. cbn [firstn swe_sum]. lia.
Qed.

(* the kept registers of the first run *)
Definition swe_r3_kept : list (bv 5) := map (Z_to_bv 5) [2;3;4;8;23;24;25;26;27].
Lemma swe_r3_thru : forall (regs1 regsT regs2 : bvmap 5 word) r,
(forall rr, In rr swe_r3_kept -> getr regsT rr = getr regs1 rr) -> aregs_preserved regsT regs2 ->
In r [2;3;4;8;23;24;25;26;27] -> getr regs2 (Z_to_bv 5 r) = getr regs1 (Z_to_bv 5 r).
Proof.
intros regs1 regsT regs2 r KR HP Hin. rewrite (HP r); [apply KR; unfold swe_r3_kept; apply in_map; exact Hin|].
unfold acallee_saved. cbn in Hin. lia.
Qed.
Definition swe_r3_kept4 : list (bv 5) := map (Z_to_bv 5) [3;4;23;24;25;26;27].

(* 0x8c204, back from rec_shape_of: a1 := the shape, a0 := the slot, a2 := 1, the frame restored, `j answer` *)
Lemma swe_r3_tail : forall ly2 S2 (W2 : world SEGS) (regs2 : bvmap 5 word) mem2 md2 k O0 D Fr NB q,
CORE 3 ly2 S2 W2 mem2 md2 k O0 D Fr NB ->
rec_repA B ly2 S2 (rdW W2 mem2) RAr3 (O0 ++ NB) ->
getr regs2 (Z_to_bv 5 2) = w64 (spZ regs - 64) -> getr regs2 (Z_to_bv 5 3) = w64 (as_gp B) ->
getr regs2 (Z_to_bv 5 4) = w64 (as_tp B) -> getr regs2 (Z_to_bv 5 8) = w64 (swe_c (R:=R)) ->
(forall r, 23 <= r <= 27 -> getr regs2 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) ->
getr regs2 (Z_to_bv 5 10) = w64 q -> 0 <= q < 2 ^ 64 ->
astr_argA B ly2 S2 (rdW W2 mem2) (in_roP SEGS RLO RHI) (O0 ++ NB) q (Some SHPr3) ->
SRr SEGS W2 (mkCfg (mkst regs2 (Z_to_bv 64 (BASE + SWE_R4)) mem2 (seg_rom SEGS)) md2) POSTr3.
Proof.
intros ly2 S2 W2 regs2 mem2 md2 k O0 D Fr NB q HC HREP2 R2 R3 R4 R8 R23 Hq10 Hqb HqA.
pose proof HC as (HJ & Hk & HFR & HP0 & HP1 & HFrO & HDO & HO0 & HNBD & HNBl & HNBb & HMLE & HO0D).
pose proof (proj1 HJ) as HAR.
destruct swe_sp_mid as (Hsp & Hsp16 & Hceil).
destruct swe_sp_bounds as (Hsp1 & Hsp47 & _ & Hceil1 & HWS).
destruct (swe_slot_bounds _ swe_c_ok) as [Hcb _].
pose proof asan_consts as (C1 & _).
assert (Esp : spZ regs2 = spZ regs - 64)
  by (unfold spZ at 1; swe_z5; rewrite R2; unfold w64; rewrite unsigned_lit_small by lia; reflexivity).
pose proof (swe_env_mid regs2) as HE. pose proof HE as (HEI & E2 & ESB & EN & EC).
assert (B2 : base_val (Eimg (Ereg regs2 EXr3)) (Some 2%nat) = spZ regs2)
  by (cbn [base_val]; rewrite E2; apply unsigned_lit_small; lia).
assert (RS : YP09.region_ok SEGS (Eimg (Ereg regs2 EXr3)) (mrestrict (w_H W2) mem2) swe_stack_mid).
{ unfold YP09.region_ok, swe_stack_mid. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  rewrite B2. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  exact (swe_r3_frame_ok W2 mem2 regs2 HFR Esp). }
destruct (swe_seed_rs ly2 S2 W2 mem2 md2 regs2 (Eimg (Ereg regs2 EXr3)) (spZ regs2) (Z.of_nat (swe_n (R:=R))) SWE_R4
  [swe_stack_mid] HAR HE
  ltac:(rewrite Esp; exact Hsp) ltac:(rewrite Esp; exact Hsp16) ltac:(pose proof swe_n_le; lia)
  (regs_ok_Eimg_Ereg regs2 _) ltac:(vm_compute; reflexivity)
  ltac:(apply Forall_cons; [exact RS | apply Forall_nil])
  ltac:(apply pairwise_disjoint_of_extents; exact (conj I I))) as [HS SHOK].
paj_run_tok RUN HS HJ SHOK swe_Bspan.
{ cbn [ss_mem]. apply (YCbq.awr_ok_cons_ro SEGS B); [cbn; lia | apply (YCbq.awr_ok_nil SEGS B)]. }
lazymatch goal with |- SRr _ _ (mkCfg _ ?mm) _ => set (mdv4 := mm) in *; clearbody mdv4 end.
pmkst HS.
assert (HAE : env_agree 32 (Ereg regs2 EXr3) (Eimg (Ereg regs2 EXr3)))
  by (split; [intros nn Hnn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
pose proof (regs_kept_of_st_ok SEGS _ _ _ regs2 EXr3 swe_r3_kept4 HS HAE ltac:(vm_compute; reflexivity)) as KR.
cbn [ms_regs restrict] in KR.
assert (KRZ : forall r, In r [3;4;23;24;25;26;27] -> getr (ms_regs ms) (Z_to_bv 5 r) = getr regs2 (Z_to_bv 5 r))
  by (intros r Hr; apply KR; unfold swe_r3_kept4; apply in_map; exact Hr).
clear KR.
sreg HS (Z_to_bv 5 1) Q1. rewrite (swe_r3_atom regs2 35 0 1 eq_refl eq_refl) in Q1.
sreg HS (Z_to_bv 5 2) Q2. rewrite E2, unsigned_lit_small, Esp in Q2 by lia. replace (spZ regs - 64 + 64) with (spZ regs) in Q2 by lia.
sreg HS (Z_to_bv 5 8) Q8. rewrite (swe_r3_atom regs2 36 1 8 eq_refl eq_refl) in Q8.
sreg HS (Z_to_bv 5 9) Q9. rewrite (swe_r3_atom regs2 37 2 9 eq_refl eq_refl) in Q9.
sreg HS (Z_to_bv 5 18) Q18. rewrite (swe_r3_atom regs2 38 3 18 eq_refl eq_refl) in Q18.
sreg HS (Z_to_bv 5 19) Q19. rewrite (swe_r3_atom regs2 39 4 19 eq_refl eq_refl) in Q19.
sreg HS (Z_to_bv 5 20) Q20. rewrite (swe_r3_atom regs2 40 5 20 eq_refl eq_refl) in Q20.
sreg HS (Z_to_bv 5 21) Q21. rewrite (swe_r3_atom regs2 41 6 21 eq_refl eq_refl) in Q21.
sreg HS (Z_to_bv 5 22) Q22. rewrite (swe_r3_atom regs2 42 7 22 eq_refl eq_refl) in Q22.
sreg HS (Z_to_bv 5 10) Q10. rewrite (ew_Eimg_Ereg_nat regs2 EXr3 8 (Z_to_bv 5 8) eq_refl), R8 in Q10.
sreg HS (Z_to_bv 5 11) Q11. rewrite (ew_Eimg_Ereg_nat regs2 EXr3 10 (Z_to_bv 5 10) eq_refl), Hq10 in Q11.
sreg HS (Z_to_bv 5 12) Q12.
rewrite swe_r3_sig_ans.
set (regsc := ms_regs ms) in *. set (memc := ms_mem ms) in *.
assert (KM : forall a, 0 <= a < 2 ^ 64 -> rdW W2 memc a = rdW W2 mem2 a).
{ intros a Ha. apply (kept_of_frame _ _ (w_H W2) mem2 memc (fun _ => False) HFr); [|exact Ha|intros H; exact H].
  intros b wlo whi a' Hin Ha'. unfold swe_stack_mid in Hin. cbn in Hin.
  destruct Hin as [E1|[]]. injection E1. intros. subst b wlo whi. lia. }
pose proof (swe_core_mem 3 ly2 S2 W2 mem2 md2 k O0 D Fr NB memc _ HC HJ KM) as HCt.
pose proof (proj1 HJ) as HARt.
assert (HREPt : rec_repA B ly2 S2 (rdW W2 memc) RAr3 (O0 ++ NB)).
{ apply (rec_repA_kept B ly2 S2 (rdW W2 mem2) ly2 S2 (rdW W2 memc) _ _ HREP2).
  - exact (rec_repA_in B ly2 S2 _ _ _ HREP2).
  - intros a Ha. apply KM. unfold A_G_REC in Ha. lia.
  - intros a Ha. apply KM. unfold A_REC_SPILL in Ha. lia.
  - intros b n i Hb Hi. apply KM.
    pose proof (rec_repA_in B ly2 S2 _ _ _ HREP2 _ Hb) as Hb2.
    destruct (al_blocks _ _ LAWS _ _ _ _ _ b n HAR Hb2) as (_ & Hb4096 & Hbc & _).
    pose proof (req_size_pos n ltac:(lia)) as [_ Hr]. lia. }
pose proof (swe_r3_arg_kept ly2 S2 W2 mem2 md2 (rdW W2 mem2) (rdW W2 memc) (O0 ++ NB) q SHPr3 HAR (proj1 Hqb) KM HqA) as HqAt.
destruct (swe_r3_old _ _ _ _ _ HREPt) as (old & Hold & Hold').
assert (Hold64 : 0 <= old < 2 ^ 64).
{ destruct Hold' as [E0 | (m & Hm)]; [rewrite E0; lia|].
  pose proof (rec_repA_in B ly2 S2 _ _ _ HREPt _ Hm) as Hm2.
  destruct (al_blocks _ _ LAWS _ _ _ _ _ old m HARt Hm2) as (_ & H4096 & Hc & _ & _ & _ & Hm0).
  pose proof (req_size_pos m ltac:(lia)) as [Hr _]. lia. }
assert (Hc64 : 0 <= swe_c (R:=R) < 2 ^ 64) by (unfold A_G_REC, OFF_CALLS, A_REC_SPILL in Hcb; lia).
assert (HspC : spZ regsc = spZ regs) by (unfold spZ at 1; swe_z5; rewrite Q2; apply unsigned_lit_small; lia).
assert (HPc : aregs_preserved regs regsc).
{ assert (G : forall r, In r [2;3;4;8;9;18;19;20;21;22;23;24;25;26;27] -> getr regsc (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)).
  { pose proof HPRE as (_ & _ & _ & Hgp & Htp & _). swe_z5.
    intros r Hr. cbn [In] in Hr.
    destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]]].
    - rewrite Q2. unfold spZ. swe_z5. apply Z_to_bv_bv_unsigned.
    - rewrite (KRZ 3 ltac:(cbn; tauto)), R3, Hgp. reflexivity.
    - rewrite (KRZ 4 ltac:(cbn; tauto)), R4, Htp. reflexivity.
    - exact Q8.
    - exact Q9.
    - exact Q18.
    - exact Q19.
    - exact Q20.
    - exact Q21.
    - exact Q22.
    - rewrite (KRZ 23 ltac:(cbn; tauto)). apply R23. lia.
    - rewrite (KRZ 24 ltac:(cbn; tauto)). apply R23. lia.
    - rewrite (KRZ 25 ltac:(cbn; tauto)). apply R23. lia.
    - rewrite (KRZ 26 ltac:(cbn; tauto)). apply R23. lia.
    - rewrite (KRZ 27 ltac:(cbn; tauto)). apply R23. lia. }
  intros r Hr. apply G. unfold acallee_saved in Hr. cbn [In]. lia. }
pose proof HPRE as (_ & Hra & Hra4 & Hgp & Htp & Hstk & _ & Hch & _).
pose proof Hstk as (_ & _ & _ & _ & _ & Hhi47 & _ & _ & Htop).
destruct (swe_r3_budget ly2 S2 W2 memc _ k O0 D Fr NB HCt) as (HEVa & HLIVEa & HMOKa).
pose proof (swe_rodata_now 3 ly2 S2 W2 memc _ k O0 D Fr NB HCt) as HRODt.
pose proof (swe_ro_now 3 ly2 S2 W2 memc _ k O0 D Fr NB HCt) as HROt.
eapply SRr_mono.
{ eapply (cl_callS_wideF B LAWS W2 regsc memc _ SUP_WORKER_ENV_STK (spZ regs) FPw ly S W mem md [] ly2 S2 _ k
     ANSWER_STK (FP1r3 old (O0 ++ NB)) EV_ANSWER 0 (getr regs 1) ch
     (fun ly' S' W' regs' mem' md' => exists p1 p2 O',
       let n := Z.of_nat (length TTr3) + 1 in
       getr regs' 10 = w64 p2 /\ 4096 <= p2 < 2 ^ 64 /\ p1 <> p2 /\
       (forall pn, In pn (ablocks B ly2 S2) -> fst pn <> old -> pn <> (p1, n) /\ pn <> (p2, n)) /\
       (forall pn, In pn (ablocks B ly' S') <->
         (In pn (ablocks B ly2 S2) /\ fst pn <> old) \/ pn = (p1, n) \/ pn = (p2, n)) /\
       rec_repA B ly' S' (rdW W' mem') (fst (rec_answer RAr3 (REC_WORKER_ENV, A3) SHPr3 true)) O' /\
       (forall pn, In pn O' <-> (In pn (O0 ++ NB) /\ fst pn <> old) \/ pn = (p1, n)) /\
       astr_atR (rdW W' mem') p2 TTr3 /\
       blocks_bytes S' <= blocks_bytes S2 + LIVE_ANSWER TTr3 /\
       mo_le MT S2 S' (XM_ANSWER MT TTr3)) HJ).
  - rewrite HspC. lia.
  - reflexivity.
  - lia.
  - apply Z.leb_le. vm_compute. reflexivity.
  - apply Z.leb_le. vm_compute. reflexivity.
  - swe_z5. rewrite (KRZ 3 ltac:(cbn; tauto)). exact R3.
  - swe_z5. rewrite (KRZ 4 ltac:(cbn; tauto)). exact R4.
  - swe_z5. exact Q1.
  - exact Hra.
  - exact Hra4.
  - assert (Hs0 : s0Z regsc = s0Z regs) by (unfold s0Z; swe_z5; rewrite Q8; reflexivity).
    rewrite Hs0, Z.add_0_r.
    pose proof HJ as (_ & Hly & _). pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _).
    apply (achain_ly_top ly ly2 _ _ _ _ Etop).
    apply (achain_kept ly (rdW W mem) (rdW W2 memc) (spZ regs) (s0Z regs) ch (spZ regs) Hch ltac:(lia) ltac:(lia)).
    intros a Ha. pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & F1 & _).
    apply F1; [lia | lia | apply swe_r3_notFP_hi; lia].
  - intros HPRE1. eapply SRr_mono.
    { apply (TANSWER fx ly2 S2 W2 regsc memc _ ch (swe_c (R:=R)) q old (REC_WORKER_ENV, A3) SHPr3 true RAr3 (O0 ++ NB) HPRE1).
      - exact HFRM.
      - pose proof HJ as (_ & _ & _ & _ & _ & Hfrs & _). rewrite Hfrs. cbn [app]. exact HFR8.
      - exact HRODt.
      - exact HROt.
      - swe_z5. exact Q10.
      - exact Hc64.
      - swe_z5. exact Q11.
      - exact Hqb.
      - swe_z5. rewrite Q12. first [reflexivity | vm_compute; reflexivity | rewrite unsigned_lit_small by lia; reflexivity].
      - exact HREPt.
      - exact Hold.
      - exact Hold64.
      - intros _. split; [exact HqAt | exact swe_r3_fits].
      - intros _ _. exact swe_r3_slot.
      - exact HEVa.
      - exact HLIVEa.
      - exact HMOKa. }
    cbv beta. intros W' c' _ (fx' & ly' & S' & regs' & mem' & md' & -> & Hf1 & Hf2 & HJ' & HP' & HK').
    exists fx', ly', S', regs', mem', md'. swe_z5. rewrite Q1. split; [reflexivity|]. split; [exact Hf1|]. split; [exact Hf2|].
    split; [exact HJ'|]. split; [exact HP' | exact HK'].
  - intros a Ha. exact (swe_r3_fp ly2 S2 W2 memc _ k O0 D Fr NB old a HCt HREPt Ha).
  - intros ly4 S4 W4 regs4 mem4 md4 _ a Ha Hw _. exfalso.
    pose proof (swe_r3_fp_low ly2 S2 W2 memc _ (O0 ++ NB) old a HARt (rec_repA_in B ly2 S2 _ _ _ HREPt) Ha). lia. }
cbv beta. intros W3 c3 _ (fx3 & ly3 & S3 & regs3 & mem3 & md3 & Hfx3 & -> & HJ3 & _ & HP3 & HK3).
destruct HK3 as (p1 & p2 & O' & HK). cbv zeta in HK.
destruct HK as (Hk10 & Hp2 & Hp12 & HG1 & Hbl & HREP' & HO' & Hstr' & Hbb' & MLE').
destruct (swe_r3_post ly2 S2 W2 memc _ k O0 D Fr NB old ly3 S3 W3 regs3 mem3 md3 p1 p2 O' HCt HREPt Hold' HJ3
  Hk10 Hp2 Hp12 HG1 Hbl HREP' HO' Hstr' Hbb' MLE') as [HJF HQ].
unfold swe_POST.
exact (apost_baseF_intro (fx := fx) SEGS fx3 _ _ _ _ _ _ _ _ _ _ _ _ ly3 S3 regs3 mem3 md3 Hfx3 HJF
  (aregs_preserved_trans _ _ _ HPc HP3) HQ).
Qed.

(* 0x8c1c4 (SWE_R3): nargs := 3, args[2] := p, then a0 := "worker_env", a1 := 10, jal rec_shape_of *)
Lemma swe_R3_ok : RSr3 3 SWE_R3.
Proof.
intros lyc Sc Wc regs1 memc mdc k O0 D Fr NB p x HC HRB HRC HRR Hp10 HREPc Hp4096 Hstrp Hfresh.
unfold swe_at.
pose proof HC as (HJ & Hk & HFR & HP0 & HP1 & HFrO & HDO & HO0 & HNBD & HNBl & HNBb & HMLE & HO0D).
pose proof HRB as (R2 & R3 & R4 & R8 & R21 & R23). pose proof HRC as (R18 & R22). cbn [swe_R_regs] in HRR. rename HRR into R20.
pose proof (proj1 HJ) as HAR.
destruct swe_sp_mid as (Hsp & Hsp16 & Hceil).
destruct swe_sp_bounds as (Hsp1 & Hsp47 & _ & Hceil1 & HWS).
destruct (swe_slot_bounds _ swe_c_ok) as [Hcb Hc8].
pose proof asan_consts as (C1 & _).
assert (Esp : spZ regs1 = spZ regs - 64) by (unfold spZ; rewrite R2; unfold w64; rewrite unsigned_lit_small by lia; reflexivity).
assert (Hpin : In (p, Z.of_nat (length x) + 1) (ablocks B lyc Sc))
  by (apply (Permutation_in _ (Permutation_sym HP1)); apply in_or_app; right; apply in_or_app; right; left; reflexivity).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hpin) as (_ & _ & Hpceil & _).
pose proof (req_size_pos (Z.of_nat (length x) + 1) ltac:(lia)) as [_ Hpr].
set (Ex := EXr3) in *.
pose proof (swe_env_mid regs1) as HE. fold Ex in HE. pose proof HE as (HEI & E2 & ESB & EN & EC).
pose proof (swe_rep_nargs lyc Sc (rdW Wc memc) _ _ HREPc) as HNA. cbn [length firstn Nat.sub swe_A3] in HNA.
assert (HCK : YP09.chunk_ok SEGS (Eimg (Ereg regs1 Ex)) (mrestrict (w_H Wc) memc) (swe_c (R:=R)) (YP09.mkChunk 4 (CVal 4 (SLit 2))))
  by (apply (chunk_ok_val SEGS _ _ _ 4 4%N (SLit 2) 2); [reflexivity | lia | lia | exact (val_mem_view SEGS _ _ _ _ _ HNA)]).
assert (RN : YP09.region_ok SEGS (Eimg (Ereg regs1 Ex)) (mrestrict (w_H Wc) memc) (swe_regN 2)).
{ unfold swe_regN. apply (swe_slot_rok lyc Sc Wc memc mdc (Eimg (Ereg regs1 Ex)) (spZ regs1) (Z.of_nat (swe_n (R:=R))));
  [exact HAR | exact HE | lia | unfold CALL_SIZE; lia | lia | unfold CALL_SIZE; lia | apply Forall_cons; [exact HCK | apply Forall_nil]]. }
assert (RA : YP09.region_ok SEGS (Eimg (Ereg regs1 Ex)) (mrestrict (w_H Wc) memc) (swe_regA 2)).
{ unfold swe_regA. apply (swe_slot_rok lyc Sc Wc memc mdc (Eimg (Ereg regs1 Ex)) (spZ regs1) (Z.of_nat (swe_n (R:=R))));
  [exact HAR | exact HE | lia | unfold CALL_SIZE; lia | lia | unfold CALL_SIZE; lia | apply Forall_nil]. }
destruct (swe_seed_rs lyc Sc Wc memc mdc regs1 (Eimg (Ereg regs1 Ex)) (spZ regs1) (Z.of_nat (swe_n (R:=R))) SWE_R3 [swe_regN 2; swe_regA 2] HAR HE
  ltac:(rewrite Esp; exact Hsp) ltac:(rewrite Esp; exact Hsp16) ltac:(pose proof swe_n_le; lia)
  (regs_ok_Eimg_Ereg regs1 _) ltac:(vm_compute; reflexivity)
  ltac:(apply Forall_cons; [exact RN | apply Forall_cons; [exact RA | apply Forall_nil]])
  ltac:(apply pairwise_disjoint_of_extents; unfold swe_regN, swe_regA, extent_of_region;
        cbn [map YP09.r_base YP09.r_lo YP09.r_hi]; cbn [zpairwise_disjoint zall_disjoint]; unfold zdisj; cbn [fst snd];
        repeat split; lia)) as [HS SHOK].
assert (U34 : bv_unsigned (ew (Eimg (Ereg regs1 Ex)) SW_C) = swe_c (R:=R))
  by (rewrite EC; apply unsigned_lit_small; unfold A_G_REC, A_REC_SPILL, OFF_CALLS in *; lia).
assert (U34n : bv_unsigned (ew (Eimg (Ereg regs1 Ex)) 34%nat) = swe_c (R:=R)) by exact U34.
assert (U32 : bv_unsigned (ew (Eimg (Ereg regs1 Ex)) SW_SB) = SB) by (rewrite ESB; apply unsigned_lit_small; unfold SB; lia).
swe_z5.
pose proof (st_ok_pi_set_reg _ _ _ (Z_to_bv 5 21) (SOff SW_SB 0) HS ltac:(discriminate)
  ltac:(cbn [ms_regs restrict mkst sv_denot]; rewrite U32, Z.add_0_r; exact R21)) as HS2. clear HS.
pose proof (st_ok_pi_set_reg _ _ _ (Z_to_bv 5 18) (SOff SW_C 4) HS2 ltac:(discriminate)
  ltac:(cbn [ms_regs restrict mkst sv_denot]; rewrite U34; exact R18)) as HS3. clear HS2.
pose proof (st_ok_pi_set_reg _ _ _ (Z_to_bv 5 20) (SOff SW_C 8) HS3 ltac:(discriminate)
  ltac:(cbn [ms_regs restrict mkst sv_denot]; rewrite U34; exact R20)) as HS4. clear HS3.
pose proof (st_ok_pi_set_reg _ _ _ (Z_to_bv 5 22) (SAlu ALU_ADD (SAlu ALU_SRL (SOff SW_C 4) (SLit 3)) (SOff SW_SB 0)) HS4 ltac:(discriminate)
  ltac:(cbn [ms_regs restrict mkst]; rewrite (denot_shx _ SW_C SW_SB 4 (swe_c (R:=R)) SB EC ESB) by (unfold SB, A_G_REC, A_REC_SPILL, OFF_CALLS in *; lia);
        exact R22)) as HS. clear HS4.
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS.
paj_run_tok RUN HS HJ SHOK swe_Bspan.
{ cbn [ss_mem]. apply swe_awr_slots; [exact EC|].
  apply Forall_cons; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi swe_regN swe_regA]; unfold CALL_SIZE; split; [reflexivity | lia]|].
  apply Forall_cons; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi swe_regN swe_regA]; unfold CALL_SIZE; split; [reflexivity | lia]|]. apply Forall_nil. }
lazymatch goal with |- SRr _ _ (mkCfg _ ?mm) _ => set (mdv3 := mm) in *; clearbody mdv3 end.
pmkst HS.
assert (HAE : env_agree 32 (Ereg regs1 Ex) (Eimg (Ereg regs1 Ex)))
  by (split; [intros nn Hnn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
pose proof (regs_kept_of_st_ok SEGS _ _ _ regs1 Ex swe_r3_kept HS HAE ltac:(vm_compute; reflexivity)) as KR.
cbn [ms_regs restrict] in KR.
sreg HS (Z_to_bv 5 10) Q10. change 311%nat with SW_VERB in Q10.
rewrite (img_env_atomP _ SW_VERB HEI ltac:(unfold SW_VERB, A_OBJ, A_TEXT, A_LIM; lia)), (swe_verb_val VOBJS) in Q10.
sreg HS (Z_to_bv 5 11) Q11. sreg HS (Z_to_bv 5 1) Q1. rewrite (img_env_codeptr _ HEI) in Q1.
pose proof (st_ok_region_nth _ _ _ 0 (swe_regN 3) HS eq_refl) as RG0.
pose proof (st_ok_region_nth _ _ _ 1 (YP09.mkRegion (Some SW_C) 24 32 24 32 [YP09.mkChunk 24 (CVal 8 (SOff 10 0))]) HS eq_refl) as RG1.
cbn [ms_mem restrict] in RG0, RG1. unfold swe_regN in RG0.
rewrite swe_r3_sig_rso.
set (regsT := ms_regs ms) in *. set (memT := ms_mem ms) in *.
assert (KM : forall a, 0 <= a < 2 ^ 64 -> ~ (swe_c (R:=R) + 4 <= a < swe_c (R:=R) + 8) ->
  ~ (swe_c (R:=R) + 8 + 8 * Z.of_nat (3 - 1) <= a < swe_c (R:=R) + 16 + 8 * Z.of_nat (3 - 1)) -> rdW Wc memT a = rdW Wc memc a).
{ intros a Ha H1 H2.
  apply (kept_of_frame _ _ (w_H Wc) memc memT
    (fun a => (swe_c (R:=R) + 4 <= a < swe_c (R:=R) + 8) \/ (swe_c (R:=R) + 24 <= a < swe_c (R:=R) + 32)) HFr);
    [|exact Ha| cbv beta; change (Z.of_nat (3 - 1)) with 2 in H2; lia].
  intros b wlo whi a' Hin Ha'. unfold swe_regN, swe_regA in Hin. cbn in Hin. cbv beta.
  destruct Hin as [E1|[E1|[]]]; injection E1; intros; subst b wlo whi; cbn [base_val] in Ha';
  first [rewrite U34n in Ha' | rewrite U34 in Ha']; lia. }
pose proof (field_of_region _ _ 34%nat (swe_c (R:=R)) _ 4 8 4 8 4 4%N (SLit 3) 3 RG0 U34n (or_introl eq_refl) eq_refl
  ltac:(cbn; lia) ltac:(cbn; lia)) as HV3.
assert (Hden : sv_denot (Eimg (Ereg regs1 Ex)) (SOff 10 0) = Z_to_bv 64 p).
{ cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. rewrite (ew_Eimg_Ereg_nat regs1 Ex 10 (Z_to_bv 5 10) eq_refl). exact Hp10. }
pose proof (field_of_region _ _ 34%nat (swe_c (R:=R)) _ 24 32 24 32 24 8%N (SOff 10 0) p RG1 U34n (or_introl eq_refl) Hden
  ltac:(rewrite swe_pow8; lia) ltac:(cbn; lia)) as HVp.
assert (HN3 : aval_mem (rdW Wc memT) (swe_c (R:=R) + 4) 4 (Z.of_nat 3)) by exact (aval_mem_view SEGS _ _ _ _ _ HV3).
assert (HA3 : aval_mem (rdW Wc memT) (swe_c (R:=R) + 8 + 8 * Z.of_nat (3 - 1)) 8 p).
{ replace (swe_c (R:=R) + 8 + 8 * Z.of_nat (3 - 1)) with (swe_c (R:=R) + 24) by (change (Z.of_nat (3 - 1)) with 2; lia).
  exact (aval_mem_view SEGS _ _ _ _ _ HVp). }
destruct (swe_R_to_X 3 lyc Sc Wc memc mdc k O0 D Fr NB p memT _ ltac:(lia) HC HREPc Hp4096 Hfresh Hstrp HJ KM HN3 HA3)
  as [HC3 HREP3].
change (firstn 3 (swe_A3 (format:=format) (cpus:=cpus) (nice:=nice))) with (swe_A3 (format:=format) (cpus:=cpus) (nice:=nice)) in HREP3.
pose proof (swe_rodata_now 3 lyc Sc Wc memT _ k O0 D Fr _ HC3) as HRODT.
pose proof (swe_ro_now 3 lyc Sc Wc memT _ k O0 D Fr _ HC3) as HROT.
assert (HspT : spZ regsT = spZ regs + -64).
{ unfold spZ at 1. swe_z5. rewrite (KR (Z_to_bv 5 2) ltac:(unfold swe_r3_kept; apply in_map; cbn; tauto)), R2. unfold w64.
  rewrite unsigned_lit_small by lia. lia. }
pose proof pa_base_lo as HBLO. pose proof pa_B_ok as HBOK.
change (Z.of_nat 3) with 3 in Hk.
eapply SRr_bind.
{ eapply (cl_callS_na B LAWS Wc regsT memT _ SUP_WORKER_ENV_STK (spZ regs) FPw ly S W mem md [] lyc Sc _ k
     REC_SHAPE_OF_STK [] EV_REC_SHAPE_OF (-64) (Z_to_bv 64 (BASE + 23840))
     (fun ly2 S2 W2 regs2 mem2 md2 =>
       (exists q, getr regs2 10 = w64 q /\ 0 <= q < 2 ^ 64 /\
         forall Oa, astr_argA B ly2 S2 (rdW W2 mem2) (in_roP SEGS RLO RHI) Oa q (Some SHPr3)) /\
       Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) /\ ly2 = lyc /\ S2 = Sc) HJ HspT).
  - reflexivity.
  - lia.
  - apply Z.leb_le. vm_compute. reflexivity.
  - apply Z.leb_le. vm_compute. reflexivity.
  - swe_z5. rewrite (KR (Z_to_bv 5 3) ltac:(unfold swe_r3_kept; apply in_map; cbn; tauto)). exact R3.
  - swe_z5. rewrite (KR (Z_to_bv 5 4) ltac:(unfold swe_r3_kept; apply in_map; cbn; tauto)). exact R4.
  - swe_z5. exact Q1.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - rewrite unsigned_lit_small by lia. lia.
  - intros HPRE1. eapply SRr_mono.
    { apply (TREC_SHAPE_OF fx lyc Sc Wc regsT memT _ 0x21ec0 swe_r3_v HPRE1 HRODT).
      - swe_z5. exact Q10.
      - lia.
      - swe_z5. rewrite Q11. reflexivity.
      - change (Z.of_nat (length swe_r3_v)) with 10. lia.
      - exact HROT.
      - exact VOBJS.
      - intros _. destruct (swe_r3_verb lyc Sc Wc memT HROT) as [Hby Harg].
        split; [exact Hby | right; exact Harg].
      - pose proof HJ as (_ & _ & _ & _ & _ & _ & Hnev & _).
        unfold EV_REC_SHAPE_OF. unfold EV_SUP_WORKER_ENV, EV_ANSWER, EV_HAND_BACK, EV_XSTRDUP in HEV. lia. }
    cbv beta. intros W2 c2 _ (ly' & S' & regs' & mem' & md' & -> & HJ' & HP' & HK').
    exists ly', S', regs', mem', md'. swe_z5. rewrite Q1. split; [reflexivity|]. split; [exact HJ'|]. split; [exact HP' | exact HK'].
  - intros a Ha. exfalso. exact (inFP_nil a Ha). }
cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HJc & HP2 &
  ((q & Hq10 & Hqb & HqA) & _ & -> & ->)).
destruct (swe_r3_after_rso lyc Sc Wc memT _ k O0 D Fr _ W2 mem2 md2 HC3 HREP3 HJ2 HJc) as [HC2 HREP2].
change (Z_to_bv 64 (BASE + 23840)) with (Z_to_bv 64 (BASE + SWE_R4)).
apply (swe_r3_tail lyc Sc W2 regs2 mem2 md2 k O0 D Fr _ q HC2 HREP2).
- rewrite (swe_r3_thru regs1 regsT regs2 2 KR HP2 ltac:(cbn; tauto)). exact R2.
- rewrite (swe_r3_thru regs1 regsT regs2 3 KR HP2 ltac:(cbn; tauto)). exact R3.
- rewrite (swe_r3_thru regs1 regsT regs2 4 KR HP2 ltac:(cbn; tauto)). exact R4.
- rewrite (swe_r3_thru regs1 regsT regs2 8 KR HP2 ltac:(cbn; tauto)). exact R8.
- intros r Hr. rewrite (swe_r3_thru regs1 regsT regs2 r KR HP2 ltac:(cbn; lia)). exact (R23 r Hr).
- swe_z5. exact Hq10.
- exact Hqb.
- exact (HqA _).
Qed.

(* the walk: the entry segment, the join, the three xstrdup calls with their arg_s stores, and the tail *)
#[local] Notation POSTz := (swe_POST (B:=B) (MT:=MT) (ly:=ly) (S:=S) (W:=W) (regs:=regs) (mem:=mem) (md:=md)
  (format:=format) (cpus:=cpus) (nice:=nice) (R:=R) (O:=O)).
Lemma swe_walk : SRr SEGS W (cfg_at SEGS (BASE + AF_sup_worker_env) regs mem md) POSTz.
Proof using TRCF TXSTRDUP TREC_SHAPE_OF TANSWER VOBJS TL HB MTL SIGP cmd_prog_img cmd_prog_writable cmd_ro_prog_apart cmd_ro_ok_of_aro cmd_heap_tail_vis CMD_RO_IN HPRE HFRM HROD HRO H10 HB10 H11 HB11 H12 HB12 HAFx HACx HANx HREP HFR8 HEV HLIVE HMOK.
apply swe_entry_ok. apply swe_J_ok. apply swe_X1_ok. apply swe_R1_ok. apply swe_X2_ok. apply swe_R2_ok. apply swe_X3_ok.
apply swe_R3_ok.
Qed.

End w.
End e.
End f.
End d.
