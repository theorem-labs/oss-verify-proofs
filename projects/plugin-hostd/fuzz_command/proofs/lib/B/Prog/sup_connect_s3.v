(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: one part of sup_connect's walk on fuzz_command.asan-ubsan (image B),
   `scb_seg2 : SCB_3_stmt -> SCB_2_stmt` (the interface lib/B/Prog/sup_connect_s0.v): from the return point
   BASE + SCB_R2 = 0x8b49c of arg_s(c, verb) to the return point BASE + SCB_R3 = 0x8b4a8 of arg_line(c, line).

   0x8b49c .. 0x8b4a4: `mv a0,s4; mv a1,s2; jal arg_line`. The run reads no memory and writes none (the one region
   of the seed is the frame, read-only), so every byte is kept up to the call. arg_line takes the raw slot form
   (lib/B/Prog/arg_line_c.v:85-87): RecBridge.v's rec_bridge_slot gives the slot disjunction and c->nargs = 1 from
   the recorder holding (REC_CONNECT, [sarg verb]). The line is the statement's block argument; its block is none of
   O, so it stays live (scb_mid's third bookkeeping clause) and the walk's journal keeps its bytes. The call goes
   through PaCallPg.v's cl_callS_pg (arg_line writes c->nargs and c->args[1], two fields of g_rec or record.spill).
   arg_line's post arm m = 6 is impossible (m = 1); the other gives the fresh block p of |line| + 1 bytes holding
   `canon line`, c->nargs = 2 and c->args[1] = p, and rec_bridge_add rebuilds the recorder holding
   (REC_CONNECT, [sarg verb; canon line]) with p's block added. The hand-over at SCB_R3 (scb_mid at stage 3) then
   takes the frame from arg_line's journal (the frame lies above arg_line's stack window and outside its
   footprint) and the registers from aregs_preserved. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import String ZArith NArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI00 YI04 YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaStep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YI16.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs RtString.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdPaLib.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
PaDenot PaLibG PaCall CmdBase CmdRep CmdObj CmdRo.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
record_c arg_s_c arg_line_c answer_c sup_connect_c RecBLemmas.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
CmdRecBase CmdRecImg CmdRecRest PaCallPg RecBridge xmalloc_c hand_back_c rec_canonical_c sup_connect_s0.
Import ListNotations.
#[local] Unset Lia Cache. #[local] Unset Nia Cache.
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
#[local] Notation SIGMA := (@pa_sigma _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
(* the callee's contract *)
Hypothesis TARG_LINE : forall fx0 : YK11.FPState, @targ_line_spec fx0 rc SK PI B MT.
Hypothesis VOBJS : cmd_val_objs.
(* the per-binary facts *)
Hypothesis HB : CmdBSyms B.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis MTL : ameter_laws MT.
Hypothesis SIGP : cmd_sig_prog.
Hypothesis IMG : cmd_img_facts SEGS B.
Let RUN := paj_run B LAWS.

Local Ltac scb3_name_ms HS nm :=
lazymatch type of HS with
| st_ok_pi _ _ _ _ (restrict _ ?m) => rename m into nm
| st_ok _ _ _ (restrict _ ?m) => rename m into nm
end.
Local Ltac scb3_set_md nm :=
lazymatch goal with |- SRr _ _ (mkCfg _ ?mdx) _ => set (nm := mdx) in *; clearbody nm end.
(* a callee-saved register r (as the bv numeral rb) that aregs_preserved keeps *)
Local Ltac scb3_pres HP r rb X :=
pose proof (HP r ltac:(unfold acallee_saved; lia)) as X;
replace (Z_to_bv 5 r) with rb in X by (apply bv_eq; reflexivity).

(* ---------------------------------------------------------------------------------------------- *)
(* Facts about the slot, the footprint and the blocks                                               *)

(* the two fields arg_line writes when c->nargs = 1 *)
Definition scb3_FP1 (c : Z) : list (Z * Z) :=
[(c + CALL_OFF_NARGS, c + CALL_OFF_NARGS + 4); (c + CALL_OFF_ARGS + 8 * 1, c + CALL_OFF_ARGS + 8 * 1 + 8)].

Lemma scb3_FP1_cases : forall c a, inFP (scb3_FP1 c) a ->
c + CALL_OFF_NARGS <= a < c + CALL_OFF_NARGS + 4 \/ c + CALL_OFF_ARGS + 8 <= a < c + CALL_OFF_ARGS + 16.
Proof.
intros c a Ha. unfold scb3_FP1 in Ha.
apply inFP_cons in Ha. destruct Ha as [Ha | Ha]; [left; exact Ha|].
apply inFP_cons in Ha. destruct Ha as [Ha | Ha]; [right; lia | destruct (inFP_nil a Ha)].
Qed.

(* a byte of the slot (g_rec's call table or record.spill) is in the walk's footprint, in the program's statics
   and in g_rec or record.spill *)
Lemma scb3_slot_in : forall O c a,
((exists i, 0 <= i < REC_CALLS_MAX /\ c = A_G_REC + OFF_CALLS + CALL_SIZE * i) \/ c = A_REC_SPILL) ->
c <= a < c + CALL_SIZE ->
inFP (scb_FP O) a /\ inFP cmd_PG a /\ (A_G_REC <= a < A_G_REC + REC_SIZE \/ A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE).
Proof.
intros O c a [(i & Hi & ->) | ->] Ha.
- split; [|split].
  + exists (A_G_REC + OFF_CALLS, A_G_REC + OFF_ANSWER + 8). split; [unfold scb_FP; right; left; reflexivity|].
    cbn [fst snd]. unfold A_G_REC, OFF_CALLS, OFF_ANSWER, CALL_SIZE, REC_CALLS_MAX in *. lia.
  + exists (A_G_REC, A_G_REC + 960). split; [unfold cmd_PG; left; reflexivity|].
    cbn [fst snd]. unfold A_G_REC, OFF_CALLS, CALL_SIZE, REC_CALLS_MAX in *. lia.
  + left. unfold A_G_REC, OFF_CALLS, CALL_SIZE, REC_CALLS_MAX, REC_SIZE in *. lia.
- split; [|split].
  + exists (A_REC_SPILL, A_REC_SPILL + SC_SIZE). split; [unfold scb_FP; right; right; right; left; reflexivity|].
    cbn [fst snd]. unfold A_REC_SPILL, SC_SIZE, CALL_SIZE in *. lia.
  + exists (A_REC_SPILL, A_REC_SPILL + 56). split; [unfold cmd_PG; right; left; reflexivity|].
    cbn [fst snd]. unfold CALL_SIZE in *. lia.
  + right. unfold SC_SIZE, CALL_SIZE in *. lia.
Qed.

(* a byte of the walk's footprint is a static of the program or a byte of one of O's blocks *)
Lemma scb3_fp_cases : forall O a, inFP (scb_FP O) a ->
inFP cmd_PG a \/ exists p n, In (p, n) O /\ p <= a < p + req_size n.
Proof.
intros O a (r & Hr & Ha). unfold scb_FP in Hr.
destruct Hr as [<- | [<- | [<- | [<- | Hr]]]]; cbn [fst snd] in Ha.
- left. exists (A_G_REC, A_G_REC + 960). split; [unfold cmd_PG; left; reflexivity|].
  cbn [fst snd]. unfold OFF_NCALLS in Ha. lia.
- left. exists (A_G_REC, A_G_REC + 960). split; [unfold cmd_PG; left; reflexivity|].
  cbn [fst snd]. unfold OFF_CALLS, OFF_ANSWER in Ha. lia.
- left. exists (A_G_REC, A_G_REC + 960). split; [unfold cmd_PG; left; reflexivity|].
  cbn [fst snd]. unfold OFF_STATE in Ha. lia.
- left. exists (A_REC_SPILL, A_REC_SPILL + 56). split; [unfold cmd_PG; right; left; reflexivity|].
  cbn [fst snd]. unfold SC_SIZE in Ha. lia.
- right. apply inFP_ablocks_fp_inv. exists r. split; [exact Hr | exact Ha].
Qed.

(* the program's statics in the record's (lo, len) form *)
Lemma scb3_pg_static : forall a, inFP cmd_PG a -> Exists (in_zr a) TFIB_PROG_STATIC.
Proof.
intros a (r & Hr & Ha). change (Exists (in_zr a) recb_PG). unfold cmd_PG in Hr.
destruct Hr as [<- | [<- | [<- | []]]]; cbn [fst snd] in Ha.
- apply recb_grec_in. unfold REC_SIZE. lia.
- apply recb_spill_in. unfold SC_SIZE. lia.
- apply Exists_cons_tl, Exists_cons_tl, Exists_cons_hd. unfold in_zr. cbn [fst snd]. lia.
Qed.

Lemma scb3_prog_static : forall a, (A_G_REC <= a < A_G_REC + REC_SIZE \/ A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE) ->
Exists (in_zr a) (as_prog_static B).
Proof.
intros a Ha. rewrite (ts_prog B HB). change (Exists (in_zr a) recb_PG).
destruct Ha as [Ha | Ha]; [exact (recb_grec_in a Ha) | exact (recb_spill_in a Ha)].
Qed.

(* a byte of a live block is no byte of the image *)
Lemma scb3_blk_noimg : forall ly S (W : world SEGS) mem md b m a,
AR SEGS B ly S W mem md -> In (b, m) (ablocks B ly S) -> b <= a < b + req_size m -> ~ in_img SEGS a.
Proof.
intros ly S W mem md b m a HAR Hin Ha.
exact (proj2 (al_client_img _ _ LAWS ly S W mem md a HAR (or_introl (ex_intro _ b (ex_intro _ m (conj Hin Ha)))))).
Qed.

(* a live block is apart from a range of image bytes *)
Lemma scb3_apart_img : forall ly S (W : world SEGS) mem md p n lo len,
AR SEGS B ly S W mem md -> In (p, n) (ablocks B ly S) -> 0 < len ->
(forall a, lo <= a < lo + len -> in_img SEGS a) -> iv_apart p n lo len.
Proof.
intros ly S W mem md p n lo len HAR Hin Hlen Himg. unfold iv_apart.
destruct (al_blocks _ _ LAWS ly S W mem md p n HAR Hin) as (_ & _ & _ & _ & _ & _ & Hn).
destruct (Z_le_gt_dec (p + n) lo) as [H|H]; [left; exact H|].
destruct (Z_le_gt_dec (lo + len) p) as [H'|H']; [right; exact H'|]. exfalso.
pose proof (req_size_pos n ltac:(lia)) as Hq.
apply (scb3_blk_noimg ly S W mem md p n (Z.max p lo) HAR Hin); [lia | apply Himg; lia].
Qed.

(* a block the walk's footprint does not name keeps its bytes across a journal of the walk (A's s6_blk_keep) *)
Lemma scb3_blk_keep : forall STK sp0 O ly S (W : world SEGS) mem md own ly' S' (W' : world SEGS) mem' md' k q m a,
AR SEGS B ly S W mem md -> (forall pn, In pn O -> In pn (ablocks B ly S)) ->
ajournal SEGS B STK sp0 (scb_FP O) ly S W mem md own ly' S' W' mem' md' k ->
In (q, m) (ablocks B ly S) -> ~ In (q, m) O -> In (q, m) (ablocks B ly' S') -> q <= a < q + m ->
rdW W' mem' a = rdW W mem a.
Proof.
intros STK sp0 O ly S W mem md own ly' S' W' mem' md' k q m a HAR HOin HJ Hq Hno Hq' Ha.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _).
destruct (al_blocks _ _ LAWS ly S W mem md q m HAR Hq) as (_ & _ & _ & _ & _ & _ & Hm).
pose proof (req_size_pos m ltac:(lia)) as [_ Hrq].
replace a with (q + (a - q)) by lia. apply (F2 q m (a - q)); [exact Hq | exact Hq' | lia |].
intros Hin. destruct (scb3_fp_cases O (q + (a - q)) Hin) as [Hpg | (p & n & Hpn & Hr)].
- apply (scb3_blk_noimg ly S W mem md q m (q + (a - q)) HAR Hq ltac:(lia)). exact (cif_prog_img _ _ IMG _ Hpg).
- destruct (recb_pair_dec (p, n) (q, m)) as [Heq | Ne]; [rewrite Heq in Hpn; exact (Hno Hpn)|].
  pose proof (sep_blocks SEGS B LAWS ly S W mem md p n q m HAR (HOin _ Hpn) Hq Ne) as D.
  unfold zdisjoint in D. cbn [fst snd] in D. lia.
Qed.

(* arg_line's post at the call state, the K of cl_callS_pg (the arm m = 6 is impossible: c->nargs is 1) *)
Definition scb3_K (lyc : alayout) (Sc : astate) (c : Z) (line : list byte) :
alayout -> astate -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop :=
fun ly2 S2 W2 regs2 mem2 md2 =>
  blocks_bytes S2 <= blocks_bytes Sc + LIVE_ARG_LINE line /\
  mo_le MT Sc S2 (XM_ARG_LINE MT line) /\
  exists p, 4096 <= p < 2 ^ 64 /\
    Permutation (ablocks B ly2 S2) ((p, Z.of_nat (length line) + 1) :: ablocks B lyc Sc) /\
    Forall (fun qk => iv_apart p (Z.of_nat (length line) + 1) (fst qk) (snd qk)) (ablocks B lyc Sc) /\
    aval_mem (rdW W2 mem2) (c + CALL_OFF_NARGS) 4 2 /\
    aval_mem (rdW W2 mem2) (c + CALL_OFF_ARGS + 8 * 1) 8 p /\
    astr_atR (rdW W2 mem2) p (canon line).

(* ---------------------------------------------------------------------------------------------- *)
(* 0x8b49c -> 0x8b4a8: arg_line(c, line)                                                            *)

Lemma scb_seg2 : SCB_3_stmt B MT -> SCB_2_stmt B MT.
Proof using TARG_LINE VOBJS HB LAWS MTL SIGP IMG.
intros SCB3 ly S W regs mem md ch pv pl pa pb verb line port_a port_b R O lyc Sc Wc regsc memc mdc kc Oc t
  HPRE HMID H20.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof scb_stk as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9).
pose proof HPRE as (HPRE0 & Hfrm & Hfr8 & HROD & HRO & H10 & Hpv64 & H11 & Hpl64 & H12 & Hpa64 & H13 &
  Hpb64 & HSV & HSVT & HSL & HSA & HSB & HREP0 & Hev & Hlive & HMOK).
pose proof HPRE0 as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof HMID as (HJc & Hk & HRA & HFR & HREP & HOc1 & HOc2 & HOc3 & Hfrc & Hbbc & MLEc).
pose proof HRA as (Rsp & R8 & R9 & R18 & R19 & R3 & R4 & Rhi).
pose proof HJc as (HARc & _).
unfold scb_A2 in HREP.
assert (HOin : forall pn, In pn O -> In pn (ablocks B ly S))
by (intros pn Hpn; exact (scb_rep_live B ly S _ R O pn HREP0 Hpn)).
assert (HOcin : forall pn, In pn Oc -> In pn (ablocks B lyc Sc))
by (intros pn Hpn; exact (scb_rep_live B lyc Sc _ _ Oc pn HREP Hpn)).
(* the slot c = rec_slot R and its nargs field (RecBridge.v) *)
destruct (rec_bridge_slot B lyc Sc (rdW Wc memc) R REC_CONNECT [sarg verb] Oc HREP) as (Hslot & Hnargs & _ & _).
change (Z.of_nat (length [sarg verb])) with 1 in Hnargs.
assert (Hcr : A_G_REC + OFF_CALLS <= rec_slot R /\ rec_slot R + CALL_SIZE <= A_REC_SPILL + SC_SIZE).
{ destruct Hslot as [(i & Hi & Hc) | Hc]; rewrite Hc;
  unfold A_G_REC, A_REC_SPILL, OFF_CALLS, CALL_SIZE, SC_SIZE, REC_CALLS_MAX in *; lia. }
(* the line's block: live at the entry, none of O, so live here *)
pose proof HSL as ((ql & ml & Hql & Hql1 & Hql2) & Hlap & Hlstr & Hllen).
assert (HqlO : ~ In (ql, ml) O).
{ intros Hin. pose proof (proj1 (Forall_forall _ _) Hlap _ Hin) as Hd. unfold iv_apart in Hd.
  cbn [fst snd] in Hd. lia. }
assert (Hqlc : In (ql, ml) (ablocks B lyc Sc)) by exact (HOc3 _ Hql HqlO).
(* port_b's pointer pb (s0) is a heap pointer, below alloc_ceiling *)
assert (Hpbc : pb < alloc_ceiling).
{ destruct HSB as ((qb & mb & Hqb & Hqb1 & Hqb2) & _).
  destruct (al_blocks _ _ LAWS ly S W mem md qb mb HAR Hqb) as (_ & _ & Hc & _ & _ & _ & Hm).
  pose proof (req_size_pos mb ltac:(lia)) as [_ Hrq]. lia. }
(* the seed at 0x8b49c *)
destruct (scb_seed B SCB_R2 ly regs regsc lyc Sc Wc memc mdc Hstk HARc Rsp HFR) as [HS SHOK].
remember (Eimg (Ereg regsc (scb_extra_m regs))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regsc r).
{ intros n r Hn. pose proof (bv_unsigned_in_range 5 r) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  subst E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn. }
assert (HAE : env_agree 32 (Ereg regsc (scb_extra_m regs)) E).
{ split; [intros n Hn; subst E; apply Eimg_low; unfold A_TEXT; lia | subst E; reflexivity]. }
clear HE.
(* 0x8b49c .. 0x8b4a4: a0 := s4, a1 := s2, the call of arg_line *)
paj_run_tok RUN HS HJc SHOK scb_Bspan.
{ awr_ok_tac. }
scb3_set_md mdv1. scb3_name_ms HS ms1.
pose proof (kept_of_frame (segs:=SEGS) E _ (w_H Wc) memc (ms_mem ms1) (fun _ => False) HFr
  ltac:(intros b wlo whi a' Hin Hrr; vm_compute in Hin;
        repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; lia|]); destruct Hin)) as KEEP1.
clear HF HFr HG.
assert (KR : forall a, 0 <= a < 2 ^ 64 -> rdW Wc (ms_mem ms1) a = rdW Wc memc a)
by (intros a Ha; exact (KEEP1 a Ha (fun x => x))).
pose proof (aregs_preserved_of_st_ok SEGS _ E _ _ regsc (scb_extra_m regs) HS HAE ltac:(vm_compute; reflexivity))
  as HPR1.
cbn [ms_regs restrict] in HPR1.
pmkst HS.
prreg HS (1%bv : bv 5) P1. prreg HS (10%bv : bv 5) P10. prreg HS (11%bv : bv 5) P11.
scb3_pres HPR1 2 (2%bv : bv 5) X2. scb3_pres HPR1 3 (3%bv : bv 5) X3. scb3_pres HPR1 4 (4%bv : bv 5) X4.
scb3_pres HPR1 8 (8%bv : bv 5) X8.
assert (Hsp1 : spZ (ms_regs ms1) = spZ regs + -48).
{ unfold spZ at 1. rewrite X2. change (bv_unsigned (getr regsc 2)) with (spZ regsc). lia. }
assert (Hc0 : getr (ms_regs ms1) 10 = w64 (rec_slot R)) by (rewrite P10, (EE 20%nat 20%bv eq_refl); exact H20).
assert (Hl1 : getr (ms_regs ms1) 11 = w64 pl) by (rewrite P11, (EE 18%nat 18%bv eq_refl), R18; exact H11).
(* the facts arg_line's contract asks at the call state *)
assert (Hnargs1 : aval_mem (rdW Wc (ms_mem ms1)) (rec_slot R + CALL_OFF_NARGS) 4 1).
{ intros k0 Hk0. rewrite KR; [exact (Hnargs k0 Hk0)|].
  unfold CALL_OFF_NARGS, A_G_REC, A_REC_SPILL, OFF_CALLS, CALL_SIZE, SC_SIZE in *. lia. }
assert (Hlblk1 : in_blockA (ablocks B lyc Sc) pl (Z.of_nat (length line) + 1))
by (exists ql, ml; split; [exact Hqlc | lia]).
assert (Hlstr1 : astr_atR (rdW Wc (ms_mem ms1)) pl line).
{ apply (astr_atR_kept_r (rdW W mem)); [|exact Hlstr].
  intros x Hx. exact (scb3_blk_keep SUP_CONNECT_STK (spZ regs) O ly S W mem md [] lyc Sc Wc (ms_mem ms1) mdv1 kc
    ql ml x HAR HOin HJc Hql HqlO Hqlc ltac:(lia)). }
assert (HROD1 : arodata_okP SEGS RLO RHI B (rdW Wc (ms_mem ms1))).
{ apply (cmd_rodata_kept SEGS B LAWS HB IMG ly S W mem md lyc Sc Wc (ms_mem ms1) mdv1 SUP_CONNECT_STK (spZ regs)
    (scb_FP O) [] kc HAR HJc); [|exact HROD].
  intros a Ha. destruct (scb3_fp_cases O a Ha) as [Hpg | (p0 & n0 & Hin & Hr)].
  - left. exact (scb3_pg_static a Hpg).
  - right. exists p0, n0. split; [apply in_or_app; left; exact (HOin _ Hin) | exact Hr]. }
assert (HnevJ : st_nev Sc + EV_ARG_LINE <= EV_MAX).
{ pose proof HJc as (_ & _ & _ & _ & _ & _ & Hnev & _).
  assert (Hev0 : 0 <= EV_ARG_S + EV_ARG_S + EV_ANSWER) by (vm_compute; intro; discriminate).
  unfold SCB_EV2, SCB_EV1 in Hk. unfold EV_SUP_CONNECT in Hev. lia. }
assert (HLIVE1 : blocks_bytes Sc + LIVE_ARG_LINE line <= LIVE_MAX).
{ assert (Hl0 : 0 <= LIVE_ARG_S (Some port_a) + LIVE_ARG_S (Some port_b) + LIVE_ANSWER t)
    by (unfold LIVE_ARG_S, LIVE_ANSWER, LIVE_HAND_BACK, LIVE_XMALLOC; lia).
  unfold SCB_LV2, SCB_LV1 in Hbbc. unfold LIVE_SUP_CONNECT in Hlive. lia. }
assert (HMOK1 : mo_ok MT Sc (XM_ARG_LINE MT line)).
{ pose proof (mo_free_nonneg MT MTL) as M0.
  assert (Mx : 0 <= XM_ARG_LINE MT line /\ 0 <= XM_ARG_S MT (Some port_a) /\ 0 <= XM_ARG_S MT (Some port_b) /\
    0 <= XM_ANSWER MT t).
  { unfold XM_ARG_LINE, XM_REC_CANONICAL, XM_ARG_S, XM_ANSWER, XM_HAND_BACK, XM_XMALLOC, LIVE_XMALLOC.
    repeat split; repeat apply Z.add_nonneg_nonneg; first [exact M0 | apply (mo_malloc_nonneg MT MTL); lia]. }
  destruct Mx as (Mx1 & Mx2 & Mx3 & Mx4).
  apply (mok_station MT S Sc _ _ (XM_ARG_LINE MT line) MTL HMOK MLEc Mx1).
  unfold SCB_XM2, SCB_XM1, XM_SUP_CONNECT. lia. }
(* 0x8b4a4: the call of arg_line, through the call rule for a callee that writes program statics *)
rewrite (scb_sig_arg_line SIGP).
eapply SRr_bind.
{ eapply (cl_callS_pg B LAWS Wc (ms_regs ms1) (ms_mem ms1) _ SUP_CONNECT_STK (spZ regs) (scb_FP O) ly S W mem md []
    lyc Sc mdv1 kc ARG_LINE_STK (scb3_FP1 (rec_slot R)) EV_ARG_LINE (-48) (Z_to_bv 64 (BASE + SCB_R3)) []
    (scb3_K lyc Sc (rec_slot R) line) HJc Hsp1).
  - reflexivity.
  - lia.
  - lia.
  - lia.
  - rewrite X3, R3. exact Hgp.
  - rewrite X4, R4. exact Htp.
  - rewrite P1. reflexivity.
  - apply ret_ok_codeptr_v; [unfold SCB_R3; lia | reflexivity].
  - rewrite unsigned_lit_small by (unfold SCB_R3; lia). unfold SCB_R3. lia.
  - apply achain_low. unfold s0Z. rewrite X8, R8, H13. unfold w64. rewrite unsigned_lit_small by lia. exact Hpbc.
  - intros HPREA. eapply SRr_mono.
    { exact (TARG_LINE fx lyc Sc Wc (ms_regs ms1) (ms_mem ms1) mdv1 [] (rec_slot R) pl 1 line HPREA HROD1
        Hc0 Hl1 Hpl64 Hslot Hnargs1 ltac:(unfold REC_ARGS_MAX; lia) Hlblk1 Hlstr1 Hllen HnevJ HLIVE1 HMOK1). }
    cbv beta. unfold apost_base. intros W6 c6 _ (ly6 & S6 & regs6 & mem6 & md6 & -> & HJ6 & HP6 & Hbb6 & Hmle6 & HQ6).
    exists ly6, S6, regs6, mem6, md6. split; [rewrite P1; reflexivity|]. split; [exact HJ6|]. split; [exact HP6|].
    unfold scb3_K. split; [exact Hbb6|]. split; [exact Hmle6|].
    destruct HQ6 as [(Hm6 & _) | (_ & q & Hq4096 & Hqperm & Hqfresh & Hqn & Hqa & Hqs)];
    [unfold REC_ARGS_MAX in Hm6; lia|].
    exists q. split; [exact Hq4096|]. split; [exact Hqperm|]. split; [exact Hqfresh|].
    split; [exact Hqn|]. split; [exact Hqa | exact Hqs].
  - intros a Ha. left.
    assert (Hin : rec_slot R <= a < rec_slot R + CALL_SIZE)
    by (destruct (scb3_FP1_cases _ a Ha) as [H | H]; unfold CALL_OFF_NARGS, CALL_OFF_ARGS, CALL_SIZE in *; lia).
    destruct (scb3_slot_in O (rec_slot R) a Hslot Hin) as (Hfp & Hpg & Hgs).
    split; [exact Hfp|]. right. split; [exact (scb3_prog_static a Hgs) | exact (cif_prog_img _ _ IMG a Hpg)]. }
cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HJ2c & HP2 & Hbb2 & Hmle2 &
  p & [Hp4096 Hp64] & Hperm & Hfresh & Hna2 & Harg2 & Hstr2).
pose proof HJ2 as (HAR2 & _ & _ & _ & _ & Hfr2 & _).
pose proof HJ2c as (_ & _ & _ & _ & _ & _ & _ & _ & F1c & F2c & F3c & _).
pose proof (aregs_preserved_trans _ _ _ HPR1 HP2) as HPRt.
assert (HpIn : In (p, Z.of_nat (length line) + 1) (ablocks B ly2 S2))
by (eapply Permutation_in; [apply Permutation_sym; exact Hperm | left; reflexivity]).
assert (KBL : forall pn, In pn (ablocks B lyc Sc) -> In pn (ablocks B ly2 S2))
by (intros pn Hpn; eapply Permutation_in; [apply Permutation_sym; exact Hperm | right; exact Hpn]).
assert (HpnotC : ~ In (p, Z.of_nat (length line) + 1) (ablocks B lyc Sc)).
{ intros Hin. pose proof (proj1 (Forall_forall _ _) Hfresh _ Hin) as Hd. unfold iv_apart in Hd.
  cbn [fst snd] in Hd. lia. }
(* the frame: above arg_line's stack window and outside its footprint, kept by its journal *)
assert (FRK : forall a, spZ regs - 48 <= a < spZ regs -> rdW W2 mem2 a = rdW Wc memc a).
{ intros a Ha. rewrite <- (KR a ltac:(lia)).
  apply F1c; [lia | lia |].
  intros Hf. destruct (scb3_FP1_cases _ a Hf) as [H | H];
  unfold CALL_OFF_NARGS, CALL_OFF_ARGS, A_G_REC, A_REC_SPILL, OFF_CALLS, CALL_SIZE, SC_SIZE in *; lia. }
(* the recorder: (REC_CONNECT, [sarg verb; canon line]) with p's block added *)
assert (HREP2 : rec_repA B ly2 S2 (rdW W2 mem2) (rec_record R REC_CONNECT ([sarg verb] ++ [canon line]))
  ((p, Z.of_nat (length line) + 1) :: Oc)).
{ pose proof (canon_length line) as Hcl.
  apply (rec_bridge_add B lyc Sc ly2 S2 (rdW Wc memc) (rdW W2 mem2) R REC_CONNECT [sarg verb] Oc (canon line) p
    (Z.of_nat (length line) + 1) HREP).
  - cbn. lia.
  - intros a Ha Hn1 Hn2. change (Z.of_nat (length [sarg verb])) with 1 in Hn2.
    assert (Hpg : inFP cmd_PG a).
    { destruct Ha as [Ha | Ha].
      - exists (A_G_REC, A_G_REC + 960). split; [unfold cmd_PG; left; reflexivity|].
        cbn [fst snd]. unfold REC_SIZE in Ha. lia.
      - exists (A_REC_SPILL, A_REC_SPILL + 56). split; [unfold cmd_PG; right; left; reflexivity|].
        cbn [fst snd]. unfold SC_SIZE in Ha. lia. }
    destruct (cmd_prog_unowned SEGS B LAWS HB IMG a Hpg) as (Himg & Hown & Herr).
    rewrite <- (KR a ltac:(unfold A_G_REC, A_REC_SPILL, REC_SIZE, SC_SIZE in Ha; lia)).
    apply F3c; [exact Himg | exact Hown | exact Herr |].
    apply fp_spares_closed.
    + apply sink_closed_pos. unfold scb3_FP1. repeat constructor; cbn [fst];
      unfold CALL_OFF_NARGS, CALL_OFF_ARGS, A_G_REC, A_REC_SPILL, OFF_CALLS, CALL_SIZE, SC_SIZE in *; lia.
    + intros Hf. destruct (scb3_FP1_cases _ a Hf) as [H | H]; [exact (Hn1 H)|].
      apply Hn2. unfold CALL_OFF_ARGS in *. lia.
  - intros [q m] Hpn. cbn [fst snd].
    pose proof (HOcin _ Hpn) as Hqc.
    destruct (al_blocks _ _ LAWS lyc Sc Wc memc mdc q m HARc Hqc) as (_ & Hq4096 & Hqceil & _ & _ & _ & Hm).
    pose proof (req_size_pos m ltac:(lia)) as [Hrq1 Hrq].
    split; [exact (KBL _ Hqc)|].
    intros i Hi. rewrite <- (KR (q + i) ltac:(lia)).
    apply (F2c q m i); [exact Hqc | exact (KBL _ Hqc) | lia |].
    intros Hf. apply (scb3_blk_noimg lyc Sc Wc memc mdc q m (q + i) HARc Hqc ltac:(lia)).
    apply (cif_prog_img _ _ IMG).
    assert (Hin : rec_slot R <= q + i < rec_slot R + CALL_SIZE)
    by (destruct (scb3_FP1_cases _ _ Hf) as [H | H]; unfold CALL_OFF_NARGS, CALL_OFF_ARGS, CALL_SIZE in *; lia).
    exact (proj1 (proj2 (scb3_slot_in O (rec_slot R) (q + i) Hslot Hin))).
  - exact HpIn.
  - intros Hin. apply in_map_iff in Hin as ([q m] & Hq & Hqm). cbn [fst] in Hq. subst q.
    pose proof (HOcin _ Hqm) as Hqc.
    destruct (Z.eq_dec m (Z.of_nat (length line) + 1)) as [-> | Hne]; [exact (HpnotC Hqc)|].
    pose proof (sep_blocks SEGS B LAWS ly2 S2 W2 mem2 md2 p m p (Z.of_nat (length line) + 1) HAR2 (KBL _ Hqc) HpIn
      ltac:(intros Heq; injection Heq; lia)) as D.
    destruct (al_blocks _ _ LAWS ly2 S2 W2 mem2 md2 p m HAR2 (KBL _ Hqc)) as (_ & _ & _ & _ & _ & _ & Hm).
    pose proof (req_size_pos m ltac:(lia)) as [Hm1 _].
    pose proof (req_size_pos (Z.of_nat (length line) + 1) ltac:(lia)) as [Hn1 _].
    unfold zdisjoint in D. cbn [fst snd] in D. lia.
  - apply (scb3_apart_img ly2 S2 W2 mem2 md2 p _ A_G_REC REC_SIZE HAR2 HpIn ltac:(unfold REC_SIZE; lia)).
    intros a Ha. apply (cif_prog_img _ _ IMG). exists (A_G_REC, A_G_REC + 960).
    split; [unfold cmd_PG; left; reflexivity | cbn [fst snd]; unfold REC_SIZE in Ha; lia].
  - apply (scb3_apart_img ly2 S2 W2 mem2 md2 p _ A_REC_SPILL SC_SIZE HAR2 HpIn ltac:(unfold SC_SIZE; lia)).
    intros a Ha. apply (cif_prog_img _ _ IMG). exists (A_REC_SPILL, A_REC_SPILL + 56).
    split; [unfold cmd_PG; right; left; reflexivity | cbn [fst snd]; unfold SC_SIZE in Ha; lia].
  - lia.
  - lia.
  - unfold LMAX in *. lia.
  - change (Z.of_nat (length [sarg verb]) + 1) with 2. exact Hna2.
  - change (Z.of_nat (length [sarg verb])) with 1. exact Harg2.
  - exact Hstr2. }
apply (SCB3 ly S W regs mem md ch pv pl pa pb verb line port_a port_b R O ly2 S2 W2 regs2 mem2 md2
  (kc + EV_ARG_LINE) ((p, Z.of_nat (length line) + 1) :: Oc) HPRE).
2: { scb3_pres HPRt 20 (20%bv : bv 5) X20. rewrite X20. exact H20. }
split; [exact HJ2|].
split; [unfold SCB_EV3; lia|].
split.
{ scb3_pres HPRt 2 (2%bv : bv 5) Y2. scb3_pres HPRt 3 (3%bv : bv 5) Y3. scb3_pres HPRt 4 (4%bv : bv 5) Y4.
  scb3_pres HPRt 8 (8%bv : bv 5) Y8. scb3_pres HPRt 9 (9%bv : bv 5) Y9. scb3_pres HPRt 18 (18%bv : bv 5) Y18.
  scb3_pres HPRt 19 (19%bv : bv 5) Y19.
  split; [unfold spZ at 1; rewrite Y2; change (bv_unsigned (getr regsc 2)) with (spZ regsc); exact Rsp|].
  split; [rewrite Y8; exact R8|]. split; [rewrite Y9; exact R9|].
  split; [rewrite Y18; exact R18|]. split; [rewrite Y19; exact R19|].
  split; [rewrite Y3; exact R3|]. split; [rewrite Y4; exact R4|].
  intros r Hr. rewrite (HPRt r ltac:(unfold acallee_saved; lia)). exact (Rhi r Hr). }
split.
{ intros j r Hj.
  assert (Hjr : (j < length scb_saved)%nat) by (apply nth_error_Some; rewrite Hj; discriminate).
  cbn [scb_saved length] in Hjr.
  apply val_mem_view. intros k0 Hk0.
  rewrite (FRK (spZ regs - 8 - 8 * Z.of_nat j + Z.of_nat k0)) by lia.
  exact (aval_mem_view SEGS (w_H Wc) memc _ _ _ (HFR j r Hj) k0 Hk0). }
split; [exact HREP2|].
split.
{ intros pn [<- | Hpn] Hin; [|exact (HOc1 pn Hpn Hin)].
  destruct (In_dec recb_pair_dec (p, Z.of_nat (length line) + 1) O) as [HO | HnO]; [exact HO|].
  exfalso. exact (HpnotC (HOc3 _ Hin HnO)). }
split.
{ intros pn Hpn. apply (Permutation_in _ Hperm) in Hpn. destruct Hpn as [<- | Hpn]; [right; left; reflexivity|].
  destruct (HOc2 pn Hpn) as [H | H]; [left; exact H | right; right; exact H]. }
split; [intros pn Hin HnO; exact (KBL _ (HOc3 pn Hin HnO))|].
split; [rewrite Hfr2; reflexivity|].
split; [unfold SCB_LV3; lia|].
exact (mle_station MT S Sc S2 _ _ MTL MLEc Hmle2).
Qed.

End e.
End f.
End d.
