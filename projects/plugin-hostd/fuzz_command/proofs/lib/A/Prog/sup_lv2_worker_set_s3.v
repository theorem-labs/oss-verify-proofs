(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: restated for the statement of an earlier commit (heap-block string arguments).
   Modified by Theorem Labs, 2026-10: the walk of sup_lv2_worker_set (plugin-hostd/fuzz_command.asan) from the
   return of its first xstrdup (+0xc0) to the return of its second (+0x110), after
   proofs/cgif/cgif_file_fuzzer/lib/A/ACh2.v (a call and the walk back from it). *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YI16 YM05 YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs RtAPI.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal CmdSyms CmdAddr CmdList CmdPa CmdPaLib PaCall PaCallRun PaLibF PaLibG
PaLibH PaSB PaDenot PaNoChain.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob CmdBase CmdRep CmdObj CmdRo CmdZsh.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
rec_calls_free_c xstrdup_c rec_shape_of_c answer_c hand_back_c sup_lv2_worker_set_c RecBTemplate sup_lv2_worker_set_s1 sup_lv2_worker_set_s2.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require RecBLemmas.
Import RecBLemmas(aval_mem_view, recb_ablocks_nodup_m).
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
(* the per-binary record, as the walks take it *)
Hypothesis HB : CmdBSyms B.
Hypothesis TL : PALib B.
Hypothesis VOBJS : cmd_val_objs.
(* the program's writable statics (RecBTemplate.v:102-106 forms) *)
Hypothesis cmd_prog_img : forall a, Exists (in_zr a) recb_PG -> in_img SEGS a.
Hypothesis cmd_prog_writable : forall ly S (W : world SEGS) mem md a,
AR SEGS B ly S W mem md -> Exists (in_zr a) recb_PG -> writable_at SEGS (mrestrict (w_H W) mem) a.
(* the statement's Section hypotheses (sup_lv2_worker_set_c.v:68-72) *)
Hypothesis TRCF : forall fx0 : YK11.FPState, @trec_calls_free_spec fx0 rc SK PI B MT.
Hypothesis TXSTRDUP : forall fx0 : YK11.FPState, @txstrdup_spec fx0 rc SK PI B MT.
Hypothesis TREC_SHAPE_OF : forall fx0 : YK11.FPState, @trec_shape_of_spec fx0 rc SK PI B MT.
Hypothesis TANSWER : forall fx0 : YK11.FPState, @tanswer_spec fx0 rc SK PI B MT.
(* the walk hypotheses (cgif's names) and the walks' shared facts the statement does not carry yet (CmdRecFacts.v
   was not yet in the tree), each under its canonical name *)
Hypothesis MTL : ameter_laws MT.
Hypothesis SIGP : cmd_sig_prog.
Hypothesis cmd_ro_ok_of_aro : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md ->
arodata_okP SEGS RLO RHI B (rdW W mem) -> cmd_ro_ok (rdW W mem).
Hypothesis RRO : ro_below_ofl SEGS RLO RHI.
Hypothesis RELRO_IMG : forall a, RLO <= a < RHI -> in_img SEGS a.
Hypothesis cmd_ro_prog_apart : forall a, in_roP SEGS RLO RHI a -> in_img SEGS a /\ ~ Exists (in_zr a) recb_PG.
(* the premise an earlier commit deleted from the statements, which rec_shape_of's read-only arm needs for the verb
   literal (CmdRo.v:434; one name for all walks) *)
Hypothesis CMD_RO_IN : cmd_ro_in (in_roP SEGS CMD_RLO CMD_RHI).
(* a string in a live heap block: the bytes after its terminator, to the end of its 8-byte word, are readable
   (cmd_heap_tail_vis, this port's HEAP_TAIL_VIS; the strlen wrapper under xstrdup reads whole words) *)
Hypothesis cmd_heap_tail_vis : forall ly S (W : world SEGS) mem md p n e, AR SEGS B ly S W mem md ->
In (p, n) (ablocks B ly S) -> p <= e < p + n -> atail_vis SEGS W mem e.
Let LAWS : AR_laws SEGS B := AR_laws_ok SEGS B.
Let RUN := paj_run B LAWS.
Let BR := paj_branch (PI := PI).

Ltac tmpl_args := first [exact LAWS | exact HB | exact TL | exact VOBJS | exact (recb_ts_prog_m B HB) | exact cmd_prog_img
  | exact cmd_prog_writable].

Ltac slw_hyps H := repeat (lazymatch type of H with forall _ : ?P, _ => lazymatch type of P with Prop => specialize (H ltac:(assumption)) end end).

(* the writes a segment of C makes: the slot's nargs word and one argument word, any chunks *)
Lemma slw_awr_ok2 : forall E (st : YP09.region) cs1 cs2 aw STK sp0 O bl0 blc fr0 ly own c,
YP09.r_whi st <= YP09.r_wlo st ->
bv_unsigned (ew E RB_C) = c -> rbt_slot_ok c -> 8 <= aw -> aw + 8 <= CALL_SIZE ->
awr_ok SEGS B E [st; YP09.mkRegion (Some RB_C) 4 8 4 8 cs1; YP09.mkRegion (Some RB_C) aw (aw + 8) aw (aw + 8) cs2]
  STK sp0 (slw_FP O) bl0 blc fr0 ly own.
Proof.
intros E st cs1 cs2 aw STK sp0 O bl0 blc fr0 ly own c Hst Hc Hok Haw1 Haw2.
pose proof (slw_inFP_prog B) as INFP. slw_hyps INFP.
apply awr_ok_cons_ro; [exact Hst|].
eapply awr_ok_cons_gen; [reflexivity | exact Hc | | ].
{ intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha.
  right; right; right; right; left. apply INFP.
  replace a with (c + (a - c)) by lia. apply slw_slot_in; [exact Hok | unfold CALL_SIZE; lia]. }
eapply awr_ok_cons_gen; [reflexivity | exact Hc | | apply awr_ok_nil].
intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha.
right; right; right; right; left. apply INFP.
replace a with (c + (a - c)) by lia. apply slw_slot_in; [exact Hok | unfold CALL_SIZE in *; lia].
Qed.

Ltac slw_awr UC Hslot :=
  lazymatch goal with |- awr_ok _ _ _ ?rs _ _ _ _ _ _ _ _ => let rs' := eval vm_compute in rs in change rs with rs' end;
  eapply slw_awr_ok2; [cbn; lia | exact UC | exact Hslot | lia | unfold CALL_SIZE; lia].


(* a heap string argument: its block, and its address in [4096, 2^47) *)
Lemma slw_harg_blk : forall ly S (W : world SEGS) mem md rd O p v, AR SEGS B ly S W mem md -> slw_harg B ly S rd O p v ->
exists x q k, v = Some x /\ In (q, k) (ablocks B ly S) /\ q <= p /\ p + Z.of_nat (length x) + 1 <= q + k /\
  4096 <= p < 2 ^ 47.
Proof.
intros ly S W mem md rd O p v HAR (x & -> & (q & k & Hqk & Hq & Hqe) & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ q k HAR Hqk) as (_ & H4 & Hpc & _ & _ & _ & Hk0).
pose proof (req_size_pos k ltac:(lia)) as [_ Hrq]. pose proof asan_consts as (C1 & _).
exists x, q, k. split; [reflexivity|]. split; [exact Hqk|]. lia.
Qed.

(* the call of xstrdup on the second argument (+0x10c) and the state MID2 at its return: the slot holds FN, the
   first argument p1 and nargs = 1 (the stores of segment C), a0 the second argument pw *)
Lemma slw_xcall : forall ly S W regs mem md ch pu pw uri worker R O lyc Sc Wc regs1 memc mdc k p1 Df Lk O1
  (regsb : bvmap 5 word) memb mdb,
slw_pre B MT ly S W regs mem md ch pu pw uri worker R O ->
slw_mid1 B MT ly S W regs mem md pw uri worker R O lyc Sc Wc regs1 memc mdc k p1 Df Lk O1 ->
ajournal SEGS B SUP_LV2_WORKER_SET_STK (spZ regs) (slw_FP O) ly S W mem md [] lyc Sc Wc memb mdb k ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (slw_slot R + 4 <= a < slw_slot R + 16) -> rdW Wc memb a = rdW Wc memc a) ->
aval_mem (rdW Wc memb) (slw_slot R + 4) 4 1 -> aval_mem (rdW Wc memb) (slw_slot R + 8) 8 p1 ->
getr regsb 1 = Z_to_bv 64 (BASE + SLW_RET2) -> getr regsb 2 = w64 (spZ regs - 64) ->
getr regsb 3 = getr regs 3 -> getr regsb 4 = getr regs 4 ->
getr regsb 8 = w64 (slw_slot R) -> getr regsb 10 = w64 pw ->
getr regsb 18 = w64 (slw_slot R + 4) -> getr regsb 19 = w64 (slw_slot R + 8) -> getr regsb 20 = w64 SHADOW_OFF ->
getr regsb 21 = w64 (SHADOW_OFF + (slw_slot R + 4) / 8) ->
(forall r, 22 <= r <= 27 -> getr regsb (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) ->
SRr SEGS Wc (mkCfg (mkst regsb (Z_to_bv 64 (BASE + AF_xstrdup)) memb (seg_rom SEGS)) mdb)
  (slw_post B MT ly S W regs mem md R uri worker O).
Proof.
intros ly S W regs mem md ch pu pw uri worker R O lyc Sc Wc regs1 memc mdc k p1 Df Lk O1 regsb memb mdb
  PRE MID HJb KEEPb HNA HP1b Q1 Q2 Q3 Q4 Q8 Q10 Q18 Q19 Q20 Q21 Qhi.
pose proof PRE as PRE0.
destruct PRE as (HFN & HFM0 & HROD & HRO & H10 & Hpub & H11 & Hpwb & HSU & HSW & HREP & HFR8 & HEV & HLIVE & HMOK).
pose proof HFN as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO. pose proof pa_segs_low as Hsegs.
assert (HSTK : SUP_LV2_WORKER_SET_STK = 16592) by (vm_compute; reflexivity).
assert (HXS : 0 <= XSTRDUP_STK /\ XSTRDUP_STK - -64 <= SUP_LV2_WORKER_SET_STK)
  by (split; vm_compute; intro HH; discriminate HH).
destruct MID as (HJ & Hk & HFRM & R2 & R3 & R4 & R8 & R9 & R18 & R20 & R21 & R10 & Rhi & HREP1 & HO1 & HDf & HDf0 &
  HPS & HP1 & Hap1 & Hp1 & Hstr1 & HSW1 & MLE1).
set (sp0 := spZ regs) in *. set (c := slw_slot R) in *.
pose proof (proj1 HJ) as HARc. pose proof (proj1 HJb) as HARb.
pose proof (rec_repA_in B) as RIN. pose proof (rec_repA_kept B) as RKEPT.
pose proof (slw_heap_prog_apart B) as HPA. slw_hyps HPA.
pose proof (slw_blk_apart B) as BAP. slw_hyps BAP.
pose proof (recb_ablocks_nodup_m B) as NDP. slw_hyps NDP.
pose proof (slw_callee_keeps B) as CKEEP. slw_hyps CKEEP.
pose proof (slw_aro_at B) as ARO. slw_hyps ARO.
pose proof (slw_bsum_nonneg B) as BSN. slw_hyps BSN.
pose proof (slw_FP_low B) as FPL. slw_hyps FPL.
pose proof (slw_rep_push B) as PUSH.
pose proof (slw_D2 B MT) as D2. slw_hyps D2.
assert (Hlen : (length (r_calls R) <= 16)%nat) by exact (slw_rep_len B _ _ _ _ _ HREP).
assert (Hslot : rbt_slot_ok c) by exact (slw_slot_ok R Hlen).
destruct (rbt_slot_bounds c Hslot) as [Hcb Hc8].
assert (Hcz : 0 <= c < 2 ^ 40) by (unfold A_G_REC, A_REC_SPILL, OFF_CALLS in Hcb; lia).
assert (Hsp' : 2 ^ 46 + 64 <= sp0 <= 2 ^ 47) by (rewrite HSTK in Hslo; lia).
assert (HOb : forall pn, In pn O -> In pn (ablocks B ly S)) by exact (RIN ly S _ R O HREP).
assert (HRODb : arodata_okP SEGS RLO RHI B (rdW Wc memb)) by exact (ARO ly S W mem md O _ _ _ _ _ _ _ _ _ HAR HOb HJb HROD).
pose proof HJb as (_ & _ & _ & _ & _ & HFRb & HNEVb & _).
(* the blocks of the state at the call, and record()'s blocks O1 among them *)
assert (Hbnd : forall p n, In (p, n) (ablocks B lyc Sc) -> 4096 <= p /\ p + n < 2 ^ 47 /\ 0 <= n /\ n <= req_size n).
{ intros p n Hpn. destruct (al_blocks _ _ LAWS lyc Sc Wc memc mdc p n HARc Hpn) as (_ & H4 & Hpc & _ & _ & _ & Hn).
  pose proof (req_size_pos n ltac:(lia)) as [Rq1 Rq2]. lia. }
assert (Hp1in : In (p1, slw_n uri) (ablocks B lyc Sc)) by (apply (Permutation_in _ (Permutation_sym HP1)); left; reflexivity).
assert (HND1 : List.NoDup ((p1, slw_n uri) :: Lk)) by exact (Permutation_NoDup HP1 (NDP lyc Sc Wc memc mdc HARc)).
apply NoDup_cons_iff in HND1 as [Hn1 HNDLk].
assert (HO1Lk : forall pn, In pn O1 -> In pn Lk).
{ intros pn Hpn. destruct (proj1 (HO1 pn) Hpn) as [HinO HnDf].
  pose proof (HOb pn HinO) as Hin.
  apply (Permutation_in _ HPS), in_app_iff in Hin as [Hin|Hin]; [contradiction | exact Hin]. }
assert (HinLk : forall pn, In pn Lk -> In pn (ablocks B lyc Sc))
  by (intros pn Hpn; apply (Permutation_in _ (Permutation_sym HP1)); right; exact Hpn).
assert (Hkeepblk : forall q m i, In (q, m) (ablocks B lyc Sc) -> 0 <= i < m -> rdW Wc memb (q + i) = rdW Wc memc (q + i)).
{ intros q m i Hq Hi. destruct (Hbnd q m Hq) as (Hq1 & Hq2 & Hq3 & _).
  destruct (HPA lyc Sc Wc memc mdc q m HARc Hq) as [Ag As].
  apply KEEPb; [lia|]. pose proof Hslot as Hs'.
  destruct Hs' as [(Hc1 & Hc2 & _) | Hc'];
  unfold iv_apart, A_G_REC, REC_SIZE, A_REC_SPILL, SC_SIZE, OFF_CALLS, CALL_SIZE in *; lia. }
(* the recorder after segment C's stores: the slot holds FN and the first argument *)
assert (HREPb : rec_repA B lyc Sc (rdW Wc memb) (rec_record R REC_LV2_WORKER_SET [sarg uri]) (O1 ++ [(p1, slw_n uri)])).
{ change [sarg uri] with ([] ++ [sarg uri]).
  apply (PUSH lyc Sc (rdW Wc memc) lyc Sc (rdW Wc memb) R REC_LV2_WORKER_SET [] O1 (sarg uri) p1 (slw_n uri)
    HREP1 Hlen ltac:(cbn; lia) (slw_harg_len B _ _ _ _ _ _ HSU)).
  - intros a Ha Hn4 Hn8. apply KEEPb; [unfold A_G_REC, REC_SIZE, A_REC_SPILL, SC_SIZE in Ha; lia|].
    fold c in Hn4, Hn8. cbn [length] in Hn8. lia.
  - exact HNA.
  - cbn [length]. change (slw_slot R) with c. replace (c + 8 + 8 * Z.of_nat 0) with (c + 8) by lia. exact HP1b.
  - intros q m i Hq Hi. exact (Hkeepblk q m i (HinLk _ (HO1Lk _ Hq)) Hi).
  - intros pn Hpn. exact (HinLk _ (HO1Lk _ Hpn)).
  - exact Hp1in.
  - lia.
  - pose proof (slw_harg_len B _ _ _ _ _ _ HSU). unfold slw_n. lia.
  - apply (rastr_kept (rdW Wc memc)); [exact Hstr1|]. intros i Hi.
    apply (Hkeepblk p1 (slw_n uri) i Hp1in). unfold slw_n in *. lia.
  - intros pn Hpn Heq. pose proof (HO1Lk _ Hpn) as HpnL.
    destruct (slw_pair_dec pn (p1, slw_n uri)) as [-> | Hne2]; [exact (Hn1 HpnL)|].
    destruct pn as [pp pm]. cbn in Heq. subst pp.
    exact (proj2 (BAP _ _ _ _ _ _ _ _ _ HARc (HinLk _ HpnL) Hp1in Hne2) eq_refl).
  - exact (proj1 (HPA lyc Sc Wc memc mdc p1 _ HARc Hp1in)).
  - exact (proj2 (HPA lyc Sc Wc memc mdc p1 _ HARc Hp1in)). }
(* the second argument at the call: its block, its bytes kept by the stores, its tail *)
destruct (slw_harg_blk lyc Sc Wc memc mdc _ O1 pw worker HARc HSW1) as (x & qw & kw & -> & Hqw & Hqw1 & Hqw2 & Hpw4).
destruct HSW1 as (x' & Ex' & Hinbw & Hstrw & Hlenw & Hapw). injection Ex' as <-.
assert (HSTR : astr_argA B lyc Sc (rdW Wc memb) (in_roP SEGS RLO RHI) [] pw (Some x)).
{ cbn [astr_argA]. split; [lia|]. split.
  { apply (rastr_kept (rdW Wc memc)); [exact Hstrw|]. intros i Hi.
    replace (pw + i) with (qw + (pw + i - qw)) by lia. apply (Hkeepblk qw kw); [exact Hqw | lia]. }
  split; [exact Hlenw|]. left. split; [exact Hinbw | constructor]. }
assert (HTL : atail_vis SEGS Wc memb (pw + Z.of_nat (length x))).
{ apply (cmd_heap_tail_vis lyc Sc Wc memb mdb qw kw); [exact HARb | exact Hqw | lia]. }
(* xstrdup's premises *)
assert (HEVb : st_nev Sc + EV_XSTRDUP <= EV_MAX).
{ unfold EV_SUP_LV2_WORKER_SET, EV_ANSWER, EV_HAND_BACK, EV_XSTRDUP in *. lia. }
assert (HBB : blocks_bytes Sc <= blocks_bytes S + slw_n uri).
{ rewrite (blocks_bytes_bsum B lyc Sc), (blocks_bytes_bsum B ly S).
  rewrite (slw_bsum_perm _ _ HP1), (slw_bsum_perm _ _ HPS), bsum_app, bsum_cons. cbn [snd].
  assert (0 <= bsum Df) by (apply (BSN ly S W mem md Df HAR); intros pn Hpn; exact (HOb _ (HDf _ Hpn))).
  lia. }
assert (HLIVEb : blocks_bytes Sc + LIVE_XSTRDUP x <= LIVE_MAX).
{ unfold LIVE_SUP_LV2_WORKER_SET, LIVE_ANSWER, LIVE_HAND_BACK, LIVE_XSTRDUP, slw_n in *. cbn [sarg] in *. lia. }
assert (HMOKb : mo_ok MT Sc (XM_XSTRDUP MT x)).
{ apply (mok_station MT S Sc (XM_SUP_LV2_WORKER_SET MT R uri (Some x)) (rec_spill_frees R * mo_free MT + XM_XSTRDUP MT (sarg uri))
    _ MTL HMOK MLE1).
  - unfold XM_XSTRDUP. apply (mo_malloc_nonneg MT MTL). lia.
  - unfold XM_SUP_LV2_WORKER_SET, XM_ANSWER, XM_HAND_BACK, XM_XSTRDUP. cbn [sarg].
    pose proof (mo_free_nonneg MT MTL).
    pose proof (mo_malloc_nonneg MT MTL (Z.of_nat (length (snd (sup_lv2_worker_set_m R uri (Some x)))) + 1) ltac:(lia)).
    lia. }
assert (HspB : spZ regsb = sp0 + -64) by (unfold spZ; rewrite Q2; unfold w64; rewrite unsigned_lit_small by lia; lia).
eapply SRr_bind.
{ eapply (cl_callS B LAWS Wc regsb memb (Z_to_bv 64 (BASE + AF_xstrdup)) SUP_LV2_WORKER_SET_STK sp0 (slw_FP O) ly S W mem md []
    lyc Sc mdb k XSTRDUP_STK [] EV_XSTRDUP (-64) (getr regsb 1) [] _ HJb HspB ltac:(reflexivity) ltac:(lia)
    ltac:(lia) ltac:(lia) ltac:(rewrite Q3; exact Hgp) ltac:(rewrite Q4; exact Htp) eq_refl
    ltac:(rewrite Q1; apply ret_ok_codeptr_v; [unfold SLW_RET2, AF_sup_lv2_worker_set; lia | reflexivity])
    ltac:(rewrite Q1, unsigned_lit_small by (unfold SLW_RET2, AF_sup_lv2_worker_set; lia);
          unfold SLW_RET2, AF_sup_lv2_worker_set; lia)
    ltac:(apply achain_low; unfold s0Z; rewrite Q8; unfold w64;
          rewrite unsigned_lit_small by (unfold A_G_REC, A_REC_SPILL, OFF_CALLS in Hcb; lia);
          unfold A_G_REC, A_REC_SPILL, OFF_CALLS in Hcb; lia)).
  - intros HPRE1.
    pose proof (TXSTRDUP fx lyc Sc Wc regsb memb mdb [] pw x HPRE1 HRODb Q10 (or_introl HSTR) HTL HEVb HLIVEb
      HMOKb) as HT.
    unfold apost_base, cfg_at, w64 in HT. exact HT.
  - intros a (r & [] & _). }
cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HJx & HP2 & HK2).
destruct HK2 as (p2 & Hp2r & Hp24 & HPERMx & HAPx & HINBx & HCP & HSRC & HBBx & HMLEx).
pose proof (proj1 HJ2) as HAR2.
destruct (CKEEP _ _ _ _ _ _ _ _ _ _ _ _ _ HJx) as (KPG & KSTK & KBLK).
assert (Hra2 : forall r, acallee_saved r -> getr regs2 (Z_to_bv 5 r) = getr regsb (Z_to_bv 5 r)) by exact HP2.
assert (HIN2 : forall pn, In pn (ablocks B lyc Sc) -> In pn (ablocks B ly2 S2))
  by (intros pn Hpn; apply (Permutation_in _ (Permutation_sym HPERMx)); right; exact Hpn).
rewrite Q1.
apply (D2 ly S W regs mem md ch pu pw uri (Some x) R O ly2 S2 W2 regs2 mem2 md2 (k + EV_XSTRDUP) p1 p2 Df Lk O1 PRE0).
unfold slw_mid2. cbn zeta. fold sp0 c.
split; [exact HJ2|].
split; [unfold EV_XSTRDUP in *; lia|].
split.
{ intros j r Hj. assert (Hj7 : (j < 7)%nat) by (apply (proj1 (nth_error_Some slw_saved j)); rewrite Hj; discriminate).
  apply (aval_mem_kept (rdW Wc memc)); [exact (HFRM j r Hj)|]. intros kk Hkk.
  rewrite KSTK by lia. apply KEEPb; lia. }
split; [etransitivity; [exact (Hra2 2 ltac:(unfold acallee_saved; lia)) | exact Q2]|].
split; [etransitivity; [exact (Hra2 3 ltac:(unfold acallee_saved; lia)) | exact Q3]|].
split; [etransitivity; [exact (Hra2 4 ltac:(unfold acallee_saved; lia)) | exact Q4]|].
split; [etransitivity; [exact (Hra2 8 ltac:(unfold acallee_saved; lia)) | exact Q8]|].
split; [etransitivity; [exact (Hra2 18 ltac:(unfold acallee_saved; lia)) | exact Q18]|].
split; [etransitivity; [exact (Hra2 19 ltac:(unfold acallee_saved; lia)) | exact Q19]|].
split; [etransitivity; [exact (Hra2 20 ltac:(unfold acallee_saved; lia)) | exact Q20]|].
split; [etransitivity; [exact (Hra2 21 ltac:(unfold acallee_saved; lia)) | exact Q21]|].
split; [exact Hp2r|].
split; [intros r Hr; etransitivity; [exact (Hra2 r ltac:(unfold acallee_saved; lia)) | exact (Qhi r Hr)]|].
split.
{ apply (RKEPT lyc Sc (rdW Wc memb) ly2 S2 (rdW W2 mem2) _ _ HREPb).
  - intros pn Hpn. exact (HIN2 _ (RIN _ _ _ _ _ HREPb pn Hpn)).
  - intros a Ha. apply KPG. apply recb_grec_in. unfold REC_SIZE. exact Ha.
  - intros a Ha. apply KPG. apply recb_spill_in. unfold SC_SIZE. exact Ha.
  - intros p n i Hpn Hi. pose proof (RIN _ _ _ _ _ HREPb _ Hpn) as Hpc.
    destruct (Hbnd p n Hpc) as (_ & _ & _ & Rn).
    exact (KBLK p n i Hpc (HIN2 _ Hpc) ltac:(lia)). }
split; [exact HO1|]. split; [exact HDf|]. split; [exact HDf0|]. split; [exact HPS|].
split; [eapply Permutation_trans; [exact HPERMx | apply perm_skip; exact HP1]|].
assert (Hnw : 1 <= LIVE_XSTRDUP x) by (unfold LIVE_XSTRDUP; lia).
split; [exact Hn1|].
split.
{ intros Hin. rewrite Forall_forall in HAPx.
  pose proof (HAPx (p2, slw_n (Some x)) (Permutation_in _ (Permutation_sym HP1) Hin)) as Hap.
  unfold iv_apart, slw_n, LIVE_XSTRDUP in *. cbn [sarg fst snd] in *. lia. }
split; [lia|]. split; [lia|]. split; [exact HCP|].
exact (mle_station MT S Sc S2 _ _ MTL MLE1 HMLEx).
Qed.

Ltac slw_md N := lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?m |} _ =>
  set (N := m) in *; clearbody N end.

(* --- segment C: from the return of the first xstrdup (+0xc0) to the call of the second (+0x10c) ------------ *)
Lemma slw_C_ok : SLW_C_stmt B MT.
Proof.
intros ly S W regs mem md ch pu pw uri worker R O lyc Sc Wc regs1 memc mdc k p1 Df Lk O1 HPRE MID.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HPRE as HPRE0. pose proof MID as MID0.
destruct HPRE as (HFN & HFM0 & HROD & HRO & H10 & Hpub & H11 & Hpwb & HSU & HSW & HREP & HFR8 & HEV & HLIVE & HMOK).
pose proof HFN as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
destruct MID as (HJ & Hk & HFRM & R2 & R3 & R4 & R8 & R9 & R18 & R20 & R21 & R10 & Rhi & HREP1 & HO1 & HDf & HDf0 &
  HPS & HP1 & Hap1 & Hp1 & Hstr1 & HSW1 & MLE1).
pose proof (proj1 HJ) as HAR1.
set (sp0 := spZ regs) in *. set (c := slw_slot R) in *.
assert (Hlen : (length (r_calls R) <= 16)%nat) by exact (slw_rep_len B _ _ _ _ _ HREP).
assert (Hslot : rbt_slot_ok c) by exact (slw_slot_ok R Hlen).
destruct (rbt_slot_bounds c Hslot) as [Hcb Hc8].
assert (HSTK : SUP_LV2_WORKER_SET_STK = 16592) by (vm_compute; reflexivity).
destruct (slw_harg_blk lyc Sc Wc memc mdc _ O1 pw worker HAR1 HSW1) as (x & qw & kw & Ew & Hqw & Hqw1 & Hqw2 & Hpw4).
set (n0 := Z.of_nat (length (r_calls R))) in *.
set (E := Eimg (Ereg regs1 (slw_extra regs n0 c))).
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EEo : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs1 rr).
{ intros n rr Hn. pose proof (bv_unsigned_in_range 5 rr) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  subst E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn. }
assert (EX : forall j, (j < 10)%nat -> ew E (32 + j) = nth j (slw_extra regs n0 c) (Z_to_bv 64 0))
  by (intros j Hj; subst E; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
assert (EC : ew E 34 = Z_to_bv 64 c) by (change 34%nat with (32 + 2)%nat; rewrite EX by lia; reflexivity).
assert (ESB : ew E 32 = Z_to_bv 64 SB) by (change 32%nat with (32 + 0)%nat; rewrite EX by lia; reflexivity).
assert (Hc0 : 0 <= c < 2 ^ 40) by (unfold A_G_REC, A_REC_SPILL, OFF_CALLS in Hcb; lia).
pose proof (slw_seed B) as SEED. slw_hyps SEED.
destruct (SEED SLW_RET1 slw_sregs1 (slw_nargs 0) 8 lyc Sc Wc memc mdc regs regs1 (sp0 - 64) n0 c HAR1) as [HS SHOK].
{ lia. } { lia. } { Z.div_mod_to_equations. lia. } { subst n0; lia. } { exact Hslot. }
{ rewrite R2. unfold w64. rewrite unsigned_lit_small by lia. reflexivity. }
{ replace (sp0 - 64 + 64) with sp0 by lia. exact HFRM. }
{ fold E. apply regs_ok_by_cases. intros r Hr. cbv [all_regs In] in Hr.
  repeat (destruct Hr as [<- | Hr];
    [ lazymatch goal with |- getr _ ?rr = sv_denot _ (sr_get ?l ?rr) =>
        let v := eval vm_compute in (sr_get l rr) in change (sr_get l rr) with v end;
      first [ (cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; symmetry; apply EEo; reflexivity)
            | (cbn [sv_denot]; rewrite getr_zero; reflexivity)
            | idtac ]
    | ]); try (destruct Hr; fail).
  - cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned, EC. exact R8.
  - cbn [sv_denot]. rewrite EC, unsigned_lit_small by lia. exact R18.
  - cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned, ESB. exact R20.
  - unfold slw_shx4. rewrite (denot_shx E 34 32 4 c SB EC ESB) by (unfold SB, A_G_REC, A_REC_SPILL, OFF_CALLS in *; lia).
    exact R21. }
{ apply Forall_cons; [|apply Forall_nil].
  apply (chunk_ok_val SEGS _ _ c 4 4 (SLit 0) 0); [reflexivity | lia | lia |].
  apply (RecBLemmas.val_mem_view SEGS). exact (slw_slot_nargs B _ _ _ _ _ _ _ HREP1 Hlen). }
{ vm_compute. reflexivity. }
{ lia. }
fold E in HS, SHOK.
unfold cfg_at, w64.
assert (UC : bv_unsigned (ew E RB_C) = c) by (unfold RB_C; rewrite EC; apply unsigned_lit_small; lia).
assert (UC' : bv_unsigned (ew E 34%nat) = c) by exact UC.
paj_run_tok RUN HS HJ SHOK slw_Bspan.
{ slw_awr UC Hslot. }
slw_md mdC1.
assert (E9 : ew E 9 = Z_to_bv 64 pw) by (rewrite (EEo 9%nat 9%bv eq_refl); exact R9).
psrr_branch_tok RUN BR HS SHOK slw_Bspan.
2: { exfalso. rewrite branch_ne_U, (U_atom E 9 pw E9 ltac:(lia)), U_SLit in Hc.
     replace (zcanon 0) with 0 in Hc by (vm_compute; reflexivity).
     apply negb_false_iff, Z.eqb_eq in Hc. lia. }
(* s1 <> 0: the second argument is a string; run to the call of xstrdup at +0x10c *)
paj_run_tok RUN HS HJ SHOK slw_Bspan.
{ slw_awr UC Hslot. }
slw_md mdC2.
pmkst HS.
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
prreg HS (8%bv : bv 5) Q8. prreg HS (10%bv : bv 5) Q10. prreg HS (18%bv : bv 5) Q18. prreg HS (19%bv : bv 5) Q19.
prreg HS (20%bv : bv 5) Q20. prreg HS (21%bv : bv 5) Q21.
lazymatch goal with
| H1 : frame_of _ _ (mrestrict _ memc) (mrestrict _ ?m1), H2 : frame_of _ _ (mrestrict _ ?m1) (mrestrict _ ?m2) |- _ =>
  pose proof (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun a => c + 4 <= a < c + 16) H1
    ltac:(intros b wlo whi a' Hin Hrr; vm_compute in Hin;
          repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?UC' in Hrr; lia|]);
          destruct Hin)) as KEEP1;
  pose proof (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun a => c + 4 <= a < c + 16) H2
    ltac:(intros b wlo whi a' Hin Hrr; vm_compute in Hin;
          repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?UC' in Hrr; lia|]);
          destruct Hin)) as KEEP2
end.
assert (KEEPb : forall a, 0 <= a < 2 ^ 64 -> ~ (slw_slot R + 4 <= a < slw_slot R + 16) ->
  rdW Wc (ms_mem ms0) a = rdW Wc memc a).
{ intros a Ha H1. fold c in H1. rewrite (KEEP2 a Ha H1). exact (KEEP1 a Ha H1). }
pose proof (st_ok_region_nth E _ _ 1 _ HS eq_refl) as HRg1. cbn [ms_mem restrict] in HRg1.
pose proof (st_ok_region_nth E _ _ 2 _ HS eq_refl) as HRg2. cbn [ms_mem restrict] in HRg2.
pose proof (field_of_region_any E _ 34 c _ _ _ _ _ 4 4 (SLit 1) HRg1 UC' ltac:(cbn; tauto) ltac:(cbn; lia)) as V4.
pose proof (field_of_region_any E _ 34 c _ _ _ _ _ 8 8 (SOff 10 0) HRg2 UC' ltac:(cbn; tauto) ltac:(cbn; lia)) as V8.
assert (D4 : bv_unsigned (sv_denot E (SLit 1)) mod 2 ^ (8 * Z.of_N 4) = 1)
  by (cbn [sv_denot]; rewrite unsigned_lit_small by lia; reflexivity).
assert (D8 : bv_unsigned (sv_denot E (SOff 10 0)) mod 2 ^ (8 * Z.of_N 8) = p1).
{ cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (EEo 10%nat 10%bv eq_refl), R10. unfold w64.
  rewrite unsigned_lit_small by lia. apply Z.mod_small. cbn. lia. }
rewrite D4 in V4. rewrite D8 in V8.
apply (aval_mem_view SEGS) in V4. apply (aval_mem_view SEGS) in V8.
assert (Q1' : getr (ms_regs ms0) 1 = Z_to_bv 64 (BASE + SLW_RET2)) by (rewrite Q1; reflexivity).
assert (Q2' : getr (ms_regs ms0) 2 = w64 (spZ regs - 64)) by (rewrite Q2, (EEo 2%nat 2%bv eq_refl); exact R2).
assert (Q3' : getr (ms_regs ms0) 3 = getr regs 3) by (rewrite Q3, (EEo 3%nat 3%bv eq_refl); exact R3).
assert (Q4' : getr (ms_regs ms0) 4 = getr regs 4) by (rewrite Q4, (EEo 4%nat 4%bv eq_refl); exact R4).
assert (Q8' : getr (ms_regs ms0) 8 = w64 (slw_slot R)) by (rewrite Q8; exact EC).
assert (Q10' : getr (ms_regs ms0) 10 = w64 pw) by (rewrite Q10; exact E9).
assert (Q18' : getr (ms_regs ms0) 18 = w64 (slw_slot R + 4)) by (rewrite Q18, UC'; reflexivity).
assert (Q19' : getr (ms_regs ms0) 19 = w64 (slw_slot R + 8)) by (rewrite Q19, UC'; reflexivity).
assert (Q20' : getr (ms_regs ms0) 20 = w64 SHADOW_OFF) by (rewrite Q20, ESB; reflexivity).
assert (Q21' : getr (ms_regs ms0) 21 = Z_to_bv 64 (SB + (c + 4) / 8)).
{ rewrite Q21, <- (denot_shx E 34 32 4 c SB EC ESB) by (unfold SB, A_G_REC, A_REC_SPILL, OFF_CALLS in *; lia).
  cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
assert (Qhi : forall r, 22 <= r <= 27 -> getr (ms_regs ms0) (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)).
{ intros r Hr. assert (Hr6 : r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
  destruct Hr6 as [-> | [-> | [-> | [-> | [-> | ->]]]]];
  rewrite (st_ok_restrict_reg SEGS (w_H Wc) E _ _ _ HS); cbn [ms_regs];
  lazymatch goal with |- sv_denot _ (sr_get ?a ?rr2) = _ =>
    let v := eval vm_compute in (sr_get a rr2) in change (sr_get a rr2) with v end;
  cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned;
  lazymatch goal with |- ew E ?n = getr regs (Z_to_bv 5 ?m) =>
    rewrite (EEo n (Z_to_bv 5 m) eq_refl); apply Rhi; lia end. }
pose proof slw_sig_xstrdup as SX. slw_hyps SX. rewrite SX.
exact (slw_xcall ly S W regs mem md ch pu pw uri worker R O lyc Sc Wc regs1 memc mdc k p1 Df Lk O1
  (ms_regs ms0) (ms_mem ms0) mdC2 HPRE0 MID0 HJ KEEPb V4 V8 Q1' Q2' Q3' Q4' Q8' Q10' Q18' Q19' Q20' Q21' Qhi).
Qed.

End e.
End f.
End d.
