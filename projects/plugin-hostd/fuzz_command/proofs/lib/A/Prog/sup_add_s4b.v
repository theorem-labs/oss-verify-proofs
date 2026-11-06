(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: check_reply's ASan walk (fuzz_command.asan, 0x86d78) assembled from its
   segments, as proofs/cgif/cgif_file_fuzzer/lib/A/ACh5.v assembles cgif_close's (pb_cgif_closeX):
     s1 the entry to the memchr call, s2 memchr / check_reply_answer / sup_reply_code, s3 the code's split,
     s4 snprintf, s4b rec_code_declared, s5 strcmp, s6 strlen / rec_shape_of, s7 syntax_reply_matches twice,
     s8 the frame's release and the return.
   snprintf is the only call that changes the FP state, so s4b, s5 and s8 (the segments after it) are taken at every
   FP state and s4 uses them at the state the wrapper returns.
   `pb_check_reply` is tcheck_reply_spec (lib/A/Prog/check_reply_c.v). The walk's facts at the entry that the
   statement no longer states come from its premises: the record's cells (replace_str flag byte, stack guard, errno)
   from CmdRecCells' cmd_rec_cells, the recorder's GOT words from cmd_ro_ok's RO_ptr_a70xx bytes, the read-only
   ranges from CmdRecRo's cmd_ro_in_img, and the words' shadow from AR's zshadow_ok of the stack window
   [ly_stk_lo, ly_stk_hi) (the words lie in it: spZ regs <= w and w + WORDS_W + 12 <= ly_stk_hi ly). The kit lemmas
   take the image facts IMG (cmd_img_facts); the segments take CmdRecImg's cmd_heap_tail_vis, and its
   cmd_prog_unowned and cmd_rom_view_on at IMG, so no record fact is a Section hypothesis (the walk hypotheses keep
   cgif's names; the record facts are lemmas of lib/A/Prog/CmdRecFacts.v). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/check_reply.v, with its module names changed; 237 of its 266 lines of code are new or changed and 123 lines of the source are left out. *)
(* sup_add's walk, stage M2 -> M3 (plugin-hostd/fuzz_command, ASan build): one call of xstrdup.

   `s4_call_post` turns the call's result (the two journals, the kept registers, xstrdup's post) into the stage's
   mid-state at the return, with the copy in the block accounting but not yet in the recorder, and the fresh
   block's facts; `s4_call` composes xstrdup's statement by cl_callS and hands that state to a continuation. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdPaLib PaCall PaDenot PaSB PaLibH.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs RtFormat.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
CmdGlob CmdAddr CmdBase CmdRep CmdObj CmdRo CmdZsh.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
rec_calls_free_c xstrdup_c arg_i_c mix_call_c hand_back_c answer_c sup_add_c sup_add_s0 sup_add_lem sup_add_s4a.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdRecFacts.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation SIG s := (@pa_sigma _ cmd_listing PI s).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
Hypothesis HB : CmdBSyms B.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis MTL : ameter_laws MT.
Hypothesis SIGP : cmd_sig_prog.
Hypothesis IMG : cmd_img_facts SEGS B.
Let cif_prog_img : forall a, inFP cmd_PG a -> in_img SEGS a :=
  CmdRecBase.cif_prog_img _ _ IMG.
Let cif_relro_img : forall a, CMD_RLO <= a < CMD_RHI -> in_img SEGS a :=
  CmdRecBase.cif_relro_img _ _ IMG.
Let cif_prog_not_ro : forall a, inFP cmd_PG a -> ~ in_roP SEGS CMD_RLO CMD_RHI a :=
  CmdRecBase.cif_prog_not_ro _ _ IMG.
Let cmd_ro_in_img : cmd_ro_in (in_roP SEGS CMD_RLO CMD_RHI) :=
  CmdRecRo.cmd_ro_in_img SEGS B LAWS HB IMG.
Let cmd_heap_tail_vis : forall ly S (W : world SEGS) mem md p n e, AR SEGS B ly S W mem md ->
  In (p, n) (ablocks B ly S) -> p <= e < p + req_size n -> atail_vis SEGS W mem e :=
  CmdRecImg.cmd_heap_tail_vis SEGS B LAWS HB.
Let cmd_tail_vis_at : forall ly S (W : world SEGS) mem md e, AR SEGS B ly S W mem md -> In e cmd_ro_ends ->
  atail_vis SEGS W mem e :=
  CmdRecRo.cmd_tail_vis_at SEGS B LAWS HB IMG.
Hypothesis TXSTRDUP : forall fx0 : YK11.FPState, @txstrdup_spec fx0 rc SK PI B MT.

(* after the call: the mid-state at the return, the copy in the accounting (Ok) but not yet in the recorder (Oj) *)
Lemma s4_call_post : forall ly S W regs mem md R O lyc Sc Wc regsA memA mdA pos args Oj ev acc live str sp1
    ly2 S2 W2 regs2 mem2 md2 p,
  s4_mid B MT ly S W regs mem md R O lyc Sc Wc regsA memA mdA pos args Oj Oj ev acc live ->
  sp1 = sa_s1 (spZ regs) ->
  ajournal SEGS B SUP_ADD_STK (spZ regs) (sa_FP O) ly S W mem md [(1, pos)] ly2 S2 W2 mem2 md2 (ev + EV_XSTRDUP) ->
  ajournal SEGS B XSTRDUP_STK sp1 [] lyc Sc Wc memA mdA [] ly2 S2 W2 mem2 md2 EV_XSTRDUP ->
  aregs_preserved regsA regs2 ->
  4096 <= p ->
  Permutation (ablocks B ly2 S2) ((p, LIVE_XSTRDUP str) :: ablocks B lyc Sc) ->
  Forall (fun qk => iv_apart p (LIVE_XSTRDUP str) (fst qk) (snd qk)) (ablocks B lyc Sc) ->
  astr_atR (rdW W2 mem2) p str ->
  Z.of_nat (length str) <= LMAX ->
  mo_le MT Sc S2 (XM_XSTRDUP MT str) ->
  s4_mid B MT ly S W regs mem md R O ly2 S2 W2 regs2 mem2 md2 pos args Oj (Oj ++ [(p, LIVE_XSTRDUP str)])
    (ev + EV_XSTRDUP) (acc + XM_XSTRDUP MT str) (live + LIVE_XSTRDUP str) /\
  s4_fresh B ly2 S2 (rdW W2 mem2) Oj p (LIVE_XSTRDUP str) str.
Proof using fx rc SK PI HB LAWS MTL cif_prog_img cmd_heap_tail_vis.
intros ly S W regs mem md R O lyc Sc Wc regsA memA mdA pos args Oj ev acc live str sp1 ly2 S2 W2 regs2 mem2 md2 p
  HMID Hsp1 HJout HJin HPres Hp4096 HPerm HFor Hstrp Hlenstr HMLEx.
subst sp1.
destruct HMID as (HC & H20 & H22 & H23 & H24 & H27 & HBUF & HREP & HSUB & HACCT & HMLE).
unfold sa_core in HC. cbv zeta in HC.
destruct HC as (HJ & HFRAME & Hs16 & Hs24 & Hs48 & HFLAG & A2 & A3 & A4 & A8 & A9 & A18 & A19 & A21 & A25 & A26).
pose proof (proj1 HJ) as HARc.
pose proof HJ as (_ & _ & _ & _ & _ & Hfrsc & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
destruct Hstk as (Hal16 & _ & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & _).
assert (HSTKa : 176 <= SUP_ADD_STK /\ 0 <= XSTRDUP_STK) by (vm_compute; split; discriminate).
pose proof (s4_s1_facts (spZ regs) Hal16) as Hs1v.
pose proof HJin as (HAR2 & Hly2 & _ & _ & _ & _ & _ & _ & K1 & K2 & K3 & K4 & _).
pose proof HACCT as (_ & _ & _ & ACC4 & _).
assert (HEFR : frame_addr ly2 1 pos = frame_addr lyc 1 pos)
  by (pose proof Hly2 as (_ & _ & _ & _ & _ & EF & _); unfold frame_addr; rewrite EF; reflexivity).
assert (HEFL : flag_addr ly2 1 pos = flag_addr lyc 1 pos)
  by (pose proof Hly2 as (_ & _ & _ & _ & _ & EF & _); unfold flag_addr; rewrite EF; reflexivity).
assert (HinS2 : forall pn, In pn (ablocks B lyc Sc) -> In pn (ablocks B ly2 S2))
  by (intros pn Hpn; eapply Permutation_in; [apply Permutation_sym; exact HPerm | right; exact Hpn]).
assert (Hnoopen : ~ YI16.sink_open_fp (@nil (Z * Z))) by (intros (r & Hr & _); destruct Hr).
assert (KIMG : forall a, in_rec a -> rdW W2 mem2 a = rdW Wc memA a).
{ intros a Ha. pose proof (s4_rec_pg a Ha) as HPG.
  destruct (sa_prog_unowned B HB LAWS a HPG) as [Hown Herr].
  exact (K3 a (cif_prog_img a HPG) Hown Herr (fp_spares_closed [] a Hnoopen (inFP_nil a))). }
assert (KBLK : forall p0 n0 i, In (p0, n0) (ablocks B lyc Sc) -> 0 <= i < n0 ->
   rdW W2 mem2 (p0 + i) = rdW Wc memA (p0 + i)).
{ intros p0 n0 i Hin Hi. pose proof (req_size_pos n0 ltac:(lia)) as [_ Hrq].
  exact (K2 p0 n0 i Hin (HinS2 (p0, n0) Hin) ltac:(lia) (inFP_nil _)). }
assert (KSTK : forall a, sa_s1 (spZ regs) <= a < spZ regs -> rdW W2 mem2 a = rdW Wc memA a)
  by (intros a Ha; exact (K1 a ltac:(lia) ltac:(lia) (inFP_nil a))).
assert (Hin1pos : In (1, pos) (frames Sc)) by (rewrite Hfrsc; left; reflexivity).
assert (HFB : fs_frame_bytes 1 = 128) by (vm_compute; reflexivity).
assert (KF8 : forall x, frame_addr lyc 1 pos <= x < frame_addr lyc 1 pos + fs_frame_bytes 1 ->
   rdW W2 mem2 x = rdW Wc memA x).
{ intros x Hx. refine (K4 1 pos x Hin1pos _ (inFP_nil x)).
  left. unfold in_zr, frame_rng. cbn [fst snd]. exact Hx. }
assert (KFS : forall x, shadow_addr (frame_addr lyc 1 pos) <= x < shadow_addr (frame_addr lyc 1 pos) + fs_frame_bytes 1 / 8 ->
   rdW W2 mem2 x = rdW Wc memA x).
{ intros x Hx. refine (K4 1 pos x Hin1pos _ (inFP_nil x)).
  right. unfold in_zr. cbn [fst snd]. exact Hx. }
assert (KR : forall z, In z s4_kz -> getr regs2 (Z_to_bv 5 z) = getr regsA (Z_to_bv 5 z))
  by (intros z Hz; exact (HPres z (s4_kz_cs z Hz))).
assert (Hnew2 : In (p, LIVE_XSTRDUP str) (ablocks B ly2 S2))
  by (eapply Permutation_in; [apply Permutation_sym; exact HPerm | left; reflexivity]).
split.
- unfold s4_mid. rewrite HEFR. split.
  + unfold sa_core. cbv zeta. rewrite HEFR, HEFL.
    split; [exact HJout|].
    split.
    { intros j r Hj.
      assert (Hjlt : (j < 13)%nat) by (apply (proj1 (nth_error_Some sa_saved j)); rewrite Hj; discriminate).
      apply (s4_aval_kept _ _ _ 8 _ (HFRAME j r Hj)). intros x Hx. apply KSTK. lia. }
    split; [apply (s4_aval_kept _ _ _ 8 _ Hs16); intros x Hx; apply KSTK; lia|].
    split; [apply (s4_aval_kept _ _ _ 8 _ Hs24); intros x Hx; apply KSTK; lia|].
    split; [apply (s4_aval_kept _ _ _ 8 _ Hs48); intros x Hx; apply KSTK; lia|].
    split; [unfold rdword in HFLAG |- *; rewrite !KF8 by lia; exact HFLAG|].
    split; [s4_kr KR A2 2|]. split; [s4_kr KR A3 3|]. split; [s4_kr KR A4 4|].
    split; [s4_kr KR A8 8|]. split; [s4_kr KR A9 9|]. split; [s4_kr KR A18 18|].
    split; [s4_kr KR A19 19|]. split; [s4_kr KR A21 21|]. split; [s4_kr KR A25 25|].
    s4_kr KR A26 26.
  + split; [s4_kr KR H20 20|]. split; [s4_kr KR H22 22|]. split; [s4_kr KR H23 23|].
    split; [s4_kr KR H24 24|]. split; [s4_kr KR H27 27|].
    split.
    { intros i Hi. rewrite KFS; [exact (HBUF i Hi)|].
      unfold shadow_addr. rewrite HFB. change (128 / 8) with 16. lia. }
    split.
    { apply (rec_repA_kept B HB LAWS lyc Sc (rdW Wc memA) ly2 S2 (rdW W2 mem2) _ Oj HREP).
      - exact KIMG.
      - intros p0 n0 i Hin Hi. exact (KBLK p0 n0 i (ACC4 (p0, n0) Hin) Hi).
      - intros pn Hpn. exact (HinS2 pn (ACC4 pn Hpn)). }
    split; [intros pn Hpn; apply in_or_app; left; exact Hpn|].
    split.
    * exact (s4_acct_step B ly S R O lyc Sc Oj live ly2 S2 p (LIVE_XSTRDUP str) HACCT HPerm HFor
               ltac:(unfold LIVE_XSTRDUP; lia)).
    * exact (mle_station MT S Sc S2 acc (XM_XSTRDUP MT str) MTL HMLE HMLEx).
- unfold s4_fresh.
  split; [exact Hnew2|]. split; [exact Hp4096|]. split; [reflexivity|]. split; [exact Hlenstr|].
  split; [exact Hstrp|].
  split.
  { intros Hin. apply in_map_iff in Hin as ((p0, n0) & Hfst & Hin0). cbn [fst] in Hfst. subst p0.
    destruct (rec_repA_fields B HB LAWS lyc Sc (rdW Wc memA) (rec_record R REC_ADD args) Oj HREP)
      as (_ & _ & _ & _ & _ & _ & _ & _ & Hsz).
    destruct (Hsz (p, n0) Hin0) as (Hin0c & Hn1 & _). cbn [snd] in Hn1.
    pose proof (proj1 (Forall_forall _ _) HFor (p, n0) Hin0c) as Hap.
    unfold iv_apart in Hap. cbn [fst snd] in Hap. unfold LIVE_XSTRDUP in Hap. lia. }
  pose proof (blk_off_imgP B ly2 S2 W2 mem2 md2 p (LIVE_XSTRDUP str) HAR2 Hnew2) as Hoff.
  pose proof (req_size_pos (LIVE_XSTRDUP str) ltac:(unfold LIVE_XSTRDUP; lia)) as [_ Hrq].
  unfold off_img in Hoff. unfold iv_apart, A_G_REC, REC_SIZE, A_REC_SPILL, SC_SIZE.
  split; lia.
Qed.

(* one call of xstrdup at a mid-state: the copy it makes joins the block accounting *)
Lemma s4_call : forall ly S (W : world SEGS) (regs : bvmap 5 word) mem md ch pu id pp pcl uri placement client R O
  lyc Sc (Wc : world SEGS) (regsA : bvmap 5 word) memA mdA pos args Oj ev acc live q str retk,
  sa_cx B MT ly S W regs mem md ch pu id pp pcl uri placement client R O ->
  s4_mid B MT ly S W regs mem md R O lyc Sc Wc regsA memA mdA pos args Oj Oj ev acc live ->
  getr regsA 1 = Z_to_bv 64 (BASE + retk) -> 0 <= retk < 2 ^ 40 -> retk mod 2 = 0 ->
  getr regsA 10 = w64 q ->
  astr_argA B lyc Sc (rdW Wc memA) (in_roP SEGS RLO RHI) [] q (Some str) ->
  atail_vis SEGS Wc memA (q + Z.of_nat (length str)) ->
  ev + EV_XSTRDUP <= EV_SUP_ADD R ->
  live + LIVE_XSTRDUP str <= LIVE_SUP_ADD uri id placement client (snd (sup_add_m R uri id placement client)) ->
  acc + XM_XSTRDUP MT str <= XM_SUP_ADD MT R uri id placement client (snd (sup_add_m R uri id placement client)) ->
  (forall ly1 S1 (W1 : world SEGS) (regs1 : bvmap 5 word) mem1 md1 p n,
     s4_mid B MT ly S W regs mem md R O ly1 S1 W1 regs1 mem1 md1 pos args Oj (Oj ++ [(p, n)])
       (ev + EV_XSTRDUP) (acc + XM_XSTRDUP MT str) (live + LIVE_XSTRDUP str) ->
     s4_fresh B ly1 S1 (rdW W1 mem1) Oj p n str -> getr regs1 10 = w64 p ->
     SRr SEGS W1 (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + retk)) mem1 (seg_rom SEGS)) md1)
       (sa_final B MT ly S W regs mem md R O uri id placement client)) ->
  SRr SEGS Wc (mkCfg (mkst regsA (Z_to_bv 64 (SIG CS_xstrdup)) memA (seg_rom SEGS)) mdA)
    (sa_final B MT ly S W regs mem md R O uri id placement client).
Proof using fx rc SK PI HB LAWS MTL SIGP cif_prog_img cif_relro_img cif_prog_not_ro cmd_ro_in_img cmd_heap_tail_vis
  cmd_tail_vis_at TXSTRDUP.
intros ly S W regs mem md ch pu id pp pcl uri placement client R O lyc Sc Wc regsA memA mdA pos args Oj ev acc live
  q str retk HCX HMID Hra Hrk1 Hrk2 Ha0 HSTR HTAIL HEVb HLIVEb HACCb KONT.
pose proof HMID as HMID0.
unfold sa_cx in HCX. cbv zeta in HCX.
destruct HCX as (HPRE & Hfr & HROD & HRO & H10 & Hpu & H11 & Hid & H12 & Hpp & H13 & Hpc & HU & HP & HPT &
  HC & HCT & HREP0 & Hev & Hlive & MOK).
destruct HMID as (HCORE & H20 & H22 & H23 & H24 & H27 & HBUF & HREP & HSUB & HACCT & HMLE).
unfold sa_core in HCORE. cbv zeta in HCORE.
destruct HCORE as (HJ & HFRAME & Hs16 & Hs24 & Hs48 & HFLAG & A2 & A3 & A4 & A8 & A9 & A18 & A19 & A21 & A25 & A26).
pose proof HPRE as (HAR0 & _ & _ & _ & _ & Hstk & _).
destruct Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & _).
pose proof pa_base_lo as HBLO. pose proof pa_B_ok as (HB0 & HB1 & HB4).
assert (HSTKa : 176 <= SUP_ADD_STK /\ XSTRDUP_STK + 176 <= SUP_ADD_STK /\ 0 <= XSTRDUP_STK)
  by (vm_compute; repeat split; discriminate).
pose proof (s4_s1_facts (spZ regs) Hal16) as Hs1v.
assert (Hspa : spZ regsA = spZ regs + (sa_s1 (spZ regs) - spZ regs))
  by (unfold spZ at 1; rewrite A2; unfold w64; rewrite unsigned_lit_small by lia; lia).
assert (Hal : (sa_s1 (spZ regs) - spZ regs) mod 16 = 0).
{ destruct Hs1v as [Hv | Hv]; rewrite Hv;
  [replace (spZ regs - 160 - spZ regs) with (-160) by lia | replace (spZ regs - 176 - spZ regs) with (-176) by lia];
  reflexivity. }
assert (HSIGX : SIG CS_xstrdup = BASE + AF_xstrdup).
{ rewrite (SIGP CS_xstrdup); [reflexivity|]. cbn [cmd_prog_syms In]; repeat (first [left; reflexivity | right]). }
destruct (sa_achain B HB LAWS ly S W regs mem md ch R O [(1, pos)] lyc Sc Wc memA mdA ev
  HPRE HREP0 HJ HFRAME) as [ch1 HCH].
assert (HCH' : achain lyc (rdW Wc memA) (spZ regs + (sa_s1 (spZ regs) - spZ regs)) (s0Z regsA) ch1).
{ unfold s0Z. rewrite A8. unfold w64. rewrite unsigned_lit_small by lia.
  replace (spZ regs + (sa_s1 (spZ regs) - spZ regs)) with (sa_s1 (spZ regs)) by lia. exact HCH. }
assert (HARO : arodata_okP SEGS RLO RHI B (rdW Wc memA))
  by exact (sa_aro_kept B HB LAWS IMG
    SUP_ADD_STK (spZ regs) ly S W mem md [(1, pos)] lyc Sc Wc memA mdA ev R O HAR0 HJ HREP0 HROD).
pose proof HJ as (_ & _ & _ & _ & _ & _ & Hnevc & _).
pose proof HACCT as (_ & _ & _ & _ & ACC5).
assert (HEVc : st_nev Sc + EV_XSTRDUP <= EV_MAX) by lia.
assert (HLIVEc : blocks_bytes Sc + LIVE_XSTRDUP str <= LIVE_MAX) by lia.
assert (HXnn : 0 <= XM_XSTRDUP MT str) by (unfold XM_XSTRDUP; apply (mo_malloc_nonneg MT MTL); lia).
assert (HMOKc : mo_ok MT Sc (XM_XSTRDUP MT str))
  by exact (mok_station MT S Sc (XM_SUP_ADD MT R uri id placement client (snd (sup_add_m R uri id placement client)))
    acc (XM_XSTRDUP MT str) MTL MOK HMLE HXnn HACCb).
assert (Hret : YK0s.ret_ok (Z_to_bv 64 (BASE + retk))) by (apply ret_ok_codeptr_v; [lia | exact Hrk2]).
assert (Hret4 : 4096 <= bv_unsigned (Z_to_bv 64 (BASE + retk))) by (rewrite unsigned_lit_small by lia; lia).
pose proof HSTR as (_ & _ & HLS & _).
clear HFRAME Hs16 Hs24 Hs48 HFLAG HBUF HREP HSUB HACCT HU HP HPT HC HCT.
eapply SRr_bind.
{ apply (cl_callS B LAWS Wc regsA memA (Z_to_bv 64 (SIG CS_xstrdup)) SUP_ADD_STK (spZ regs) (sa_FP O)
    ly S W mem md [(1, pos)] lyc Sc mdA ev XSTRDUP_STK [] EV_XSTRDUP (sa_s1 (spZ regs) - spZ regs)
    (Z_to_bv 64 (BASE + retk)) ch1
    (fun ly' S' W' regs' mem' md' => exists p : Z, getr regs' 10 = w64 p /\ 4096 <= p < 2 ^ 64 /\
       Permutation (ablocks B ly' S') ((p, LIVE_XSTRDUP str) :: ablocks B lyc Sc) /\
       Forall (fun qk => iv_apart p (LIVE_XSTRDUP str) (fst qk) (snd qk)) (ablocks B lyc Sc) /\
       in_blockA (ablocks B ly' S') p (LIVE_XSTRDUP str) /\
       astr_atR (rdW W' mem') p str /\ astr_atR (rdW W' mem') q str /\
       blocks_bytes S' <= blocks_bytes Sc + LIVE_XSTRDUP str /\
       mo_le MT Sc S' (XM_XSTRDUP MT str))
    HJ Hspa Hal ltac:(lia) ltac:(lia) ltac:(lia) A3 A4 Hra Hret Hret4 HCH').
  - intros HPRE1. eapply SRr_mono.
    { rewrite HSIGX.
      apply (TXSTRDUP fx lyc Sc Wc regsA memA mdA ch1 q str HPRE1 HARO Ha0 (or_introl HSTR) HTAIL
        HEVc HLIVEc HMOKc). }
    cbv beta. unfold apost_base. intros W3 c3 _ (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ3 & HP3 & HK3).
    exists ly3, S3, regs3, mem3, md3. split; [rewrite Hra; reflexivity|]. split; [exact HJ3|].
    split; [exact HP3 | exact HK3].
  - intros a Ha. destruct (inFP_nil a Ha). }
cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJout & HJin & HPres & HK).
destruct HK as (p & Hp10 & Hp4096 & HPerm & HFor & _ & Hstrp & _ & _ & HMLEx).
destruct (s4_call_post ly S W regs mem md R O lyc Sc Wc regsA memA mdA pos args Oj ev acc live str
  (spZ regs + (sa_s1 (spZ regs) - spZ regs)) ly2 S2 W2 regs2 mem2 md2 p HMID0 ltac:(lia) HJout HJin HPres
  ltac:(lia) HPerm HFor Hstrp ltac:(lia) HMLEx) as [HM HF].
exact (KONT ly2 S2 W2 regs2 mem2 md2 p (LIVE_XSTRDUP str) HM HF Hp10).
Qed.
End e.
End f.
End d.
