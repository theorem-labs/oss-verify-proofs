(* rule 24: proves no function (kind: segment lemma of check_round_trip's walk, PORTED from a working branch d25a984c903 proofs/omx-clap-core/fuzz_state/lib/A/Prog/check_round_trip_sd16.v crt16_runB :541 - the stretch 0x82274 .. the entry of fuzz_free, i.e. the length check of the second decode, the bcmp wrapper and the empty-body arm crt_skipbcmp2 - the bespoke ASan proof of THIS function on THESE bytes). CHECKER VERDICT: CONFIRM (a Theorem Labs lane, role check, 2026-10-29 04:3xZ) on (internal path) lines 6-21 (proof index v5, 31 named hits all plain/ubsan, the hit's Require closure 334 files with 0 Admitted/Axiom/Parameter).

   check_round_trip (fs.asan 0x81a9c), build A, lane D1, SEGMENT 31: from the return of the second
   preset_base64_decode (0x82274, crtD1_INV_82274) to the return of the bcmp thunk (0x82298, crtD1_INV_82298) when the
   body is not empty, and to the return of fuzz_free (got) (0x822a4, crtD1_INV_822a4) when it is (`beqz s4` at 0x82284
   jumps over bcmp to the free of got, which calls fuzz_free straight from the stretch).
   - BODY ARM (|bs| >= 1): the read-only start state crtD1_ss31 (FSH_crt_segD1.v) with atom 10 = got in [4096, 2 ^ 47]
     and atom 20 = |bs| in [1, 2 ^ 32]; the engine runs to the __wrap_bcmp thunk (crtD1_run31); the call is
     FSH_crt_segD1_bcmp.crtD1_bcmp_call with every data premise from FSH_crt_segD1_bd.crtD1_bcmp_data, which also gives
     the byte equality that makes bcmp answer 0; the walk's boundary state at 0x82298 is crtD1_bcmp_resume's, over a
     call-site state crtD1_ssB that carries crt_ss_ret's four regions (the run reads the frame only, so the frame and
     shadow regions of the boundary state at 0x82274 hold at the call site: crtD1_ssB_ok); the invariant's data facts
     are carried to the call site by same_below and across the call by FSW_rd's *_kept_call lemmas over
     crtD1_bcmp_journal (FPc = []).
   - EMPTY-BODY ARM (|bs| = 0): atom 10 only; the engine stops at `beqz s4` (crtD1_br31z), the taken arm is the
     condition `s4 = 0` (st_ok_add_cond), the engine runs to fuzz_free (crtD1_run31z), the frame's read-only region is
     dropped (crtD1_sc31zd) and FSH_crt_site.crt_call_core crosses the call with the Section hypothesis FREEZ (a Theorem Labs lane
     is proving it, as crtD1_free_hcall).
   A new file: no licence lines (internal). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YI16 YK06 YM05 YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import
AB1v AB1w FSupoison FSupoisonU FSH_YC20 FSH_Gen FSH_Base FSH_Rt FSPstat FSW_K FSW_ret FSW_K3 FSH_Fn_reader
FSH_Fn_writer FSH_Fn_alloc FSH_Fn_crt FSW_frame FSW_frame3 FSW_rres FSW_crt_tbl FSW_strkit FSW_rd FSH_crt_base
FSH_crt_site FSH_crt_segD1 FSH_crt_segD1_inv FSH_crt_segD1_bcmp FSH_crt_segD1_bd.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require WriterSpec WriterSpecFacts.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ---- pure facts ---- *)
(* the second decode's block holds the whole body: |bs| <= dec_size (b64_enc bs) *)
Lemma crtD1_dsz_len : forall bs : list Z,
  Z.of_nat (length bs) <= FSH_Fn_writer.dec_size (WriterSpec.b64_enc bs).
Proof.
intros bs. unfold FSH_Fn_writer.dec_size. rewrite WriterSpecFacts.b64_enc_length.
rewrite Nat2Z.inj_mul, Nat2Z.inj_div, Nat2Z.inj_add.
change (Z.of_nat 2) with 2. change (Z.of_nat 3) with 3. change (Z.of_nat 4) with 4.
Z.div_mod_to_equations. lia.
Qed.

(* the run's read-only frame region has an empty write window, so a frame over the three regions is a frame over the
   two stack regions *)
Lemma crtD1_frame_ro : forall E (m m' : word -> option byte),
  frame_of E [crt_s0_region; crt_slot_region crt_cs1; crtD1_fr_ro] m m' ->
  frame_of E [crt_s0_region; crt_slot_region crt_cs1] m m'.
Proof.
intros E m m' HF x Hx. apply HF. intros (r & Hin & Hr). apply Hx.
destruct Hin as [<-|[<-|[<-|[]]]].
- exists crt_s0_region. split; [left; reflexivity | exact Hr].
- exists (crt_slot_region crt_cs1). split; [right; left; reflexivity | exact Hr].
- exfalso. unfold crtD1_fr_ro in Hr. cbn [YP09.r_wlo YP09.r_whi] in Hr. lia.
Qed.

(* a region below alloc_ceiling holds on a memory that agrees below alloc_ceiling *)
Lemma crtD1_region_below : forall {rc : YM05.RunCeil} E (H : word -> bool) (m m' : word -> option byte) r,
  same_below m m' alloc_ceiling -> YP09.region_wf r = true ->
  base_val E (YP09.r_base r) + YP09.r_hi r <= alloc_ceiling ->
  region_ok tfibsegs E (mrestrict H m) r -> region_ok tfibsegs E (mrestrict H m') r.
Proof.
intros rc E H m m' r Hs Hwf Hhi (R1 & R2 & R3 & R4).
apply region_wf_facts in Hwf as (W1 & W2 & W3).
split; [exact R1|]. split; [exact R2|]. split.
- intros o Ho. destruct W2 as [W2|W2]; [lia|].
  apply (fsw_writable_below H m m' _ Hs); [lia | exact (R3 o Ho)].
- rewrite Forall_forall in R4 |- *. intros c Hc.
  apply (chunk_ok_mbyte E (mrestrict H m)); [|exact (R4 c Hc)].
  rewrite forallb_forall in W3. pose proof (W3 c Hc) as Hin. unfold YP09.chunk_inside in Hin.
  rewrite !andb_true_iff, !Z.leb_le in Hin. destruct Hin as ((I1 & I2) & I3).
  intros i Hi. apply (mbyte_below H m m' alloc_ceiling); [exact Hs | lia].
Qed.

(* the saved registers at the bcmp call site (read off the engine's answer) *)
Lemma crtD1_sc31_saved : forall q, In q [8; 9; 18; 19; 20; 21; 22; 24; 25; 26]%nat ->
  sr_get (ss_regs crtD1_sc31) (Z_to_bv 5 (Z.of_nat q)) = SOff q 0.
Proof.
intros q Hq. cbn [In] in Hq.
repeat (destruct Hq as [<-|Hq]; [vm_compute; reflexivity|]). destruct Hq.
Qed.
Lemma crtD1_sc31_s11 : sr_get (ss_regs crtD1_sc31) (Z_to_bv 5 (Z.of_nat 27)) = SOff 47 0x1a0.
Proof. vm_compute. reflexivity. Qed.

(* ---- the bcmp call site with crt_ss_ret's four regions: the engine's registers and facts at PC_bcmp, the memory of
   the boundary state (the run reads the frame only, so its frame and shadow regions still hold) ---- *)
Definition crtD1_ssB : sstate :=
  mkSS (ss_pc crtD1_sc31) (ss_regs crtD1_sc31) (ss_mem (crt_ss_ret 0 crt_cs1 crt_csF)) (ss_resv crtD1_sc31)
    (ss_facts crtD1_sc31).
Lemma crtD1_ssB_ok : forall {fx : YK11.FPState} {rc : YM05.RunCeil} E (H : word -> bool) ms0 ms,
  st_ok tfibsegs E (crt_ss_ret 0x82274 crt_cs1 crt_csF) (restrict H ms0) ->
  st_ok tfibsegs E crtD1_sc31 (restrict H ms) ->
  same_below (ms_mem ms0) (ms_mem ms) alloc_ceiling ->
  bv_unsigned (ew E 47) + 512 <= alloc_ceiling -> bv_unsigned (ew E 19) + 64 <= alloc_ceiling ->
  st_ok tfibsegs E crtD1_ssB (restrict H ms).
Proof.
intros fx rc E H ms0 ms HS0 HSC Hs HF HSF.
pose proof (st_ok_mem_ok tfibsegs E _ _ HS0) as (_ & Hok0 & Hpd0).
destruct HSC as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & (_ & Hok & _) & H9).
assert (Msc : ss_mem crtD1_sc31 = [crt_s0_region; crt_slot_region crt_cs1; crtD1_fr_ro]) by (vm_compute; reflexivity).
rewrite Msc in Hok.
apply Forall_cons_iff in Hok as (Ok0 & Hok). apply Forall_cons_iff in Hok as (Ok1 & _).
cbn [ss_mem crt_ss_ret fss_ret_s0_args fss_ret_s0_regs crt_ret_regions] in Hok0.
apply Forall_cons_iff in Hok0 as (_ & Hok0). apply Forall_cons_iff in Hok0 as (_ & Hok0).
apply Forall_cons_iff in Hok0 as (Ok2 & Hok0). apply Forall_cons_iff in Hok0 as (Ok3 & _).
unfold crtD1_ssB, st_ok. cbn [ss_pc ss_regs ss_mem ss_resv ss_facts].
split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|]. split; [exact H5|].
split; [exact H6|]. split; [exact H7|]. split; [|exact H9].
split; [vm_compute; reflexivity|]. split; [|exact Hpd0].
cbn [ss_mem crt_ss_ret fss_ret_s0_args fss_ret_s0_regs crt_ret_regions].
apply Forall_cons; [exact Ok0|]. apply Forall_cons; [exact Ok1|].
apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
- apply (crtD1_region_below E H (ms_mem ms0) (ms_mem ms) _ Hs); [vm_compute; reflexivity | | exact Ok2].
  unfold crt_frame_region. cbn [YP09.r_base YP09.r_hi base_val]. rewrite crt_frame3. exact HF.
- apply (crtD1_region_below E H (ms_mem ms0) (ms_mem ms) _ Hs); [vm_compute; reflexivity | | exact Ok3].
  unfold crt_shadow_region. cbn [YP09.r_base YP09.r_hi base_val]. rewrite crt_frame3.
  change (512 / 8) with 64. exact HSF.
Qed.

(* a callee-saved register of the env resumed after a call is the call site's value *)
Lemma crtD1_keep_sv : forall {fx : YK11.FPState} E ss (H : word -> bool) ms regs2 extra (q : nat) v,
  st_ok tfibsegs E ss (restrict H ms) -> aregs_preserved (ms_regs ms) regs2 ->
  acallee_saved (Z.of_nat q) -> (q < 32)%nat ->
  sr_get (ss_regs ss) (Z_to_bv 5 (Z.of_nat q)) = v ->
  ew (Ereg regs2 extra) q = sv_denot E v.
Proof.
intros fx E ss H ms regs2 extra q v HS HP Hq Hq32 Hr.
rewrite (ew_Ereg_lt regs2 extra q Hq32), (HP _ Hq), (st_ok_restrict_reg tfibsegs H E ss ms _ HS), Hr.
reflexivity.
Qed.

(* ---- the empty-body arm's call site without the frame's read-only region: crt_csite's shape ---- *)
Definition crtD1_sc31zd : sstate :=
  mkSS (ss_pc crtD1_sc31z) (ss_regs crtD1_sc31z) [crt_s0_region; crt_slot_region crt_cs1] (ss_resv crtD1_sc31z)
    (ss_facts crtD1_sc31z).
Lemma crtD1_sc31zd_site : crt_csite crtD1_sc31zd A_fuzz_free 0x822a4.
Proof. unfold crt_csite. repeat split; vm_compute; reflexivity. Qed.

Section s31. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable SK : YI16.sink_head.
Variable B : asyms.
Hypothesis RT : CrtRt B.
Hypothesis HENV : api_env tfibsegs B.
(* the empty-body arm calls fuzz_free (got) straight from 0x82274. That crossing is FSH_crt_segD1_free.v's
   crtD1_freez (a crt_hcall over the call-site state crtD1_sc31z); FSH_crt_segD1_main.crtD1_main passes it here: *)
Hypothesis FREEZ : crt_hcall SK B crtD1_sc31z A_fuzz_free 0x822a4 STK_fuzz_free
                     (fun cx E k ly3 S3 U3 W3 ms3 md3 =>
                        crtD1_INV_82274 B cx E k ly3 S3 U3 W3 ms3 md3 /\ Z.of_nat (length (c_bs cx)) = 0)
                     (crtD1_INV_822a4 B).

(* the run's write window over the three regions of segment 31's states: the two stack regions (crt_awr2) and the
   read-only frame *)
Lemma crtD1_awr3 : forall cx E ly3 S3, crt_base B cx -> crt_E cx E ->
  awr_ok tfibsegs B E [crt_s0_region; crt_slot_region crt_cs1; crtD1_fr_ro] STK_check_round_trip
    (spZ (c_regs cx)) FS_PSTAT_FP (ablocks B (c_ly cx) (c_S cx)) (ablocks B ly3 S3) ly3 [(3, c_pos cx)]
    (frames (c_S cx)).
Proof.
intros cx E ly3 S3 HB HE a (r & Hin & Hr).
apply (crt_awr2 B cx E ly3 S3 HB HE). exists r. split; [|exact Hr].
destruct Hin as [<-|[<-|[<-|[]]]]; [left; reflexivity | right; left; reflexivity |].
exfalso. unfold crtD1_fr_ro in Hr. cbn [YP09.r_wlo YP09.r_whi] in Hr. lia.
Qed.

(* ---- the lane's boundary data carried to a memory that agrees below alloc_ceiling (the store-free run) ---- *)
Lemma crtD1_common_below : forall cx ly S (W : world tfibsegs) mx md m m' back Ddoc Dback tback,
  AR tfibsegs B ly S W mx md -> same_below m m' alloc_ceiling ->
  crtD1_common B cx ly S W m back Ddoc Dback tback -> crtD1_common B cx ly S W m' back Ddoc Dback tback.
Proof.
intros cx ly S W mx md m m' back Ddoc Dback tback HAR Hs (C1 & C2 & C3 & C4 & C5 & C6 & C7).
pose proof (fsw_pobj_low B ly S W mx md m _ HAR C6) as (P1 & P2).
pose proof (fsw_pobj_low B ly S W mx md m _ HAR C7) as (Q1 & Q2).
split; [exact (fs_rblock_below B ly S W mx md m m' _ _ HAR Hs C1)|].
split; [exact (fs_rblock_below B ly S W mx md m m' _ _ HAR Hs C2)|].
split; [refine (rnode_below B ly S W mx md m m' _ _ _ _ HAR Hs _ Q2 C3); lia|].
split; [refine (rnode_below B ly S W mx md m m' _ _ _ _ HAR Hs _ P2 C4); lia|].
split; [exact C5|].
split; [exact (pobj_below B ly S W mx md m m' _ HAR Hs C6)|].
exact (pobj_below B ly S W mx md m m' _ HAR Hs C7).
Qed.

(* ---- the same data across a callee whose journal has an EMPTY footprint (the bcmp thunk, crtD1_bcmp_journal) ---- *)
Lemma crtD1_common_kept : forall cx STK1 sp1 lyc Sc Uc (W : world tfibsegs) memc mdc ly' S' U' (W' : world tfibsegs)
  mem' md' kc back Ddoc Dback tback,
  @ajournal rc SK tfibsegs B STK1 sp1 [] lyc Sc W (unpoison Uc memc) mdc [] ly' S' W' (unpoison U' mem') md' kc ->
  ARU tfibsegs B lyc Sc Uc W memc mdc -> ARU tfibsegs B ly' S' U' W' mem' md' -> FSupoisonU.fs_heads B ly' S' U' ->
  crtD1_common B cx lyc Sc W memc back Ddoc Dback tback -> crtD1_common B cx ly' S' W' mem' back Ddoc Dback tback.
Proof.
intros cx STK1 sp1 lyc Sc Uc W memc mdc ly' S' U' W' mem' md' kc back Ddoc Dback tback HJ HU HU' FH
  (C1 & C2 & C3 & C4 & C5 & C6 & C7).
pose proof HU' as (_ & HO' & HP').
assert (NS : forall a, inFP [] a -> ~ (SHADOW_OFF <= a < SHADOW_OFF + 2 ^ 44)) by (intros a Ha; destruct (inFP_nil a Ha)).
split; [exact (fs_rblock_kept_call B STK1 sp1 [] lyc Sc Uc W memc mdc ly' S' U' W' mem' md' kc _ _ HJ HU HO' HP'
  (fun x _ => inFP_nil x) C1)|].
split; [exact (fs_rblock_kept_call B STK1 sp1 [] lyc Sc Uc W memc mdc ly' S' U' W' mem' md' kc _ _ HJ HU HO' HP'
  (fun x _ => inFP_nil x) C2)|].
split; [exact (rtree_kept_call B STK1 sp1 [] lyc Sc Uc W memc mdc ly' S' U' W' mem' md' kc _ _ _ HJ HU HO' HP'
  (fun x _ => inFP_nil x) (fun a k x _ _ => inFP_nil x) C7 C3)|].
split; [exact (rnode_kept_call B STK1 sp1 [] lyc Sc Uc W memc mdc ly' S' U' W' mem' md' kc _ _ _ _ HJ HU HO' HP'
  (fun x _ => inFP_nil x) (fun a k x _ _ => inFP_nil x) C6 C4)|].
split; [exact C5|].
split; [exact (pobj_kept_call B STK1 sp1 [] lyc Sc Uc W memc mdc ly' S' U' W' mem' md' kc _ HJ HU HO' HP'
  (fun x _ => inFP_nil x) NS FH C6)|].
exact (pobj_kept_call B STK1 sp1 [] lyc Sc Uc W memc mdc ly' S' U' W' mem' md' kc _ HJ HU HO' HP'
  (fun x _ => inFP_nil x) NS FH C7).
Qed.

(* ================= SEGMENT 31 ================= *)
Lemma crtD1_seg31 :
  crt_from SK B (crt_ss_ret 0x82298 crt_cs1 crt_csF) (crtD1_INV_82298 B) ->
  crt_from SK B (crt_ss_ret 0x822a4 crt_cs1 crt_csF) (crtD1_INV_822a4 B) ->
  crt_from SK B (crt_ss_ret 0x82274 crt_cs1 crt_csF) (crtD1_INV_82274 B).
Proof.
intros N98 Na4 cx E k ly3 S3 U3 W3 ms3 md3 HB HE HJ HARU HFO HINV HS.
pose proof HINV as HINV0.
unfold crtD1_INV_82274 in HINV. cbv beta zeta in HINV.
destruct HINV as (E18 & E20 & E21 & E26 & E27 & same & nsame & file & nfile & back & got & Dback & Ddoc & tback &
  live & peak & cnt & E22 & E24 & E25 & E10 & Hgot & HPa & HPu & FH & HCOM & Hfile & Hgotb & Hzb & Hval & Hra &
  HG & HL & Hbb & Hcnt & Hk & Hroom).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (@alloc_ceiling_lt rc) as HC47.
pose proof HFO as (Hfr & Hnin & Hflag).
pose proof (ARU_AR tfibsegs B _ _ _ _ _ _ HARU) as HAR.
destruct (crt_F_facts SK B cx ly3 S3 U3 W3 (ms_mem ms3) md3 k HJ HARU Hfr) as (FAl & F4096 & Fceil & Fapp & FS1 & FS2).
pose proof HE as (E2 & E3 & E4 & E8 & E9 & E19 & EX).
assert (E47 : bv_unsigned (ew E 47) = crt_F cx) by (rewrite (crt_E_F cx E HE); apply wz; lia).
pose proof HB as ((HPREU & _) & _).
pose proof (fsw_sp B _ _ _ _ _ _ _ _ _ HPREU) as (H16 & Hceil0 & H47 & _).
pose proof HPREU as ((_ & _ & _ & Hgp & Htp & _) & _).
pose proof crt_STK_eq as HSTK. unfold crt_STK in HSTK.
assert (H0 : 192 <= spZ (c_regs cx)) by lia.
destruct (crt_sp1_facts cx H16 H0) as (Hsp1b & _ & _).
(* the body's length and the block got *)
pose proof (crtD1_dsz_len (c_bs cx)) as Hdsz.
pose proof Hgotb as (Hgin & _ & Hgn & _).
assert (Rg : req_size (FSH_Fn_writer.dec_size (WriterSpec.b64_enc (c_bs cx)) + HEAD) =
             FSH_Fn_writer.dec_size (WriterSpec.b64_enc (c_bs cx)) + HEAD)
  by (apply crtD1_req_size; cbv [HEAD]; lia).
destruct (crtD1_blk_user B ly3 S3 U3 W3 (ms_mem ms3) md3 (got - HEAD)
  (FSH_Fn_writer.dec_size (WriterSpec.b64_enc (c_bs cx)) + HEAD) got (Z.of_nat (length (c_bs cx)))
  HARU FH Hgin ltac:(lia) ltac:(lia) ltac:(rewrite Rg; lia)) as (G4096 & Gceil & GMx & _).
cbv [MALLOC_MAX HEAD] in GMx.
assert (Eg : bv_unsigned (ew E 10) = got) by (rewrite E10; apply wz; lia).
(* the start state of segment 31 (the length cell in the read-only frame, s11 on the frame atom) *)
pose proof (crtD1_ss31_ok cx E W3 ms3 (Z.of_nat (length (c_bs cx))) HE ltac:(lia) E20 ltac:(lia) E27 ltac:(lia)
  Hval HS) as HSb.
pose proof HSb as (_ & _ & _ & _ & _ & _ & _ & _ & HGb).
assert (A10 : afact_ok E 10 crtD1_fptr).
{ unfold afact_ok, crtD1_fptr. cbn [af_lo af_hi af_al2]. rewrite Eg. change (2 ^ 0) with 1.
  rewrite Z.mod_1_r. lia. }
assert (AWR : forall ssx, ss_mem ssx = [crt_s0_region; crt_slot_region crt_cs1; crtD1_fr_ro] ->
  awr_ok tfibsegs B E (ss_mem ssx) STK_check_round_trip (spZ (c_regs cx)) FS_PSTAT_FP
    (ablocks B (c_ly cx) (c_S cx)) (ablocks B ly3 S3) ly3 [(3, c_pos cx)] (frames (c_S cx)))
  by (intros ssx Hx; rewrite Hx; exact (crtD1_awr3 cx E ly3 S3 HB HE)).
destruct (Z.eq_dec (Z.of_nat (length (c_bs cx))) 0) as [Hl0 | Hl1].
- (* ======== EMPTY-BODY ARM: `beqz s4` taken, fuzz_free (got) ======== *)
  pose proof (st_ok_facts tfibsegs E crtD1_ss31_base _ _ HSb (facts_ok_add_atom E _ 10 crtD1_fptr HGb A10))
    as HS31z.
  change (st_ok tfibsegs E crtD1_ss31z (restrict (w_H W3) ms3)) in HS31z.
  eapply (fsw_run_AJU B crt_tbl crt_tbl_ok W3 D1_FUEL E crtD1_ss31z crtD1_sb31z _ ms3
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HS31z crtD1_br31z I HARU HJ (AWR crtD1_ss31z eq_refl)).
  intros ms1 mat1 HS1 HJ1 HARU1 HF1 HFr1 HG1.
  assert (HBR : branch_taken BC_EQ (sv_denot E (SOff 20 0)) (sv_denot E (SLit 0)) = true).
  { rewrite branch_eq_U, (U_atom E 20 _ E20 ltac:(lia)), (U_lit E 0 ltac:(lia)). apply Z.eqb_eq. exact Hl0. }
  pose proof (st_ok_add_cond tfibsegs E crtD1_sb31z _ BC_EQ (SOff 20 0) (SLit 0) HS1 HBR) as HS1c.
  change (st_ok tfibsegs E crtD1_ss31zc (restrict (w_H W3) ms1)) in HS1c.
  assert (HMz : ss_mem crtD1_ss31zc = [crt_s0_region; crt_slot_region crt_cs1; crtD1_fr_ro])
    by (vm_compute; reflexivity).
  eapply (fsw_run_to_AJU B crt_tbl crt_tbl_ok W3 D1_FUEL A_fuzz_free E crtD1_ss31zc crtD1_sc31z RS_running ms1
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HS1c crtD1_run31z I HARU1 HJ1 (AWR crtD1_ss31zc HMz)).
  intros ms mat HSC HJC HARUC HF HFr HGr.
  assert (HF1' : frame_of E [crt_s0_region; crt_slot_region crt_cs1; crtD1_fr_ro] (ms_mem ms3) (ms_mem ms1))
    by exact HF1.
  assert (HF' : frame_of E [crt_s0_region; crt_slot_region crt_cs1; crtD1_fr_ro] (ms_mem ms1) (ms_mem ms))
    by (rewrite <- HMz; exact HF).
  (* drop the frame's read-only region: the call site of crt_call_core *)
  assert (HSUBz : submem [crt_s0_region; crt_slot_region crt_cs1] (ss_mem crtD1_sc31z)).
  { assert (Mz : ss_mem crtD1_sc31z = [crt_s0_region; crt_slot_region crt_cs1; crtD1_fr_ro])
      by (vm_compute; reflexivity).
    rewrite Mz. apply submem_keep; [apply subregion_refl|]. apply submem_keep; [apply subregion_refl|].
    apply submem_nil. }
  pose proof (st_ok_submem tfibsegs E crtD1_sc31z _ _ HSC HSUBz ltac:(vm_compute; reflexivity)) as HSCd.
  change (st_ok tfibsegs E crtD1_sc31zd (restrict (w_H W3) ms)) in HSCd.
  exact (crt_call_core SK B crtD1_sc31zd A_fuzz_free 0x822a4
    (fun cx E k ly3 S3 U3 W3 ms3 md3 =>
       crtD1_INV_82274 B cx E k ly3 S3 U3 W3 ms3 md3 /\ Z.of_nat (length (c_bs cx)) = 0)
    (crtD1_INV_822a4 B) STK_fuzz_free cx E k ly3 S3 U3 W3 ms3 md3 ms _
    crtD1_sc31zd_site ltac:(lia) eq_refl ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
    FREEZ Na4 HB HE HFO (conj HINV0 Hl0) HSCd HJC HARUC
    (same_below_trans _ _ _ _ (crt_sb B cx E _ _ HB HE (crtD1_frame_ro E _ _ HF1'))
       (crt_sb B cx E _ _ HB HE (crtD1_frame_ro E _ _ HF')))).
- (* ======== BODY ARM: bcmp (got, bd, len), which answers 0 ======== *)
  assert (A20 : afact_ok E 20 (mkAF 1 (2 ^ 32) 0)).
  { unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E20, wz by lia. change (2 ^ 0) with 1.
    rewrite Z.mod_1_r. change (2 ^ 32) with 4294967296. lia. }
  pose proof (st_ok_facts tfibsegs E crtD1_ss31_base _ _ HSb
    (facts_ok_add_atom E _ 20 _ (facts_ok_add_atom E _ 10 crtD1_fptr HGb A10) A20)) as HS31.
  change (st_ok tfibsegs E crtD1_ss31 (restrict (w_H W3) ms3)) in HS31.
  eapply (fsw_run_to_AJU B crt_tbl crt_tbl_ok W3 D1_FUEL PC_bcmp E crtD1_ss31 crtD1_sc31 RS_running ms3
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HS31 crtD1_run31 I HARU HJ (AWR crtD1_ss31 eq_refl)).
  intros ms mat HSC HJC HARUC HF HFr HG0.
  assert (HSB : same_below (ms_mem ms3) (ms_mem ms) alloc_ceiling)
    by exact (crt_sb B cx E _ _ HB HE (crtD1_frame_ro E _ _ HF)).
  destruct crtD1_sc31_regs as (Hpc31 & _ & Hres31).
  assert (R1 : sr_get (ss_regs crtD1_sc31) 1%bv = SLit 0x82298) by (vm_compute; reflexivity).
  assert (R10 : sr_get (ss_regs crtD1_sc31) 10%bv = SOff 10 0) by (vm_compute; reflexivity).
  assert (R11 : sr_get (ss_regs crtD1_sc31) 11%bv = SOff 21 0) by (vm_compute; reflexivity).
  assert (R12 : sr_get (ss_regs crtD1_sc31) 12%bv = SOff 20 0) by (vm_compute; reflexivity).
  assert (R2 : sr_get (ss_regs crtD1_sc31) 2%bv = SOff 2 0) by (vm_compute; reflexivity).
  assert (R3 : sr_get (ss_regs crtD1_sc31) 3%bv = SOff 3 0) by (vm_compute; reflexivity).
  assert (R4 : sr_get (ss_regs crtD1_sc31) 4%bv = SOff 4 0) by (vm_compute; reflexivity).
  assert (R23 : sr_get (ss_regs crtD1_sc31) 23%bv = SOff 10 0) by (vm_compute; reflexivity).
  pose proof (crt_mkst (w_H W3) E crtD1_sc31 ms HSC Hres31) as Ems. rewrite Hpc31 in Ems.
  set (mdT := with_vm_backing (m_vm_lazy md3) mat md3) in *.
  set (regsT := ms_regs ms) in *. set (memT := ms_mem ms) in *.
  rewrite Ems in HSC. rewrite Ems.
  assert (HspT : spZ regsT = crt_sp1 cx).
  { unfold spZ. rewrite (st_ok_restrict_reg tfibsegs (w_H W3) E crtD1_sc31 _ 2%bv HSC), R2, fsw_SOff0.
    exact E2. }
  (* the invariant's data at the call site *)
  assert (HgotT : fs_rblock tfibsegs B ly3 S3 W3 memT got (FSH_Fn_writer.dec_size (WriterSpec.b64_enc (c_bs cx))))
    by exact (fs_rblock_below B ly3 S3 W3 _ _ _ _ _ _ HAR HSB Hgotb).
  assert (HzbT : zbytes_at tfibsegs W3 memT got (c_bs cx)).
  { apply (garr8_frame tfibsegs _ _ got (c_bs cx) Hzb). intros a Ha.
    apply (mbyte_below (w_H W3) (ms_mem ms3) memT alloc_ceiling a HSB). lia. }
  assert (Hkeep : forall b, In b (ablocks B (c_ly cx) (c_S cx)) -> In b (ablocks B ly3 S3)).
  { intros b Hb. apply (Permutation_in _ (Permutation_sym HPa)). apply in_or_app. left. exact Hb. }
  destruct (crtD1_bcmp_data SK B cx ly3 S3 U3 W3 regsT memT mdT k got
    (FSH_Fn_writer.dec_size (WriterSpec.b64_enc (c_bs cx))) HB HJC HARUC FH Hkeep HgotT HzbT Hdsz HspT)
    as (Dl & Dg0 & Dg1 & Db0 & Db1 & Dsg & Dsb & Dwg & Dwb & Dmg & Dmb & Dag & Dhg & Dab & Dhb & DEQ).
  assert (HRet : YK0s.ret_ok (Z_to_bv 64 0x82298)) by (apply ret_ok_even; rewrite (wz 0x82298) by lia; reflexivity).
  assert (Ebd : bv_unsigned (ew E 21) = c_bd cx) by (rewrite E21; apply wz; lia).
  assert (Elen : bv_unsigned (ew E 20) = Z.of_nat (length (c_bs cx))) by (rewrite E20; apply wz; lia).
  (* the frame word at the call site *)
  assert (HFOT : crt_frame_ok cx S3 W3 (mkst regsT (Z_to_bv 64 PC_bcmp) memT (seg_rom tfibsegs))).
  { split; [exact Hfr|]. split; [exact Hnin|]. cbn [ms_mem mkst].
    rewrite <- Hflag. apply rdword_ext. intros i Hi. rewrite crt_frame3 in *.
    exact (aview_below (w_H W3) (ms_mem ms3) memT alloc_ceiling (crt_F cx + 512 - 8 + i) HSB ltac:(lia)). }
  (* the call site with crt_ss_ret's four regions *)
  assert (HSBk : st_ok tfibsegs E crtD1_ssB
    (restrict (w_H W3) (mkst regsT (Z_to_bv 64 PC_bcmp) memT (seg_rom tfibsegs)))).
  { apply (crtD1_ssB_ok E (w_H W3) ms3 _ HS HSC HSB); [rewrite E47; exact Fceil|].
    rewrite E19. unfold kHighShadowEnd in FS2. lia. }
  (* the call *)
  eapply (crtD1_bcmp_call (SKfp := SK) B crtD1_sc31 0x82298 10 cx E k ly3 S3 U3 W3 regsT memT mdT got _
    R1 ltac:(lia) R10 R11 R12 R2 R3 R4 HRet RT HE H16 H0 H47 Hgp Htp HSC Eg Ebd Elen
    Dl Dg0 Dg1 Db0 Db1 Dsg Dsb Dwg Dwb Dmg Dmb Dag Dhg Dab Dhb HJC HARUC).
  intros regs2 mem2 md2 v HJ2 HARU2 HSM2 HP2 HFR2 Hv Hres.
  (* bcmp answered 0: the two byte ranges are equal *)
  pose proof (proj2 Hres (fun i Hi => eq_sym (DEQ i Hi))) as Hv0.
  assert (G1 : YK11.getr regsT 1%bv = Z_to_bv 64 0x82298)
    by exact (fsw_reg_lit (w_H W3) E crtD1_sc31 (mkst regsT (Z_to_bv 64 PC_bcmp) memT (seg_rom tfibsegs)) 1%bv
                0x82298 HSC R1 ltac:(lia)).
  rewrite G1.
  (* the walk's boundary state at 0x82298 *)
  assert (HcsFin : Forall (fun c => 0 <= YP09.c_off c /\ 0 <= YP09.c_len c /\
      YP09.c_off c + YP09.c_len c <= fs_frame_bytes 3) crt_csF)
    by (unfold crt_csF; rewrite crt_frame3; apply Forall_cons; [cbn; lia | apply Forall_nil]).
  assert (HcsFat : crt_atom_chunks crt_csF)
    by (unfold crt_atom_chunks, crt_csF; apply Forall_cons; [do 4 eexists; split; [reflexivity | lia] | apply Forall_nil]).
  destruct (crtD1_bcmp_resume (SKfp := SK) B cx E crtD1_ssB k ly3 S3 U3 W3 regsT memT regs2 mem2 md2 crt_csF
    0x82298 HE HJ2 HARU2 HFOT HSBk eq_refl ltac:(vm_compute; reflexivity) HP2 HFR2 HcsFin HcsFat)
    as (HE' & HFO' & HS').
  refine (N98 cx (Ereg regs2 (crt_extra cx)) k ly3 S3 U3 W3 (mkst regs2 (Z_to_bv 64 0x82298) mem2 (seg_rom tfibsegs))
    md2 HB HE' HJ2 HARU2 HFO' _ HS').
  (* ---- crtD1_INV_82298 after the call ---- *)
  (* the callee journal of bcmp, with its empty footprint *)
  pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres2 & _).
  assert (Hpr : forall a, spZ regsT - ASTACK <= a < spZ regsT -> apresent (w_H W3) mem2 a).
  { intros a Ha. rewrite HspT in Ha. unfold ASTACK in Ha.
    apply (fsw_apresent_unpoison B ly3 S3 U3 W3 mem2 md2 a HARU2); [unfold kHighMemBeg in *; lia|].
    apply Hpres2. lia. }
  pose proof (crtD1_bcmp_journal (SKfp := SK) B HENV cx ly3 S3 U3 W3 regsT memT mdT mem2 md2 k HJC HARUC HARU2
    HSM2 HspT HFR2 Hpr) as J0.
  pose proof HARU2 as (_ & HO2 & HP2').
  (* the data facts: ms3 -> the call site (same_below) -> after the call (the empty-footprint journal) *)
  assert (KB : forall p n, fs_rblock tfibsegs B ly3 S3 W3 (ms_mem ms3) p n -> fs_rblock tfibsegs B ly3 S3 W3 mem2 p n).
  { intros p n Hp.
    exact (fs_rblock_kept_call B ASTACK (spZ regsT) [] ly3 S3 U3 W3 memT mdT ly3 S3 U3 W3 mem2 md2 0 p n J0 HARUC
      HO2 HP2' (fun x _ => inFP_nil x) (fs_rblock_below B ly3 S3 W3 _ _ _ _ _ _ HAR HSB Hp)). }
  assert (HCOM2 : crtD1_common B cx ly3 S3 W3 mem2 back Ddoc Dback tback).
  { apply (crtD1_common_kept cx ASTACK (spZ regsT) ly3 S3 U3 W3 memT mdT ly3 S3 U3 W3 mem2 md2 0 _ _ _ _ J0 HARUC
      HARU2 FH).
    exact (crtD1_common_below cx ly3 S3 W3 _ _ _ _ back Ddoc Dback tback HAR HSB HCOM). }
  assert (HG2 : fs_glob tfibsegs W3 mem2 live peak cnt SIZE_MAXZ).
  { apply (crtD1_glob_keep W3 memT mem2).
    - intros a Ha. apply HFR2; [lia|]. rewrite HspT. unfold ESTACK. lia.
    - apply (crtD1_glob_keep W3 (ms_mem ms3) memT); [|exact HG].
      intros a Ha. apply (aview_below (w_H W3) (ms_mem ms3) memT alloc_ceiling a HSB). lia. }
  (* the registers of the resumed env *)
  assert (KR : forall (q n : nat), (q < 32)%nat -> acallee_saved (Z.of_nat q) ->
      sr_get (ss_regs crtD1_sc31) (Z_to_bv 5 (Z.of_nat q)) = SOff n 0 -> ew (Ereg regs2 (crt_extra cx)) q = ew E n).
  { intros q n Hq Hc Hs. rewrite (crtD1_keep_sv E crtD1_sc31 (w_H W3) _ regs2 (crt_extra cx) q _ HSC HP2 Hc Hq Hs).
    apply fsw_SOff0. }
  assert (KS : forall q, In q [8; 9; 18; 19; 20; 21; 22; 24; 25; 26]%nat ->
      ew (Ereg regs2 (crt_extra cx)) q = ew E q).
  { intros q Hq. apply (KR q q); [cbn [In] in Hq; lia | unfold acallee_saved; cbn [In] in Hq; lia |
      exact (crtD1_sc31_saved q Hq)]. }
  assert (G27 : ew (Ereg regs2 (crt_extra cx)) 27 = Z_to_bv 64 (crt_F cx + 0x1a0)).
  { rewrite (crtD1_keep_sv E crtD1_sc31 (w_H W3) _ regs2 (crt_extra cx) 27 _ HSC HP2
      ltac:(unfold acallee_saved; lia) ltac:(lia) crtD1_sc31_s11).
    apply bv_eq. rewrite denot_SOff, E47.
    rewrite Z_to_bv_unsigned, bv_wrap_small by (change (bv_modulus 64) with (2 ^ 64); lia).
    apply zcanon_id. unfold M64. lia. }
  assert (G23 : ew (Ereg regs2 (crt_extra cx)) 23 = ew E 10)
    by exact (KR 23%nat 10%nat ltac:(lia) ltac:(unfold acallee_saved; lia) R23).
  assert (G10 : ew (Ereg regs2 (crt_extra cx)) 10 = Z_to_bv 64 0)
    by (rewrite (ew_Ereg_lt regs2 _ 10 ltac:(lia)); exact (eq_trans Hv Hv0)).
  unfold crtD1_INV_82298. cbn [ms_mem mkst].
  split; [exact G10|].
  split; [rewrite (KS 18%nat ltac:(cbn; tauto)); exact E18|].
  split; [rewrite (KS 20%nat ltac:(cbn; tauto)); exact E20|].
  split; [rewrite (KS 21%nat ltac:(cbn; tauto)); exact E21|].
  split; [rewrite (KS 26%nat ltac:(cbn; tauto)); exact E26|].
  split; [exact G27|].
  exists same, nsame, file, nfile, back, got, Dback, Ddoc, tback, live, peak, cnt.
  split; [rewrite (KS 22%nat ltac:(cbn; tauto)); exact E22|].
  split; [rewrite (KS 24%nat ltac:(cbn; tauto)); exact E24|].
  split; [rewrite (KS 25%nat ltac:(cbn; tauto)); exact E25|].
  split; [rewrite G23; exact E10|].
  split; [exact Hgot|]. split; [exact HPa|]. split; [exact HPu|]. split; [exact FH|].
  split; [exact HCOM2|]. split; [exact (KB _ _ Hfile)|]. split; [exact (KB _ _ Hgotb)|].
  split; [exact HG2|]. split; [exact HL|]. split; [exact Hbb|]. split; [exact Hcnt|].
  (* bcmp ticks nothing: the remaining allowance carries over with the same k *)
  split; [exact Hk | exact Hroom].
Qed.
End s31.

(* Each lemma below prints only the 13 kernel primitives (PrimInt63 / PrimString / PrimArray) or nothing; crtD1_seg31
   also prints Stdlib's FunctionalExtensionality.functional_extensionality_dep, which enters through the run kit
   FSW_K.fsw_run_AJU / fsw_run_to_AJU (measured: FSH_crt_site.crt_seg_call prints it too). No project axiom. *)
Print Assumptions crtD1_dsz_len.
Print Assumptions crtD1_frame_ro.
Print Assumptions crtD1_region_below.
Print Assumptions crtD1_sc31_saved.
Print Assumptions crtD1_sc31_s11.
Print Assumptions crtD1_ssB_ok.
Print Assumptions crtD1_keep_sv.
Print Assumptions crtD1_sc31zd_site.
Print Assumptions crtD1_awr3.
Print Assumptions crtD1_common_below.
Print Assumptions crtD1_common_kept.
Print Assumptions crtD1_seg31.
About crtD1_seg31.
