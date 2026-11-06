(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/Prog/S8aNumC.v, with its module names and numbers changed; 1538 of its 1659 lines of code are new or changed and 807 lines of the source are left out. *)
(* fuzz_preset image B (asan-ubsan), parse_value 0x8637c, SEGMENT N (the number arm), sub-piece D (lane PvnD /
   h-w6u-pre for h-hpreset-7): pnD_stmt of PvB_NCut.v, the cut M (B 0x86778, fuzz_malloc (m + 1) returned res) to the
   tail T (B 0x8688c, outcome (b): res = 0) or to R (B 0x8681c, strtod returned).
   rule 24: no function proved
   rule 24: proves no function (kind: segment lemma). Reuse search: `proof-index parse_value` (h-hpreset-7
   04:10Z, EXIT=0 unpiped, index built 2026-10-29T04:26:29Z): "parse_value: 14 file(s) named for it, 35 file(s) use its
   address, 0 related; in an earlier delivery 58 named for it and 794 name(s) that hold it, in 68 tree(s)"; second-agent
   CONFIRM (ParseValueLookupConfirm 04:21Z): no released srealizes-form proof of this program's parse_value; new proof.
   WHAT THE CODE DOES (the neutral listing, the internal file parse_value.fuzz_preset.asan-ubsan.s,
   B 0x86778 .. 0x86818, the report arm 0x86898 and the slow arms 0x86918, 0x86920, 0x86928, 0x868c8, 0x86930): the
   UBSan check v <> 0; Y + 0 := v mod 8 (= 0); the instrumented check of v + 16; v->str := res; res = 0 goes to T.
   Else Y + 8 := the shadow address of v + 16, Y + 16 := v + 16; the instrumented check of q; __asan_memcpy (res,
   in->p = p1, m); the re-check of v + 16; a0 := v->str + m with the UBSan pointer checks; the instrumented check of
   the byte res + m and its NUL store; s9 := Y + 24's value fa + 32; strtod (v->str, fa + 32) returns at R.
   HOW: four runs of the PA-listing engine (YC80x / YC1fPx over YCbqG's ajournal_x): run 1n (res = 0) M -> T; run 1
   M -> the __asan_memcpy call (YGcallMxmn.aj_intrin_at_xm); run 2 memcpy's return -> B 0x867f0 (a0 = res + m); run 3
   B 0x867f0 -> the strtod call (YStrtodRowX.aj_strtod_at_x). Runs 1 and 1n write v->str, which may lie in one of the
   caller's frames: their write premise is awr_byte \/ wr_fp_frame, by pnd_run_fr / pnd_run_to_fr below (YC80x's
   runner with YCbqG.ajournal_x_exec_fr in place of ajournal_x_exec).
   MEMNORM: M's last conjunct `YStrtodRowX.aj_memnorm SEGS mem` (YAkMemnorm.memnorm SEGS mem by conversion) is carried
   as a state fact to the strtod call: runs 1n and 1 by pnd_run_to_fr / pnd_run_fr (YSRrMemnorm.SRr_msteps_inv at
   P := YAkMemnorm.memnorm SEGS, laws srr_inv_laws_memnorm_k), __asan_memcpy by CPY's keep (YGcallMxmn.aj_intrin_at_xm),
   runs 2 and 3 (run 3 holds the NUL store) by YSRrMemnorm's paj_run_to_x_inv / paj_run_x_inv. It discharges
   strtod_site_x's `aj_memnorm` at the call and T's last conjunct (from run 1n); R's last conjunct is the strtod row's
   post (aj_strtod_row's last conjunct `aj_memnorm mem2`, YStrtodRowX.v blob 10e84e44e24e by path from
   origin/cold/h-verbs-1-preset-strtodB 29dd557e413d).
   ROOM: M's room conjunct (PvB_NCut.v) goes to T's outcome (b) at res = 0 (its NULL half: rp_keep from the entry and
   pn_null_off, the NULL off the grant-all run)
   and to R at res <> 0 (its success half pn_rp1, the room post of EAlloc (S m)): neither the runs nor the memcpy /
   strtod calls move the allocator state Sc. The ledger carries the #102 statics most / own (f97c), kept with the
   other five statics by pnd_ledger_keep (prh_pst's seven cells).
   Section hypotheses: LAWS (AR_laws_x at the harness block's head length hl, a Section Context, as YCbqG.v states
   it); the call texts CPY (__asan_memcpy, with its memnorm keep) and STR (musl strtod); IMG_COVER, B_errno, IMG_GOTV
   (marked image facts); IMG_GOTC (marked image binding of B); FS_HI (marked allocator-layout law); CUTFIX_head8.
   No memnorm law: the universal MEMNORM law is deleted (refuted, owner 09:45Z).
   Numerals: listing offsets 20724 20772 (DERIVED: B pc - B_prog_base 0x816cc, memcpy's return 0x867c0 and 0x867f0);
   8 16 24 32 40 48 56 104 (LENGTH: node, frame and spill offsets); 160 176 320 (LENGTH: parse_value's real frame);
   64 (LENGTH: the class-0 fake frame); 4096 4112 (LENGTH: the low guard; plus cf_head rounded to 16); 16384 (LENGTH:
   STK_RT_STRTOD = 4 * ESTACK); 16560 16880 (LENGTH: LEAF_pv_pi, STK_parse_value's floor); 256 2 ^ 30 2 ^ 44 2 ^ 46
   2 ^ 47 2 ^ 61 2 ^ 64 (LENGTH: byte, text, shadow band, stack band and word bounds); 3 4 5 (LENGTH: alignment logs);
   0x7fff7f800000 (DERIVED: asan_consts' floor of alloc_ceiling); 63 (WORD: srl's shift mask); 43 45 46 48 57 69 101
   (DERIVED: PjGrammar's number characters); register and atom numbers (WORD: RISC-V register numbers; DERIVED: the
   engine's atom numbering, 240 = A_TEXT, 32 the extra atom). No ADDRESS. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YK0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YG0s YP07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YK06 YImgTop.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YCbqG YC80x YC1fPx YG0p FCiface YGcallMx YStrtodRowX.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YGcfRoomKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcallMxmn YSRrMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjGrammar PjRoundTrip.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import
PRH_Base PRH_Reader PRH_FnReader PRH_FnParse PRH_FnAlloc.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import PRH_ImgB Listing_prog PAImg_prog.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import PvB_Defs PvB_Model PvB_NCut.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require strtod_c strtod_row.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require PvB_NQ.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.P Require FmtFp_facts3.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

#[local] Existing Instance PvB_NCut.PIBn.

(* ======== the pure layer ======== *)

Lemma pnd_numch_eq : forall c, FmtFp_facts3.is_numch c = PjGrammar.numch c.
Proof.
intros c. unfold FmtFp_facts3.is_numch, PjGrammar.numch, PjGrammar.digit.
destruct ((48 <=? c) && (c <=? 57)), (c =? 43), (c =? 45), (c =? 46), (c =? 69), (c =? 101); reflexivity.
Qed.

(* the token strtod reads, x[0, m): the sign (a number character) and the span *)
Lemma pnd_txt_numch : forall c y (m : nat), pn_span (c :: y) (pn_sg c) m -> (pn_sg c < m)%nat ->
  Forall (fun z => PjGrammar.numch z = true) (firstn m (c :: y)).
Proof.
intros c y m Hs Hm. unfold pn_span, pn_sg in *. destruct (Z.eqb_spec c 45) as [E|E].
- subst c. destruct m as [|m]; [lia|]. cbn [firstn]. constructor; [reflexivity|].
  replace (S m - 1)%nat with m in Hs by lia. exact Hs.
- rewrite Nat.sub_0_r in Hs. exact Hs.
Qed.

(* ======== YC80x's runner with the caller-frame write premise (YCbqG.ajournal_x_exec_fr), carrying a memory
   invariant P (YSRrMemnorm.v's twins: SRr_msteps_inv, run_post_pi_tok_AJx_inv; P's premise right after AJ) ======== *)
Section fr. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Context {L : ptable asym} {PL : PAListing L} {PI : PAImg L}.
Variable B : asyms.
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world pa_segs -> (word -> option byte) -> Model -> Prop.
Context {hl : Z}.
Hypothesis LAWS : AR_laws_x pa_segs B ARx hl.
Variable P : (word -> option byte) -> Prop.
Hypothesis PLAW : srr_inv_laws pa_segs P.
#[local] Notation AJ := (ajournal_x (SK := SK) pa_segs B PST ARx).

Lemma pnd_chain_fr : forall W E K Bx SH ws ss (st' : shst) (r : ptrun_status asym) ms msr' STK sp0 FP ly S Hp W0 mem md
    own lyc Sc Hpc mdc k Q,
  msteps pa_segs (restrict (w_H W) ms) msr' ->
  length ws = sh_j st' ->
  img_env pa_val A_LIM (extK E K ws) ->
  match r with
  | PTS_call s => st_ok pa_segs (extK E K ws) (setpc (sh_ss st') (pa_sigma s)) msr'
  | _ => st_ok_pi pa_segs pa_val (extK E K ws) (sh_ss st') msr'
  end ->
  sh_ok pa_segs Bx SH (extK E K ws) (ms_mem msr') ->
  frame_of E (ss_mem ss) (ms_mem (restrict (w_H W) ms)) (ms_mem msr') ->
  AJ STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k ->
  P (ms_mem ms) ->
  (forall a, in_wrange E (ss_mem ss) a ->
     awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a \/ wr_fp_frame FP S lyc a) ->
  run_post_pi_tok_AJx_inv (SK := SK) asym pa_segs B PST ARx pa_val pa_sigma A_LIM P W E K Bx SH ss st' r ms STK sp0 FP
    ly S Hp W0 mem md own lyc Sc Hpc mdc k Q ->
  SRr pa_segs W (mkCfg ms mdc) Q.
Proof.
intros W E K Bx SH ws ss st' r ms msr' STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q Hms Hlen HE' HS' Hsh' Hfr HJ
  HPm Hwr Hk.
apply (SRr_msteps_inv pa_segs pa_wx P PLAW W ms msr' mdc Q Hms HPm).
intros model' Hsame Hcl HPm'.
rewrite (same_but_materialized_wvb mdc model' Hsame).
pose proof (restrict_unrestrict_clean (w_H W) (ms_mem ms) msr' Hcl) as Hrr.
pose proof (mrestrict_unrestrict_mem (w_H W) (ms_mem ms) msr' Hcl) as Hmm.
pose proof (msteps_mem_grows pa_segs _ _ Hms) as Hgr. cbn [ms_mem restrict] in Hgr.
apply (Hk ws (unrestrict (w_H W) (ms_mem ms) msr') (m_vm_materialized model') Hlen HE').
- rewrite Hrr. exact HS'.
- rewrite Hmm. exact Hsh'.
- eapply (ajournal_x_exec_fr (SK := SK) pa_segs B PST ARx LAWS pa_segs_low) with (Wr := in_wrange E (ss_mem ss));
    [exact HJ | | | | | exact Hwr].
  + rewrite Hmm. exact Hfr.
  + rewrite Hmm. exact Hgr.
  + intros x Hx. cbn [unrestrict ms_mem]. unfold munrestrict. rewrite Hx. reflexivity.
  + rewrite <- (same_but_materialized_wvb mdc model' Hsame). exact Hsame.
- exact HPm'.
- cbn [unrestrict ms_mem]. apply frame_of_unrestrict. exact Hfr.
- rewrite Hmm. exact Hfr.
- rewrite Hmm. exact Hgr.
Qed.

Lemma pnd_run_fr : forall W n E K Bx Bspan SH ss st' r ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q,
  (A_LIM <= K)%nat -> img_env pa_val A_LIM E ->
  st_ok_pi pa_segs pa_val E ss (restrict (w_H W) ms) ->
  sh_ok pa_segs Bx SH E (mrestrict (w_H W) (ms_mem ms)) ->
  sh_static_ok K Bx Bspan SH (ss_facts ss) (ss_mem ss) = true ->
  sym_runN_pi_tok pl_tpi pl_tw K Bx Bspan SH n ss = (st', r) ->
  AJ STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k ->
  P (ms_mem ms) ->
  Forall (ob_holds pa_segs Bx E (mrestrict (w_H W) (ms_mem ms))) (sh_obls st') ->
  (forall a, in_wrange E (ss_mem ss) a ->
     awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a \/ wr_fp_frame FP S lyc a) ->
  run_post_pi_tok_AJx_inv (SK := SK) asym pa_segs B PST ARx pa_val pa_sigma A_LIM P W E K Bx SH ss st' r ms STK sp0 FP
    ly S Hp W0 mem md own lyc Sc Hpc mdc k Q ->
  SRr pa_segs W (mkCfg ms mdc) Q.
Proof.
intros W n E K Bx Bspan SH ss st' r ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q HK HE HS Hsh Hchk Hrun HJ
  HPm Hobl Hwr Hk.
rewrite <- pl_tpi_eq, <- pl_tw_eq in Hrun.
destruct (sym_run_pi_tok_sound asym pa_segs (clookup pa_tbl) pa_val pa_sigma L pa_fetch_ok pa_cert pa_B_ok A_LIM
  A_LIM_text pl_lim pl_len K Bx Bspan SH HK n E ss _ st' r HE HS Hsh Hchk Hrun Hobl)
  as (ws & msr' & Hlen & Hms & HE' & HP & Hsh' & _ & Hfr).
eapply pnd_chain_fr;
  [exact Hms | exact Hlen | exact HE' | | exact Hsh' | exact Hfr | exact HJ | exact HPm | exact Hwr | exact Hk].
destruct r; cbn [ptok_post] in HP; first [exact HP | destruct HP].
Qed.

Lemma pnd_run_to_fr : forall W n stop E K Bx Bspan SH ss st' r ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q,
  (A_LIM <= K)%nat -> img_env pa_val A_LIM E ->
  st_ok_pi pa_segs pa_val E ss (restrict (w_H W) ms) ->
  sh_ok pa_segs Bx SH E (mrestrict (w_H W) (ms_mem ms)) ->
  sh_static_ok K Bx Bspan SH (ss_facts ss) (ss_mem ss) = true ->
  sym_run_toN_pi_tok pl_tpi pl_tw K Bx Bspan SH n stop ss = (st', r) ->
  AJ STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k ->
  P (ms_mem ms) ->
  Forall (ob_holds pa_segs Bx E (mrestrict (w_H W) (ms_mem ms))) (sh_obls st') ->
  (forall a, in_wrange E (ss_mem ss) a ->
     awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a \/ wr_fp_frame FP S lyc a) ->
  run_post_pi_tok_AJx_inv (SK := SK) asym pa_segs B PST ARx pa_val pa_sigma A_LIM P W E K Bx SH ss st' r ms STK sp0 FP
    ly S Hp W0 mem md own lyc Sc Hpc mdc k Q ->
  SRr pa_segs W (mkCfg ms mdc) Q.
Proof.
intros W n stop E K Bx Bspan SH ss st' r ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q HK HE HS Hsh Hchk Hrun HJ
  HPm Hobl Hwr Hk.
rewrite <- pl_tpi_eq, <- pl_tw_eq in Hrun.
destruct (sym_run_to_pi_tok_sound asym pa_segs (clookup pa_tbl) pa_val pa_sigma L pa_fetch_ok pa_cert pa_B_ok A_LIM
  A_LIM_text pl_lim pl_len K Bx Bspan SH HK n stop E ss _ st' r HE HS Hsh Hchk Hrun Hobl)
  as (ws & msr' & Hlen & Hms & HE' & HP & Hsh' & _ & Hfr).
eapply pnd_chain_fr;
  [exact Hms | exact Hlen | exact HE' | | exact Hsh' | exact Hfr | exact HJ | exact HPm | exact Hwr | exact Hk].
destruct r; cbn [ptok_post] in HP; first [exact HP | destruct HP].
Qed.
End fr.

(* ======== the symbolic states (closed terms; vm_compute runs the engine over them) ======== *)
(* atoms: 9 s1 = Y, 10 a0, 19 s3 = v, 20 s4 = q, 23 s7 = SHADOW_OFF, 25 s9 = m, 26 s10 = fa, 32 the extra atom *)
Definition PND_Bx : sv := SOff 23 0.
Definition PND_Bspan : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
(* the shadow address of atom n + c in the form the instrumented code computes it: ((n + c) >> 3) + s7 *)
Definition pnd_shx (n : nat) (c : Z) : sv := SAlu ALU_ADD (SAlu ALU_SRL (SOff n c) (SLit 3)) (SOff 23 0).
Definition PND_TOP : Z := 2 ^ 47 - 64.
Definition fa_Y : nat * afact := (9%nat, mkAF (2 ^ 46) (2 ^ 47) 5).
Definition fa_v : nat * afact := (19%nat, mkAF 4096 (2 ^ 47 - 56) 3).
Definition fa_q : nat * afact := (20%nat, mkAF (2 ^ 46) (2 ^ 47 - 24) 3).
Definition fa_B : nat * afact := (23%nat, mkAF SHADOW_OFF SHADOW_OFF 0).
Definition fa_res : nat * afact := (10%nat, mkAF 4112 PND_TOP 4).
Definition fa_m : nat * afact := (25%nat, mkAF 1 (2 ^ 30) 0).
Definition fa_nul : nat * afact := (10%nat, mkAF 4112 PND_TOP 0).
Definition fa_fa : nat * afact := (26%nat, mkAF 4096 PND_TOP 5).

(* run 1n, res = 0: M (20652) -> T (20928); writes Y + 0 and v->str *)
Definition r1n_Y : YP09.region := YP09.mkRegion (Some 9%nat) 0 8 0 8 [].
Definition r1_v : YP09.region := YP09.mkRegion (Some 19%nat) 16 24 16 24 [].
Definition ss1n : sstate := mkSS AF_pn_mret (sr_set sr_atoms 10%bv (SLit 0)) [r1n_Y; r1_v] None
  (mkFacts [fa_Y; fa_v; fa_B] [] []).
Definition SH1n : list shent := [mkSHE 19 16 24].
(* run 1, res <> 0: M -> the __asan_memcpy call; writes Y + 0, Y + 8, Y + 16 and v->str; in->p (= p1) is the extra
   atom 32 *)
Definition r1_Y : YP09.region := YP09.mkRegion (Some 9%nat) 0 24 0 24 [].
Definition r1_q : YP09.region := YP09.mkRegion (Some 20%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 32 0))].
Definition ss1 : sstate := mkSS AF_pn_mret (sr_set sr_atoms 24%bv (pnd_shx 20 0)) [r1_Y; r1_v; r1_q] None
  (mkFacts [fa_Y; fa_v; fa_q; fa_B; fa_res] [] []).
Definition SH1 : list shent := [mkSHE 19 16 24; mkSHE 20 0 8].
(* run 2: memcpy's return (20724) -> 20772, where a0 = res + m; the bound res + m >= res is the one condition *)
Definition PND_RET1 : Z := 20724.
Definition PND_NUL : Z := 20772.
Definition r2_Y : YP09.region := YP09.mkRegion (Some 9%nat) 8 24 0 0
  [YP09.mkChunk 8 (CVal 8 (pnd_shx 19 16)); YP09.mkChunk 16 (CVal 8 (SOff 19 16))].
Definition r2_v : YP09.region := YP09.mkRegion (Some 19%nat) 16 24 0 0 [YP09.mkChunk 16 (CVal 8 (SOff 10 0))].
Definition ss2 : sstate := mkSS PND_RET1 sr_atoms [r2_Y; r2_v] None
  (mkFacts [fa_Y; fa_v; fa_B; fa_res; fa_m] [mkAC BC_GEU (SAlu ALU_ADD (SOff 10 0) (SOff 25 0)) (SOff 10 0)] []).
Definition SH2 : list shent := [mkSHE 19 16 24].
(* run 3: 20772 (a0 = res + m, a5 = v + 16's shadow address) -> the strtod call; v->str = res is the extra atom 32 *)
Definition r3_b : YP09.region := YP09.mkRegion (Some 10%nat) 0 1 0 1 [].
Definition r3_Y : YP09.region := YP09.mkRegion (Some 9%nat) 24 32 0 0 [YP09.mkChunk 24 (CVal 8 (SOff 26 32))].
Definition r3_v : YP09.region := YP09.mkRegion (Some 19%nat) 16 24 0 0 [YP09.mkChunk 16 (CVal 8 (SOff 32 0))].
Definition ss3 : sstate := mkSS PND_NUL (sr_set sr_atoms 15%bv (pnd_shx 19 16)) [r3_b; r3_Y; r3_v] None
  (mkFacts [fa_Y; fa_v; fa_B; fa_nul; fa_fa] [] []).
Definition SH3 : list shent := [mkSHE 10 0 1; mkSHE 19 16 24].

Lemma pnd_static : sh_static_ok (run_K A_LIM PND_Bx SH1n ss1n) PND_Bx PND_Bspan SH1n (ss_facts ss1n) (ss_mem ss1n) = true /\
  sh_static_ok (run_K A_LIM PND_Bx SH1 ss1) PND_Bx PND_Bspan SH1 (ss_facts ss1) (ss_mem ss1) = true /\
  sh_static_ok (run_K A_LIM PND_Bx SH2 ss2) PND_Bx PND_Bspan SH2 (ss_facts ss2) (ss_mem ss2) = true /\
  sh_static_ok (run_K A_LIM PND_Bx SH3 ss3) PND_Bx PND_Bspan SH3 (ss_facts ss3) (ss_mem ss3) = true.
Proof. vm_compute. repeat split. Qed.

(* ======== the lane ======== *)
Section c. Context {fx0 : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
Context {SK : YI16.sink_head}.
Context {PA : PAImg B_prog_listing}.
#[local] Notation SEGS := (@pa_segs _ B_prog_listing PA).
#[local] Notation VAL := (@pa_val _ B_prog_listing PA).
#[local] Notation SIGMA := (@pa_sigma _ B_prog_listing PA).
#[local] Notation BASE := (@pa_val _ B_prog_listing PA A_TEXT).
#[local] Notation PST := (@prh_pst prh_img_B).
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).

(* ---- the Section hypotheses ---- *)
(* the kit's allocator laws (YCbqG.v AR_laws_x), at the harness block's head length hl *)
Context {hl : Z}.
Hypothesis LAWS : AR_laws_x SEGS B ARx hl.
(* the call texts, by the kit's names: __asan_memcpy (YGcallMxmn.v) at any float state, musl strtod (YStrtodRowX.v; its B
   instance is strtod_row.v strtod_row_B at sm := strtod_model, txt_ok := pnd_txt_ok, STKS := STK_RT_STRTOD).
   CPY is YGcallMx.v's aintrin_realizes_x OCpy with the memnorm keep `(MN.memnorm segs mem -> MN.memnorm segs mem')` as
   its last post conjunct (YGcallMxmn.v:104 aintrin_realizes_xm). The keep is a CLASS-B row (c-omx-alloc
   the internal file MEMNORM-KEEPS.md sec. 0 and 4.1): true in the model (no LPS step breaks memnorm), and the row owner of
   po_asan_memcpy_cf (YG0d2cf.aintrin_realizes_cf) pays it from the row's own run (memnorm_msteps / SRr_msteps_inv) *)
Hypothesis CPY : forall fx1 : YK11.FPState, aintrin_realizes_xm (fx := fx1) SEGS B ARx OCpy (SIGMA AS___asan_memcpy).
Definition pnd_txt_ok (txt : list Z) : Prop :=
  Forall (fun z => FmtFp_facts3.is_numch z = true) txt /\ Z.of_nat (length txt) < 2 ^ 30.
Hypothesis STR : @astrtod_realizes_x fx0 rc SEGS B ARx strtod_row.strtod_img_B (SIGMA AS_strtod) STK_RT_STRTOD
  strtod_c.strtod_model pnd_txt_ok.
(* the universal MEMNORM law (ARx -> aj_memnorm) is REFUTED and DELETED (owner 09:45Z); no memnorm hypothesis is
   left. M's last conjunct `YStrtodRowX.aj_memnorm SEGS mem` is carried to the strtod call as a state fact (header). *)
(* MARKED image fact, discharged at PI_prog_B: the image covers [IMG_LO_B, IMG_TOP_B) *)
Hypothesis IMG_COVER : forall a, IMG_LO_B <= a < IMG_TOP_B -> in_img SEGS a.
(* MARKED image fact, discharged at PI_prog_B: errno is strtod's cell (strtod_c.v) *)
Hypothesis B_errno : as_errno B = strtod_c.STRTOD_ERRNO.
(* MARKED image fact, discharged at PI_prog_B (pa_segs := rsegs) by strtod_row.v strtod_got_B: the eight read-only
   image bytes at strtod's GOT guard word hold the guard cell's address STRTOD_GUARD *)
Hypothesis IMG_GOTV : srx_got_b SEGS strtod_c.STRTOD_GOT_GUARD strtod_c.STRTOD_GUARD = true.
(* MARKED image binding of B, discharged at the image-B binding TfibSyms (Reusable/YE22.v canary_cell_in, the cell
   Tfib_const_abs index 169): strtod's GOT guard word is one of B's const cells, so AR_laws_x field 16
   alx_const_cells keeps it in every ARx state *)
Hypothesis IMG_GOTC : forall ly, In (z8 (ANum strtod_c.STRTOD_GOT_GUARD) strtod_c.STRTOD_GUARD) (as_const B ly).
(* CUTFIX (h-w6u-pre, discharged at the instance CfParams_preset, cf_head = 16): a harness head lies below the
   block's user bytes *)
Hypothesis CUTFIX_head8 : 8 <= cf_head.
(* MARKED allocator-layout law (h-w6u-pre: discharged at the ARcf instance, where the fake stack lies above the
   image): strtod_site_x asks the end cell fa + 32 above the image's globals *)
Hypothesis FS_HI : forall ly S Hp W mem md cid pos, ARx ly S Hp W mem md -> In (cid, pos) (frames S) ->
  IMG_TOP_B <= frame_addr ly cid pos.

(* ---- bytes and views ---- *)
Definition pnd_offband (a : Z) : Prop := a < SHADOW_OFF \/ SHADOW_OFF + 2 ^ 44 <= a.

Lemma pnd_band : forall x, 0 <= x < 2 ^ 47 -> ~ pnd_offband (SHADOW_OFF + x / 8).
Proof.
intros x Hx. unfold pnd_offband.
assert (0 <= x / 8 < 2 ^ 44) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia). lia.
Qed.

Lemma pnd_band_hull : forall x n s, 0 <= x -> 0 < n -> x + n <= 2 ^ 47 ->
  shadow_addr x / 8 * 8 <= s < shadow_addr (x + n - 1) / 8 * 8 + 8 -> ~ pnd_offband s.
Proof. intros x n s H0 Hn Hx Hs. unfold pnd_offband, shadow_addr, SHADOW_OFF in *. lia. Qed.

Lemma pnd_vm_keep : forall H (m m' : word -> option byte) a n v,
  val_mem SEGS (mrestrict H m) a n v ->
  (forall k, (k < n)%nat -> aview SEGS H m' (a + Z.of_nat k) = aview SEGS H m (a + Z.of_nat k)) ->
  val_mem SEGS (mrestrict H m') a n v.
Proof. intros H m m' a n v HV HK k Hk. rewrite (mbyte_of_aview SEGS H H m m' _ (HK k Hk)). exact (HV k Hk). Qed.

Lemma pnd_garr8_keep : forall H (m m' : word -> option byte) a l,
  garr8 SEGS (mrestrict H m) a l ->
  (forall j, (j < length l)%nat -> aview SEGS H m' (a + Z.of_nat j) = aview SEGS H m (a + Z.of_nat j)) ->
  garr8 SEGS (mrestrict H m') a l.
Proof.
intros H m m' a l G HK j Hj. destruct (G j Hj) as [V R]. split; [|exact R].
apply (pnd_vm_keep H m m' _ 1 _ V). intros kk Hkk. assert (kk = 0%nat) by lia. subst kk. cbn [Z.of_nat].
rewrite !Z.add_0_r. exact (HK j Hj).
Qed.

Lemma pnd_ra_keep : forall H (m m' : word -> option byte) a n,
  range_addressable (aview SEGS H m) SHADOW_OFF a n ->
  (forall x, a <= x < a + n -> aview SEGS H m' (SHADOW_OFF + x / 8) = aview SEGS H m (SHADOW_OFF + x / 8)) ->
  range_addressable (aview SEGS H m') SHADOW_OFF a n.
Proof.
intros H m m' a n RA HK x Hx. destruct (RA x Hx) as (s & Hs & Ok). exists s. split; [|exact Ok].
unfold shadow_of_addr in *. rewrite (HK x Hx). exact Hs.
Qed.

Lemma pnd_hull_keep : forall H (m m' : word -> option byte) x n,
  shadow_hull_vis (aview SEGS H m) x n ->
  (forall s, shadow_addr x / 8 * 8 <= s < shadow_addr (x + n - 1) / 8 * 8 + 8 ->
     aview SEGS H m' s = aview SEGS H m s) ->
  shadow_hull_vis (aview SEGS H m') x n.
Proof. intros H m m' x n HV HK s Hs. rewrite (HK s Hs). exact (HV s Hs). Qed.

Lemma pnd_rd32_keep : forall H (m m' : word -> option byte) a v,
  rd32 (aview SEGS H m) a v -> (forall i, a <= i < a + 4 -> aview SEGS H m' i = aview SEGS H m i) ->
  rd32 (aview SEGS H m') a v.
Proof. intros H m m' a v R HK kk Hk. rewrite (HK (a + Z.of_nat kk)) by lia. exact (R kk Hk). Qed.

Lemma pnd_aview_of_frame : forall H (E' : env) rs (m m' : word -> option byte) a,
  frame_of E' rs (mrestrict H m) (mrestrict H m') -> ~ in_wrange E' rs a -> 0 <= a < 2 ^ 64 ->
  aview SEGS H m' a = aview SEGS H m a.
Proof.
intros H E' rs m m' a HF Hn Ha. unfold aview. f_equal. unfold mbyte.
rewrite (HF (Z_to_bv 64 a)); [reflexivity|].
rewrite unsigned_lit_small by lia. exact Hn.
Qed.

(* PvB_X.v's pvx_region_nth / pvx_field: a region of the engine's state, and a chunk's value *)
Lemma pnd_region_nth : forall (fx : YK11.FPState) E ss ms i r,
  @st_ok_pi SEGS VAL fx E ss ms -> nth_error (ss_mem ss) i = Some r -> region_ok SEGS E (ms_mem ms) r.
Proof.
intros fx E ss ms i r HS Hi. destruct (st_ok_mem_ok SEGS E (abs_ss VAL ss) ms HS) as (_ & Hrs & _).
exact (proj1 (Forall_forall _ _) Hrs r (nth_error_In _ _ Hi)).
Qed.
Lemma pnd_field : forall E m n b cs lo hi wlo whi od (w : N) e v,
  region_ok SEGS E m (YP09.mkRegion (Some n) lo hi wlo whi cs) ->
  bv_unsigned (ew E n) = b -> In (YP09.mkChunk od (CVal w e)) cs -> sv_denot E e = Z_to_bv 64 v ->
  0 <= v < 2 ^ (8 * Z.of_N w) -> (Z.of_N w <= 8) ->
  val_mem SEGS m (b + od) (N.to_nat w) v.
Proof.
intros E m n b cs lo hi wlo whi od w e v (_ & _ & _ & Hcs) Hn Hc He Hv Hw.
pose proof (proj1 (Forall_forall _ _) Hcs _ Hc) as Hck. cbn [YP09.r_base base_val] in Hck. rewrite Hn in Hck.
exact (val_of_chunk_ok SEGS E m b od w e v Hck He Hv Hw).
Qed.

(* ---- the ledger and the allocator's NULL arms across writes that keep the statics, the heads and errno ---- *)
Lemma pnd_pst_b : forallb (fun r => (IMG_LO_B <=? fst r) && (fst r + snd r <=? IMG_TOP_B)) prh_pst = true.
Proof. vm_compute. reflexivity. Qed.
Lemma pnd_pst_rng : forall a, Exists (in_zr a) prh_pst -> IMG_LO_B <= a < IMG_TOP_B.
Proof.
intros a H. apply Exists_exists in H as (r & Hr & Hz). pose proof pnd_pst_b as Hb.
rewrite forallb_forall in Hb. specialize (Hb r Hr). apply andb_prop in Hb as [H1 H2].
apply Z.leb_le in H1. apply Z.leb_le in H2. unfold in_zr in Hz. lia.
Qed.
Lemma pnd_errno_rng : IMG_LO_B <= as_errno B /\ as_errno B + 4 <= IMG_TOP_B.
Proof. rewrite B_errno. unfold strtod_c.STRTOD_ERRNO, IMG_LO_B, IMG_TOP_B. lia. Qed.
Lemma pnd_errno_img : forall a, as_errno B <= a < as_errno B + 4 -> in_img SEGS a.
Proof. intros a Ha. pose proof pnd_errno_rng. apply IMG_COVER. lia. Qed.

Lemma pnd_ledger_keep : forall ly S Hp (W : world SEGS) m m' Lam peak cnt fail ran most own,
  prh_ledger B ly S Hp W m Lam peak cnt fail ran most own ->
  (forall a, Exists (in_zr a) prh_pst -> aview SEGS (w_H W) m' a = aview SEGS (w_H W) m a) ->
  (forall a k i, In (a, k) Lam -> 0 <= i < 8 ->
     aview SEGS (w_H W) m' (a - cf_head + i) = aview SEGS (w_H W) m (a - cf_head + i)) ->
  prh_ledger B ly S Hp W m' Lam peak cnt fail ran most own.
Proof.
intros ly S Hp W m m' Lam peak cnt fail ran most own (HG & HND & HF & HP) HS HH.
split; [|split; [exact HND | split; [|exact HP]]].
- destruct HG as (G1 & G2 & G3 & G4 & G5 & (G6 & R6) & (G7 & R7) & Rest).
  refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj (conj _ R6) (conj (conj _ R7) Rest)))))));
  [ apply (pnd_vm_keep _ m m' _ _ _ G1) | apply (pnd_vm_keep _ m m' _ _ _ G2) | apply (pnd_vm_keep _ m m' _ _ _ G3)
  | apply (pnd_vm_keep _ m m' _ _ _ G4) | apply (pnd_vm_keep _ m m' _ _ _ G5) | apply (pnd_vm_keep _ m m' _ _ _ G6)
  | apply (pnd_vm_keep _ m m' _ _ _ G7) ];
  intros kk Hkk; apply HS; unfold prh_pst;
  [ apply Exists_cons_hd | apply Exists_cons_tl, Exists_cons_hd | do 2 apply Exists_cons_tl; apply Exists_cons_hd
  | do 3 apply Exists_cons_tl; apply Exists_cons_hd | do 4 apply Exists_cons_tl; apply Exists_cons_hd
  | do 5 apply Exists_cons_tl; apply Exists_cons_hd | do 6 apply Exists_cons_tl; apply Exists_cons_hd ];
  unfold in_zr; cbn [fst snd]; clear - Hkk; lia.
- rewrite Forall_forall in HF |- *. intros [a k] Hin. destruct (HF _ Hin) as (H0 & Hab & Hhp & Hal & Hv).
  cbn [fst snd] in *. split; [exact H0|]. split; [exact Hab|]. split; [exact Hhp|]. split; [exact Hal|].
  apply (pnd_vm_keep _ m m' _ _ _ Hv). intros kk Hkk. apply (HH a k (Z.of_nat kk) Hin). clear - Hkk; lia.
Qed.

Lemma pnd_apost0_keep : forall n ly S Hp W Lam peak cnt fail ran most own ly' S' Hp' (W' : world SEGS) m m',
  prh_alloc_post B n ly S Hp W Lam peak cnt fail ran most own 0 ly' S' Hp' W' m ->
  (forall a, Exists (in_zr a) prh_pst -> aview SEGS (w_H W') m' a = aview SEGS (w_H W') m a) ->
  (forall a k i, In (a, k) Lam -> 0 <= i < 8 ->
     aview SEGS (w_H W') m' (a - cf_head + i) = aview SEGS (w_H W') m (a - cf_head + i)) ->
  (forall a, as_errno B <= a < as_errno B + 4 -> aview SEGS (w_H W') m' a = aview SEGS (w_H W') m a) ->
  prh_alloc_post B n ly S Hp W Lam peak cnt fail ran most own 0 ly' S' Hp' W' m'.
Proof.
intros n ly S Hp W Lam peak cnt fail ran most own ly' S' Hp' W' m m' HAP HS HH HE.
destruct HAP as [(H1 & H2 & H3 & H4 & HL) | [(H1 & H2 & H3 & H4 & H5 & H6 & HL) | (_ & H1 & _)]].
- left. split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|].
  exact (pnd_ledger_keep _ _ _ _ m m' _ _ _ _ _ _ _ HL HS HH).
- right; left. split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|]. split; [exact H5|].
  split; [exact (pnd_rd32_keep _ m m' _ _ H6 HE)|]. exact (pnd_ledger_keep _ _ _ _ m m' _ _ _ _ _ _ _ HL HS HH).
- exfalso. pose proof cf_head_nonneg. lia.
Qed.

(* ---- the entry: the stack geometry, and where the node lies ---- *)
Lemma pnd_geo : forall en, pv_pre (fx0 := fx0) B ARx en ->
  YM05.alloc_ceiling <= ly_stk_lo (pe_ly en) /\ ly_stk_lo (pe_ly en) + pe_STK en <= pe_sp en /\
  pe_sp en + pe_e en <= ly_top (pe_ly en) /\ ly_top (pe_ly en) <= ly_stk_hi (pe_ly en) /\
  ly_stk_hi (pe_ly en) <= 2 ^ 47 /\ pe_sp en mod 16 = 0 /\ 0 <= pe_e en /\ pe_e en mod 16 = 0 /\
  16880 <= pe_STK en.
Proof.
intros en (HFP & _ & _ & _ & _ & _ & _ & _ & HRDP & _).
destruct HFP as ((_ & _ & _ & _ & _ & Hstk & _) & _).
destruct Hstk as (H16 & _ & Hc & Hlo & _ & H47 & _ & Htop & Htophi).
destruct HRDP as (_ & _ & _ & _ & _ & (He0 & He16 & Hetop & _) & _).
unfold pe_sp. split; [exact Hc|]. split; [exact Hlo|]. split; [exact Hetop|]. split; [exact Htophi|].
split; [lia|]. split; [exact H16|]. split; [exact He0|]. split; [exact He16|].
unfold pe_STK, STK_parse_value.
assert (E1 : @pi_frame PvB_Defs.PIB F_parse_value + @pi_frame PvB_Defs.PIB F_parse_items = 320) by reflexivity.
assert (E2 : @LEAF_pv_pi PvB_Defs.PIB = 16560) by reflexivity.
rewrite E1, E2. assert (1 <= Z.of_nat (S (PjGrammar.MAXD - pe_d en))) by lia. nia.
Qed.

Lemma pnd_vcases : forall en, pv_pre (fx0 := fx0) B ARx en ->
  (pe_sp en <= pe_v en /\ pe_v en + 56 <= pe_sp en + pe_e en) \/
  (exists b n, In (b, n) (ablocks B (pe_ly en) (pe_S en)) /\ b <= pe_v en /\ pe_v en + 56 <= b + n /\
     forall a k, In (a, k) (pe_Lam en) -> (b, n) = (a - cf_head, k + cf_head) -> a <= pe_v en) \/
  (exists cid p, In (cid, p) (frames (pe_S en)) /\ frame_addr (pe_ly en) cid p <= pe_v en /\
     pe_v en + 56 <= frame_addr (pe_ly en) cid p + fs_frame_bytes cid).
Proof.
intros en (_ & _ & _ & _ & _ & _ & _ & _ & HRDP & _).
destruct HRDP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hnode & _ & _ & _ & HLED & _).
destruct Hnode as (_ & _ & _ & _ & Hat & _).
destruct HLED as (_ & _ & HF & _).
unfold prhReader_at in Hat. unfold pe_sp.
pose proof cf_head_nonneg as Hch.
destruct Hat as [(a & k & Hin & H1 & H2) | [(b & n & Hin & Hnl & H1 & H2) | [(cid & p & Hin & H1 & H2) | (H1 & H2)]]].
- right; left. rewrite Forall_forall in HF. destruct (HF (a, k) Hin) as (Hk & Hab & _ & _ & _). cbn [fst snd] in *.
  exists (a - cf_head), (k + cf_head). split; [exact Hab|]. split; [lia|]. split; [lia|].
  intros a' k' Hin' E. injection E as E1 E2. lia.
- right; left. exists b, n. split; [exact Hin|]. split; [exact H1|]. split; [exact H2|].
  intros a' k' Hin' E. exfalso. apply Hnl. injection E as E1 E2. subst b n.
  replace (a' - cf_head + cf_head) with a' by lia. replace (k' + cf_head - cf_head) with k' by lia. exact Hin'.
- right; right. exists cid, p. auto.
- left. auto.
Qed.

Lemma pnd_entry_ar : forall en, pv_pre (fx0 := fx0) B ARx en ->
  ARx (pe_ly en) (pe_S en) (pe_Hp en) (pe_W en) (pe_mem en) (pe_md en).
Proof. intros en (((HAR & _) & _) & _). exact HAR. Qed.

Lemma pnd_vfacts : forall en, pv_pre (fx0 := fx0) B ARx en ->
  4096 <= pe_v en /\ pe_v en mod 8 = 0 /\
  ((pe_sp en <= pe_v en /\ pe_v en + 56 <= pe_sp en + pe_e en) \/ pe_v en + 56 <= YM05.alloc_ceiling) /\
  (pe_v en + 56 <= kLowShadowBeg \/ kHighMemBeg <= pe_v en) /\ pe_v en + 56 <= 2 ^ 47.
Proof.
intros en HPRE. pose proof (pnd_geo en HPRE) as (Gc & Glo & Gtop & Gth & G47 & _ & _ & _ & GS).
pose proof (pnd_entry_ar en HPRE) as HAR0. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HPRE as (_ & _ & _ & _ & _ & _ & _ & _ & HRDP & _).
destruct HRDP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (Hv4 & Hv8 & _) & _).
split; [exact Hv4|]. split; [exact Hv8|].
destruct (pnd_vcases en HPRE) as [(H1 & H2) | [(b & n & Hin & H1 & H2 & _) | (cid & p & Hin & H1 & H2)]].
- unfold kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. split; [left; lia|]. split; [right; lia | lia].
- destruct (alx_blocks SEGS B ARx LAWS _ _ _ _ _ _ b n HAR0 Hin) as (_ & H4096 & Hbc & Happ & _).
  assert (Hn : n <= req_size n) by (unfold req_size; destruct (Z.eqb_spec n 0); lia).
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. split; [right; lia|]. split; lia.
- destruct (frames_bounds_x SEGS B ARx LAWS _ _ _ _ _ _ cid p HAR0 Hin) as (Hf0 & Hfc & Happ).
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. split; [right; lia|]. split; lia.
Qed.

Lemma pnd_vnotimg : forall en a, pv_pre (fx0 := fx0) B ARx en -> pe_v en <= a < pe_v en + 56 -> ~ in_img SEGS a.
Proof.
intros en a HPRE Ha. pose proof (pnd_geo en HPRE) as (Gc & Glo & _ & _ & _ & _ & _ & _ & GS).
pose proof (pnd_entry_ar en HPRE) as HAR0. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (pnd_vcases en HPRE) as [(H1 & H2) | [(b & n & Hin & H1 & H2 & _) | (cid & p & Hin & H1 & H2)]].
- intros Hi. pose proof (pa_segs_low a Hi). unfold kLowMemEnd in *. lia.
- assert (Hn : n <= req_size n) by (unfold req_size; destruct (Z.eqb_spec n 0); lia).
  exact (blk_img_x SEGS B ARx LAWS _ _ _ _ _ _ b n a HAR0 Hin ltac:(lia)).
- exact (frm_img_x SEGS B ARx LAWS _ _ _ _ _ _ cid p a HAR0 Hin ltac:(lia)).
Qed.

(* a byte of the node, at a later allocator state that keeps the entry's blocks and frames *)
Lemma pnd_vwrite : forall en lyc Sc own a, pv_pre (fx0 := fx0) B ARx en ->
  (forall b n, In (b, n) (ablocks B (pe_ly en) (pe_S en)) -> In (b, n) (ablocks B lyc Sc)) ->
  (forall cid p, frame_addr lyc cid p = frame_addr (pe_ly en) cid p) ->
  pe_v en <= a < pe_v en + 56 ->
  awr_byte (pe_STK en + pe_e en) (pe_sp en + pe_e en) (pe_FP en) (ablocks B (pe_ly en) (pe_S en))
    (ablocks B lyc Sc) lyc own a \/ wr_fp_frame (pe_FP en) (pe_S en) lyc a.
Proof.
intros en lyc Sc own a HPRE Hbl Hfa Ha. pose proof (pnd_geo en HPRE) as (_ & _ & _ & _ & _ & _ & He0 & _ & GS).
assert (HFP : inFP (pe_FP en) a) by (exists (pe_v en, pe_v en + 56); split; [right; right; left; reflexivity | cbn; lia]).
destruct (pnd_vcases en HPRE) as [(H1 & H2) | [(b & n & Hin & H1 & H2 & _) | (cid & p & Hin & H1 & H2)]].
- left. left. lia.
- left. right. left. split; [exact HFP|]. exists b, n. split; [exact (Hbl b n Hin)|].
  unfold req_size; destruct (Z.eqb_spec n 0); lia.
- right. split; [exact HFP|]. exists cid, p. split; [exact Hin|]. unfold in_zr, frame_rng. cbn [fst snd].
  rewrite Hfa. lia.
Qed.

Lemma pnd_vpresent : forall en STKj sp0j lyc Sc Hpc Wc memc mdc pos k, pv_pre (fx0 := fx0) B ARx en ->
  STKj = pe_STK en + pe_e en -> sp0j = pe_sp en + pe_e en ->
  ajournal_x (SK := SK) SEGS B PST ARx STKj sp0j (pe_FP en) (pe_ly en) (pe_S en) (pe_Hp en) (pe_W en) (pe_mem en)
    (pe_md en) [(0, pos)] lyc Sc Hpc Wc memc mdc k ->
  (forall b n, In (b, n) (ablocks B (pe_ly en) (pe_S en)) -> In (b, n) (ablocks B lyc Sc)) ->
  forall a, pe_v en <= a < pe_v en + 56 -> apresent (w_H Wc) memc a.
Proof.
intros en STKj sp0j lyc Sc Hpc Wc memc mdc pos k HPRE -> -> HJ Hbl a Ha.
pose proof HJ as (HAR & Hly & _ & _ & _ & Hfrs & _).
assert (Hfa : forall cid p, frame_addr lyc cid p = frame_addr (pe_ly en) cid p).
{ intros cid p. unfold frame_addr. destruct Hly as (_ & _ & _ & _ & _ & EF & _). rewrite EF. reflexivity. }
destruct (pnd_vwrite en lyc Sc [(0, pos)] a HPRE Hbl Hfa Ha) as [Hw | (_ & cid & p & Hin & Hr)].
- exact (proj1 (awr_byte_present_x (SK := SK) SEGS B PST ARx LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJ Hw)).
- assert (HinC : In (cid, p) (frames Sc)) by (rewrite Hfrs; right; exact Hin).
  destruct (alx_frames SEGS B ARx LAWS _ _ _ _ _ _ cid p HAR HinC) as (_ & _ & Hb & _).
  unfold in_zr, frame_rng in Hr. cbn [fst snd] in Hr. exact (proj1 (Hb a Hr)).
Qed.

(* a harness head [a - cf_head, a - cf_head + 8) is not a byte of the node *)
Lemma pnd_head_v : forall en lyc Sc Hpc Wc memc mdc a k i, pv_pre (fx0 := fx0) B ARx en ->
  ARx lyc Sc Hpc Wc memc mdc ->
  (forall b n, In (b, n) (ablocks B (pe_ly en) (pe_S en)) -> In (b, n) (ablocks B lyc Sc)) ->
  (forall f, In f (frames (pe_S en)) -> In f (frames Sc)) ->
  (forall cid p, frame_addr lyc cid p = frame_addr (pe_ly en) cid p) ->
  In (a - cf_head, k + cf_head) (ablocks B lyc Sc) -> 0 <= k ->
  (In (a, k) (pe_Lam en) \/ ~ In (a - cf_head, k + cf_head) (ablocks B (pe_ly en) (pe_S en))) ->
  0 <= i < 8 -> ~ (pe_v en <= a - cf_head + i < pe_v en + 56).
Proof.
intros en lyc Sc Hpc Wc memc mdc a k i HPRE HAR Hbl Hfl Hfa Hab Hk Hwh Hi.
pose proof (pnd_geo en HPRE) as (Gc & Glo & _ & _ & _ & _ & _ & _ & GS). pose proof CUTFIX_head8 as H8.
destruct (alx_blocks SEGS B ARx LAWS _ _ _ _ _ _ _ _ HAR Hab) as (_ & H4096 & Hbc & _).
assert (Hrq : k + cf_head <= req_size (k + cf_head)) by (unfold req_size; destruct (Z.eqb_spec (k + cf_head) 0); lia).
destruct (pnd_vcases en HPRE) as [(H1 & H2) | [(b & n & Hin & H1 & H2 & Hown) | (cid & p & Hin & H1 & H2)]].
- lia.
- assert (Hdec : {(b, n) = (a - cf_head, k + cf_head)} + {(b, n) <> (a - cf_head, k + cf_head)})
    by (decide equality; apply Z.eq_dec).
  destruct Hdec as [E | E].
  + destruct Hwh as [Hl | Hn].
    * pose proof (Hown a k Hl E). lia.
    * exfalso. apply Hn. rewrite <- E. exact Hin.
  + pose proof (sep_blocks_x SEGS B ARx LAWS _ _ _ _ _ _ b n _ _ HAR (Hbl b n Hin) Hab E) as Hd.
    unfold zdisjoint in Hd. cbn [fst snd] in Hd.
    assert (Hn : n <= req_size n) by (unfold req_size; destruct (Z.eqb_spec n 0); lia). lia.
- pose proof (sep_block_frame_x SEGS B ARx LAWS _ _ _ _ _ _ _ _ cid p HAR Hab (Hfl _ Hin)) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite Hfa in Hd. lia.
Qed.

(* the node is apart from the arm's own fake frame (0, pos) *)
Lemma pnd_v_own : forall en lyc Sc Hpc Wc memc mdc pos a, pv_pre (fx0 := fx0) B ARx en ->
  ARx lyc Sc Hpc Wc memc mdc -> frames Sc = (0, pos) :: frames (pe_S en) ->
  (forall b n, In (b, n) (ablocks B (pe_ly en) (pe_S en)) -> In (b, n) (ablocks B lyc Sc)) ->
  (forall cid p, frame_addr lyc cid p = frame_addr (pe_ly en) cid p) ->
  pe_v en <= a < pe_v en + 56 -> ~ (frame_addr lyc 0 pos <= a < frame_addr lyc 0 pos + 64).
Proof.
intros en lyc Sc Hpc Wc memc mdc pos a HPRE HAR Hfrs Hbl Hfa Ha.
pose proof (pnd_geo en HPRE) as (Gc & Glo & _ & _ & _ & _ & _ & _ & GS).
assert (HinF : In (0, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
destruct (frames_bounds_x SEGS B ARx LAWS _ _ _ _ _ _ 0 pos HAR HinF) as (Hf0 & Hfc & _).
change (fs_frame_bytes 0) with 64 in Hfc.
destruct (pnd_vcases en HPRE) as [(H1 & H2) | [(b & n & Hin & H1 & H2 & _) | (cid & p & Hin & H1 & H2)]].
- lia.
- pose proof (sep_block_frame_x SEGS B ARx LAWS _ _ _ _ _ _ b n 0 pos HAR (Hbl b n Hin) HinF) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. change (fs_frame_bytes 0) with 64 in Hd.
  assert (Hn : n <= req_size n) by (unfold req_size; destruct (Z.eqb_spec n 0); lia). lia.
- destruct (in_split _ _ Hin) as (l2 & l3 & El).
  pose proof (sep_frames_pos_x SEGS B ARx LAWS _ _ _ _ _ _ (0, pos) (cid, p) [] l2 l3 HAR
    ltac:(rewrite Hfrs, El; reflexivity)) as Hd.
  unfold zdisjoint, frame_rng in Hd. cbn [fst snd] in Hd. change (fs_frame_bytes 0) with 64 in Hd.
  rewrite !Hfa in *. lia.
Qed.

(* pv_frame across a write that keeps its places *)
Lemma pnd_frame_keep : forall regs0 sp0 Y fa fl shb (W : world SEGS) m m',
  pv_frame (PA := PA) regs0 sp0 Y fa fl shb W m ->
  (forall a, (sp0 - 104 <= a < sp0 \/ Y + 48 <= a < Y + 56 \/ fa <= a < fa + 24 \/ fa + 56 <= a < fa + 64 \/
     SHADOW_OFF + fa / 8 <= a < SHADOW_OFF + fa / 8 + 8) -> aview SEGS (w_H W) m' a = aview SEGS (w_H W) m a) ->
  (forall a, apresent (w_H W) m a -> apresent (w_H W) m' a) ->
  pv_frame regs0 sp0 Y fa fl shb W m'.
Proof.
intros regs0 sp0 Y fa fl shb W m m' (HY1 & HY32 & HPR & Vsav & V48 & Vmg & Vds & Vpc & Vfl & HPRfa & Hlen & Gsh)
  HK HG.
split; [exact HY1|]. split; [exact HY32|].
split; [intros a Ha; exact (HG a (HPR a Ha))|].
split.
{ rewrite Forall_forall in Vsav |- *. intros oc Hoc. apply (pnd_vm_keep _ m m' _ _ _ (Vsav oc Hoc)).
  intros kk Hkk. apply HK. left.
  assert (Hr : -104 <= fst oc <= -8)
    by (unfold pv_saved in Hoc; cbn [In] in Hoc; repeat (destruct Hoc as [<- | Hoc]; [cbn; lia|]); destruct Hoc).
  lia. }
split; [apply (pnd_vm_keep _ m m' _ _ _ V48); intros kk Hkk; apply HK; right; left; lia|].
split; [apply (pnd_vm_keep _ m m' _ _ _ Vmg); intros kk Hkk; apply HK; right; right; left; lia|].
split; [apply (pnd_vm_keep _ m m' _ _ _ Vds); intros kk Hkk; apply HK; right; right; left; lia|].
split; [apply (pnd_vm_keep _ m m' _ _ _ Vpc); intros kk Hkk; apply HK; right; right; left; lia|].
split; [apply (pnd_vm_keep _ m m' _ _ _ Vfl); intros kk Hkk; apply HK; right; right; right; left; lia|].
split; [intros a Ha; exact (HG a (HPRfa a Ha))|].
split; [exact Hlen|].
apply (pnd_garr8_keep _ m m' _ _ Gsh). intros j Hj. rewrite Hlen in Hj. apply HK. right; right; right; right. lia.
Qed.

(* the reader's cursor, text and node across a write set WR the arm's writes stay in *)
Lemma pnd_reader_keep : forall en p (W : world SEGS) m m' (WR : Z -> Prop), pv_pre (fx0 := fx0) B ARx en ->
  pn_reader en p W m (fun _ => False) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ WR a -> aview SEGS (w_H W) m' a = aview SEGS (w_H W) m a) ->
  (forall a, WR a -> pnd_offband a) ->
  (forall a, WR a -> ~ (pe_q en <= a < pe_q en + 24)) ->
  (forall a, WR a -> ~ (pe_text en <= a < pe_text en + pe_len en)) ->
  (forall a, WR a -> pe_v en <= a < pe_v en + 56 -> pe_v en + 16 <= a < pe_v en + 24) ->
  (forall a, pe_q en <= a < pe_q en + 24 -> writable_at SEGS (rdW W m') a) ->
  pn_reader en p W m' (fun a => pe_v en + 16 <= a < pe_v en + 24).
Proof.
intros en p W m m' WR HPRE (HIN & HSRC & HNODE & HRAV) HK Hband Hq Ht Hv Hwr.
pose proof (pnd_vfacts en HPRE) as (Hv4 & _ & _ & _ & Hv47).
pose proof HIN as (Vp & Ve & Vd & Hrw & Hq8 & Ht0 & Ht62 & Hp & Hlen & Gt & Hqt & Hd).
pose proof HSRC as (Gt' & Ht4 & Htc & Ham & Hra & Hhull).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HPRE as (_ & _ & _ & _ & _ & _ & _ & _ & HRDP & _).
destruct HRDP as (_ & _ & _ & _ & _ & _ & Hqlo & Hqhi & _).
pose proof (pnd_geo en HPRE) as (Gc & Glo & Gtop & Gth & G47 & _ & _ & _ & GS).
unfold pe_sp in Glo, Gtop.
assert (Hq0 : 0 <= pe_q en /\ pe_q en + 24 <= 2 ^ 47) by lia.
assert (KQ : forall a, pe_q en <= a < pe_q en + 24 -> aview SEGS (w_H W) m' a = aview SEGS (w_H W) m a)
  by (intros a Ha; apply HK; [lia | intros Hw; exact (Hq a Hw Ha)]).
assert (KT : forall a, pe_text en <= a < pe_text en + pe_len en -> aview SEGS (w_H W) m' a = aview SEGS (w_H W) m a)
  by (intros a Ha; apply HK; [lia | intros Hw; exact (Ht a Hw Ha)]).
assert (KS : forall x, 0 <= x < 2 ^ 47 ->
  aview SEGS (w_H W) m' (SHADOW_OFF + x / 8) = aview SEGS (w_H W) m (SHADOW_OFF + x / 8)).
{ intros x Hx. assert (0 <= x / 8 < 2 ^ 44) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
  apply HK; [unfold SHADOW_OFF; lia|]. intros Hw. exact (pnd_band x Hx (Hband _ Hw)). }
split; [|split; [|split]].
- split; [apply (pnd_vm_keep _ m m' _ _ _ Vp); intros kk Hkk; apply KQ; lia|].
  split; [apply (pnd_vm_keep _ m m' _ _ _ Ve); intros kk Hkk; apply KQ; lia|].
  split; [apply (pnd_vm_keep _ m m' _ _ _ Vd); intros kk Hkk; apply KQ; lia|].
  split; [intros x Hx; exact (Hwr x Hx)|].
  split; [exact Hq8|]. split; [exact Ht0|]. split; [exact Ht62|]. split; [exact Hp|]. split; [exact Hlen|].
  split; [apply (pnd_garr8_keep _ m m' _ _ Gt); intros j Hj; apply KT; lia|].
  split; [exact Hqt | exact Hd].
- split; [apply (pnd_garr8_keep _ m m' _ _ Gt'); intros j Hj; apply KT; lia|].
  split; [exact Ht4|]. split; [exact Htc|]. split; [exact Ham|].
  split; [apply (pnd_ra_keep _ m m' _ _ Hra); intros x Hx; apply KS; lia|].
  intros Hn. apply (pnd_hull_keep _ m m' _ _ (Hhull Hn)). intros s Hs.
  apply HK; [unfold shadow_addr, SHADOW_OFF in *; lia|]. intros Hw.
  exact (pnd_band_hull (pe_text en) (Z.of_nat (length (pe_tb en))) s ltac:(lia) Hn ltac:(lia) Hs (Hband _ Hw)).
- intros a Ha Hn. rewrite <- (HNODE a Ha (fun x => x)). apply HK; [lia|]. intros Hw. exact (Hn (Hv a Hw Ha)).
- apply (pnd_ra_keep _ m m' _ _ HRAV). intros x Hx. apply KS. lia.
Qed.

(* ---- the success path's helpers ---- *)
Lemma pnd_pw_last : forall {X} (R : X -> X -> Prop) l x, pairwise R (l ++ [x]) -> In x l -> R x x.
Proof.
intros X R l x. induction l as [|a l IH]; intros Hp Hin; [destruct Hin|].
cbn in Hp. destruct Hp as [Hf Hp]. destruct Hin as [<- | Hin].
- rewrite Forall_forall in Hf. apply Hf. apply in_or_app. right. left. reflexivity.
- exact (IH Hp Hin).
Qed.

Lemma pnd_mb_move : forall H H' (m m' : word -> option byte) a b v,
  aview SEGS H' m' a = aview SEGS H m b -> mbyte SEGS (mrestrict H m) b = Some v ->
  mbyte SEGS (mrestrict H' m') a = Some v.
Proof.
intros H H' m m' a b v HA V. unfold aview in HA. rewrite V in HA. cbn [option_map] in HA.
destruct (mbyte SEGS (mrestrict H' m') a) as [b'|] eqn:Eb; cbn [option_map] in HA; [|discriminate HA].
injection HA as Hb. f_equal. apply bv_eq. exact Hb.
Qed.
Lemma pnd_vm_move : forall H H' (m m' : word -> option byte) x d n v,
  val_mem SEGS (mrestrict H m) x n v ->
  (forall k, (k < n)%nat -> aview SEGS H' m' (d + Z.of_nat k) = aview SEGS H m (x + Z.of_nat k)) ->
  val_mem SEGS (mrestrict H' m') d n v.
Proof. intros H H' m m' x d n v HV HK k Hk. exact (pnd_mb_move H H' m m' _ _ _ (HK k Hk) (HV k Hk)). Qed.
Lemma pnd_garr8_aview : forall H m p l j, garr8 SEGS (mrestrict H m) p l -> (j < length l)%nat ->
  aview SEGS H m (p + Z.of_nat j) = Some (nth j l 0).
Proof.
intros H m p l j G Hj. unfold aview. rewrite (garr8_mbyte SEGS _ p l j G Hj). cbn [option_map]. f_equal.
rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256.
apply Z.mod_small. exact (proj2 (G j Hj)).
Qed.
Lemma pnd_nth_skipn : forall (l : list Z) k j, nth j (skipn k l) 0 = nth (k + j) l 0.
Proof.
intros l k. revert l. induction k as [|k IH]; intros l j; [reflexivity|].
destruct l as [|h t]; [cbn; destruct j; reflexivity | cbn; apply IH].
Qed.

Lemma pnd_U_shx : forall E n c x, ew E n = Z_to_bv 64 x -> 0 <= x < 2 ^ 64 -> 0 <= x + c < 2 ^ 64 ->
  ew E 23 = Z_to_bv 64 SHADOW_OFF -> sv_denot E (pnd_shx n c) = Z_to_bv 64 (SHADOW_OFF + (x + c) / 8).
Proof.
intros E n c x Hn Hx Hxc H23. apply bv_eq.
change (bv_unsigned (sv_denot E (pnd_shx n c))) with (U E (pnd_shx n c)). unfold pnd_shx.
rewrite !U_SAlu, (U_atom_off E n x c Hn Hx Hxc), U_SLit, (U_atom E 23 SHADOW_OFF H23) by (unfold SHADOW_OFF; lia).
cbn [zalu_raw]. change (zcanon 3) with 3. change (Z.land 3 63) with 3. rewrite Z.shiftr_div_pow2 by lia.
change (2 ^ 3) with 8. rewrite Z_to_bv_unsigned. unfold bv_wrap, zcanon, M64, SHADOW_OFF.
change (bv_modulus 64) with (2 ^ 64).
assert (0 <= (x + c) / 8 < 2 ^ 61) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
rewrite (Z.mod_small ((x + c) / 8)) by lia. rewrite Z.mod_small by lia. rewrite Z.mod_small by lia. lia.
Qed.

Lemma pnd_hull_sub : forall (rd : reader) p m d n, shadow_hull_vis rd p m -> p <= d -> d + n <= p + m -> 0 < n ->
  shadow_hull_vis rd d n.
Proof.
intros rd p m d n Hh Hpd Hdn Hn s Hs. apply Hh.
pose proof (shadow_mono p d Hpd) as M1. pose proof (shadow_mono (d + n - 1) (p + m - 1) ltac:(lia)) as M2.
assert (R8 : forall u v, u <= v -> u / 8 * 8 <= v / 8 * 8)
  by (intros u v Huv; apply Z.mul_le_mono_nonneg_r; [lia|]; apply Z.div_le_mono; lia).
pose proof (R8 _ _ M1). pose proof (R8 _ _ M2). lia.
Qed.

(* where the text lies: in a block of the entry, or in read-only image bytes off errno *)
Lemma pnd_tloc : forall en, pv_pre (fx0 := fx0) B ARx en ->
  (exists b n, In (b, n) (ablocks B (pe_ly en) (pe_S en)) /\ b <= pe_text en /\ pe_text en + pe_len en <= b + n) \/
  (forall a, pe_text en <= a < pe_text en + pe_len en -> in_img SEGS a /\ ~ (as_errno B <= a < as_errno B + 4)).
Proof.
intros en (_ & _ & _ & _ & _ & _ & _ & _ & HRDP & _).
destruct HRDP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hhome & _ & _ & _ & _ & _ & HLED & _).
destruct HLED as (_ & _ & HF & _). pose proof cf_head_nonneg as Hch.
destruct Hhome as [[(a & k & Hin & H1 & H2) | [(_ & _ & _ & HR) | (_ & _ & HR)]] | (b & n & Hin & _ & H1 & H2)].
- left. rewrite Forall_forall in HF. destruct (HF (a, k) Hin) as (Hk & Hab & _). cbn [fst snd] in *.
  exists (a - cf_head), (k + cf_head). split; [exact Hab|]. lia.
- right. intros a Ha. destruct (HR a Ha) as (Hro & _ & He). split; [|exact He].
  destruct Hro as [(sg & Hsg & _ & Hr) | Hr]; [exists sg; split; [exact Hsg | exact Hr] | exact (pa_relro_img a Hr)].
- (* kept_at's third arm kept_img (an image string): read-only image bytes off errno, as the second *)
  right. intros a Ha. destruct (HR a Ha) as (Hro & _ & He & _). split; [|exact He].
  destruct Hro as [(sg & Hsg & _ & Hr) | Hr]; [exists sg; split; [exact Hsg | exact Hr] | exact (pa_relro_img a Hr)].
- left. exists b, n. auto.
Qed.

Lemma pnd_region_nth_c : forall (fx : YK11.FPState) E ss ms i r,
  @st_ok SEGS fx E ss ms -> nth_error (ss_mem ss) i = Some r -> region_ok SEGS E (ms_mem ms) r.
Proof.
intros fx E ss ms i r HS Hi. destruct (st_ok_mem_ok SEGS E ss ms HS) as (_ & Hrs & _).
exact (proj1 (Forall_forall _ _) Hrs r (nth_error_In _ _ Hi)).
Qed.

(* the registers a call keeps: the callee-saved ones (S8aNumC.v evc_pres / evc_pres_l) *)
Definition PND_KL : list (bv 5) :=
  [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 18%bv; 19%bv; 20%bv; 21%bv; 22%bv; 23%bv; 24%bv; 25%bv; 26%bv; 27%bv].
Lemma pnd_pres : forall r r', aregs_preserved r r' -> forall x : bv 5, acallee_saved (bv_unsigned x) -> getr r' x = getr r x.
Proof. intros r r' H x Hx. rewrite <- (Z_to_bv_bv_unsigned 5 x). exact (H _ Hx). Qed.
Lemma pnd_pres_l : forall r r', aregs_preserved r r' -> forall x, In x PND_KL -> getr r' x = getr r x.
Proof.
intros r r' H x Hx. apply (pnd_pres r r' H). unfold acallee_saved.
unfold PND_KL in Hx. repeat (destruct Hx as [<-|Hx];
  [match goal with |- context [bv_unsigned ?b] => let v := eval vm_compute in (bv_unsigned b) in
     change (bv_unsigned b) with v end; lia|]). destruct Hx.
Qed.

Lemma pnd_add_denot : forall E a b, ew E 10 = Z_to_bv 64 a -> ew E 25 = Z_to_bv 64 b -> 0 <= a -> 0 <= b ->
  a + b < 2 ^ 64 -> sv_denot E (SAlu ALU_ADD (SOff 10 0) (SOff 25 0)) = Z_to_bv 64 (a + b).
Proof.
intros E a b Ha Hb H0a H0b Hab. rewrite denot_lit_U, U_SAlu, (U_atom E 10 a Ha), (U_atom E 25 b Hb) by lia.
cbn [zalu_raw]. rewrite zcanon_id by (unfold M64; lia). reflexivity.
Qed.

Lemma pnd_garr8_skipn : forall H (m : word -> option byte) p (l : list Z) k, garr8 SEGS (mrestrict H m) p l ->
  garr8 SEGS (mrestrict H m) (p + Z.of_nat k) (skipn k l).
Proof.
intros H m p l k G j Hj. rewrite length_skipn in Hj. rewrite pnd_nth_skipn.
replace (p + Z.of_nat k + Z.of_nat j) with (p + Z.of_nat (k + j)) by lia. apply G. lia.
Qed.
(* the token copied to d (n bytes of l from src) and its NUL (S8aNumC.v evc_garr8_build) *)
Lemma pnd_garr8_build : forall H (m m' : word -> option byte) src (l : list Z) d (n : nat),
  garr8 SEGS (mrestrict H m) src l -> (n <= length l)%nat ->
  (forall j, (j < n)%nat -> aview SEGS H m' (d + Z.of_nat j) = aview SEGS H m (src + Z.of_nat j)) ->
  val_mem SEGS (mrestrict H m') (d + Z.of_nat n) 1 0 ->
  garr8 SEGS (mrestrict H m') d (firstn n l ++ [0]).
Proof.
intros H m m' src l d n G Hn HA HZ j Hj.
rewrite length_app, firstn_length, Nat.min_l in Hj by lia. cbn [length] in Hj.
destruct (Nat.lt_ge_cases j n) as [Hjn | Hjn].
- rewrite app_nth1 by (rewrite firstn_length; lia). rewrite nth_firstn.
  replace (j <? n)%nat with true by (symmetry; apply Nat.ltb_lt; exact Hjn).
  destruct (G j ltac:(lia)) as [V R]. split; [|exact R].
  apply (pnd_vm_move H H m m' _ _ 1 _ V). intros kk Hkk. assert (kk = 0%nat) by lia. subst kk.
  rewrite !Z.add_0_r. exact (HA j Hjn).
- assert (j = n) by lia. subst j.
  rewrite app_nth2 by (rewrite firstn_length; lia).
  rewrite firstn_length, Nat.min_l, Nat.sub_diag by lia. cbn [nth]. split; [exact HZ | lia].
Qed.

(* errno is none of alloc.c's statics *)
Lemma pnd_pst_errno_b : forallb (fun r => (fst r + snd r <=? strtod_c.STRTOD_ERRNO) ||
  (strtod_c.STRTOD_ERRNO + 4 <=? fst r)) prh_pst = true.
Proof. vm_compute. reflexivity. Qed.
Lemma pnd_pst_errno : forall a, Exists (in_zr a) prh_pst -> ~ (as_errno B <= a < as_errno B + 4).
Proof.
intros a H He. rewrite B_errno in He. apply Exists_exists in H as (r & Hr & Hz). pose proof pnd_pst_errno_b as Hb.
rewrite forallb_forall in Hb. specialize (Hb r Hr). apply orb_prop in Hb as [Hb | Hb]; apply Z.leb_le in Hb;
  unfold in_zr in Hz; lia.
Qed.

Lemma pnd_grows_of_pres : forall H (m m' : word -> option byte),
  (forall a, apresent H m a -> apresent H m' a) -> mem_grows (mrestrict H m) (mrestrict H m').
Proof.
intros H m m' HP x Hx. unfold mrestrict in *.
destruct (H x) eqn:Hh; [exfalso; apply Hx; reflexivity|].
destruct (m x) as [b|] eqn:Em; [|exfalso; apply Hx; reflexivity].
assert (Ha : apresent H m (bv_unsigned x))
  by (unfold apresent; rewrite Z_to_bv_bv_unsigned; split; [exact Hh | exists b; exact Em]).
destruct (HP _ Ha) as [Hh' [b' Hb']]. rewrite Z_to_bv_bv_unsigned in Hb'. rewrite Hb'. discriminate.
Qed.

(* ---- the arm's places as linear facts: each check runs lia in a small context ---- *)
(* the bytes the arm writes after M: the stack below Y (memcpy's and strtod's frames) and Y's spills, v->str, the
   block's bytes and its NUL, strtod's end cell, errno *)
Definition pnd_WR (Y v res m fa er a : Z) : Prop :=
  (Y - 16384 <= a < Y + 24) \/ (v + 16 <= a < v + 24) \/ (res <= a < res + m + 1) \/ (fa + 32 <= a < fa + 40) \/
  (er <= a < er + 4).

Lemma pnd_WR_band : forall AC Y v res m ch fa er a,
  0x7fff7f800000 <= AC -> AC + 16384 <= Y ->
  (v + 56 <= kLowShadowBeg \/ kHighMemBeg <= v) -> v + 56 <= 2 ^ 47 ->
  (fa + 64 <= kLowShadowBeg \/ kHighMemBeg <= fa) -> fa + 64 <= AC ->
  8 <= ch -> (res + m + 1 <= kLowShadowBeg \/ kHighMemBeg <= res - ch) -> res + m + 1 <= AC -> AC <= 2 ^ 47 ->
  IMG_LO_B <= er -> er + 4 <= IMG_TOP_B ->
  pnd_WR Y v res m fa er a -> pnd_offband a.
Proof.
intros AC Y v res m ch fa er a HAC HY HVB HV47 HFB HFA H8 HRB HRA HAC47 HE1 HE2 HW.
unfold pnd_WR, pnd_offband, kLowShadowBeg, kHighMemBeg, SHADOW_OFF, IMG_LO_B, IMG_TOP_B in *.
destruct HW as [Ha | [Ha | [Ha | [Ha | Ha]]]].
- clear -HAC HY Ha. lia.
- clear -HVB HV47 Ha. lia.
- clear -HRB HRA H8 Ha HAC47. lia.
- clear -HFB HFA Ha HAC47. lia.
- clear -HE1 HE2 Ha. lia.
Qed.

Lemma pnd_frame_places : forall sp e Y v fa res m ch AC er a,
  0x7fff7f800000 <= AC -> AC + 16384 <= Y -> Y + 160 <= sp -> sp <= 2 ^ 47 ->
  ((sp <= v /\ v + 56 <= sp + e) \/ v + 56 <= AC) -> (v + 56 <= kLowShadowBeg \/ kHighMemBeg <= v) ->
  IMG_TOP_B <= fa -> fa + 64 <= AC -> (fa + 64 <= kLowShadowBeg \/ kHighMemBeg <= fa) ->
  (fa + 64 <= v \/ v + 56 <= fa) ->
  8 <= ch -> 0 <= m -> res + m + 1 <= AC -> (res + m + 1 <= kLowShadowBeg \/ kHighMemBeg <= res - ch) ->
  (res + m + 1 <= fa \/ fa + 64 <= res - ch) -> IMG_LO_B <= er -> er + 4 <= IMG_TOP_B ->
  (sp - 104 <= a < sp \/ Y + 48 <= a < Y + 56 \/ fa <= a < fa + 24 \/ fa + 56 <= a < fa + 64 \/
   SHADOW_OFF + fa / 8 <= a < SHADOW_OFF + fa / 8 + 8) ->
  0 <= a < 2 ^ 64 /\ ~ pnd_WR Y v res m fa er a.
Proof.
intros sp e Y v fa res m ch AC er a HAC HY HYs Hs47 HVL HVB HFI HFA HFB HFV H8 Hm HRA HRB HRF HE1 HE2 Hp.
assert (Hsf : 0 <= fa / 8 /\ 8 * (fa / 8) <= fa < 8 * (fa / 8) + 8).
{ pose proof (Z.div_mod fa 8 ltac:(discriminate)) as D1. pose proof (Z.mod_pos_bound fa 8 ltac:(reflexivity)) as D2.
  unfold IMG_TOP_B in HFI. split; [apply Z.div_pos; [clear -HFI; lia | reflexivity] | clear -D1 D2; lia]. }
set (sf := fa / 8) in *. clearbody sf.
unfold pnd_WR, kLowShadowBeg, kHighMemBeg, SHADOW_OFF, IMG_LO_B, IMG_TOP_B in *.
destruct Hp as [Ha | [Ha | [Ha | [Ha | Ha]]]].
- split; [clear -Ha HYs Hs47 HY HAC; lia|]. intros [Hc | [Hc | [Hc | [Hc | Hc]]]].
  + clear -Ha Hc HYs. lia.
  + clear -Ha Hc HVL HY HYs. lia.
  + clear -Ha Hc HRA HY HYs. lia.
  + clear -Ha Hc HFA HY HYs. lia.
  + clear -Ha Hc HE2 HFI HFA HY HYs. lia.
- split; [clear -Ha HY HAC HYs Hs47; lia|]. intros [Hc | [Hc | [Hc | [Hc | Hc]]]].
  + clear -Ha Hc. lia.
  + clear -Ha Hc HVL HY HYs. lia.
  + clear -Ha Hc HRA HY. lia.
  + clear -Ha Hc HFA HY. lia.
  + clear -Ha Hc HE2 HFI HFA HY. lia.
- split; [clear -Ha HFI HFA HY HYs Hs47; lia|]. intros [Hc | [Hc | [Hc | [Hc | Hc]]]].
  + clear -Ha Hc HFA HY. lia.
  + clear -Ha Hc HFV. lia.
  + clear -Ha Hc HRF H8 Hm. lia.
  + clear -Ha Hc. lia.
  + clear -Ha Hc HE2 HFI. lia.
- split; [clear -Ha HFI HFA HY HYs Hs47; lia|]. intros [Hc | [Hc | [Hc | [Hc | Hc]]]].
  + clear -Ha Hc HFA HY. lia.
  + clear -Ha Hc HFV. lia.
  + clear -Ha Hc HRF H8 Hm. lia.
  + clear -Ha Hc. lia.
  + clear -Ha Hc HE2 HFI. lia.
- assert (Hsf2 : sf + 8 <= 2 ^ 44) by (clear -Hsf HFA HY HYs Hs47; lia).
  split; [clear -Ha Hsf Hsf2; lia|]. intros [Hc | [Hc | [Hc | [Hc | Hc]]]].
  + clear -Ha Hc Hsf2 HAC HY. lia.
  + clear -Ha Hc Hsf Hsf2 HVB. lia.
  + clear -Ha Hc Hsf Hsf2 HRB H8 Hm. lia.
  + clear -Ha Hc Hsf Hsf2 HFB. lia.
  + clear -Ha Hc Hsf HE2. lia.
Qed.

Lemma pnd_win_places : forall sp e Y fa res m AC er a,
  AC + 16384 <= Y -> Y + 160 <= sp -> sp + e <= 2 ^ 47 ->
  IMG_TOP_B <= fa -> fa + 64 <= AC -> res + m + 1 <= AC -> er + 4 <= IMG_TOP_B ->
  sp <= a < sp + e ->
  0 <= a < 2 ^ 64 /\ ~ (Y - 16384 <= a < Y + 24) /\ ~ (res <= a < res + m + 1) /\ ~ (fa + 32 <= a < fa + 40) /\
  ~ (er <= a < er + 4).
Proof.
intros sp e Y fa res m AC er a HY HYs Hs HFI HFA HRA HE Ha. unfold IMG_TOP_B in *.
split; [lia|]. split; [lia|]. split; [lia|]. split; lia.
Qed.

Lemma pnd_v16_places : forall sp e Y v fa res m ch AC a,
  AC + 16384 <= Y -> Y + 160 <= sp ->
  ((sp <= v /\ v + 56 <= sp + e) \/ v + 56 <= AC) -> 4096 <= v -> v + 56 <= 2 ^ 47 ->
  (fa + 64 <= v \/ v + 56 <= fa) -> 8 <= ch -> (res + m + 1 <= v \/ v + 56 <= res - ch) ->
  v + 16 <= a < v + 24 ->
  0 <= a < 2 ^ 64 /\ ~ (Y - 16384 <= a < Y + 24) /\ ~ (res - ch <= a < res + m + 1) /\ ~ (fa <= a < fa + 64).
Proof.
intros sp e Y v fa res m ch AC a HY HYs HVL Hv4 Hv47 HFV H8 HRV Ha.
split; [lia|]. split; [lia|]. split; [lia | lia].
Qed.

Lemma pnd_res_places : forall Y fa res m ch AC a,
  AC + 16384 <= Y -> AC <= 2 ^ 47 -> 8 <= ch -> 4096 <= res - ch -> res + m + 1 <= AC ->
  (res + m + 1 <= fa \/ fa + 64 <= res - ch) ->
  res <= a < res + m + 1 ->
  0 <= a < 2 ^ 64 /\ ~ (fa + 32 <= a < fa + 40) /\ ~ (Y - 16384 <= a < Y + 24).
Proof. intros Y fa res m ch AC a HY HAC H8 H4 HRA HRF Ha. split; [lia|]. split; lia. Qed.

Lemma pnd_q_places : forall sp Y v q fa res m AC er,
  AC + 16384 <= Y -> Y + 160 <= sp -> sp <= q -> (q + 24 <= v \/ v + 56 <= q) ->
  IMG_TOP_B <= fa -> fa + 64 <= AC -> res + m + 1 <= AC -> er + 4 <= IMG_TOP_B ->
  forall a, pnd_WR Y v res m fa er a -> ~ (q <= a < q + 24).
Proof.
intros sp Y v q fa res m AC er HY HYs Hq HQV HFI HFA HRA HE a HW Ha. unfold pnd_WR, IMG_TOP_B in *.
destruct HW as [Hc | [Hc | [Hc | [Hc | Hc]]]]; lia.
Qed.

Definition pnd_hide (P : Prop) : Prop := P.
Ltac pnd_hide_in H := lazymatch type of H with ?P => change (pnd_hide P) in H end.
Ltac pnd_show H := let H' := fresh H in pose proof H as H'; unfold pnd_hide in H'.
Ltac pnd_rk HS Er :=
  lazymatch goal with |- getr (ms_regs ?mm) ?r = _ =>
    let H := fresh "Hrk" in prreg HS r H; rewrite H; apply Er; reflexivity end.
Ltac pnd_inc := cbn [In]; repeat (first [left; reflexivity | right]).

Lemma pnd_geu : forall E a b, ew E 10 = Z_to_bv 64 a -> ew E 25 = Z_to_bv 64 b -> 0 <= a -> 0 <= b ->
  a + b < 2 ^ 64 ->
  branch_taken BC_GEU (sv_denot E (SAlu ALU_ADD (SOff 10 0) (SOff 25 0))) (sv_denot E (SOff 10 0)) = true.
Proof.
intros E a b Ha Hb H0a H0b Hab. cbn [branch_taken]. unfold bv_ltu.
change (bv_unsigned (sv_denot E (SAlu ALU_ADD (SOff 10 0) (SOff 25 0))))
  with (U E (SAlu ALU_ADD (SOff 10 0) (SOff 25 0))).
change (bv_unsigned (sv_denot E (SOff 10 0))) with (U E (SOff 10 0)).
rewrite U_SAlu, !(U_atom E 10 a Ha), (U_atom E 25 b Hb) by lia. cbn [zalu_raw].
rewrite zcanon_id by (unfold M64; lia).
destruct (Z.ltb_spec (a + b) a); [lia | reflexivity].
Qed.

(* ======== the sub-piece: M -> T (res = 0) | R ======== *)
Theorem pnD_holds : pnD_stmt (fx0 := fx0) (rc := rc) (ci := ci) (cp := cp) (SK := SK) (PA := PA) B ARx.
Proof.
unfold pnD_stmt, pnK. intros en HPRE KT KR W' ms mdc HM.
destruct HM as (regs & mem & Y & fa & fl & pos & lyc & Sc & Hpc & k & c & y & m & res & lyc0 & Sc0 & W0 & mem0 & HM).
cbv zeta in HM.
destruct HM as (Ems & HBASE & HBODY & HR0 & HAP & HROOM & HFRS & HRD & V24 & R10 & R25 & R22 & R21 & Hlead & Hm &
  Hspan & Hstop & HQP & HMN).
subst ms. unfold pn_ms.
(* M's last conjunct, the memory normal form, as the runs' invariant P := YAkMemnorm.memnorm SEGS (by conversion) *)
assert (HPM : YAkMemnorm.memnorm SEGS mem) by exact HMN. clear HMN.
pose proof (pnd_geo en HPRE) as (Gceil & Glo & Gtop & Gtophi & G47 & G16 & Ge0 & Ge16 & GSTK).
pose proof (pnd_vfacts en HPRE) as (Hv4096 & Hv8 & Hvloc & Hvband & Hv47).
pose proof HPRE as (HFP & HCTX & _ & _ & HCHE & HCUR & Hq10 & Hv11 & HRDP & HROOMp & HFRB & _).
pose proof HRDP as (Hfrm0 & Hmuniv & Hruniv1 & Hruniv2 & Hcur0 & Hwin0 & Hqlo & Hqhi & Hqra & Hsrc0 & Hhome & Hmaxrun &
  Hnode & Hqv & Htv & Hvwin & HLED0 & Hdmax & Hcntb & Htxc).
change (spZ (pe_regs en)) with (pe_sp en) in Hqlo, Hqhi.
pose proof HBASE as (HKR & R9 & R19 & R20 & R24 & Hskip & Hc123 & Hc91 & Hc34 & Hc116 & Hc102 & Hc110).
pnd_hide_in Hc123. pnd_hide_in Hc91. pnd_hide_in Hc34. pnd_hide_in Hc116. pnd_hide_in Hc102. pnd_hide_in Hc110.
pose proof HKR as (R2 & R8 & R18 & R26 & R27 & R23 & R3 & R4).
pose proof HBODY as (HFRM & HinF & Efa & Efl & HJ & HWIN).
pose proof HFRM as (HY1 & HY32 & HPR0 & Vsav & Vfa48 & Vmagic & Vdesc & Vpc & Vfl & HPRfa & Hshlen & Gsh).
pose proof (ajx_ar HJ) as HAR. pose proof (ajx_ly HJ) as Hly. pose proof (ajx_secs HJ) as Hsecs.
pose proof (ajx_wle HJ) as Hwle. pose proof (ajx_io HJ) as Hio. pose proof (ajx_frs HJ) as Hfrs.
pose proof (ajx_nev HJ) as Hnev. pose proof (ajx_k HJ) as Hk0. pose proof (ajx_hi HJ) as J1.
pose proof (ajx_blk HJ) as J2. pose proof (ajx_img HJ) as J3. pose proof (ajx_frm HJ) as J4.
pose proof (ajx_gone HJ) as Jgone. pose proof (ajx_pres HJ) as Jpres. pose proof (ajx_stk HJ) as Jstk.
pose proof (ajx_extra HJ) as J5. pose proof (ajx_qt HJ) as JQT.
pose proof Hly as (_ & _ & _ & _ & _ & EF & _).
pose proof HRD as (HIN & HSRC & HNODE & HRAV).
pose proof HIN as (Vp & Ve & Vd & Hrw & Hq8 & Ht0 & Ht62 & Hp1 & Hlen & Gt & Hqt & Hdd).
pose proof HSRC as (Gt' & Ht4 & Htc & Ham & Hra & Hhull).
pose proof HR0 as (Hfr0 & Hab0 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (EFA : forall cid p, frame_addr lyc cid p = frame_addr (pe_ly en) cid p)
  by (intros; unfold frame_addr; rewrite EF; reflexivity).
assert (Hfrs' : frames Sc = (0, pos) :: frames (pe_S en)) by exact Hfrs.
assert (Hfl : forall f, In f (frames (pe_S en)) -> In f (frames Sc)) by (intros f Hf; rewrite Hfrs'; right; exact Hf).
assert (Efb : fs_frame_bytes 0 = 64) by reflexivity.
destruct (frames_bounds_x SEGS B ARx LAWS _ _ _ _ _ _ 0 pos HAR HinF) as (Hfa0 & Hfac & Hfapp).
rewrite <- Efa in Hfa0, Hfac, Hfapp. rewrite Efb in Hfac, Hfapp.
assert (HYc : Y = pe_sp en - 160 \/ Y = pe_sp en - 176) by lia.
(* the disjunctive facts, hidden from lia (each lia would split on all of them); pnd_show opens one *)
pnd_hide_in Hvloc. pnd_hide_in Hvband. pnd_hide_in Hqv. pnd_hide_in Htv. pnd_hide_in Hqt. pnd_hide_in HYc.
assert (Hbl : forall b n, In (b, n) (ablocks B (pe_ly en) (pe_S en)) -> In (b, n) (ablocks B lyc Sc)).
{ intros b n Hin. destruct HAP as [(_ & _ & _ & E & _) | [(_ & _ & _ & E & _) | (_ & _ & _ & _ & _ & E & _)]];
  rewrite E, Hab0; [exact Hin | exact Hin | apply in_or_app; left; exact Hin]. }
pose proof (pnd_vpresent en _ _ lyc Sc Hpc W' mem mdc pos k HPRE eq_refl eq_refl HJ Hbl) as VPRES.
assert (Hown : forall z, pe_v en <= z < pe_v en + 56 -> ~ (fa <= z < fa + 64)).
{ intros z Hz. rewrite Efa. exact (pnd_v_own en lyc Sc Hpc W' mem mdc pos z HPRE HAR Hfrs' Hbl EFA Hz). }
destruct (Z.eq_dec res 0) as [E0 | Hres0].
{ (* ======== res = 0: run 1n, M -> T, outcome (b) ======== *)
  subst res.
  assert (HLM : forall a k', In (a, k') (pe_Lam en) ->
    In (a - cf_head, k' + cf_head) (ablocks B lyc Sc) /\ 0 <= k').
  { intros a k' Hin.
    destruct HAP as [(_ & _ & _ & _ & (_ & _ & HF & _)) | [(_ & _ & _ & _ & _ & _ & (_ & _ & HF & _)) | (_ & Hneg & _)]];
      [| | exfalso; pose proof cf_head_nonneg; lia].
    all: rewrite Forall_forall in HF; destruct (HF _ Hin) as (Hk & Hab & _); split; assumption. }
  remember (@Eimg _ B_prog_listing PA (Ereg regs [])) as E eqn:HE.
  assert (Er : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r).
  { intros n r Hn. pose proof (u5_range r) as Hr5. subst E. rewrite Eimg_low by (unfold A_TEXT; lia).
    exact (ew_Ereg_nat regs [] n r Hn). }
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (RO : regs_ok E sr_atoms regs) by (subst E; apply regs_ok_Eimg_Ereg).
  clear HE.
  assert (U9 : bv_unsigned (ew E 9) = Y) by (rewrite (Er 9%nat 9%bv eq_refl), R9; apply unsigned_lit_small; lia).
  assert (U19 : bv_unsigned (ew E 19) = pe_v en)
    by (rewrite (Er 19%nat 19%bv eq_refl), R19; apply unsigned_lit_small; lia).
  assert (U23 : bv_unsigned (ew E 23) = SHADOW_OFF)
    by (rewrite (Er 23%nat 23%bv eq_refl), R23; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
  lazymatch goal with |- SRr _ _ (mkCfg ?mm _) _ =>
    assert (HS : st_ok_pi SEGS VAL E ss1n (restrict (w_H W') mm)) end.
  { rewrite restrict_mkst_fx. unfold ss1n. apply pa_entry_st_ok_full.
    - apply regs_ok_pin; [exact RO | intros X; discriminate X | rewrite R10; reflexivity].
    - vm_compute. reflexivity.
    - unfold r1n_Y, r1_v. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]; rewrite ?U9, ?U19.
      + split; [lia|]. split; [lia|]. split; [|constructor]. intros o Ho. apply (apresent_writable SEGS). apply HPR0. lia.
      + split; [lia|]. split; [lia|]. split; [|constructor]. intros o Ho. apply (apresent_writable SEGS). apply VPRES.
        lia.
    - unfold r1n_Y, r1_v. cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite ?U9, ?U19. pnd_show Hvloc. repeat split; lia.
    - split; [|split; [exact I | exact I]]. unfold fa_Y, fa_v, fa_B. cbn [f_atoms atoms_ok]. unfold afact_ok.
      cbn [af_lo af_hi af_al2]. rewrite U9, U19, U23. change (2 ^ 5) with 32. change (2 ^ 3) with 8.
      change (2 ^ 0) with 1. rewrite Z.mod_1_r. unfold SHADOW_OFF. repeat split; lia. }
  assert (SHOK : sh_ok SEGS PND_Bx SH1n E (rdW W' mem)).
  { unfold sh_ok, SH1n. constructor; [|constructor]. unfold shent_ok, app_apart. cbn [she_m she_lo she_hi].
    unfold PND_Bx. rewrite !U_SOff, U23, U19, !Z.add_0_r. rewrite !zcanon_id by (unfold M64, SHADOW_OFF; lia).
    split.
    - change (YCbn.rd_of SEGS (rdW W' mem)) with (aview SEGS (w_H W') mem).
      eapply range_addressable_sub; [exact HRAV | lia | lia].
    - intros a Ha. pnd_show Hvband. unfold kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *. lia. }
  pose proof HJ as HJa.
  pose (RUNTO := @pnd_run_to_fr fx0 rc SK B_prog_listing PL_prog_B PA B PST ARx _ LAWS (YAkMemnorm.memnorm SEGS)
    (srr_inv_laws_memnorm_k SEGS)).
  paj_run_to_tok_x_inv RUNTO HS HJa SHOK HPM PND_Bspan AF_pn_tail.
  { intros a0 (r & Hin & Ha0). vm_compute in Hin.
    destruct Hin as [<- | [<- | []]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha0; rewrite ?U9, ?U19 in Ha0.
    - left. left. lia.
    - exact (pnd_vwrite en lyc Sc [(0, pos)] a0 HPRE Hbl EFA ltac:(lia)). }
  (* ---- at T: s5 = -1, v->str = 0 ---- *)
  lazymatch type of HS with context [restrict _ ?mm] => rename mm into ms1 end.
  pmkst HS.
  assert (RK : forall x, In x [2%bv; 3%bv; 4%bv; 8%bv; 18%bv; 21%bv; 23%bv; 26%bv; 27%bv] ->
    getr (ms_regs ms1) x = getr regs x).
  { intros x Hx. cbn [In] in Hx. repeat (destruct Hx as [<- | Hx]; [pnd_rk HS Er|]). destruct Hx. }
  assert (KN : forall a, 0 <= a < 2 ^ 64 -> ~ (Y <= a < Y + 8) -> ~ (pe_v en + 16 <= a < pe_v en + 24) ->
    aview SEGS (w_H W') (ms_mem ms1) a = aview SEGS (w_H W') mem a).
  { intros a Ha H1 H2. apply (pnd_aview_of_frame (w_H W') E (ss_mem ss1n) mem (ms_mem ms1) a HFr); [|exact Ha].
    intros (r & Hin & Hr). vm_compute in Hin. destruct Hin as [<- | [<- | []]];
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?U9, ?U19 in Hr; lia. }
  lazymatch type of HS with st_ok_pi _ _ _ ?ssx _ =>
    let rg1 := eval vm_compute in (nth 1 (ss_mem ssx) r1n_Y) in
    pose proof (pnd_region_nth fx0 _ _ _ 1 rg1 HS ltac:(vm_compute; reflexivity)) as RG1
  end.
  cbn [ms_mem restrict] in RG1.
  pose proof (pnd_field E _ 19%nat (pe_v en) _ _ _ _ _ 16 8 (SLit 0) 0 RG1 U19 ltac:(cbn; tauto) eq_refl
    ltac:(cbn; lia) ltac:(cbn; lia)) as V16.
  change (N.to_nat 8) with 8%nat in V16.
  apply KT.
  exists fx0, (ms_regs ms1), (ms_mem ms1), Y, fa, fl, pos, lyc, Sc, Hpc, k, (-1).
  split; [reflexivity|].
  split; [exact Hfrm0|].
  split; [intros r _; reflexivity|].
  split; [unfold pv_keep_regs; rewrite !RK by (cbn; intuition); exact HKR|].
  split; [rewrite RK by (cbn; intuition); exact R21|].
  split.
  { (* the body: the frame, the journal, the window *)
    split.
    { apply (pnd_frame_keep _ _ _ _ _ _ _ mem _ HFRM).
      - intros a Ha. apply KN.
        + unfold SHADOW_OFF in *. lia.
        + unfold SHADOW_OFF in *. lia.
        + intros Hv. pnd_show Hvloc. pnd_show Hvband. destruct Ha as [Ha | [Ha | [Ha | [Ha | Ha]]]];
            [lia | lia | exact (Hown a ltac:(lia) ltac:(lia)) | exact (Hown a ltac:(lia) ltac:(lia)) |].
          unfold kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *.
          assert (fa / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia). lia.
      - intros a Ha. exact (apresent_grows _ _ _ a HG Ha). }
    split; [exact HinF|]. split; [exact Efa|]. split; [exact Efl|]. split; [exact HJa|].
    intros a Ha Hnf. rewrite <- (HWIN a Ha Hnf). apply KN; [lia | lia |].
    intros Hv. apply Hnf. exists (pe_v en, pe_v en + 56). split; [right; right; left; reflexivity | cbn; lia]. }
  (* T's last conjunct: run 1n's end memory's normal form (by conversion); T's run position is outcome (b)'s *)
  split; [|exact HPM].
  (* the outcome (b) *)
  exists c, y. cbv zeta.
  split; [exact Hskip|]. split; [exact Hc123|]. split; [exact Hc91|]. split; [exact Hc34|]. split; [exact Hc116|].
  split; [exact Hc102|]. split; [exact Hc110|].
  right; left. split; [reflexivity|]. split; [exact Hlead|].
  exists m, lyc0, Sc0, W0, mem0.
  split; [lia|]. split; [exact Hspan|]. split; [exact Hstop|]. split; [exact HR0|].
  split.
  { apply (pnd_apost0_keep _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mem _ HAP).
    - intros a Ha. pose proof (pnd_pst_rng a Ha). unfold IMG_LO_B, IMG_TOP_B in *. apply KN; [lia | lia |].
      intros Hv. apply (pnd_vnotimg en a HPRE ltac:(lia)). apply IMG_COVER. unfold IMG_LO_B, IMG_TOP_B. lia.
    - intros a k' i Hin Hi. destruct (HLM a k' Hin) as (Hab & Hk).
      destruct (alx_blocks SEGS B ARx LAWS _ _ _ _ _ _ _ _ HAR Hab) as (_ & H4096 & Hbc & _).
      pose proof CUTFIX_head8.
      assert (Hrq : k' + cf_head <= req_size (k' + cf_head))
        by (unfold req_size; destruct (Z.eqb_spec (k' + cf_head) 0); lia).
      apply KN; [lia | lia |]. intros Hv.
      apply (pnd_head_v en lyc Sc Hpc W' mem mdc a k' i HPRE HAR Hbl Hfl EFA Hab Hk (or_introl Hin) Hi). lia.
    - intros a Ha. pose proof pnd_errno_rng. unfold IMG_LO_B, IMG_TOP_B in *. apply KN; [lia | lia |].
      intros Hv. apply (pnd_vnotimg en a HPRE ltac:(lia)). apply IMG_COVER. unfold IMG_LO_B, IMG_TOP_B. lia. }
  split; [exact HROOM|].
  (* outcome (b)'s run position: M's NULL half (no event; Sc is M's) *)
  split; [exact (proj1 HQP eq_refl)|].
  split; [exact HFRS|].
  split; [|exact V16].
  apply (pnd_reader_keep en _ W' mem (ms_mem ms1) (fun a => (Y <= a < Y + 8) \/ (pe_v en + 16 <= a < pe_v en + 24))
    HPRE HRD).
  - intros a Ha Hn. apply KN; [exact Ha | intros H; apply Hn; left; exact H | intros H; apply Hn; right; exact H].
  - intros a [Ha | Ha]; pnd_show Hvband; unfold pnd_offband, kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *; lia.
  - intros a [Ha | Ha]; pnd_show Hqv; lia.
  - intros a [Ha | Ha]; pnd_show Htv; lia.
  - intros a [Ha | Ha] Hv; pnd_show Hvloc; lia.
  - intros a Ha. eapply writable_at_grows; [exact HG | exact (Hrw a Ha)]. }
(* ======== res <> 0 ======== *)
destruct HAP as [(_ & E1 & _) | [(_ & E1 & _) | HA3]]; [exfalso; exact (Hres0 E1) | exfalso; exact (Hres0 E1) |].
(* R's run position: M's success half *)
pose proof (proj2 HQP Hres0) as HQP1. clear HQP. rename HQP1 into HQP.
destruct HA3 as (Hcf & Hres4 & Hres16 & HresL & EHpc & Eab & HraM & HhullM & _ & HLEDM).
pnd_hide_in Hres0. pnd_hide_in Hcf.
pnd_hide_in HY32. pnd_hide_in G16. pnd_hide_in Ge16. pnd_hide_in Hq8. pnd_hide_in Hv8. pnd_hide_in Hres16.
pose proof CUTFIX_head8 as H8.
pose proof HFP as ((HAR0 & Hra0 & Hra4 & Hgp0 & Htp0 & Hstk0 & Hpres0 & Hch0 & HQT0) & _).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
pose proof Hcur0 as (_ & _ & _ & _ & _ & _ & _ & Hp0 & Hlen0 & _).
assert (Ep1 : pn_p1 en (c :: y) = pe_text en + pe_len en - Z.of_nat (length (c :: y))) by reflexivity.
(* ---- the new block NB = (res - cf_head, m + 1 + cf_head) ---- *)
assert (HNB : In (res - cf_head, Z.of_nat m + 1 + cf_head) (ablocks B lyc Sc))
  by (rewrite Eab; apply in_or_app; right; left; reflexivity).
assert (Hrq : req_size (Z.of_nat m + 1 + cf_head) = Z.of_nat m + 1 + cf_head)
  by (unfold req_size; destruct (Z.eqb_spec (Z.of_nat m + 1 + cf_head) 0); lia).
destruct (alx_blocks SEGS B ARx LAWS _ _ _ _ _ _ _ _ HAR HNB) as (Hnb16 & Hnb4096 & Hnbc & Hnbapp & Hnbpres & Hpw).
rewrite Hrq in Hnbc, Hnbapp, Hnbpres. pnd_hide_in Hnb16.
assert (HNBn : ~ In (res - cf_head, Z.of_nat m + 1 + cf_head) (ablocks B (pe_ly en) (pe_S en))).
{ intros Hin. rewrite Eab, Hab0, map_app in Hpw. cbn [map] in Hpw.
  pose proof (pnd_pw_last _ _ _ Hpw (in_map (fun b => (fst b, req_size (snd b))) _ _ Hin)) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite Hrq in Hd. lia. }
assert (HNBimg : forall a, res - cf_head <= a < res + Z.of_nat m + 1 -> ~ in_img SEGS a)
  by (intros a Ha; apply (blk_img_x SEGS B ARx LAWS _ _ _ _ _ _ _ _ a HAR HNB); rewrite Hrq; lia).
assert (HNBv : forall a, res - cf_head <= a < res + Z.of_nat m + 1 -> ~ (pe_v en <= a < pe_v en + 56)).
{ intros a Ha Hv.
  destruct (pnd_vcases en HPRE) as [(H1 & H2) | [(b & n & Hin & H1 & H2 & _) | (cid & p & Hin & H1 & H2)]].
  - lia.
  - assert (E : (b, n) <> (res - cf_head, Z.of_nat m + 1 + cf_head)) by (intros E; rewrite E in Hin; exact (HNBn Hin)).
    pose proof (sep_blocks_x SEGS B ARx LAWS _ _ _ _ _ _ b n _ _ HAR (Hbl b n Hin) HNB E) as Hd.
    unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite Hrq in Hd.
    assert (n <= req_size n) by (unfold req_size; destruct (Z.eqb_spec n 0); lia). lia.
  - pose proof (sep_block_frame_x SEGS B ARx LAWS _ _ _ _ _ _ _ _ cid p HAR HNB (Hfl _ Hin)) as Hd.
    unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite Hrq, EFA in Hd. lia. }
assert (HNBfa : forall a, res - cf_head <= a < res + Z.of_nat m + 1 -> ~ (fa <= a < fa + 64)).
{ intros a Ha Hf. pose proof (sep_block_frame_x SEGS B ARx LAWS _ _ _ _ _ _ _ _ 0 pos HAR HNB HinF) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite Hrq, <- Efa, Efb in Hd. lia. }
(* ---- the text: where it lies, and the token x[0, m) at p1 ---- *)
assert (HTL : forall a, pe_text en <= a < pe_text en + pe_len en ->
  ~ (res - cf_head <= a < res + Z.of_nat m + 1) /\ ~ (fa <= a < fa + 64) /\ ~ (as_errno B <= a < as_errno B + 4)).
{ intros a Ha. destruct (pnd_tloc en HPRE) as [(b & n & Hin & H1 & H2) | HI].
  - assert (Hn : n <= req_size n) by (unfold req_size; destruct (Z.eqb_spec n 0); lia).
    split; [|split].
    + intros Hr. assert (E : (b, n) <> (res - cf_head, Z.of_nat m + 1 + cf_head))
        by (intros E; rewrite E in Hin; exact (HNBn Hin)).
      pose proof (sep_blocks_x SEGS B ARx LAWS _ _ _ _ _ _ b n _ _ HAR (Hbl b n Hin) HNB E) as Hd.
      unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite Hrq in Hd. lia.
    + intros Hr. pose proof (sep_block_frame_x SEGS B ARx LAWS _ _ _ _ _ _ b n 0 pos HAR (Hbl b n Hin) HinF) as Hd.
      unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite <- Efa, Efb in Hd. lia.
    + intros He. exact (blk_img_x SEGS B ARx LAWS _ _ _ _ _ _ b n a HAR0 Hin ltac:(lia) (pnd_errno_img a He)).
  - destruct (HI a Ha) as [Hi He]. split; [|split; [|exact He]].
    + intros Hr. exact (HNBimg a Hr Hi).
    + intros Hr. exact (frm_img_x SEGS B ARx LAWS _ _ _ _ _ _ 0 pos a HAR HinF ltac:(rewrite <- Efa, Efb; lia) Hi). }
pose proof (pvm_skip_rest (pe_tb en) (pe_text en) (pe_len en) (pe_p en) Hlen0 Hp0) as [Hrest1 _].
change (rest_atR (pe_tb en) (pe_text en) (pe_p en)) with (pe_rest en) in Hrest1. rewrite Hskip in Hrest1.
assert (HSK : skipn (Z.to_nat (pn_p1 en (c :: y) - pe_text en)) (pe_tb en) = c :: y) by exact Hrest1.
assert (Hxl : length (c :: y) = (length (pe_tb en) - Z.to_nat (pn_p1 en (c :: y) - pe_text en))%nat)
  by (pose proof (f_equal (@length Z) HSK) as HL; rewrite length_skipn in HL; lia).
assert (HXB : forall j, (j < length (c :: y))%nat ->
  aview SEGS (w_H W') mem (pn_p1 en (c :: y) + Z.of_nat j) = Some (nth j (c :: y) 0)).
{ intros j Hj.
  replace (nth j (c :: y) 0) with (nth (Z.to_nat (pn_p1 en (c :: y) - pe_text en) + j) (pe_tb en) 0)
    by (rewrite <- pnd_nth_skipn, HSK; reflexivity).
  replace (pn_p1 en (c :: y) + Z.of_nat j) with
    (pe_text en + Z.of_nat (Z.to_nat (pn_p1 en (c :: y) - pe_text en) + j)) by lia.
  apply (pnd_garr8_aview _ _ _ _ _ Gt). lia. }
pose proof (pnd_txt_numch c y m Hspan (proj1 Hm)) as HNUM.
(* the token is shorter than 2 ^ 30 (PvB_NQ.pnq_tok_short: a run of the text's number characters, rd_pre's maxrun) *)
assert (Hm30 : Z.of_nat m < 2 ^ 30) by exact (PvB_NQ.pnq_tok_short B ARx en c y m HPRE Hskip Hm Hspan).
assert (Hlt : length (firstn m (c :: y)) = m) by (rewrite firstn_length; lia).
(* ======== run 1: M -> the __asan_memcpy call ======== *)
remember (@Eimg _ B_prog_listing PA (Ereg regs [w64 (pn_p1 en (c :: y))])) as E1 eqn:HE1.
assert (Er1 : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E1 n = getr regs r).
{ intros n r Hn. pose proof (u5_range r) as Hr5. subst E1. rewrite Eimg_low by (unfold A_TEXT; lia).
  exact (ew_Ereg_nat regs _ n r Hn). }
assert (E1_32 : ew E1 32 = w64 (pn_p1 en (c :: y))) by (subst E1; rewrite Eimg_low by (unfold A_TEXT; lia); reflexivity).
assert (HEI1 : img_env VAL A_LIM E1) by (subst E1; apply Eimg_env).
assert (RO1 : regs_ok E1 sr_atoms regs) by (subst E1; apply regs_ok_Eimg_Ereg).
clear HE1.
assert (E1_20 : ew E1 20 = w64 (pe_q en)) by (rewrite (Er1 20%nat 20%bv eq_refl); exact R20).
assert (E1_23 : ew E1 23 = w64 SHADOW_OFF) by (rewrite (Er1 23%nat 23%bv eq_refl); exact R23).
assert (U1_9 : bv_unsigned (ew E1 9) = Y) by (rewrite (Er1 9%nat 9%bv eq_refl), R9; apply unsigned_lit_small; lia).
assert (U1_19 : bv_unsigned (ew E1 19) = pe_v en)
  by (rewrite (Er1 19%nat 19%bv eq_refl), R19; apply unsigned_lit_small; lia).
assert (U1_20 : bv_unsigned (ew E1 20) = pe_q en) by (rewrite E1_20; apply unsigned_lit_small; lia).
assert (U1_23 : bv_unsigned (ew E1 23) = SHADOW_OFF)
  by (rewrite E1_23; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (U1_10 : bv_unsigned (ew E1 10) = res)
  by (rewrite (Er1 10%nat 10%bv eq_refl), R10; apply unsigned_lit_small; lia).
assert (PIN24 : getr regs 24 = sv_denot E1 (pnd_shx 20 0)).
{ rewrite R24, (pnd_U_shx E1 20 0 (pe_q en) E1_20 ltac:(lia) ltac:(lia) E1_23), Z.add_0_r. reflexivity. }
lazymatch goal with |- SRr _ _ (mkCfg ?mm _) _ =>
  assert (HS1 : st_ok_pi SEGS VAL E1 ss1 (restrict (w_H W') mm)) end.
{ rewrite restrict_mkst_fx. unfold ss1. apply pa_entry_st_ok_full.
  - apply regs_ok_pin; [exact RO1 | intros X; discriminate X | exact PIN24].
  - vm_compute. reflexivity.
  - unfold r1_Y, r1_v, r1_q. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]; rewrite ?U1_9, ?U1_19, ?U1_20.
    + split; [lia|]. split; [lia|]. split; [|constructor]. intros o Ho. apply (apresent_writable SEGS). apply HPR0. lia.
    + split; [lia|]. split; [lia|]. split; [|constructor]. intros o Ho. apply (apresent_writable SEGS). apply VPRES.
      lia.
    + split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. constructor; [|constructor].
      apply (chunk_ok_val SEGS E1 _ (pe_q en) 0 8 (SOff 32 0) (pn_p1 en (c :: y)));
        [rewrite denot_lit_U, (U_atom E1 32 _ E1_32) by lia; reflexivity | cbn; lia | cbn; lia |].
      rewrite Z.add_0_r. exact Vp.
  - unfold r1_Y, r1_v, r1_q. cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite ?U1_9, ?U1_19, ?U1_20.
    pnd_show Hvloc. pnd_show Hqv. repeat split; lia.
  - split; [|split; [exact I | exact I]]. unfold fa_Y, fa_v, fa_q, fa_B, fa_res, PND_TOP. cbn [f_atoms atoms_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U1_9, U1_19, U1_20, U1_23, U1_10.
    change (2 ^ 5) with 32. change (2 ^ 4) with 16. change (2 ^ 3) with 8. change (2 ^ 0) with 1. rewrite Z.mod_1_r.
    pnd_show HY32. pnd_show Hv8. pnd_show Hq8. pnd_show Hres16. unfold SHADOW_OFF. repeat split; lia. }
assert (SHOK1 : sh_ok SEGS PND_Bx SH1 E1 (rdW W' mem)).
{ unfold sh_ok, SH1. constructor; [|constructor; [|constructor]]; unfold shent_ok, app_apart; cbn [she_m she_lo she_hi];
    unfold PND_Bx; rewrite !U_SOff, ?U1_23, ?U1_19, ?U1_20, !Z.add_0_r; rewrite !zcanon_id by (unfold M64, SHADOW_OFF; lia);
    change (YCbn.rd_of SEGS (rdW W' mem)) with (aview SEGS (w_H W') mem); split.
  - eapply range_addressable_sub; [exact HRAV | lia | lia].
  - intros a Ha. pnd_show Hvband. unfold kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *. lia.
  - intros z Hz. exists 0. split; [|left; reflexivity]. unfold shadow_of_addr.
    apply (alx_zshadow_byte SEGS B ARx LAWS lyc Sc Hpc W' mem mdc z HAR). rewrite Eslo, Eshi. lia.
  - intros a Ha. unfold SHADOW_OFF in *. lia. }
pose proof HJ as HJb.
pose (RUN := @pnd_run_fr fx0 rc SK B_prog_listing PL_prog_B PA B PST ARx _ LAWS (YAkMemnorm.memnorm SEGS)
  (srr_inv_laws_memnorm_k SEGS)).
paj_run_tok_x_inv RUN HS1 HJb SHOK1 HPM PND_Bspan.
{ intros a0 (r & Hin & Ha0). vm_compute in Hin.
  destruct Hin as [<- | [<- | [<- | []]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha0;
    rewrite ?U1_9, ?U1_19, ?U1_20 in Ha0.
  - left. left. lia.
  - exact (pnd_vwrite en lyc Sc [(0, pos)] a0 HPRE Hbl EFA ltac:(lia)).
  - lia. }
(* ---- at the __asan_memcpy call: a0 = res, a1 = p1, a2 = m ---- *)
lazymatch type of HS1 with context [restrict _ ?mm] => rename mm into ms1 end.
pmkst HS1. rename HFr into HFr_1. rename HG into HG_1. clear HF.
assert (RK1 : forall x, In x [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 18%bv; 19%bv; 20%bv; 21%bv; 22%bv; 23%bv; 25%bv; 26%bv;
  27%bv] -> getr (ms_regs ms1) x = getr regs x).
{ intros x Hx. cbn [In] in Hx. repeat (destruct Hx as [<- | Hx]; [pnd_rk HS1 Er1|]). destruct Hx. }
assert (T24 : getr (ms_regs ms1) 24 = getr regs 24).
{ pose proof (st_ok_restrict_reg SEGS (w_H W') _ _ ms1 24%bv HS1) as T.
  lazymatch type of T with _ = sv_denot _ (sr_get (ss_regs ?ssx) _) =>
    change (sr_get (ss_regs ssx) 24%bv) with (pnd_shx 20 0) in T end.
  rewrite T, PIN24. reflexivity. }
assert (RKL1 : forall x, In x PND_KL -> getr (ms_regs ms1) x = getr regs x).
{ intros x Hx. unfold PND_KL in Hx. cbn [In] in Hx.
  repeat (destruct Hx as [<- | Hx]; [first [exact T24 | apply RK1; cbn [In]; intuition] |]). destruct Hx. }
prreg HS1 (10%bv : bv 5) T10. rewrite (Er1 10%nat 10%bv eq_refl), R10 in T10.
prreg HS1 (11%bv : bv 5) T11. rewrite E1_32 in T11.
prreg HS1 (12%bv : bv 5) T12. rewrite (Er1 25%nat 25%bv eq_refl), R25 in T12.
prreg HS1 (1%bv : bv 5) T1.
assert (K1 : forall a, 0 <= a < 2 ^ 64 -> ~ (Y <= a < Y + 24) -> ~ (pe_v en + 16 <= a < pe_v en + 24) ->
  aview SEGS (w_H W') (ms_mem ms1) a = aview SEGS (w_H W') mem a).
{ intros a Ha H1 H2. apply (pnd_aview_of_frame (w_H W') E1 (ss_mem ss1) mem (ms_mem ms1) a HFr_1); [|exact Ha].
  intros (r & Hin & Hr). vm_compute in Hin. destruct Hin as [<- | [<- | [<- | []]]];
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?U1_9, ?U1_19, ?U1_20 in Hr; lia. }
assert (KB1 : forall s, 0 <= s < 2 ^ 64 -> ~ pnd_offband s ->
  aview SEGS (w_H W') (ms_mem ms1) s = aview SEGS (w_H W') mem s).
{ intros s Hs Hb. pnd_show Hvband. apply K1; [exact Hs | |]; intros Hc; apply Hb;
  unfold pnd_offband, kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *; lia. }
assert (E1_19 : ew E1 19 = w64 (pe_v en)) by (rewrite (Er1 19%nat 19%bv eq_refl); exact R19).
assert (E1_10 : ew E1 10 = w64 res) by (rewrite (Er1 10%nat 10%bv eq_refl); exact R10).
lazymatch type of HS1 with st_ok _ _ ?ssx _ =>
  let rgY := eval vm_compute in (nth 0 (ss_mem ssx) r1_Y) in
  let rgv := eval vm_compute in (nth 1 (ss_mem ssx) r1_Y) in
  pose proof (pnd_region_nth_c fx0 _ _ _ 0 rgY HS1 ltac:(vm_compute; reflexivity)) as RGY;
  pose proof (pnd_region_nth_c fx0 _ _ _ 1 rgv HS1 ltac:(vm_compute; reflexivity)) as RGv
end.
cbn [ms_mem restrict] in RGY, RGv.
pose proof (pnd_field E1 _ 9%nat Y _ _ _ _ _ 8 8 (pnd_shx 19 16) (SHADOW_OFF + (pe_v en + 16) / 8) RGY U1_9
  ltac:(pnd_inc) (pnd_U_shx E1 19 16 (pe_v en) E1_19 ltac:(lia) ltac:(lia) E1_23)
  ltac:(cbn; unfold SHADOW_OFF; lia) ltac:(cbn; lia)) as V1_8.
pose proof (pnd_field E1 _ 9%nat Y _ _ _ _ _ 16 8 (SOff 19 16) (pe_v en + 16) RGY U1_9 ltac:(pnd_inc)
  ltac:(rewrite denot_lit_U, (U_atom_off E1 19 (pe_v en) 16 E1_19) by lia; reflexivity)
  ltac:(cbn; lia) ltac:(cbn; lia)) as V1_16.
pose proof (pnd_field E1 _ 19%nat (pe_v en) _ _ _ _ _ 16 8 (SOff 10 0) res RGv U1_19 ltac:(pnd_inc)
  ltac:(rewrite denot_lit_U, (U_atom E1 10 res E1_10) by lia; reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as V1_v.
change (N.to_nat 8) with 8%nat in V1_8, V1_16, V1_v.
(* ---- the __asan_memcpy call (YGcallMxmn.aj_intrin_at_xm, CPY's keep): res <- x[0, m) at p1, memnorm kept ---- *)
eapply SRr_bind.
{ eapply (aj_intrin_at_xm (fx := fx0) (SK := SK) SEGS B PST ARx LAWS pa_segs_low OCpy (SIGMA AS___asan_memcpy)
    (CPY fx0) W' (ms_regs ms1) (ms_mem ms1) _ _ _ _ _ _ _ _ _ [(0, pos)] lyc Sc Hpc _ k res (pn_p1 en (c :: y))
    (Z.of_nat m) (Y - (pe_sp en + pe_e en)) _ HJb).
  - exact T10.
  - exact T11.
  - exact T12.
  - lia.
  - lia.
  - lia.
  - unfold spZ. rewrite (RK1 2%bv ltac:(cbn; intuition)), R2, unsigned_lit_small by lia. lia.
  - pnd_show HY32. pnd_show G16. pnd_show Ge16. lia.
  - lia.
  - unfold ESTACK. lia.
  - rewrite (RK1 3%bv ltac:(cbn; intuition)), R3. exact Hgp0.
  - rewrite (RK1 4%bv ltac:(cbn; intuition)), R4. exact Htp0.
  - exact T1.
  - apply (ret_ok_codeptr_v (PI := PA)); [lia | reflexivity].
  - intros a Ha. split; [|unfold ESTACK; lia].
    unfold awr_byte. right; right; left. unfold in_tmp_block. exists (res - cf_head), (Z.of_nat m + 1 + cf_head).
    split; [exact HNB|]. split; [exact HNBn|]. rewrite Hrq. lia.
  - unfold amem_range, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kLowMemEnd, kHighMemEnd in *. lia.
  - apply (pnd_ra_keep _ mem (ms_mem ms1)); [eapply range_addressable_sub; [exact HraM | lia | lia] |].
    intros z Hz. apply KB1; [unfold SHADOW_OFF; lia | apply pnd_band; lia].
  - intros Hn0. apply (pnd_hull_keep _ mem (ms_mem ms1));
      [eapply pnd_hull_sub; [exact (HhullM ltac:(lia)) | lia | lia | exact Hn0] |].
    intros s Hs. apply KB1; [unfold shadow_addr, SHADOW_OFF in *; lia |].
    exact (pnd_band_hull res (Z.of_nat m) s ltac:(lia) Hn0 ltac:(lia) Hs).
  - split; [lia|]. split; [lia|]. split.
    { intros a Ha. split.
      - pnd_show Htv. rewrite (K1 a) by (unfold SHADOW_OFF in *; lia).
        replace a with (pn_p1 en (c :: y) + Z.of_nat (Z.to_nat (a - pn_p1 en (c :: y)))) by lia.
        rewrite HXB by lia. discriminate.
      - unfold spZ. rewrite (RK1 2%bv ltac:(cbn; intuition)), R2, unsigned_lit_small by lia. unfold ESTACK. lia. }
    split.
    { destruct (Z_le_gt_dec (res + Z.of_nat m) (pn_p1 en (c :: y))) as [Hl|Hl]; [left; lia|].
      destruct (Z_le_gt_dec (pn_p1 en (c :: y) + Z.of_nat m) res) as [Hr|Hr]; [right; lia|].
      exfalso. destruct (HTL (Z.max res (pn_p1 en (c :: y))) ltac:(lia)) as [Hn _]. apply Hn. lia. }
    split; [unfold amem_range in *; lia|].
    split.
    { apply (pnd_ra_keep _ mem (ms_mem ms1)); [eapply range_addressable_sub; [exact Hra | lia | lia] |].
      intros z Hz. apply KB1; [unfold SHADOW_OFF; lia | apply pnd_band; lia]. }
    intros Hn0. apply (pnd_hull_keep _ mem (ms_mem ms1));
      [eapply pnd_hull_sub; [exact (Hhull ltac:(lia)) | lia | lia | exact Hn0] |].
    intros s Hs. apply KB1; [unfold shadow_addr, SHADOW_OFF in *; lia |].
    exact (pnd_band_hull (pn_p1 en (c :: y)) (Z.of_nat m) s ltac:(lia) Hn0 ltac:(lia) Hs). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Hr2 & Hcopy & Hfr2 & Hpres2 & HPM2).
(* the engine of record's keep (YGcallMxmn 2b01e06e3fc4) is an implication from the call memory's normal form *)
cbv beta iota in Hcopy. pose proof (HPM2 HPM) as HPM3. clear HPM HPM2. rename HPM3 into HPM.
(* ======== run 2: memcpy's return (B 0x867c0) -> B 0x867f0, a0 = res + m ======== *)
assert (K2 : forall a, 0 <= a < 2 ^ 64 -> ~ (res <= a < res + Z.of_nat m) -> ~ (Y - 4096 <= a < Y) ->
  aview SEGS (w_H W') mem2 a = aview SEGS (w_H W') (ms_mem ms1) a).
{ intros a Ha H1 H2. apply Hfr2; [exact Ha | exact H1 | unfold ESTACK; lia]. }
assert (RK2 : forall x, In x PND_KL -> getr regs2 x = getr regs x)
  by (intros x Hx; rewrite (pnd_pres_l _ _ HP2 x Hx); exact (RKL1 x Hx)).
assert (KB2 : forall s, 0 <= s < 2 ^ 64 -> ~ pnd_offband s -> aview SEGS (w_H W') mem2 s = aview SEGS (w_H W') mem s).
{ intros s Hs Hb. rewrite <- (KB1 s Hs Hb). apply K2; [exact Hs | |]; intros Hc; apply Hb;
  unfold pnd_offband, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SHADOW_OFF in *; lia. }
remember (@Eimg _ B_prog_listing PA (Ereg regs2 [])) as E2 eqn:HE2.
assert (Er2 : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E2 n = getr regs2 r).
{ intros n r Hn. pose proof (u5_range r) as Hr5. subst E2. rewrite Eimg_low by (unfold A_TEXT; lia).
  exact (ew_Ereg_nat regs2 [] n r Hn). }
assert (HEI2 : img_env VAL A_LIM E2) by (subst E2; apply Eimg_env).
assert (RO2 : regs_ok E2 sr_atoms regs2) by (subst E2; apply regs_ok_Eimg_Ereg).
clear HE2.
assert (E2_9 : ew E2 9 = w64 Y) by (rewrite (Er2 9%nat 9%bv eq_refl), (RK2 9%bv ltac:(cbn; intuition)); exact R9).
assert (E2_19 : ew E2 19 = w64 (pe_v en))
  by (rewrite (Er2 19%nat 19%bv eq_refl), (RK2 19%bv ltac:(cbn; intuition)); exact R19).
assert (E2_23 : ew E2 23 = w64 SHADOW_OFF)
  by (rewrite (Er2 23%nat 23%bv eq_refl), (RK2 23%bv ltac:(cbn; intuition)); exact R23).
assert (E2_10 : ew E2 10 = w64 res) by (rewrite (Er2 10%nat 10%bv eq_refl); exact Hr2).
assert (E2_25 : ew E2 25 = w64 (Z.of_nat m))
  by (rewrite (Er2 25%nat 25%bv eq_refl), (RK2 25%bv ltac:(cbn; intuition)); exact R25).
assert (U2_9 : bv_unsigned (ew E2 9) = Y) by (rewrite E2_9; apply unsigned_lit_small; lia).
assert (U2_19 : bv_unsigned (ew E2 19) = pe_v en) by (rewrite E2_19; apply unsigned_lit_small; lia).
assert (U2_23 : bv_unsigned (ew E2 23) = SHADOW_OFF)
  by (rewrite E2_23; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (U2_10 : bv_unsigned (ew E2 10) = res) by (rewrite E2_10; apply unsigned_lit_small; lia).
assert (U2_25 : bv_unsigned (ew E2 25) = Z.of_nat m) by (rewrite E2_25; apply unsigned_lit_small; lia).
lazymatch goal with |- SRr _ _ (mkCfg ?mm _) _ =>
  assert (HS2 : st_ok_pi SEGS VAL E2 ss2 (restrict (w_H W') mm)) end.
{ rewrite restrict_mkst_fx. unfold ss2. apply pa_entry_st_ok_full.
  - exact RO2.
  - vm_compute. reflexivity.
  - unfold r2_Y, r2_v. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]; rewrite ?U2_9, ?U2_19.
    + split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. constructor; [|constructor; [|constructor]].
      * apply (chunk_ok_val SEGS E2 _ Y 8 8 (pnd_shx 19 16) (SHADOW_OFF + (pe_v en + 16) / 8));
          [exact (pnd_U_shx E2 19 16 (pe_v en) E2_19 ltac:(lia) ltac:(lia) E2_23) | cbn; unfold SHADOW_OFF; lia
          | cbn; lia |].
        apply (pnd_vm_keep _ (ms_mem ms1) mem2 _ _ _ V1_8). intros kk Hkk. apply K2; lia.
      * apply (chunk_ok_val SEGS E2 _ Y 16 8 (SOff 19 16) (pe_v en + 16));
          [rewrite denot_lit_U, (U_atom_off E2 19 (pe_v en) 16 E2_19) by lia; reflexivity | cbn; lia | cbn; lia |].
        apply (pnd_vm_keep _ (ms_mem ms1) mem2 _ _ _ V1_16). intros kk Hkk. apply K2; lia.
    + split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. constructor; [|constructor].
      apply (chunk_ok_val SEGS E2 _ (pe_v en) 16 8 (SOff 10 0) res);
        [rewrite denot_lit_U, (U_atom E2 10 res E2_10) by lia; reflexivity | cbn; lia | cbn; lia |].
      apply (pnd_vm_keep _ (ms_mem ms1) mem2 _ _ _ V1_v). intros kk Hkk. pnd_show Hvloc. apply K2; [lia | | lia].
      intros Hc. exact (HNBv (pe_v en + 16 + Z.of_nat kk) ltac:(lia) ltac:(lia)).
  - unfold r2_Y, r2_v. cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite ?U2_9, ?U2_19. pnd_show Hvloc. repeat split; lia.
  - split; [|split; [|exact I]].
    + unfold fa_Y, fa_v, fa_B, fa_res, fa_m, PND_TOP. cbn [f_atoms atoms_ok]. unfold afact_ok.
      cbn [af_lo af_hi af_al2]. rewrite U2_9, U2_19, U2_23, U2_10, U2_25. change (2 ^ 5) with 32.
      change (2 ^ 4) with 16. change (2 ^ 3) with 8. change (2 ^ 0) with 1. rewrite !Z.mod_1_r.
      pnd_show HY32. pnd_show Hv8. pnd_show Hres16. unfold SHADOW_OFF. repeat split; lia.
    + split; [|exact I]. unfold acond_ok. cbn [ac_c ac_a ac_b].
      apply (pnd_geu E2 res (Z.of_nat m) E2_10 E2_25); lia. }
assert (SHOK2 : sh_ok SEGS PND_Bx SH2 E2 (rdW W' mem2)).
{ unfold sh_ok, SH2. constructor; [|constructor]. unfold shent_ok, app_apart. cbn [she_m she_lo she_hi].
  unfold PND_Bx. rewrite !U_SOff, U2_23, U2_19, !Z.add_0_r. rewrite !zcanon_id by (unfold M64, SHADOW_OFF; lia).
  change (YCbn.rd_of SEGS (rdW W' mem2)) with (aview SEGS (w_H W') mem2). split.
  - apply (pnd_ra_keep _ mem mem2); [eapply range_addressable_sub; [exact HRAV | lia | lia] |].
    intros z Hz. apply KB2; [unfold SHADOW_OFF; lia | apply pnd_band; lia].
  - intros a Ha. pnd_show Hvband. unfold kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *. lia. }
pose proof HJ2 as HJc.
pose (RUNTO2 := @paj_run_to_x_inv fx0 rc SK B_prog_listing PL_prog_B PA B PST ARx _ LAWS (YAkMemnorm.memnorm SEGS)
  (srr_inv_laws_memnorm_k SEGS)).
paj_run_to_tok_x_inv RUNTO2 HS2 HJc SHOK2 HPM PND_Bspan PND_NUL.
{ intros a0 (r & Hin & Ha0). vm_compute in Hin.
  destruct Hin as [<- | [<- | []]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha0; lia. }
lazymatch type of HS2 with context [restrict _ ?mm] => rename mm into ms2 end.
pmkst HS2. rename HFr into HFr_2. rename HG into HG_2. clear HF.
assert (RK3 : forall x, In x PND_KL -> getr (ms_regs ms2) x = getr regs x).
{ intros x Hx. rewrite <- (RK2 x Hx). unfold PND_KL in Hx. cbn [In] in Hx.
  repeat (destruct Hx as [<- | Hx]; [pnd_rk HS2 Er2|]). destruct Hx. }
pose proof (st_ok_pi_restrict_reg (w_H W') E2 _ ms2 10%bv HS2) as T3_10.
lazymatch type of T3_10 with _ = sv_denot _ (sr_get (ss_regs ?ssx) _) =>
  change (sr_get (ss_regs ssx) 10%bv) with (SAlu ALU_ADD (SOff 10 0) (SOff 25 0)) in T3_10 end.
rewrite (pnd_add_denot E2 res (Z.of_nat m) E2_10 E2_25) in T3_10 by lia.
pose proof (st_ok_pi_restrict_reg (w_H W') E2 _ ms2 15%bv HS2) as T3_15.
lazymatch type of T3_15 with _ = sv_denot _ (sr_get (ss_regs ?ssx) _) =>
  change (sr_get (ss_regs ssx) 15%bv) with (pnd_shx 19 16) in T3_15 end.
rewrite (pnd_U_shx E2 19 16 (pe_v en) E2_19 ltac:(lia) ltac:(lia) E2_23) in T3_15.
assert (K3 : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W') (ms_mem ms2) a = aview SEGS (w_H W') mem2 a).
{ intros a Ha. apply (pnd_aview_of_frame (w_H W') E2 (ss_mem ss2) mem2 (ms_mem ms2) a HFr_2); [|exact Ha].
  intros (r & Hin & Hr). vm_compute in Hin. destruct Hin as [<- | [<- | []]];
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; lia. }
(* ======== run 3: B 0x867f0 -> the strtod call; the NUL at res + m ======== *)
remember (@Eimg _ B_prog_listing PA (Ereg (ms_regs ms2) [w64 res])) as E3 eqn:HE3.
assert (Er3 : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E3 n = getr (ms_regs ms2) r).
{ intros n r Hn. pose proof (u5_range r) as Hr5. subst E3. rewrite Eimg_low by (unfold A_TEXT; lia).
  exact (ew_Ereg_nat (ms_regs ms2) _ n r Hn). }
assert (E3_32 : ew E3 32 = w64 res) by (subst E3; rewrite Eimg_low by (unfold A_TEXT; lia); reflexivity).
assert (HEI3 : img_env VAL A_LIM E3) by (subst E3; apply Eimg_env).
assert (RO3 : regs_ok E3 sr_atoms (ms_regs ms2)) by (subst E3; apply regs_ok_Eimg_Ereg).
clear HE3.
assert (E3_9 : ew E3 9 = w64 Y) by (rewrite (Er3 9%nat 9%bv eq_refl), (RK3 9%bv ltac:(cbn; intuition)); exact R9).
assert (E3_19 : ew E3 19 = w64 (pe_v en))
  by (rewrite (Er3 19%nat 19%bv eq_refl), (RK3 19%bv ltac:(cbn; intuition)); exact R19).
assert (E3_23 : ew E3 23 = w64 SHADOW_OFF)
  by (rewrite (Er3 23%nat 23%bv eq_refl), (RK3 23%bv ltac:(cbn; intuition)); exact R23).
assert (E3_26 : ew E3 26 = w64 fa)
  by (rewrite (Er3 26%nat 26%bv eq_refl), (RK3 26%bv ltac:(cbn; intuition)); exact R26).
assert (E3_10 : ew E3 10 = w64 (res + Z.of_nat m)) by (rewrite (Er3 10%nat 10%bv eq_refl); exact T3_10).
assert (U3_9 : bv_unsigned (ew E3 9) = Y) by (rewrite E3_9; apply unsigned_lit_small; lia).
assert (U3_19 : bv_unsigned (ew E3 19) = pe_v en) by (rewrite E3_19; apply unsigned_lit_small; lia).
assert (U3_23 : bv_unsigned (ew E3 23) = SHADOW_OFF)
  by (rewrite E3_23; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (U3_26 : bv_unsigned (ew E3 26) = fa) by (rewrite E3_26; apply unsigned_lit_small; lia).
assert (U3_10 : bv_unsigned (ew E3 10) = res + Z.of_nat m) by (rewrite E3_10; apply unsigned_lit_small; lia).
assert (PIN15 : getr (ms_regs ms2) 15 = sv_denot E3 (pnd_shx 19 16))
  by (rewrite T3_15, (pnd_U_shx E3 19 16 (pe_v en) E3_19 ltac:(lia) ltac:(lia) E3_23); reflexivity).
destruct (alx_frames SEGS B ARx LAWS _ _ _ _ _ _ 0 pos HAR HinF) as (Hfa32 & _).
rewrite <- Efa in Hfa32. pnd_hide_in Hfa32.
assert (PNUL : apresent (w_H W') (ms_mem ms2) (res + Z.of_nat m)).
{ apply (apresent_grows _ _ _ _ HG_2). apply Hpres2. apply (apresent_grows _ _ _ _ HG_1).
  exact (proj1 (Hnbpres (res + Z.of_nat m) ltac:(lia))). }
lazymatch goal with |- SRr _ _ (mkCfg ?mm _) _ =>
  assert (HS3 : st_ok_pi SEGS VAL E3 ss3 (restrict (w_H W') mm)) end.
{ rewrite restrict_mkst_fx. unfold ss3. apply pa_entry_st_ok_full.
  - apply regs_ok_rereg; [exact RO3 | reflexivity | exact PIN15].
  - vm_compute. reflexivity.
  - unfold r3_b, r3_Y, r3_v. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]; rewrite ?U3_10, ?U3_9, ?U3_19.
    + split; [lia|]. split; [lia|]. split; [|constructor]. intros o Ho.
      replace (res + Z.of_nat m + o) with (res + Z.of_nat m) by lia. exact (apresent_writable SEGS _ _ _ PNUL).
    + split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. constructor; [|constructor].
      apply (chunk_ok_val SEGS E3 _ Y 24 8 (SOff 26 32) (fa + 32));
        [rewrite denot_lit_U, (U_atom_off E3 26 fa 32 E3_26) by lia; reflexivity | cbn; lia | cbn; lia |].
      apply (pnd_vm_keep _ mem (ms_mem ms2) _ _ _ V24). intros kk Hkk. pnd_show Hvloc.
      rewrite K3 by lia. rewrite K2 by lia. apply K1; lia.
    + split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. constructor; [|constructor].
      apply (chunk_ok_val SEGS E3 _ (pe_v en) 16 8 (SOff 32 0) res);
        [rewrite denot_lit_U, (U_atom E3 32 res E3_32) by lia; reflexivity | cbn; lia | cbn; lia |].
      apply (pnd_vm_keep _ (ms_mem ms1) (ms_mem ms2) _ _ _ V1_v). intros kk Hkk. pnd_show Hvloc.
      rewrite K3 by lia. apply K2; [lia | | lia].
      intros Hc. exact (HNBv (pe_v en + 16 + Z.of_nat kk) ltac:(lia) ltac:(lia)).
  - unfold r3_b, r3_Y, r3_v. cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite ?U3_10, ?U3_9, ?U3_19. pnd_show Hvloc.
    assert (~ (pe_v en <= res + Z.of_nat m < pe_v en + 56)) by (apply HNBv; lia).
    repeat split; lia.
  - split; [|split; [exact I | exact I]].
    unfold fa_Y, fa_v, fa_B, fa_nul, fa_fa, PND_TOP. cbn [f_atoms atoms_ok]. unfold afact_ok.
    cbn [af_lo af_hi af_al2]. rewrite U3_9, U3_19, U3_23, U3_10, U3_26. change (2 ^ 5) with 32.
    change (2 ^ 3) with 8. change (2 ^ 0) with 1. rewrite !Z.mod_1_r.
    pnd_show HY32. pnd_show Hv8. pnd_show Hres16. pnd_show Hfa32. unfold SHADOW_OFF. repeat split; lia. }
assert (SHOK3 : sh_ok SEGS PND_Bx SH3 E3 (rdW W' (ms_mem ms2))).
{ unfold sh_ok, SH3. constructor; [|constructor; [|constructor]]; unfold shent_ok, app_apart;
    cbn [she_m she_lo she_hi]; unfold PND_Bx; rewrite !U_SOff, ?U3_23, ?U3_10, ?U3_19, !Z.add_0_r;
    rewrite !zcanon_id by (unfold M64, SHADOW_OFF; lia);
    change (YCbn.rd_of SEGS (rdW W' (ms_mem ms2))) with (aview SEGS (w_H W') (ms_mem ms2)); split.
  - apply (pnd_ra_keep _ mem (ms_mem ms2)); [eapply range_addressable_sub; [exact HraM | lia | lia] |].
    intros z Hz. rewrite K3 by (unfold SHADOW_OFF; lia). apply KB2; [unfold SHADOW_OFF; lia | apply pnd_band; lia].
  - intros a Ha. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SHADOW_OFF in *. lia.
  - apply (pnd_ra_keep _ mem (ms_mem ms2)); [eapply range_addressable_sub; [exact HRAV | lia | lia] |].
    intros z Hz. rewrite K3 by (unfold SHADOW_OFF; lia). apply KB2; [unfold SHADOW_OFF; lia | apply pnd_band; lia].
  - intros a Ha. pnd_show Hvband. unfold kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *. lia. }
pose proof HJc as HJd.
pose (RUN3 := @paj_run_x_inv fx0 rc SK B_prog_listing PL_prog_B PA B PST ARx _ LAWS (YAkMemnorm.memnorm SEGS)
  (srr_inv_laws_memnorm_k SEGS)).
paj_run_tok_x_inv RUN3 HS3 HJd SHOK3 HPM PND_Bspan.
{ intros a0 (r & Hin & Ha0). vm_compute in Hin.
  destruct Hin as [<- | [<- | [<- | []]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha0;
    rewrite ?U3_10, ?U3_9, ?U3_19 in Ha0; [|lia|lia].
  unfold awr_byte. right; right; left. unfold in_tmp_block. exists (res - cf_head), (Z.of_nat m + 1 + cf_head).
  split; [exact HNB|]. split; [exact HNBn|]. rewrite Hrq. lia. }
lazymatch type of HS3 with context [restrict _ ?mm] => rename mm into ms3 end.
pmkst HS3. rename HFr into HFr_3. rename HG into HG_3. clear HF.
(* ---- at the strtod call (B 0x86818): a0 = v->str = res, a1 = s9 = fa + 32 ---- *)
assert (RK4 : forall x, In x [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 18%bv; 19%bv; 20%bv; 21%bv; 22%bv; 23%bv; 24%bv; 26%bv;
  27%bv] -> getr (ms_regs ms3) x = getr regs x).
{ intros x Hx. assert (Hx' : In x PND_KL) by (unfold PND_KL; cbn [In] in Hx |- *; intuition).
  rewrite <- (RK3 x Hx'). cbn [In] in Hx. repeat (destruct Hx as [<- | Hx]; [pnd_rk HS3 Er3|]). destruct Hx. }
prreg HS3 (10%bv : bv 5) T4_10. rewrite E3_32 in T4_10.
prreg HS3 (11%bv : bv 5) T4_11. rewrite U3_26 in T4_11.
prreg HS3 (25%bv : bv 5) T4_25. rewrite U3_26 in T4_25.
prreg HS3 (1%bv : bv 5) T4_1.
assert (K4 : forall a, 0 <= a < 2 ^ 64 -> a <> res + Z.of_nat m ->
  aview SEGS (w_H W') (ms_mem ms3) a = aview SEGS (w_H W') (ms_mem ms2) a).
{ intros a Ha Hn. apply (pnd_aview_of_frame (w_H W') E3 (ss_mem ss3) (ms_mem ms2) (ms_mem ms3) a HFr_3);
    [|exact Ha].
  intros (r & Hin & Hr). vm_compute in Hin. destruct Hin as [<- | [<- | [<- | []]]];
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?U3_10, ?U3_9, ?U3_19 in Hr; lia. }
lazymatch type of HS3 with st_ok _ _ ?ssx _ =>
  let rg0 := eval vm_compute in (nth 0 (ss_mem ssx) r3_b) in
  pose proof (pnd_region_nth_c fx0 _ _ _ 0 rg0 HS3 ltac:(vm_compute; reflexivity)) as RGb
end.
cbn [ms_mem restrict] in RGb.
pose proof (pnd_field _ _ 10%nat (res + Z.of_nat m) _ _ _ _ _ 0 1 (SLit 0) 0 RGb
  ltac:(cbn [ew ewset Nat.eqb]; exact U3_10) ltac:(pnd_inc) eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) as V4.
change (N.to_nat 1) with 1%nat in V4. rewrite Z.add_0_r in V4.
assert (GX : garr8 SEGS (rdW W' mem) (pn_p1 en (c :: y)) (c :: y)).
{ pose proof (pnd_garr8_skipn _ mem _ _ (Z.to_nat (pn_p1 en (c :: y) - pe_text en)) Gt) as G.
  rewrite HSK in G.
  replace (pn_p1 en (c :: y)) with (pe_text en + Z.of_nat (Z.to_nat (pn_p1 en (c :: y) - pe_text en))) by lia.
  exact G. }
assert (GM3 : garr8 SEGS (rdW W' (ms_mem ms3)) res (firstn m (c :: y) ++ [0])).
{ apply (pnd_garr8_build _ mem (ms_mem ms3) (pn_p1 en (c :: y)) (c :: y) res m GX ltac:(lia)).
  - intros j Hj. rewrite (K4 (res + Z.of_nat j)) by lia. rewrite (K3 (res + Z.of_nat j)) by lia.
    rewrite (Hcopy (Z.of_nat j)) by lia. pnd_show Htv. apply K1; lia.
  - exact V4. }
assert (Hsi : si_img_lo strtod_row.strtod_img_B = IMG_LO_B /\ si_globals_top strtod_row.strtod_img_B = IMG_TOP_B /\
  si_got_guard strtod_row.strtod_img_B = strtod_c.STRTOD_GOT_GUARD) by (vm_compute; repeat split).
destruct Hsi as (Esl & Esg & Esgot).
assert (Hfa_hi : IMG_TOP_B <= fa) by (rewrite Efa; exact (FS_HI _ _ _ _ _ _ 0 pos HAR HinF)).
(* strtod_site_x's GOT-guard clause at the call memory: the guard word is one of B's const cells (IMG_GOTC), which
   AR_laws_x field 16 alx_const_cells keeps at the call's ARx state; its eight image bytes hold the same value
   (IMG_GOTV, strtod_row.strtod_got_B at PI_prog_B) *)
assert (HGOT : forall a, si_got_guard strtod_row.strtod_img_B <= a < si_got_guard strtod_row.strtod_img_B + 8 ->
  aview SEGS (w_H W') (ms_mem ms3) a = option_map (fun b : byte => bv_unsigned b) (seg_rom SEGS (Z_to_bv 64 a))).
{ intros a Ha. rewrite Esgot in Ha.
  pose proof HJd as (HARd & _).
  pose proof (alx_const_cells SEGS B ARx LAWS _ _ _ _ _ _ HARd) as HC.
  rewrite Forall_forall in HC. specialize (HC _ (IMG_GOTC lyc)).
  unfold YG0f.cell_holds in HC. cbn [c_at c_val c_w z8 c8 aeval] in HC.
  replace a with (strtod_c.STRTOD_GOT_GUARD + Z.of_nat (Z.to_nat (a - strtod_c.STRTOD_GOT_GUARD))) by lia.
  assert (Hk : (Z.to_nat (a - strtod_c.STRTOD_GOT_GUARD) < 8)%nat) by lia.
  set (kk := Z.to_nat (a - strtod_c.STRTOD_GOT_GUARD)) in *. clearbody kk. clear Ha.
  rewrite (HC kk Hk), (srx_got_b_sound SEGS _ _ kk IMG_GOTV Hk). cbn [option_map]. f_equal.
  do 8 (destruct kk as [|kk]; [vm_compute; reflexivity|]). lia. }
(* ---- the strtod call (YStrtodRowX.aj_strtod_at_x over STR) ---- *)
eapply SRr_bind.
{ eapply (aj_strtod_at_x (fx := fx0) SEGS B ARx strtod_row.strtod_img_B (SK := SK) PST LAWS pa_segs_low pnd_errno_img
    (SIGMA AS_strtod) STK_RT_STRTOD strtod_c.strtod_model pnd_txt_ok STR ltac:(unfold STK_RT_STRTOD, ESTACK; lia)
    W' (ms_regs ms3) (ms_mem ms3) _ _ _ _ _ _ _ _ _ [(0, pos)] lyc Sc Hpc _ k res (fa + 32) (firstn m (c :: y))
    (Y - (pe_sp en + pe_e en)) _ HJd).
  - exact T4_10.
  - exact T4_11.
  - unfold spZ. rewrite (RK4 2%bv ltac:(cbn; intuition)), R2, unsigned_lit_small by lia. lia.
  - pnd_show HY32. pnd_show G16. pnd_show Ge16. lia.
  - lia.
  - unfold STK_RT_STRTOD, ESTACK. lia.
  - rewrite (RK4 3%bv ltac:(cbn; intuition)), R3. exact Hgp0.
  - rewrite (RK4 4%bv ltac:(cbn; intuition)), R4. exact Htp0.
  - exact T4_1.
  - apply (ret_ok_codeptr_v (PI := PA)); [lia | reflexivity].
  - exact GM3.
  - split; [|rewrite Hlt; lia]. rewrite Forall_forall in HNUM |- *. intros z Hz. rewrite pnd_numch_eq.
    exact (HNUM z Hz).
  - lia.
  - rewrite Hlt. lia.
  - left. rewrite Hlt. unfold STK_RT_STRTOD, ESTACK. lia.
  - intros a Ha. left. unfold awr_byte. right; right; right. unfold in_frames. exists 0, pos.
    split; [left; reflexivity|]. left. unfold in_zr. cbn [fst snd]. rewrite <- Efa, Efb. lia.
  - left. unfold STK_RT_STRTOD, ESTACK. lia.
  - rewrite Hlt. destruct (Z_le_gt_dec (fa + 32 + 8) res) as [Hl|Hl]; [left; lia|].
    destruct (Z_le_gt_dec (res + Z.of_nat m + 1) (fa + 32)) as [Hr|Hr]; [right; lia|].
    exfalso. apply (HNBfa (Z.max res (fa + 32))); lia.
  - exact Hfrm0.
  - split; [|split; [|split; [|split]]].
    + rewrite Esl, Esg, Hlt. destruct (Z_le_gt_dec (res + Z.of_nat m + 1) IMG_LO_B) as [Hl|Hl]; [left; lia|].
      right. destruct (Z_le_gt_dec IMG_TOP_B res) as [Hr|Hr]; [exact Hr|]. exfalso.
      apply (HNBimg (Z.max res IMG_LO_B)); [lia|]. apply IMG_COVER. unfold IMG_LO_B, IMG_TOP_B in *. lia.
    + rewrite Esg. lia.
    + lia.
    + exact HGOT.
    + (* the memory normal form at the call memory, carried from M (YAkMemnorm.memnorm, by conversion) *)
      exact HPM. }
cbv beta. intros W5 c5 _ (-> & fx' & regs5 & mem5 & md5 & bits & cn & -> & HFZ & HFK & HFA & HSM & Hcn & HJ5 & HP5 & VE &
  Hfr5 & Hpres5 & HMN5).
(* ======== at R (B 0x8681c) ======== *)
assert (RK5 : forall x, In x [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 18%bv; 19%bv; 20%bv; 21%bv; 22%bv; 23%bv; 24%bv; 26%bv;
  27%bv] -> getr regs5 x = getr regs x).
{ intros x Hx. assert (Hx' : In x PND_KL) by (unfold PND_KL; cbn [In] in Hx |- *; intuition).
  rewrite (pnd_pres_l _ _ HP5 x Hx'). exact (RK4 x Hx). }
assert (R5_25 : getr regs5 25 = w64 (fa + 32))
  by (rewrite (pnd_pres_l _ _ HP5 25%bv ltac:(unfold PND_KL; cbn; intuition)); exact T4_25).
assert (K5 : forall a, 0 <= a < 2 ^ 64 -> ~ (fa + 32 <= a < fa + 40) -> ~ (Y - 16384 <= a < Y) ->
  ~ (as_errno B <= a < as_errno B + 4) -> aview SEGS (w_H W') mem5 a = aview SEGS (w_H W') (ms_mem ms3) a).
{ intros a Ha H1 H2 H3. apply Hfr5;
    [exact Ha | intros Hc; apply H1; clear -Hc; lia | clear -H2; unfold STK_RT_STRTOD, ESTACK; lia | exact H3]. }
(* ---- the arm's places as linear facts (the disjunctive ones hidden from lia in this context) ---- *)
pose proof (proj1 C1) as LAC.
assert (LACH : YM05.alloc_ceiling <= 2 ^ 47) by (clear -C1; lia).
assert (LY : YM05.alloc_ceiling + 16384 <= Y /\ Y + 160 <= pe_sp en).
{ pose proof HYc as HYc'. unfold pnd_hide in HYc'. clear -HYc' Gceil Glo GSTK. lia. }
assert (LSP : pe_sp en + pe_e en <= 2 ^ 47) by (clear -Gtop Gtophi G47; lia).
assert (LRA : res + Z.of_nat m + 1 <= YM05.alloc_ceiling) by (clear -Hnbc; lia).
assert (LFB : fa + 64 <= kLowShadowBeg \/ kHighMemBeg <= fa)
  by (unfold in_app in Hfapp; destruct Hfapp as (_ & [Hl | [Hh _]]); [left; clear -Hl; lia | right; clear -Hh; lia]).
assert (LRB : res + Z.of_nat m + 1 <= kLowShadowBeg \/ kHighMemBeg <= res - cf_head)
  by (unfold in_app in Hnbapp; destruct Hnbapp as (_ & [Hl | [Hh _]]); [left; clear -Hl; lia | right; clear -Hh; lia]).
assert (LFV : fa + 64 <= pe_v en \/ pe_v en + 56 <= fa).
{ destruct (Z_le_gt_dec (fa + 64) (pe_v en)) as [Hl | Hl]; [left; exact Hl|].
  destruct (Z_le_gt_dec (pe_v en + 56) fa) as [Hr | Hr]; [right; exact Hr|].
  exfalso. apply (Hown (Z.max (pe_v en) fa)); clear -Hl Hr; lia. }
assert (LRV : res + Z.of_nat m + 1 <= pe_v en \/ pe_v en + 56 <= res - cf_head).
{ destruct (Z_le_gt_dec (res + Z.of_nat m + 1) (pe_v en)) as [Hl | Hl]; [left; exact Hl|].
  destruct (Z_le_gt_dec (pe_v en + 56) (res - cf_head)) as [Hr | Hr]; [right; exact Hr|].
  exfalso. apply (HNBv (Z.max (pe_v en) (res - cf_head))); clear -Hl Hr H8; lia. }
assert (LRF : res + Z.of_nat m + 1 <= fa \/ fa + 64 <= res - cf_head).
{ destruct (Z_le_gt_dec (res + Z.of_nat m + 1) fa) as [Hl | Hl]; [left; exact Hl|].
  destruct (Z_le_gt_dec (fa + 64) (res - cf_head)) as [Hr | Hr]; [right; exact Hr|].
  exfalso. apply (HNBfa (Z.max fa (res - cf_head))); clear -Hl Hr H8; lia. }
pnd_hide_in LFB. pnd_hide_in LRB. pnd_hide_in LFV. pnd_hide_in LRV. pnd_hide_in LRF.
pose proof pnd_errno_rng as LE.
assert (KALL : forall a, 0 <= a < 2 ^ 64 -> ~ pnd_WR Y (pe_v en) res (Z.of_nat m) fa (as_errno B) a ->
  aview SEGS (w_H W') mem5 a = aview SEGS (w_H W') mem a).
{ intros a Ha HW. unfold pnd_WR in HW.
  assert (H1 : ~ (Y - 16384 <= a < Y + 24)) by tauto. assert (H2 : ~ (pe_v en + 16 <= a < pe_v en + 24)) by tauto.
  assert (H3 : ~ (res <= a < res + Z.of_nat m + 1)) by tauto. assert (H4 : ~ (fa + 32 <= a < fa + 40)) by tauto.
  assert (H5 : ~ (as_errno B <= a < as_errno B + 4)) by tauto. clear HW.
  rewrite K5; [| exact Ha | exact H4 | intros Hc; apply H1; clear -Hc; lia | exact H5].
  rewrite K4; [| exact Ha | intros Hc; apply H3; clear -Hc; lia].
  rewrite K3 by exact Ha.
  rewrite K2; [| exact Ha | intros Hc; apply H3; clear -Hc; lia | intros Hc; apply H1; clear -Hc; lia].
  apply K1; [exact Ha | intros Hc; apply H1; clear -Hc; lia | exact H2]. }
assert (PG : forall a, apresent (w_H W') mem a -> apresent (w_H W') mem5 a).
{ intros a Ha. apply Hpres5. apply (apresent_grows _ _ _ _ HG_3). apply (apresent_grows _ _ _ _ HG_2).
  apply Hpres2. exact (apresent_grows _ _ _ _ HG_1 Ha). }
(* every byte the arm wrote lies off the shadow band *)
assert (Hband5 : forall a, pnd_WR Y (pe_v en) res (Z.of_nat m) fa (as_errno B) a -> pnd_offband a)
  by (intros a; exact (pnd_WR_band YM05.alloc_ceiling Y (pe_v en) res (Z.of_nat m) cf_head fa (as_errno B) a LAC
    (proj1 LY) Hvband Hv47 LFB Hfac H8 LRB LRA LACH (proj1 LE) (proj2 LE))).
assert (KB5 : forall s, 0 <= s < 2 ^ 64 -> ~ pnd_offband s -> aview SEGS (w_H W') mem5 s = aview SEGS (w_H W') mem s).
{ intros s Hs Hb. apply KALL; [exact Hs | intros Hc; exact (Hb (Hband5 s Hc))]. }
(* the text lies below the stack: in a block of the entry, or in the image *)
assert (HTY : forall a, pe_text en <= a < pe_text en + pe_len en -> a < Y - 16384).
{ intros a Ha. destruct (pnd_tloc en HPRE) as [(b & n & Hin & H1 & H2) | HI].
  - destruct (alx_blocks SEGS B ARx LAWS _ _ _ _ _ _ b n HAR0 Hin) as (_ & H4096 & Hbc & _).
    assert (Hn : n <= req_size n) by (unfold req_size; destruct (Z.eqb_spec n 0); lia).
    clear -Ha H1 H2 Hbc Hn LY. lia.
  - destruct (HI a Ha) as [Hi _]. pose proof (pa_segs_low a Hi) as Hlo.
    clear -Hlo LAC LY. unfold kLowMemEnd in *. lia. }
apply KR.
exists fx', regs5, mem5, Y, fa, fl, pos, lyc, Sc, Hpc, k, c, y, m, res, bits, cn. cbv zeta.
split; [reflexivity|]. split; [exact HFZ|]. split; [exact HFK|].
split.
{ unfold pn_base, pv_keep_regs. rewrite !RK5 by (cbn [In]; intuition). exact HBASE. }
split.
{ (* the body *)
  split.
  { apply (pnd_frame_keep _ _ _ _ _ _ _ mem _ HFRM).
    - intros a Ha.
      destruct (pnd_frame_places (pe_sp en) (pe_e en) Y (pe_v en) fa res (Z.of_nat m) cf_head YM05.alloc_ceiling
        (as_errno B) a LAC (proj1 LY) (proj2 LY) ltac:(clear -LSP Ge0; lia) Hvloc Hvband Hfa_hi Hfac LFB LFV H8
        (Nat2Z.is_nonneg m) LRA LRB LRF (proj1 LE) (proj2 LE) Ha) as [Hb HW].
      exact (KALL a Hb HW).
    - exact PG. }
  split; [exact HinF|]. split; [exact Efa|]. split; [exact Efl|]. split; [exact HJ5|].
  intros a Ha Hnf. rewrite <- (HWIN a Ha Hnf).
  destruct (pnd_win_places (pe_sp en) (pe_e en) Y fa res (Z.of_nat m) YM05.alloc_ceiling (as_errno B) a (proj1 LY)
    (proj2 LY) LSP Hfa_hi Hfac LRA (proj2 LE) Ha) as (Hb & W1 & W3 & W4 & W5).
  apply KALL; [exact Hb|]. unfold pnd_WR. intros [Hc | [Hc | [Hc | [Hc | Hc]]]];
    [exact (W1 Hc) | | exact (W3 Hc) | exact (W4 Hc) | exact (W5 Hc)].
  apply Hnf. exists (pe_v en, pe_v en + 56). split; [right; right; left; reflexivity | cbn; clear -Hc; lia]. }
split.
{ (* pn_ok *)
  split; [exact Hcf|]. split; [exact Hres4|]. split; [exact Hres16|]. split; [exact HresL|].
  split; [clear -LRA LACH; lia|]. split; [exact HNBn|].
  split; [intros a Ha; apply HNBv; clear -Ha H8; lia|].
  split; [exact EHpc|].
  split; [rewrite Eab, Hab0; reflexivity|].
  split.
  { apply (pnd_ra_keep _ mem mem5 _ _ HraM). intros z Hz.
    apply KB5; [clear -Hz LRA LACH Hnb4096 H8; unfold SHADOW_OFF; lia |].
    apply pnd_band. clear -Hz LRA LACH Hnb4096 H8. lia. }
  split.
  { apply (pnd_hull_keep _ mem mem5 _ _ (HhullM ltac:(clear; lia))). intros s Hs.
    apply KB5; [clear -Hs LRA LACH Hnb4096 H8; unfold shadow_addr, SHADOW_OFF in *; lia |].
    exact (pnd_band_hull res (Z.of_nat m + 1) s ltac:(clear -Hnb4096 H8; lia) ltac:(clear; lia)
      ltac:(clear -LRA LACH; lia) Hs). }
  apply (pnd_ledger_keep _ _ _ _ mem mem5 _ _ _ _ _ _ _ HLEDM).
  - intros a Ha. pose proof (pnd_pst_rng a Ha) as Hr. pose proof (pnd_pst_errno a Ha) as He.
    apply KALL; [clear -Hr; unfold IMG_LO_B, IMG_TOP_B in *; lia |].
    unfold pnd_WR. intros [Hc | [Hc | [Hc | [Hc | Hc]]]].
    + clear -Hc Hr LY Hfa_hi Hfac. unfold IMG_LO_B, IMG_TOP_B in *. lia.
    + apply (pnd_vnotimg en a HPRE ltac:(clear -Hc; lia)). apply IMG_COVER. exact Hr.
    + apply (HNBimg a ltac:(clear -Hc H8; lia)). apply IMG_COVER. exact Hr.
    + apply (frm_img_x SEGS B ARx LAWS _ _ _ _ _ _ 0 pos a HAR HinF ltac:(rewrite <- Efa, Efb; clear -Hc; lia)).
      apply IMG_COVER. exact Hr.
    + exact (He Hc).
  - intros a k' i Hin Hi.
    pose proof HLEDM as (_ & _ & HFL & _). rewrite Forall_forall in HFL.
    destruct (HFL (a, k') Hin) as (Hk' & Hab & _ & _ & _). cbn [fst snd] in Hk', Hab.
    destruct (alx_blocks SEGS B ARx LAWS _ _ _ _ _ _ _ _ HAR Hab) as (_ & H4096' & Hbc' & _).
    assert (Hrq' : k' + cf_head <= req_size (k' + cf_head))
      by (unfold req_size; destruct (Z.eqb_spec (k' + cf_head) 0); lia).
    assert (Hnot_img : ~ in_img SEGS (a - cf_head + i))
      by (apply (blk_img_x SEGS B ARx LAWS _ _ _ _ _ _ _ _ _ HAR Hab); clear -Hi H8 Hk' Hrq'; lia).
    assert (HX : 4096 <= a - cf_head + i /\ a - cf_head + i + 1 <= YM05.alloc_ceiling)
      by (clear -Hbc' H4096' Hrq' Hi H8 Hk'; lia).
    assert (HXr : ~ (res <= a - cf_head + i < res + Z.of_nat m + 1) /\ ~ (fa + 32 <= a - cf_head + i < fa + 40) /\
      ~ (pe_v en + 16 <= a - cf_head + i < pe_v en + 24)).
    { destruct Hin as [Ea | Hin].
      - injection Ea as Ea1 Ea2. subst a k'.
        assert (Hrng : res - cf_head <= res - cf_head + i < res + Z.of_nat m + 1)
          by (clear -Hi H8; lia).
        split; [clear -Hi H8; lia|]. split.
        + intros Hf. apply (HNBfa (res - cf_head + i) Hrng). clear -Hf; lia.
        + intros Hv. apply (HNBv (res - cf_head + i) Hrng). clear -Hv; lia.
      - assert (Hne : (a - cf_head, k' + cf_head) <> (res - cf_head, Z.of_nat m + 1 + cf_head)).
        { intros E. injection E as Ee1 _. apply HresL. apply in_map_iff. exists (a, k').
          split; [cbn; clear -Ee1; lia | exact Hin]. }
        pose proof (sep_blocks_x SEGS B ARx LAWS _ _ _ _ _ _ _ _ _ _ HAR Hab HNB Hne) as Hd.
        unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite Hrq in Hd.
        pose proof (sep_block_frame_x SEGS B ARx LAWS _ _ _ _ _ _ _ _ 0 pos HAR Hab HinF) as Hd2.
        unfold zdisjoint in Hd2. cbn [fst snd] in Hd2. rewrite <- Efa, Efb in Hd2.
        split; [clear -Hd Hi H8 Hrq' Hk'; lia|]. split; [clear -Hd2 Hi H8 Hrq' Hk'; lia|].
        intros Hv. apply (pnd_head_v en lyc Sc Hpc W' mem mdc a k' i HPRE HAR Hbl Hfl EFA Hab Hk' (or_introl Hin) Hi).
        clear -Hv; lia. }
    destruct HXr as (HX1 & HX2 & HX3).
    apply KALL; [clear -HX LACH; lia |]. unfold pnd_WR. intros [Hc | [Hc | [Hc | [Hc | Hc]]]].
    + clear -Hc HX LY. lia.
    + exact (HX3 Hc).
    + exact (HX1 Hc).
    + exact (HX2 Hc).
    + apply Hnot_img. apply IMG_COVER. clear -Hc LE. unfold IMG_LO_B, IMG_TOP_B in *. lia. }
split; [exact Hfrs'|]. split; [exact HROOM|].
split.
{ (* the reader's cursor, text and node *)
  apply (pnd_reader_keep en _ W' mem mem5 (pnd_WR Y (pe_v en) res (Z.of_nat m) fa (as_errno B)) HPRE HRD).
  - exact KALL.
  - exact Hband5.
  - exact (pnd_q_places (pe_sp en) Y (pe_v en) (pe_q en) fa res (Z.of_nat m) YM05.alloc_ceiling (as_errno B)
      (proj1 LY) (proj2 LY) Hqlo Hqv Hfa_hi Hfac LRA (proj2 LE)).
  - intros a Ha Ht. destruct (HTL a Ht) as (T1' & T2' & T3'). pose proof (HTY a Ht) as Hty.
    (* rd_pre's text / node apartness, guarded `0 < len -> ..` at the batch kit's tip: a is a text byte, so len > 0 *)
    assert (Htv' : pe_text en + pe_len en <= pe_v en \/ pe_v en + 56 <= pe_text en).
    { pose proof Htv as Htv0. unfold pnd_hide in Htv0. apply Htv0. clear -Ht. lia. }
    unfold pnd_WR in Ha. destruct Ha as [Ha | [Ha | [Ha | [Ha | Ha]]]].
    + clear -Ha Hty. lia.
    + clear -Ha Ht Htv'. lia.
    + apply T1'. clear -Ha H8. lia.
    + apply T2'. clear -Ha. lia.
    + exact (T3' Ha).
  - intros a Ha Hv. unfold pnd_WR in Ha. destruct Ha as [Ha | [Ha | [Ha | [Ha | Ha]]]].
    + exfalso. pose proof Hvloc as Hvl. unfold pnd_hide in Hvl. clear -Ha Hv Hvl LY. lia.
    + exact Ha.
    + exfalso. exact (HNBv a ltac:(clear -Ha H8; lia) Hv).
    + exfalso. exact (Hown a Hv ltac:(clear -Ha; lia)).
    + exfalso. exact (pnd_vnotimg en a HPRE Hv (pnd_errno_img a Ha)).
  - intros a Ha. eapply writable_at_grows; [exact (pnd_grows_of_pres _ _ _ PG) | exact (Hrw a Ha)]. }
split.
{ apply (pnd_vm_keep _ (ms_mem ms1) mem5 _ _ _ V1_v). intros kk Hkk.
  destruct (pnd_v16_places (pe_sp en) (pe_e en) Y (pe_v en) fa res (Z.of_nat m) cf_head YM05.alloc_ceiling
    (pe_v en + 16 + Z.of_nat kk) (proj1 LY) (proj2 LY) Hvloc Hv4096 Hv47 LFV H8 LRV ltac:(clear -Hkk; lia))
    as (Hb & N1 & N2 & N3).
  assert (Hvi : ~ in_img SEGS (pe_v en + 16 + Z.of_nat kk)) by (apply (pnd_vnotimg en _ HPRE); clear -Hkk; lia).
  rewrite K5; [| exact Hb | intros Hc; apply N3; clear -Hc; lia | intros Hc; apply N1; clear -Hc; lia |
    intros He; exact (Hvi (pnd_errno_img _ He))].
  rewrite K4; [| exact Hb | intros Hc; apply N2; clear -Hc H8; lia].
  rewrite K3 by exact Hb.
  apply K2; [exact Hb | intros Hc; apply N2; clear -Hc H8; lia | intros Hc; apply N1; clear -Hc; lia]. }
split.
{ apply (pnd_garr8_keep _ (ms_mem ms3) mem5 _ _ GM3). intros j Hj. rewrite length_app, Hlt in Hj. cbn [length] in Hj.
  destruct (pnd_res_places Y fa res (Z.of_nat m) cf_head YM05.alloc_ceiling (res + Z.of_nat j) (proj1 LY) LACH H8
    Hnb4096 LRA LRF ltac:(clear -Hj; lia)) as (Hb & N1 & N2).
  apply K5; [exact Hb | exact N1 | intros Hc; apply N2; clear -Hc; lia |].
  intros He. apply (HNBimg (res + Z.of_nat j) ltac:(clear -Hj H8; lia)). exact (pnd_errno_img _ He). }
split; [exact HSM|].
split; [first [exact Hcn | rewrite Hlt in Hcn; exact Hcn | lia]|].
split; [exact VE|].
split; [exact HFA|].
split; [exact R5_25|].
split; [rewrite RK5 by (cbn [In]; intuition); exact R22|].
split; [rewrite RK5 by (cbn [In]; intuition); exact R21|].
split; [exact Hlead|]. split; [exact Hm|]. split; [exact Hspan|]. split; [exact Hstop|].
(* R's run position: M's (the memcpy and strtod calls keep the allocator state Sc) *)
split; [exact HQP|].
(* R's last conjunct: the memory normal form at strtod's return memory, the strtod row's post (aj_strtod_row's last
   conjunct, YStrtodRowX.v blob 10e84e44e24e) *)
exact HMN5.
Qed.

End c.
