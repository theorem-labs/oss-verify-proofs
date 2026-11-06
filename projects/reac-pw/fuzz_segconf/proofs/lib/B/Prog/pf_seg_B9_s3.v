(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the program walk of check_round_trip on the ASan build of plugin-hostd/fuzz_command
   (0x87fd8, 286 instructions), proving tcheck_round_trip_spec (check_round_trip_c.v), in the shape of cgif_file_fuzzer's
   walks (lib/A/AChc.v, ACh1..ACh8.v, AChf.v): one statement per point between two calls (ST_B .. ST_EPI below), each
   segment proved by a run of the symbolic executor over the position-abstract listing (CmdPaLib.v) from a fresh seed,
   the inline checks removed by the shadow tokens (PaShadow.v), and the call at its end composed into the journal:
   the class-5 side-stack frame by aj_stack_malloc_atS (PaCall.v) and, from check_round_trip_k.v, aj_set_shadow_atS
   (__asan_set_shadow_f8/_00) and aj_stack_free_cls_atS (__asan_stack_free_5); the strdup wrapper by crts4_strdup_sub,
   the free wrapper by afree04_sub (PaCall.v), the strcmp wrapper by aj_art_at (PaArt.v); the program callees
   rec_calls_copy, joined, send_message and rec_calls_free by cl_callS_wide and rec_calls_equal by cl_callS_na
   (PaNoChain.v), each with its contract as a Section hypothesis. The skip path (no word, or the daemon did not act)
   joins the epilogue at 0x88314; the abort edges (0x8838c) are excluded by rt_okA and the callees' posts.
   Re-fit to statement passes 4, 4b and 5: the callee and runtime hypotheses hold at every
   FP state (forall fx0) and the segments use them at the ambient fx. send_message reaches the printf wrappers, so the
   points before its return (ST_B .. ST_F) prove the FP-existential post crt_postF (apost_baseF); crt_s6 calls
   send_message by PaFx.v's cl_callS_wideF with the rounding-mode premise HFRM and goes on at the FP state fx1 it
   returns (srr_after_callF_base). The points after it (ST_G .. ST_EPI) prove apost_base at the ambient FP state, so
   once the sections close they hold at fx1 (crt_G, used so by tcheck_round_trip_spec_holds). The skip path lifts
   ST_EPI's post by apost_baseF_of_base (crts3_skip). Pass 5 removed astack_pres: s0 is the frame pointer sp0 at every
   call, so each call's frame chain is the prologue's frame record (ra at sp0 - 8, the entry s0 at sp0 - 16, from
   crt_frame) on afn_pre's chain (achain_push, crt_chain), and chain_pre for the runtime allocation entries is
   achain_chain_pre of it. joined's new premises at its call: len's 8 bytes present (the journal's window), and
   (pass 5b) the stack from len - 16 present, from the statement's astack_pres kept by astack_pres_journal. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/check_round_trip.v, with its module paths and module names changed; 683 of its 754 lines of code are new or changed and 4982 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/pf_seg_B8a.v, with its module names changed; 335 of its 393 lines of code are new or changed and 696 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, image B (fuzz_segconf.asan-ubsan, pin c3796c0b38f3, twin 80e82127e8ca): stretch SB9_3 of
   segment B9 of reac_segconf_parse_file's walk (lib/B/Prog/pf_seg_B9_d.v): J2 0x88428 -> J3 0x88438, the UBSan
   trap T11 and the call trim(eq + 1). A B9 sub-lane of the image-B G3 walk owner, 2026-10-30.
   proves no function (kind: segment lemma of reac_segconf_parse_file's walk: stretch SB9_3 of segment B9).
   ADAPTED from a working branch's lib/A/Prog/pf_a9_s2.v (image A's stretch SA9_B, its trim half: the
   transport lemmas b2_vis / b2_keep_inbuf / b2_trim_str and the cl_callS_wide site), re-derived on image B's code
   and over image B's kit (lib/B/Prog/pf_seg_B9_k.v, pf_seg_B9_c.v, pf_seg_B9_cs.v), with the shape of the proved
   image-B stretch lib/B/Prog/pf_seg_B9_s1.v (seed, run, call, next cut).

   THE CODE (reac_segconf_parse_file.fuzz_segconf.asan-ubsan.s; reac_segconf.c:221-222):
     0x88428 beq  s8,s10,0x891c8   UBSan trap T11 (eq + 1 wraps), NOT TAKEN: s8 = eq = lp + ei and s10 = -1, and
                                   eq lies in buf (INV_J2's rest string at lp + ei + 1 is inside buf, which is
                                   inside the class-5 frame below alloc_ceiling < 2 ^ 47), so eq <> 2 ^ 64 - 1.
     0x8842c mv   s7,a0            s7 = kp (trim #1's answer, the key)
     0x88430 addi a0,s8,1          a0 = eq + 1
     0x88434 jal  trim             trim(eq + 1): the value; return 0x88438 = B9_J3
   4 instructions walked (0x88428 .. 0x88434), one UBSan trap discharged (T11), no inline check.

   THE PROOF. A seed at J2 (every register its own atom, no region, no fact); the branch is not decided by the
   seed, so it is split by psrr_branch_pi: the taken side is refuted (b9s3_t11, over s8 = lp + ei < 2 ^ 47 and
   s10 = 2 ^ 64 - 1), the other side runs on to the call (paj_run_shc). trim is stepped by PaNoChain.v
   cl_callS_wide (its footprint is the NUL at trim_end_addr, a byte of parse_file's OWN class-5 frame: awr_byte's
   own-frames arm), with the premises of its contract from pf_seg_B9_cs.v b9_trim_site_ok and the frame chain from
   pf_seg_B9_k.v b9_chain. At the return, INV_J3: pf_base by b9_move0 (trim keeps every byte off its window below
   s1 and off the NUL, both inside b9_Wrx), pf_st by b9_keep_st, the key kept (its NUL is at or below lp + ei,
   strictly below the NUL trim writes, INV_J2's kp + |key| <= lp + ei), and the value at vp0 = eq + 1 +
   trim_lead (skipn (S ei) line) from trim's post bytes and pfA_facts.v L_trim_holds.
   Section hypotheses: TRIM (trim's contract at BASE + AF_trim), SIGP (trim's call target). *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI00 YI04 YI09 YI08.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI16.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pf_pieces_spec pfA_facts.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaRun PaShadow PaJournal SegSyms SegList
SegAddr SegPa SegObj SegGlob.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPaLib PaDenot PaLibG PaLibF PaLibH PaCall
PaCallRun PaArt PaNoChain.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import trim_c refuse_c reac_segconf_parse_file_c
  SegInstB.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require reac_segconf_parse.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import pf_pieces pf_seg_B9_d pf_seg_B9_f
  pf_seg_B9_k pf_seg_B9_c pf_seg_B9_cs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* ---------- small tools (pf_seg_B9_s1.v's, and pf_a9_s2.v's b2_* renamed) ---------- *)
Lemma b9s3_bvr : forall rr (r : bv 5) k v, bv_unsigned r = k -> getr rr (Z_to_bv 5 k) = v -> getr rr r = v.
Proof. intros rr r k v Hr H. subst k. rewrite Z_to_bv_bv_unsigned in H. exact H. Qed.
Lemma b9s3_bvr' : forall rr (r : bv 5) k v, bv_unsigned r = k -> getr rr r = v -> getr rr (Z_to_bv 5 k) = v.
Proof. intros rr r k v Hr H. subst k. rewrite Z_to_bv_bv_unsigned. exact H. Qed.
Lemma b9s3_m16 : forall a b, a mod 32 = 0 -> b mod 16 = 0 -> (a - b) mod 16 = 0.
Proof.
intros a b Ha Hb. pose proof (Z.div_mod a 32 ltac:(lia)) as Da. pose proof (Z.div_mod b 16 ltac:(lia)) as Db.
rewrite Ha in Da. rewrite Hb in Db.
replace (a - b) with ((2 * (a / 32) - b / 16) * 16) by lia. apply Z_mod_mult.
Qed.
Lemma b9s3_w64_off : forall x c, Z_to_bv 64 (bv_unsigned (Z_to_bv 64 x) + c) = Z_to_bv 64 (x + c).
Proof.
intros x c. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. cbn [Z.of_N].
rewrite Zplus_mod_idemp_l. reflexivity.
Qed.
(* a reader at a reads the byte at a mod 2 ^ 64 (mbyte goes through Z_to_bv 64) *)
Lemma b9s3_aview_mod : forall segs H m a, aview segs H m a = aview segs H m (a mod 2 ^ 64).
Proof.
intros segs H m a. unfold aview, mbyte.
replace (Z_to_bv 64 (a mod 2 ^ 64)) with (Z_to_bv 64 a); [reflexivity|].
apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. cbn [Z.of_N]. rewrite Zmod_mod. reflexivity.
Qed.
(* the bytes after a NUL up to its word's end are within the next word's end of a later NUL (pf_a9_s2.v b2_tail_mono) *)
Lemma b9s3_tail_mono : forall e e' x, e <= e' -> e < x < e - e mod 8 + 8 -> x <= e' \/ e' < x < e' - e' mod 8 + 8.
Proof.
intros e e' x H Hx.
pose proof (Z.div_mod e 8 ltac:(lia)). pose proof (Z.mod_pos_bound e 8 ltac:(lia)).
pose proof (Z.div_mod e' 8 ltac:(lia)). pose proof (Z.mod_pos_bound e' 8 ltac:(lia)).
assert (e / 8 <= e' / 8) by (apply Z.div_le_mono; lia).
lia.
Qed.
(* the UBSan trap T11 at 0x88428 (`beq s8,s10`): s8 = eq is a pointer into buf, s10 = 2 ^ 64 - 1 *)
Lemma b9s3_t11 : forall E a b e, U E a = e -> U E b = 2 ^ 64 - 1 -> 0 <= e < 2 ^ 64 - 1 ->
  branch_taken BC_EQ (sv_denot E a) (sv_denot E b) = true -> False.
Proof.
intros E a b e Ha Hb He Hc. rewrite branch_eq_U, Ha, Hb in Hc. apply Z.eqb_eq in Hc. lia.
Qed.
Lemma b9s3_J3 : B9_J3 = 0x3678.
Proof. vm_compute. reflexivity. Qed.
Ltac b9s3_in := cbn [In app]; repeat first [left; reflexivity | right].
(* the denotation of a register term over atoms of known value (pf_seg_B5_r2.v b5r2_den) *)
Ltac b9s3_den :=
  cbn [sv_denot];
  repeat match goal with H : ew ?E ?n = Z_to_bv 64 _ |- context [ew ?E ?n] => rewrite H end;
  rewrite ?b9s3_w64_off, ?alu64_add_lit, ?Z.add_0_r, ?Z_to_bv_bv_unsigned;
  unfold w64; first [reflexivity | f_equal; lia].

(* the seed at J2: every register its own atom, no region, no fact *)
Definition b9s3_ss : sstate := mkSS B9_J2 sr_atoms [] None (mkFacts [] [] []).
(* the registers the run J2 -> the trim call does not write (it writes ra, s7 and a0) *)
Definition b9s3_kept : list Z := [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 24; 25; 26; 27].

Section d. Context {rc : YM05.RunCeil} {SK : YI16.sink_head} {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation SIG s := (@pa_sigma _ seg_listing PI s).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

(* a C string kept by a step that writes only bytes of E, E apart from it (pf_a9_s2.v b2_keep_inbuf) *)
Lemma b9s3_keep_str : forall (Wc : world SEGS) memc (W2 : world SEGS) mem2 (E : Z -> Prop) q l,
  (forall a, 0 <= a < 2 ^ 64 -> ~ E a -> rdW W2 mem2 a = rdW Wc memc a) ->
  (forall a, rdW Wc memc a <> None -> rdW W2 mem2 a <> None) ->
  (forall a, E a -> ~ (q <= a <= q + Z.of_nat (length l))) ->
  0 <= q -> q + Z.of_nat (length l) < 2 ^ 64 ->
  sa_str (rdW Wc memc) q l -> sa_str (rdW W2 mem2) q l.
Proof.
intros Wc memc W2 mem2 E q l HK HV HE Hq Hql ((Hz & Hn) & Ht).
split; [split; [|exact Hn]|].
- intros i Hi. pose proof Hi as Hl. rewrite length_app in Hl. cbn [length] in Hl.
  rewrite HK; [exact (Hz i Hi) | lia |].
  intros He. apply (HE _ He). lia.
- intros y Hy. apply HV. exact (Ht y Hy).
Qed.

(* trim's answer at p: the C string at p + trim_lead s is r_trim s (trim_c.v's post bytes and pfA_facts.v
   L_trim_holds; pf_a9_s2.v b2_trim_str) *)
Lemma b9s3_trim_str : forall (Wc : world SEGS) memc (W2 : world SEGS) mem2 p s,
  sa_str (rdW Wc memc) p s ->
  sa_bytes (rdW W2 mem2) p
    (seg_spec.zb (firstn (seg_spec.trim_lead s + length (r_trim s)) s) ++ [seg_spec.ZERO]) ->
  (forall a, rdW Wc memc a <> None -> rdW W2 mem2 a <> None) ->
  sa_str (rdW W2 mem2) (p + Z.of_nat (seg_spec.trim_lead s)) (r_trim s).
Proof.
intros Wc memc W2 mem2 p s ((Hz & Hn) & Ht) HBY HV.
pose proof (L_trim_holds s Hn) as (L1 & L2 & L3).
set (ld := seg_spec.trim_lead s) in *. set (rt := r_trim s) in *.
assert (HR : forall j, (j < length s)%nat -> 0 <= nth j s 0 < 256).
{ intros j Hj. assert (Hj' : (j < length (s ++ [0%Z]))%nat) by (rewrite length_app; cbn [length]; lia).
  pose proof (Hz j Hj') as Ej. rewrite app_nth1 in Ej by exact Hj. exact (sa_aview_rng _ _ _ _ _ Ej). }
assert (HLB : length (seg_spec.zb (firstn (ld + length rt) s)) = (ld + length rt)%nat)
  by (unfold seg_spec.zb; rewrite length_map, length_firstn; lia).
assert (HNTH : forall i, (i < length rt)%nat -> nth i rt 0 = nth (ld + i) s 0).
{ intros i Hi. rewrite L2, nth_firstn.
  replace ((i <? length rt)%nat) with true by (symmetry; apply Nat.ltb_lt; exact Hi).
  rewrite nth_skipn; try reflexivity; f_equal; lia. }
split; [split; [|exact L3]|].
- intros i Hi. rewrite length_app in Hi. cbn [length] in Hi.
  replace (p + Z.of_nat ld + Z.of_nat i) with (p + Z.of_nat (ld + i)) by lia.
  rewrite (HBY (ld + i)%nat) by (rewrite length_app, HLB; cbn [length]; lia). f_equal.
  destruct (Nat.lt_ge_cases i (length rt)) as [Hl | Hg].
  + rewrite app_nth1 by (rewrite HLB; lia). unfold seg_spec.zb, ZB0.
    rewrite (map_nth (Z_to_bv 8) (firstn (ld + length rt) s) 0 (ld + i)).
    rewrite nth_firstn. replace ((ld + i <? ld + length rt)%nat) with true by (symmetry; apply Nat.ltb_lt; lia).
    rewrite app_nth1 by exact Hl. rewrite HNTH by exact Hl.
    rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 8) with 256. apply HR. lia.
  + assert (i = length rt) as -> by lia.
    rewrite app_nth2 by (rewrite HLB; lia). rewrite HLB, Nat.sub_diag. cbn [nth].
    rewrite app_nth2 by lia. rewrite Nat.sub_diag. reflexivity.
- intros y Hy. apply HV.
  replace (p + Z.of_nat ld + Z.of_nat (length rt)) with (p + Z.of_nat (ld + length rt)) in Hy by lia.
  destruct (b9s3_tail_mono (p + Z.of_nat (ld + length rt)) (p + Z.of_nat (length s)) y ltac:(lia) Hy) as [Hy' | Hy'].
  + exact (b9_str_some _ p s y (conj (conj Hz Hn) Ht) ltac:(lia)).
  + exact (Ht y Hy').
Qed.

Variable B : asyms.
Hypothesis TRIM : forall fx0 : YK11.FPState, trim_contract (fx := fx0) SEGS B (BASE + AF_trim) STK_trim RLO_A RHI_A.
Hypothesis SIGP : seg_sig_prog (PI := PI).

Section x. Context {fx : YK11.FPState}.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Let RUNP := SRr_run_pi_AJ (fx := fx) B LAWS.
Let RUNC := SRr_run_pi_AJ_call (fx := fx) B LAWS.
Let BR := paj_branch (PI := PI).

Lemma b9_s3 : SB9_3 B.
Proof.
unfold SB9_3, from_J2, b9_from. intros n FJ3 x ei kp lyc Sc Wc rX memc mdc HI.
unfold INV_J2 in HI. destruct HI as (HC & HSC & HKEY & HKLE & HREST & HRG).
unfold b9_core in HC. destruct HC as (HB & HMID & HST & HLEN & HD0 & HDL).
unfold b9_inbuf, b9_buf in HKEY, HREST.
destruct HKEY as [HKS HKI]. destruct HREST as [HRS HRI].
unfold pf_inb, PF_O_BUF in HKI, HRI. destruct HKI as [HKI1 HKI2]. destruct HRI as [HRI1 HRI2].
pose proof (b9_geo B (y_v x) (y_pos x) lyc Sc Wc rX memc mdc PF_SC_LINE HB) as (HAR & Hly & Hin & G & HFP & HSP).
pose proof G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12).
pose proof (b9_st_of_base B (y_v x) (y_pos x) lyc Sc Wc rX memc mdc HB) as HST0.
pose proof HB as (HCX & HFI & HOBJ & HSL & HFSH).
pose proof HFI as (HJ & _ & _ & _ & _ & _ & HFRM & _ & _ & HRG0).
pose proof STK_values as (STR & _ & _ & SPF & _).
pose proof asan_consts as (C1 & _).
pose proof alloc_ceiling_lt as HCL.
pose proof pa_B_ok as (HB0 & HB1 & _). pose proof pa_base_lo as HBLO.
destruct (b9_chain B (y_v x) (y_pos x) lyc Sc Wc rX memc mdc PF_SC_LINE HB) as [ch1 HCH1].
assert (HC5 : sa_heap B lyc Sc (p_c (y_v x)) seg_spec.SEG_C_SIZE)
  by (destruct HOBJ as (_ & _ & _ & _ & H5 & _); exact H5).
set (p := y_lp x + Z.of_nat ei + 1) in *.
set (s := skipn (S ei) (b9_line x)) in *.
pose proof HRS as ((_ & HNs) & _).
pose proof (L_trim_holds s HNs) as (L1 & _ & _).
assert (HTE : p <= trim_end_addr p s <= p + Z.of_nat (length s)) by (unfold trim_end_addr; lia).
(* the registers of the cut *)
unfold B9_R, PF_RL, PF_RM in HRG.
assert (R24 : getr rX 24%bv = w64 (y_lp x + Z.of_nat ei)).
{ apply (b9s3_bvr _ 24%bv 24); [reflexivity|]. apply (b9_rg_get rX _ 24 _ HRG); b9s3_in. }
assert (R26 : getr rX 26%bv = w64 (-1)).
{ apply (b9s3_bvr _ 26%bv 26); [reflexivity|]. apply (b9_rg_get rX _ 26 _ HRG); b9s3_in. }
assert (R10 : getr rX 10%bv = w64 kp).
{ apply (b9s3_bvr _ 10%bv 10); [reflexivity|]. apply (b9_rg_get rX _ 10 _ HRG); b9s3_in. }
(* the seed at J2 *)
set (E := Eimg (Ereg rX [])).
assert (HS : st_ok_pi SEGS VAL E b9s3_ss
  (restrict (w_H Wc) (mkst rX (Z_to_bv 64 (BASE + B9_J2)) memc (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold b9s3_ss. apply pa_entry_st_ok_full;
    [subst E; apply regs_ok_Eimg_Ereg | vm_compute; reflexivity | constructor | cbn; tauto
    | split; [exact I | split; exact I]]. }
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n0 (r : bv 5), Z.of_nat n0 = bv_unsigned r -> ew E n0 = getr rX r)
  by (intros n0 r Hn0; subst E; apply ew_Eimg_Ereg_nat; exact Hn0).
assert (HA0 : env_agree 32 (Ereg rX []) E)
  by (subst E; split; [intros k Hk; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (E24 : ew E 24 = Z_to_bv 64 (y_lp x + Z.of_nat ei))
  by (rewrite (EE 24%nat 24%bv eq_refl); exact R24).
assert (E26 : ew E 26 = Z_to_bv 64 (2 ^ 64 - 1)).
{ rewrite (EE 26%nat 26%bv eq_refl), R26. unfold w64. apply bv_eq. vm_compute. reflexivity. }
assert (E10 : ew E 10 = Z_to_bv 64 kp) by (rewrite (EE 10%nat 10%bv eq_refl); exact R10).
unfold cfg_at. change (w64 (BASE + B9_J2)) with (Z_to_bv 64 (BASE + B9_J2)).
(* 0x88428 beq s8,s10: the UBSan trap T11 *)
psrr_branch_pi RUNP BR HS.
- (* taken: eq = 2 ^ 64 - 1, impossible (eq lies in buf) *)
  exfalso.
  lazymatch type of Hc with
  | branch_taken _ (sv_denot _ ?a) (sv_denot _ ?b) = true =>
    refine (b9s3_t11 E a b (y_lp x + Z.of_nat ei) _ _ _ Hc)
  end.
  + apply (U_atom E 24 _ E24). lia.
  + apply (U_atom E 26 _ E26). lia.
  + lia.
- (* not taken: 0x8842c mv s7,a0; 0x88430 addi a0,s8,1; 0x88434 jal trim *)
  clear Hc.
  paj_run_shc RUNP RUNC HS HJ.
  { lazymatch goal with |- awr_ok _ _ ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr0 ?lyx ?own =>
      let rs' := eval vm_compute in rs in change (awr_ok SEGS B Ex rs' stk spx fp b0 bc fr0 lyx own) end.
    apply awr_ok_nil. }
  assert (KM1 : forall a, 0 <= a < 2 ^ 64 -> rdW Wc (ms_mem ms) a = rdW Wc memc a).
  { intros a Ha. apply (kept_of_frame (segs := SEGS) E _ (w_H Wc) memc (ms_mem ms) (fun _ => False) HFr);
      [|exact Ha | tauto].
    intros b wlo whi a' Hin' Hrr. vm_compute in Hin'. destruct Hin'. }
  clear HF HFr HG.
  lazymatch goal with |- SRr _ _ (mkCfg _ ?dM) _ => set (mdv := dM) in *; clearbody mdv end.
  pmkst HS.
  (* the registers at the call *)
  pose proof (regs_kept_of_st_ok SEGS _ _ _ rX [] (map (Z_to_bv 5) b9s3_kept) HS HA0
    ltac:(vm_compute; reflexivity)) as HK.
  cbn [ms_regs restrict] in HK.
  assert (Rz : forall k z, In k b9s3_kept -> getr rX (Z_to_bv 5 k) = w64 z ->
    getr (ms_regs ms) (Z_to_bv 5 k) = w64 z).
  { intros k z Hk Hz. rewrite (HK (Z_to_bv 5 k)); [exact Hz | apply in_map; exact Hk]. }
  prreg HS (1%bv : bv 5) P1. prreg HS (10%bv : bv 5) P10. prreg HS (23%bv : bv 5) P23.
  assert (C2 : getr (ms_regs ms) 2 = w64 (pf_s1 (y_v x))).
  { apply (b9s3_bvr _ 2%bv 2); [reflexivity|]. apply Rz; [b9s3_in|].
    exact (b9_rg_get rX _ 2 _ HRG0 ltac:(b9s3_in)). }
  assert (C3 : getr (ms_regs ms) 3 = w64 (as_gp B)).
  { apply (b9s3_bvr _ 3%bv 3); [reflexivity|]. apply Rz; [b9s3_in|].
    exact (b9_rg_get rX _ 3 _ HRG0 ltac:(b9s3_in)). }
  assert (C4 : getr (ms_regs ms) 4 = w64 (as_tp B)).
  { apply (b9s3_bvr _ 4%bv 4); [reflexivity|]. apply Rz; [b9s3_in|].
    exact (b9_rg_get rX _ 4 _ HRG0 ltac:(b9s3_in)). }
  assert (C8 : getr (ms_regs ms) 8 = w64 (pf_sp0 (y_v x))).
  { apply (b9s3_bvr _ 8%bv 8); [reflexivity|]. apply Rz; [b9s3_in|].
    exact (b9_rg_get rX _ 8 _ HRG0 ltac:(b9s3_in)). }
  assert (Hsp1 : spZ (ms_regs ms) = pf_s1 (y_v x)).
  { unfold spZ. rewrite C2. unfold w64. rewrite unsigned_lit_small by lia. reflexivity. }
  assert (Hsp : spZ (ms_regs ms) = pf_sp0 (y_v x) + (pf_s1 (y_v x) - pf_sp0 (y_v x))) by (rewrite Hsp1; lia).
  assert (Ho16 : (pf_s1 (y_v x) - pf_sp0 (y_v x)) mod 16 = 0) by (apply b9s3_m16; [exact G5 | exact G3]).
  assert (C1r : getr (ms_regs ms) 1 = Z_to_bv 64 (BASE + B9_J3)) by (rewrite P1; reflexivity).
  assert (C10 : getr (ms_regs ms) 10 = w64 p).
  { rewrite P10. unfold p. b9s3_den. }
  assert (C23 : getr (ms_regs ms) 23 = w64 kp).
  { rewrite P23. b9s3_den. }
  (* the state at the call: the run wrote nothing *)
  pose proof (b9_keep_art B (y_v x) (y_pos x) lyc Sc Wc memc mdc (ms_mem ms) mdv 0 0 HST0 HJ
    ltac:(rewrite SPF; lia) (fun a Ha _ _ => KM1 a Ha)) as HST1.
  assert (HP0 : 0 <= p) by lia.
  assert (HP1 : p + Z.of_nat (length s) < alloc_ceiling) by lia.
  assert (HQ0 : 0 <= kp) by lia.
  assert (HQ1 : kp + Z.of_nat (length (b9_key x ei)) < alloc_ceiling) by lia.
  assert (HRS1 : sa_str (rdW Wc (ms_mem ms)) p s).
  { apply (reac_segconf_parse.sa_str_low _ _ _ _ HRS HP0 HP1). intros a Ha. apply KM1. lia. }
  assert (HKS1 : sa_str (rdW Wc (ms_mem ms)) kp (b9_key x ei)).
  { apply (reac_segconf_parse.sa_str_low _ _ _ _ HKS HQ0 HQ1). intros a Ha. apply KM1. lia. }
  (* the frame chain at the call's memory (the run wrote nothing) *)
  pose proof HCX as (HPRE0 & _).
  pose proof HPRE0 as (_ & _ & _ & _ & _ & Hstk0 & _).
  pose proof Hstk0 as (Sk1 & Sk2 & Sk3 & Sk4 & Sk5 & Sk6 & Sk7 & Sk8 & Sk9).
  assert (HLT64 : ly_top lyc <= 2 ^ 64) by (rewrite Hly; lia).
  assert (HCH2 : achain lyc (rdW Wc (ms_mem ms)) (pf_s1 (y_v x)) (pf_sp0 (y_v x)) ch1).
  { apply (achain_kept lyc (rdW Wc memc) (rdW Wc (ms_mem ms)) (pf_s1 (y_v x)) (pf_sp0 (y_v x)) ch1 0
      HCH1 ltac:(lia) HLT64). intros a Ha. apply KM1. lia. }
  (* VERIFY rule 1j-bis at 0x88434: trim's premises besides afn_pre *)
  pose proof (b9_trim_site_ok B (y_v x) (y_pos x) lyc Sc Wc (ms_mem ms) mdv (ms_regs ms) p s HST1 C10 HRS1
    ltac:(unfold pf_inb, PF_O_BUF; lia)) as HTC.
  unfold b9_trim_call in HTC. destruct HTC as (ROD & R10c & Hp64 & TPRE & TEV).
  rewrite (SIGP SS_trim ltac:(unfold seg_prog_syms; cbn [In]; repeat (first [left; reflexivity | right]))).
  replace (seg_af SS_trim) with AF_trim by (vm_compute; reflexivity).
  eapply SRr_bind.
  { eapply (cl_callS_wide B LAWS Wc (ms_regs ms) (ms_mem ms) _ STK_reac_segconf_parse_file (pf_sp0 (y_v x))
      (seg_spec.RC_PARSE_W (p_c (y_v x))) (p_ly (y_v x)) (p_S (y_v x)) (p_W (y_v x)) (p_mem (y_v x))
      (p_md (y_v x)) [(5, y_pos x)] lyc Sc mdv 0 STK_trim
      [(trim_end_addr p s, trim_end_addr p s + 1)] EV_trim (pf_s1 (y_v x) - pf_sp0 (y_v x))
      (Z_to_bv 64 (BASE + B9_J3)) ch1
      (fun ly' S' W' regs' mem' md' =>
         getr regs' 10 = w64 (p + Z.of_nat (seg_spec.trim_lead s)) /\
         sa_bytes (aview SEGS (w_H W') mem') p
           (seg_spec.zb (firstn (seg_spec.trim_lead s + length (r_trim s)) s) ++ [seg_spec.ZERO]) /\
         sa_kept SEGS Wc (ms_mem ms) W' mem' (ms_regs ms) STK_trim (fun a => a = trim_end_addr p s) /\
         sa_noalloc B lyc Sc ly' S') HJ).
    - exact Hsp.
    - exact Ho16.
    - lia.
    - rewrite STR. lia.
    - rewrite STR, SPF. lia.
    - exact C3.
    - exact C4.
    - exact C1r.
    - rewrite b9s3_J3. apply ret_ok_codeptr_v; [lia | reflexivity].
    - rewrite b9s3_J3. rewrite unsigned_lit_small by lia. lia.
    - replace (pf_sp0 (y_v x) + (pf_s1 (y_v x) - pf_sp0 (y_v x))) with (pf_s1 (y_v x)) by lia.
      unfold s0Z. rewrite C8. unfold w64. rewrite unsigned_lit_small by lia. exact HCH2.
    - intros HPRE1. eapply SRr_mono.
      { exact (TRIM fx lyc Sc Wc (ms_regs ms) (ms_mem ms) mdv ch1 p s HPRE1 ROD R10c Hp64 TPRE TEV). }
      cbv beta. intros W' c' _ (ly' & S' & regs' & mem' & md' & -> & HJ' & HP' & HK').
      exists ly', S', regs', mem', md'. split; [rewrite C1r; reflexivity|].
      split; [exact HJ'|]. split; [exact HP' | exact HK'].
    - intros a Ha. apply inFP_cons in Ha as [Ha | Ha]; [|exfalso; exact (inFP_nil a Ha)].
      right; right; right; left. exists 5, (y_pos x). split; [left; reflexivity|].
      left. unfold in_zr. cbn [fst snd]. rewrite Hly.
      change (frame_addr (p_ly (y_v x)) 5 (y_pos x)) with (pf_F (y_v x) (y_pos x)).
      change (fs_frame_bytes 5) with 2048. lia.
    - intros ly2 S2 W2 regs2 mem2 md2 _ a Ha Hw Hn.
      apply inFP_cons in Ha as [Ha | Ha]; [|exfalso; exact (inFP_nil a Ha)].
      exfalso. rewrite SPF in Hw. lia. }
  (* back at 0x88438 = J3 *)
  cbv beta.
  intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HJc2 & HP2 & (Ha02 & HBY2 & HKT2 & HNA2)).
  destruct HNA2 as (HPm2 & Hly2 & HSf2). subst ly2.
  replace (0 + EV_trim) with 0 in HJ2 by (unfold EV_trim; lia).
  assert (HKT : forall a, 0 <= a < 2 ^ 64 -> ~ (pf_s1 (y_v x) - STK_trim <= a < pf_s1 (y_v x)) ->
    ~ (a = trim_end_addr p s) -> rdW W2 mem2 a = rdW Wc (ms_mem ms) a).
  { intros a Ha Hw He. apply HKT2; [exact Ha | rewrite Hsp1; exact Hw | exact He]. }
  assert (HTEV : rdW W2 mem2 (trim_end_addr p s) <> None).
  { unfold trim_end_addr. rewrite (HBY2 (seg_spec.trim_lead s + length (r_trim s))%nat); [discriminate|].
    unfold seg_spec.zb. rewrite length_app, length_map, length_firstn. cbn [length]. lia. }
  assert (KV1 : forall a, rdW Wc memc a <> None -> rdW Wc (ms_mem ms) a <> None).
  { intros a0 Hv0. rewrite b9s3_aview_mod in Hv0 |- *.
    pose proof (Z.mod_pos_bound a0 (2 ^ 64) ltac:(lia)) as Ha. rewrite (KM1 _ Ha). exact Hv0. }
  assert (KV2 : forall a, rdW Wc (ms_mem ms) a <> None -> rdW W2 mem2 a <> None).
  { intros a0 Hv0. rewrite b9s3_aview_mod in Hv0 |- *.
    pose proof (Z.mod_pos_bound a0 (2 ^ 64) ltac:(lia)) as Ha.
    destruct (Z.eq_dec (a0 mod 2 ^ 64) (trim_end_addr p s)) as [He | He]; [rewrite He; exact HTEV|].
    destruct (Z_lt_le_dec (a0 mod 2 ^ 64) (pf_s1 (y_v x) - STK_trim)) as [Hlo | Hlo];
      [|destruct (Z_lt_le_dec (a0 mod 2 ^ 64) (pf_s1 (y_v x))) as [Hhi | Hhi]].
    - rewrite (HKT (a0 mod 2 ^ 64) Ha ltac:(lia) He). exact Hv0.
    - pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres2 & _).
      apply (aview_some_of_apresent SEGS). apply Hpres2. rewrite SPF, STR in *. lia.
    - rewrite (HKT (a0 mod 2 ^ 64) Ha ltac:(lia) He). exact Hv0. }
  assert (KV : forall a, rdW Wc memc a <> None -> rdW W2 mem2 a <> None)
    by (intros a Hv; exact (KV2 a (KV1 a Hv))).
  assert (KW : forall a, 0 <= a < 2 ^ 64 -> ~ b9_Wrx (y_v x) (y_pos x) true a ->
    rdW W2 mem2 a = rdW Wc memc a).
  { intros a Ha Hw. rewrite (HKT a Ha).
    - exact (KM1 a Ha).
    - intros Hn. apply Hw. left. rewrite SPF, STR in *. lia.
    - intros Hn. apply Hw. right; right. unfold PF_O_BUF. lia. }
  (* the registers after the call *)
  assert (Hpre : forall k z, In k b9s3_kept -> getr rX (Z_to_bv 5 k) = w64 z ->
    getr regs2 (Z_to_bv 5 k) = w64 z).
  { intros k z Hk Hz. rewrite (HP2 k); [exact (Rz k z Hk Hz)|].
    unfold b9s3_kept in Hk. cbn [In] in Hk. unfold acallee_saved.
    repeat (destruct Hk as [<- | Hk]; [lia |]). destruct Hk. }
  assert (C23' : getr regs2 (Z_to_bv 5 23) = w64 kp).
  { rewrite (HP2 23 ltac:(unfold acallee_saved; lia)).
    apply (b9s3_bvr' _ 23%bv 23); [reflexivity | exact C23]. }
  assert (C10' : getr regs2 (Z_to_bv 5 10) = w64 (p + Z.of_nat (seg_spec.trim_lead s))).
  { apply (b9s3_bvr' _ 10%bv 10); [reflexivity | exact Ha02]. }
  assert (HFI2 : pf_rg regs2 (b9_FI B (y_v x))).
  { unfold b9_FI, pf_rg. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd];
      (apply Hpre; [b9s3_in | apply (b9_rg_get rX _ _ _ HRG0); b9s3_in]). }
  assert (HB2 : pf_base B (y_v x) (y_pos x) lyc S2 W2 regs2 mem2 md2 PF_SC_LINE).
  { eapply (b9_move0 B (y_v x) (y_pos x) lyc Sc Wc rX memc mdc PF_SC_LINE S2 W2 regs2 mem2 md2 PF_SC_LINE
      HB HJ2 HSf2 HPm2 KW KV HFI2).
    eapply b9_keep_fsh; [exact G | exact KW | exact HFSH]. }
  assert (HST2 : pf_st (y_v x) (y_pos x) (rdW W2 mem2) (y_cf x) (y_cur x) (y_nm x) (b9_k x)).
  { first
      [ exact (b9_keep_st B (y_v x) (y_pos x) lyc Sc Wc memc mdc (rdW W2 mem2) G HAR Hin Hly KW
                 (y_cf x) (y_cur x) (y_nm x) (b9_k x) HC5 HST)
      | exact (b9_keep_st B (y_v x) (y_pos x) lyc Sc Wc memc mdc (rdW W2 mem2) G HAR Hin Hly KW KV
                 (y_cf x) (y_cur x) (y_nm x) (b9_k x) HC5 HST)
      | (eapply b9_keep_st; eassumption) ]. }
  (* the key survives trim's NUL (it ends at or below lp + ei < p <= the NUL) *)
  assert (HKS2 : sa_str (rdW W2 mem2) kp (b9_key x ei)).
  { apply (b9s3_keep_str Wc (ms_mem ms) W2 mem2
      (fun a => (pf_s1 (y_v x) - STK_trim <= a < pf_s1 (y_v x)) \/ a = trim_end_addr p s)
      kp (b9_key x ei)); [| | | lia | lia | exact HKS1].
    - intros a Ha He. apply HKT; [exact Ha | intros Hw; apply He; left; exact Hw
      | intros Hw; apply He; right; exact Hw].
    - intros a Hv. exact (KV2 a Hv).
    - intros a [Hw | Hw]; [rewrite SPF, STR in *; lia | lia]. }
  (* the value: trim's answer at vp0 = p + trim_lead s *)
  assert (HV02 : sa_str (rdW W2 mem2) (p + Z.of_nat (seg_spec.trim_lead s)) (r_trim s))
    by exact (b9s3_trim_str Wc (ms_mem ms) W2 mem2 p s HRS1 HBY2 KV2).
  change (mkCfg (mkst regs2 (Z_to_bv 64 (BASE + B9_J3)) mem2 (seg_rom SEGS)) md2)
    with (cfg_at SEGS (BASE + B9_J3) regs2 mem2 md2).
  unfold from_J3, b9_from in FJ3.
  apply (FJ3 x ei kp (p + Z.of_nat (seg_spec.trim_lead s)) lyc S2 W2 regs2 mem2 md2).
  unfold INV_J3, b9_core, b9_inbuf, b9_buf, pf_inb, PF_O_BUF.
  assert (EV : b9_v0 x ei = r_trim s) by reflexivity.
  split; [|split; [|split; [|split; [|split]]]].
  + (* b9_core *)
    split; [exact HB2|]. split; [exact HMID|]. split; [exact HST2|].
    split; [exact HLEN|]. split; [exact HD0 | exact HDL].
  + exact HSC.
  + split; [exact HKS2 | lia].
  + lia.
  + rewrite EV. split; [exact HV02 | lia].
  + unfold B9_R, PF_RL, PF_RM, pf_rg. cbn [app].
    repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd];
      first [ exact C23' | exact C10' | apply Hpre; [b9s3_in | apply (b9_rg_get rX _ _ _ HRG); b9s3_in] ].
Qed.

End x.
End d.
