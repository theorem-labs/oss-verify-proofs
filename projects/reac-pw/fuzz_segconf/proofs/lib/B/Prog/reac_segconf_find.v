(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the program walk of rec_calls_equal on the ASan+UBSan build of plugin-hostd/fuzz_command
   (0x89ef8, 164 instructions, frame 144 bytes), ported from the ASan walk lib/A/Prog/rec_calls_equal.v (0x89968). The
   shape is the A walk's: the symbolic executor over the position-abstract listing (CmdPaLib.v), the inline checks removed
   by the shadow tokens (PaShadow.v), the strcmp wrapper's call stepped through by its Theorem Labs lane contract (PaArt.v
   aj_art_at), the two loops cut at their heads (0x89f98, 0x8a064) and at the outer latch (0x8a0b4), each piece re-seeded
   from the concrete state there, the loops proved by induction. What B changes:
   - the frame (144 bytes) keeps n at 0(sp), the UBSan predicates `b mod 8 = 0 && b <> 0`, `b <> 0`,
     `a mod 8 = 0 && a <> 0` at 8(sp), 16(sp), 24(sp), and b at 32(sp); a stays in a5/s11 and `a <> 0` in a4/s8;
   - the inner loop counts s5 = 8k up to s2 = 8 * nargs and forms both argument addresses from s3/s10 (a[i].args) and
     s1/s9 (b[i].args) plus s5 (the seed's alias facts name the two sums);
   - eight UBSan trap branches, all to the `unimp` at 0x8a168, are refuted from the run's facts: 0x89fac, 0x89fbc,
     0x89fe4, 0x89ff4 are decided by the executor (a4 = 1 and the three predicate slots = 1 at the outer seed, which the
     entry derives from rce_calls' `a mod 8 = 0` and rce_home's 4096 <= a; a + 56i >= 4096 by the seed's atom fact);
     0x89fb4 and 0x89fec (a + 56i < a, b + 56i < b unsigned) and 0x8a064, 0x8a068 (~(a[i].args) < 8k, ~(b[i].args) < 8k)
     are refuted at the branch from the values of their operands. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/B/Prog/rec_calls_equal.v, with its module paths, module names and numbers changed; 527 of its 679 lines of code are new or changed and 1440 lines of the source are left out. *)
(* The walk of reac_segconf_find on fuzz_segconf image B (fuzz_segconf.asan-ubsan, entry BASE +
   AF_reac_segconf_find = 0x89a84, 61 instructions, a 64-byte frame) against reac_segconf_find_contract
   (lib/B/Prog/reac_segconf_find_c.v, image B's copy of the FINAL contract text).
   ADAPTED: the image-B port of lib/A/Prog/reac_segconf_find.v (commit 561c4bddbbdf, which
   carries that walk's step plan plan-reac_segconf_find.md (image A's walk record), not its Rocq text); the loop's cut, the
   UBSan trap branches and the wrapper call follow plugin-hostd/fuzz_command's image-B lib/B/Prog/rec_calls_equal.v
   (origin/ossv/recipes 501c0d516c69). Step plan: the unit record's Bwalks-G45-plans/plan-reac_segconf_find.md.

   The symbolic executor runs over the position-abstract listing (lib/B/Prog/SegList.v). The one instrumented
   check (the 4-byte load of c->n at c + 0x2c80, 0x89ad8 .. 0x89ae4) is discharged as the run's shadow obligation
   from the contract's heap premise on c, so the slow path 0x89b68 and its error call are not reached. The three
   UBSan trap branches to the `unimp` at 0x89b64 are refuted at the branch: 0x89abc (c & 7 <> 0) by the contract's
   `c mod 16 = 0`, 0x89b08 (32 - k = 0) by k < n <= 32, 0x89b0c (c + 356 k wraps) by c + 16616 <= alloc_ceiling.
   The loop is cut at its head 0x89b08 and the epilogue at 0x89b40, each re-seeded from the concrete state there;
   the loop is proved by induction on the entries left.
   Section hypotheses: ASTRCMP (the strcmp wrapper's contract, lib/B/Rt/RtString.v, the image-A wrapper interface row 17)
   and TL (PALib B: the shadow-base GOT word and cell, and api_env for aj_art_at's errno arm). *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI04 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import
PaRun PaShadow PaJournal SegSyms SegList SegPa SegPaLib SegObj SegGlob PaDenot PaSB PaCall PaLibG PaLibH.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require Import RtDefs RtString.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec seg_query_facts.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPgBase SegABase PaArt PaNoChain
  reac_segconf_find_c reac_segconf_find_lem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require SegInstB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation SIG s := (@pa_sigma _ seg_listing PI s).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
#[local] Notation FSTK := SegInstB.STK_reac_segconf_find.
Section e.
Variable B : asyms.
Hypothesis ASTRCMP : forall fx0 : YK11.FPState,
  @astrcmp_realizes fx0 rc SEGS B (SIG SS___interceptor_trampoline_strcmp).
Hypothesis TL : PALib B.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (L := seg_listing) (PI := PI).
Let RET := paj_ret_at (L := seg_listing) (PI := PI).

(* a stretch of this walk writes only its own frame, so it keeps every byte of the window [lo, hi) *)
Ltac fnd_keep_empty HFr K lo hi :=
  lazymatch type of HFr with frame_of _ _ (mrestrict ?H ?m1) (mrestrict ?H ?m2) =>
  assert (K : kept_out (aview SEGS H m1) (aview SEGS H m2) lo hi)
  by (intros x0 Hx0 Hn0; apply (kept_of_frame (segs := SEGS) _ _ _ _ _ (fun _ => False) HFr);
      [ let b0 := fresh "b0" in let wlo := fresh "wlo" in let whi := fresh "whi" in let a0 := fresh "a0" in
        let Hi := fresh "Hi" in let Hrr := fresh "Hrr" in let Hq := fresh "Hq" in
        intros b0 wlo whi a0 Hi Hrr; vm_compute in Hi;
        repeat (destruct Hi as [Hq | Hi]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; lia|]); destruct Hi
      | exact Hx0 | tauto ]) end.
(* the same, for a stretch whose frame region is the walk's own 64-byte frame *)
Ltac fnd_keep_win HFr K lo hi Usp :=
  lazymatch type of HFr with frame_of _ _ (mrestrict ?H ?m1) (mrestrict ?H ?m2) =>
  assert (K : kept_out (aview SEGS H m1) (aview SEGS H m2) lo hi)
  by (intros x0 Hx0 Hn0; apply (kept_of_frame (segs := SEGS) _ _ _ _ _ (fun x => lo <= x < hi) HFr);
      [ let b0 := fresh "b0" in let wlo := fresh "wlo" in let whi := fresh "whi" in let a0 := fresh "a0" in
        let Hi := fresh "Hi" in let Hrr := fresh "Hrr" in let Hq := fresh "Hq" in
        intros b0 wlo whi a0 Hi Hrr; vm_compute in Hi;
        repeat (destruct Hi as [Hq | Hi]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?Usp in Hrr; lia|]);
        destruct Hi
      | exact Hx0 | exact Hn0 ]) end.
Ltac fnd_md :=
  lazymatch goal with HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?md2 _ |- _ =>
    lazymatch md2 with with_vm_backing _ _ _ => let m := fresh "mdv" in set (m := md2) in *; clearbody m | _ => idtac end end.

Section w.
Variables (ly : alayout) (S : astate) (W : world SEGS) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
  (c name : Z) (rcs : rconf) (nm : list Z).
Hypothesis HPRE : afn_pre_na SEGS B FSTK ly S W regs mem md.
Hypothesis HROD : arodata_okP SEGS SegInstB.RLO_A SegInstB.RHI_A B (rdW W mem).
Hypothesis H10 : getr regs 10 = w64 c.
Hypothesis H11 : getr regs 11 = w64 name.
Hypothesis HQP : query_pre SEGS B ly S (rdW W mem) c name rcs nm.

Definition fnd_N : Z := Z.of_nat (length (rc_seg rcs)).

Definition fnd_Q : world SEGS -> config -> Prop :=
apost_base SEGS B FSTK [] regs ly S W mem md 0
(fun ly' S' W' regs' mem' md' =>
 getr regs' 10 = w64 (seg_spec.find_ptr c rcs nm) /\
 sa_kept SEGS W mem W' mem' regs FSTK (fun _ => False) /\
 sa_noalloc B ly S ly' S').

(* ------------------------------- the facts the contract's premises give ------------------------------- *)
Lemma fnd_sp : spZ regs mod 16 = 0 /\ alloc_ceiling + FSTK <= spZ regs /\ spZ regs <= 2 ^ 47.
Proof using B ASTRCMP TL LAWS RUN RUNTO BR RET ly S W regs mem md c name rcs nm HPRE HROD H10 H11 HQP.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2). lia.
Qed.

Lemma fnd_cb : 4096 <= c /\ c + 16616 <= alloc_ceiling /\ (c + 16616 <= 0x10000 \/ kImgEnd <= c) /\
  exists b m, In (b, m) (ablocks B ly S) /\ b <= c /\ c + 16616 <= b + req_size m.
Proof using B ASTRCMP TL LAWS RUN RUNTO BR RET ly S W regs mem md c name rcs nm HPRE HROD H10 H11 HQP.
pose proof HPRE as (HAR & _).
destruct HQP as (_ & _ & _ & (b & m & Hin & Hb & Hbm) & _).
unfold seg_spec.SEG_C_SIZE in Hbm.
destruct (al_blocks _ _ LAWS ly S W mem md b m HAR Hin) as (Hb16 & H4096 & Hceil & Happ & Hpr & Hpw & Hmm).
pose proof (req_size_pos m ltac:(lia)) as [Hr1 Hr2].
pose proof (blk_off_imgP B ly S W mem md b m HAR Hin) as Hoff. unfold off_img in Hoff.
split; [lia|]. split; [lia|].
split; [unfold kImgEnd in *; destruct Hoff as [Ho|Ho]; [left | right]; lia|].
exists b, m. split; [exact Hin|]. split; lia.
Qed.

Lemma fnd_nfacts : 0 <= fnd_N <= 32 /\ sa_val (rdW W mem) (c + 0x2c80) 4 fnd_N.
Proof using B ASTRCMP TL LAWS RUN RUNTO BR RET ly S W regs mem md c name rcs nm HPRE HROD H10 H11 HQP.
destruct HQP as (_ & _ & (bs & HBS & HENC) & _).
pose proof HENC as (HL & HLS & _ & HN & _). unfold seg_spec.SEG_C_SIZE in HL.
split; [unfold fnd_N; lia|].
apply (fnd_u32_val (rdW W mem) c bs seg_spec.RC_N fnd_N HBS); [unfold seg_spec.RC_N; lia | unfold seg_spec.RC_N; lia|].
exact HN.
Qed.

Lemma fnd_nmfacts : 1 <= name /\ name + Z.of_nat (length nm) + 1 <= alloc_ceiling /\
  name + Z.of_nat (length nm) + 1 <= 2 ^ 63 /\ Z.of_nat (length nm) + 1 < 2 ^ 32 /\
  sa_strz (rdW W mem) name nm /\ sa_tail (rdW W mem) (name + Z.of_nat (length nm)) /\
  sa_addr (rdW W mem) name (Z.of_nat (length nm) + 1).
Proof using B ASTRCMP TL LAWS RUN RUNTO BR RET ly S W regs mem md c name rcs nm HPRE HROD H10 H11 HQP.
pose proof HPRE as (HAR & _).
destruct HQP as (_ & _ & _ & _ & _ & Hn0 & (HNZ & HNT) & HNL & HNA & HN32).
pose proof HNA as (Ha0 & Ha63 & _).
destruct (fnd_loc_below B ly S W mem md name (Z.of_nat (length nm) + 1) HAR HNL ltac:(lia)) as [Hl0 Hlc].
split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
split; [exact HNZ|]. split; [exact HNT | exact HNA].
Qed.

(* entry k's name: a C string of at most 15 bytes inside c's block *)
Lemma fnd_segname : forall k, (k < length (rc_seg rcs))%nat ->
  sa_strz (rdW W mem) (c + 356 * Z.of_nat k) (rs_name (r_seg rcs k)) /\
  (length (rs_name (r_seg rcs k)) < 16)%nat /\
  sa_tail (rdW W mem) (c + 356 * Z.of_nat k + Z.of_nat (length (rs_name (r_seg rcs k)))) /\
  sa_addr (rdW W mem) (c + 356 * Z.of_nat k) (Z.of_nat (length (rs_name (r_seg rcs k))) + 1).
Proof using B ASTRCMP TL LAWS RUN RUNTO BR RET ly S W regs mem md c name rcs nm HPRE HROD H10 H11 HQP.
intros k Hk.
destruct HQP as (_ & _ & (bs & HBS & HENC) & _ & HCA & _).
pose proof HENC as (HL & HLS & _). unfold seg_spec.SEG_C_SIZE in HL.
destruct (fnd_name_strz (rdW W mem) c bs rcs k HBS HENC Hk) as [HS Hlen].
split; [exact HS|]. split; [exact Hlen|].
split; [exact (fnd_name_tail (rdW W mem) c bs k _ HBS HL ltac:(lia) Hlen)|].
unfold seg_spec.SEG_C_SIZE in HCA.
apply (fnd_addr_sub (rdW W mem) c 16616); [exact HCA | lia | lia | lia].
Qed.

Lemma fnd_zrange : forall k, (k < length (rc_seg rcs))%nat ->
  Forall (fun z => 0 <= z < 256) (rs_name (r_seg rcs k)) /\ ~ In 0 (rs_name (r_seg rcs k)).
Proof using B ASTRCMP TL LAWS RUN RUNTO BR RET ly S W regs mem md c name rcs nm HPRE HROD H10 H11 HQP.
intros k Hk. destruct (fnd_segname k Hk) as (HS & _). pose proof HS as [HZ HN].
split; [|exact HN].
pose proof (fnd_zs_range SEGS (w_H W) mem _ _ HZ) as R. apply Forall_app in R as [R _]. exact R.
Qed.

Lemma fnd_nmrange : Forall (fun z => 0 <= z < 256) nm /\ ~ In 0 nm.
Proof using B ASTRCMP TL LAWS RUN RUNTO BR RET ly S W regs mem md c name rcs nm HPRE HROD H10 H11 HQP.
destruct HQP as (_ & _ & _ & _ & _ & _ & ((HZ & HN) & _) & _).
split; [|exact HN].
pose proof (fnd_zs_range SEGS (w_H W) mem _ _ HZ) as R. apply Forall_app in R as [R _]. exact R.
Qed.

(* ----------------------------------------- the cut ----------------------------------------- *)
(* the seven words the prologue saved: ra s0 s1 s2 s3 s4 s5 at sp0-8 .. sp0-56 *)
Definition fnd_frame (rd : reader) : Prop :=
forall j r, nth_error fnd_saved j = Some r ->
sa_val rd (spZ regs - 8 - 8 * Z.of_nat j) 8 (bv_unsigned (getr regs (Z_to_bv 5 r))).
(* the registers the code and the wrapper keep: sp (its own frame), gp, tp and s6..s11 *)
Definition fnd_keep (regs1 : bvmap 5 word) : Prop :=
getr regs1 2 = w64 (spZ regs - 64) /\ getr regs1 3 = getr regs 3 /\ getr regs1 4 = getr regs 4 /\
getr regs1 22 = getr regs 22 /\ getr regs1 23 = getr regs 23 /\ getr regs1 24 = getr regs 24 /\
getr regs1 25 = getr regs 25 /\ getr regs1 26 = getr regs 26 /\ getr regs1 27 = getr regs 27.
Definition fnd_cut (regs1 : bvmap 5 word) (mem1 : word -> option byte) (md1 : Model) : Prop :=
ajournal SEGS B FSTK (spZ regs) [] ly S W mem md [] ly S W mem1 md1 0 /\
kept_out (rdW W mem) (rdW W mem1) (spZ regs - FSTK) (spZ regs) /\
fnd_frame (rdW W mem1) /\ fnd_keep regs1.

Lemma fnd_cut_kept : forall regs1 mem1 md1 regs2 mem2 md2 lo hi,
fnd_cut regs1 mem1 md1 ->
ajournal SEGS B FSTK (spZ regs) [] ly S W mem md [] ly S W mem2 md2 0 ->
kept_out (rdW W mem1) (rdW W mem2) lo hi -> spZ regs - FSTK <= lo -> hi <= spZ regs - 64 ->
getr regs2 2 = getr regs1 2 -> getr regs2 3 = getr regs1 3 -> getr regs2 4 = getr regs1 4 ->
getr regs2 22 = getr regs1 22 -> getr regs2 23 = getr regs1 23 -> getr regs2 24 = getr regs1 24 ->
getr regs2 25 = getr regs1 25 -> getr regs2 26 = getr regs1 26 -> getr regs2 27 = getr regs1 27 ->
fnd_cut regs2 mem2 md2.
Proof using B ASTRCMP TL LAWS RUN RUNTO BR RET ly S W regs mem md c name rcs nm HPRE HROD H10 H11 HQP.
intros regs1 mem1 md1 regs2 mem2 md2 lo hi (HJ & HK & HFR & R2 & R3 & R4 & R22 & R23 & R24 & R25 & R26 & R27)
  HJ2 HK2 Hlo Hhi Q2 Q3 Q4 Q22 Q23 Q24 Q25 Q26 Q27.
pose proof fnd_sp as (Hal16 & Hslo & Hshi). pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HST : FSTK = 8256) by reflexivity.
split; [exact HJ2|]. split.
{ intros x Hx Hn. destruct (Z_lt_le_dec x lo) as [Hl|Hl]; [rewrite (HK2 x Hx) by lia; exact (HK x Hx Hn)|].
  destruct (Z_lt_le_dec x hi) as [Hh|Hh]; [exfalso; apply Hn; lia|]. rewrite (HK2 x Hx) by lia. exact (HK x Hx Hn). }
split.
{ intros j r Hr. assert (Hj : (j < 7)%nat)
    by (change 7%nat with (length fnd_saved); apply (proj1 (nth_error_Some fnd_saved j)); rewrite Hr; discriminate).
  intros kk Hk. rewrite (HK2 (spZ regs - 8 - 8 * Z.of_nat j + Z.of_nat kk)) by lia. exact (HFR j r Hr kk Hk). }
split; [rewrite Q2; exact R2|]. split; [rewrite Q3; exact R3|]. split; [rewrite Q4; exact R4|].
split; [rewrite Q22; exact R22|]. split; [rewrite Q23; exact R23|]. split; [rewrite Q24; exact R24|].
split; [rewrite Q25; exact R25|]. split; [rewrite Q26; exact R26 | rewrite Q27; exact R27].
Qed.

(* a saved word of the frame, read out of the stack region of a symbolic state *)
Lemma fnd_stack_field : forall E H mem' cs off v e,
region_ok SEGS E (mrestrict H mem') (YP09.mkRegion (Some 2%nat) (-64) 0 (-64) 0 cs) ->
bv_unsigned (ew E 2) = spZ regs ->
In (YP09.mkChunk off (CVal 8 e)) cs -> sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
sa_val (aview SEGS H mem') (spZ regs + off) 8 v.
Proof using B ASTRCMP TL LAWS RUN RUNTO BR RET ly S W regs mem md c name rcs nm HPRE HROD H10 H11 HQP.
intros E H mem' cs off v e HR Hsp Hin He Hv. apply fnd_sa_of_val_mem.
change 8%nat with (N.to_nat 8).
apply (field_of_region E _ 2 (spZ regs) cs (-64) 0 (-64) 0 off 8 e v HR Hsp Hin He).
- change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). exact Hv.
- cbn. lia.
Qed.

Lemma fnd_frame_of_region : forall E H mem' cs,
region_ok SEGS E (mrestrict H mem') (YP09.mkRegion (Some 2%nat) (-64) 0 (-64) 0 cs) ->
bv_unsigned (ew E 2) = spZ regs ->
(forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r) ->
(forall j r, nth_error fnd_saved j = Some r -> In (YP09.mkChunk (-8 - 8 * Z.of_nat j) (CVal 8 (SOff (Z.to_nat r) 0))) cs) ->
fnd_frame (aview SEGS H mem').
Proof using B ASTRCMP TL LAWS RUN RUNTO BR RET ly S W regs mem md c name rcs nm HPRE HROD H10 H11 HQP.
intros E H mem' cs HR Hsp EE Hin j r Hr.
assert (Hr' : 1 <= r <= 21) by (apply nth_error_In in Hr; cbn in Hr; intuition lia).
replace (spZ regs - 8 - 8 * Z.of_nat j) with (spZ regs + (-8 - 8 * Z.of_nat j)) by lia.
apply (fnd_stack_field E H mem' cs _ _ (SOff (Z.to_nat r) 0)); [exact HR | exact Hsp | exact (Hin j r Hr) | |
  pose proof (bv_unsigned_in_range 64 (getr regs (Z_to_bv 5 r))) as HRr; change (bv_modulus 64) with (2 ^ 64) in HRr; exact HRr].
cbn [sv_denot]. rewrite Z.add_0_r, !Z_to_bv_bv_unsigned.
apply (EE (Z.to_nat r) (Z_to_bv 5 r)).
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32. rewrite Z.mod_small by lia. lia.
Qed.

(* ------------------------------- the epilogue 0x89b40 .. 0x89b60 ------------------------------- *)
Definition fnd_e_extra : list word := map (fun r => getr regs (Z_to_bv 5 r)) fnd_saved.
Lemma fnd_e_nth : forall j r, nth_error fnd_saved j = Some r -> nth j fnd_e_extra (Z_to_bv 64 0) = getr regs (Z_to_bv 5 r).
Proof using B ASTRCMP TL LAWS RUN RUNTO BR RET ly S W regs mem md c name rcs nm HPRE HROD H10 H11 HQP.
intros j r H. unfold fnd_e_extra. apply nth_error_nth.
rewrite (map_nth_error (fun r0 => getr regs (Z_to_bv 5 r0)) j fnd_saved H). reflexivity.
Qed.

Lemma fnd_epi_seed : forall regs1 mem1, getr regs1 2 = w64 (spZ regs - 64) -> fnd_frame (rdW W mem1) ->
st_ok_pi SEGS VAL (Eimg (Ereg regs1 fnd_e_extra)) fnd_ss_epi
  (restrict (w_H W) (mkst regs1 (Z_to_bv 64 (BASE + FND_EPI)) mem1 (seg_rom SEGS)))
/\ sh_ok SEGS fnd_Bx [] (Eimg (Ereg regs1 fnd_e_extra)) (mrestrict (w_H W) mem1).
Proof using B ASTRCMP TL LAWS RUN RUNTO BR RET ly S W regs mem md c name rcs nm HPRE HROD H10 H11 HQP.
intros regs1 mem1 R2 HFR. pose proof fnd_sp as (Hal16 & Hlo & Hhi).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). assert (HST : FSTK = 8256) by reflexivity.
set (E := Eimg (Ereg regs1 fnd_e_extra)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs - 64).
{ subst E. rewrite (ew_Eimg_Ereg_nat regs1 _ 2 2%bv eq_refl), R2. unfold w64. apply unsigned_lit_small. lia. }
split; [|apply Forall_nil].
rewrite restrict_mkst_fx. unfold fnd_ss_epi. apply pa_entry_st_ok_full.
- subst E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_nil]. unfold region_ok, fnd_estack.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite Usp.
  split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  apply Forall_forall. intros ch Hch. apply in_map_iff in Hch as (j & <- & Hj). apply in_seq in Hj.
  destruct (nth_error fnd_saved j) as [r|] eqn:Hr; [| apply nth_error_None in Hr; cbn in Hr; lia].
  pose proof (bv_unsigned_in_range 64 (getr regs (Z_to_bv 5 r))) as HRr. change (bv_modulus 64) with (2 ^ 64) in HRr.
  apply (chunk_ok_val SEGS E _ (spZ regs - 64) (56 - 8 * Z.of_nat j) 8 (SOff (32 + j) 0)
    (bv_unsigned (getr regs (Z_to_bv 5 r)))).
  + cbn [sv_denot]. subst E. rewrite Eimg_low by (unfold A_TEXT; lia). rewrite ew_Ereg_extra, (fnd_e_nth j r Hr).
    rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
  + change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). exact HRr.
  + cbn. lia.
  + replace (spZ regs - 64 + (56 - 8 * Z.of_nat j)) with (spZ regs - 8 - 8 * Z.of_nat j) by lia.
    apply fnd_val_mem_of_sa. exact (HFR j r Hr).
- cbn. tauto.
- split; [|split; exact I]. cbn [f_atoms atoms_ok]. split; [|exact I].
  unfold afact_ok, fnd_spF. cbn [af_lo af_hi af_al2]. rewrite Usp.
  change (2 ^ 4) with 16. split; [lia|]. split; [|lia]. rewrite Zminus_mod, Hal16. reflexivity.
Qed.

Lemma fnd_epi : forall v regs1 mem1 md1, fnd_cut regs1 mem1 md1 -> getr regs1 10 = w64 v ->
v = seg_spec.find_ptr c rcs nm ->
SRr SEGS W (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + FND_EPI)) mem1 (seg_rom SEGS)) md1) fnd_Q.
Proof using B ASTRCMP TL LAWS RUN RUNTO BR RET ly S W regs mem md c name rcs nm HPRE HROD H10 H11 HQP.
intros v regs1 mem1 md1 (HJ & HK & HFR & R2 & R3 & R4 & R22 & R23 & R24 & R25 & R26 & R27) R10 Hv.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & HQT).
pose proof fnd_sp as (Hal16 & Hlo & Hhi).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). assert (HST : FSTK = 8256) by reflexivity.
destruct (fnd_epi_seed regs1 mem1 R2 HFR) as [HS SHOK].
assert (HEI : img_env VAL A_LIM (Eimg (Ereg regs1 fnd_e_extra))) by apply Eimg_env.
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (Eimg (Ereg regs1 fnd_e_extra)) n = getr regs1 r)
  by (intros n r Hn; apply ew_Eimg_Ereg_nat; exact Hn).
assert (EX : forall j r, nth_error fnd_saved j = Some r ->
  ew (Eimg (Ereg regs1 fnd_e_extra)) (32 + j) = getr regs (Z_to_bv 5 r)).
{ intros j r Hr. assert (Hj : (j < 7)%nat)
    by (change 7%nat with (length fnd_saved); apply (proj1 (nth_error_Some fnd_saved j)); rewrite Hr; discriminate).
  rewrite Eimg_low by (unfold A_TEXT; lia). rewrite ew_Ereg_extra. exact (fnd_e_nth j r Hr). }
assert (Usp : bv_unsigned (ew (Eimg (Ereg regs1 fnd_e_extra)) 2) = spZ regs - 64).
{ rewrite (EE 2%nat 2%bv eq_refl), R2. unfold w64. apply unsigned_lit_small. lia. }
pose proof (EX 0%nat 1 eq_refl) as E32. pose proof (EX 1%nat 8 eq_refl) as E33. pose proof (EX 2%nat 9 eq_refl) as E34.
pose proof (EX 3%nat 18 eq_refl) as E35. pose proof (EX 4%nat 19 eq_refl) as E36. pose proof (EX 5%nat 20 eq_refl) as E37.
pose proof (EX 6%nat 21 eq_refl) as E38.
cbn [Nat.add] in E32, E33, E34, E35, E36, E37, E38.
pose proof (EE 3%nat 3%bv eq_refl) as E3. pose proof (EE 4%nat 4%bv eq_refl) as E4.
pose proof (EE 10%nat 10%bv eq_refl) as E10v.
pose proof (EE 22%nat 22%bv eq_refl) as E22. pose proof (EE 23%nat 23%bv eq_refl) as E23.
pose proof (EE 24%nat 24%bv eq_refl) as E24. pose proof (EE 25%nat 25%bv eq_refl) as E25.
pose proof (EE 26%nat 26%bv eq_refl) as E26. pose proof (EE 27%nat 27%bv eq_refl) as E27.
clear EX.
remember (Eimg (Ereg regs1 fnd_e_extra)) as E eqn:HE. clear HE.
paj_run_tok RUN HS HJ SHOK Bspan.
{ awr_ok_tac; exact Usp. }
fnd_md.
fnd_keep_empty HFr KEEP (spZ regs - FSTK) (spZ regs). clear HF HFr HG.
prreg HS (1%bv : bv 5) F1. prreg HS (10%bv : bv 5) F10.
eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros mat'. unfold fnd_Q, apost_base.
lazymatch goal with |- exists _ _ _ _ _, mkCfg (mkst ?r _ ?m _) ?d = _ /\ _ => exists ly, S, r, m, d end.
split.
{ rewrite F1, E32. change (getr regs (Z_to_bv 5 1)) with (getr regs 1).
  unfold YK0s.ret_ok in Hra. rewrite Hra. reflexivity. }
split.
{ apply (ajournal_materialize SEGS B LAWS pa_segs_low). exact HJ. }
split.
{ unfold aregs_preserved. intros r Hr.
  assert (Hcases : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/
    r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by (unfold acallee_saved in Hr; lia).
  clear Hr.
  repeat (destruct Hcases as [-> | Hcases]); [..| subst r];
  rewrite (st_ok_pi_restrict_reg (w_H W) E _ _ _ HS); cbn [ms_regs];
  lazymatch goal with |- sv_denot _ (sr_get ?a ?rr2) = _ =>
    let v2 := eval vm_compute in (sr_get a rr2) in change (sr_get a rr2) with v2 end;
  cbn [sv_denot];
  first
  [ rewrite Usp; replace (spZ regs - 64 + 64) with (spZ regs) by lia; unfold spZ; rewrite Z_to_bv_bv_unsigned; reflexivity
  | rewrite Z.add_0_r, Z_to_bv_bv_unsigned;
    first [ rewrite E3, R3; reflexivity | rewrite E4, R4; reflexivity
          | rewrite E33; reflexivity | rewrite E34; reflexivity | rewrite E35; reflexivity
          | rewrite E36; reflexivity | rewrite E37; reflexivity | rewrite E38; reflexivity
          | rewrite E22, R22; reflexivity | rewrite E23, R23; reflexivity | rewrite E24, R24; reflexivity
          | rewrite E25, R25; reflexivity | rewrite E26, R26; reflexivity | rewrite E27, R27; reflexivity ] ]. }
split; [rewrite F10, E10v, R10, Hv; reflexivity|].
split.
{ unfold sa_kept. cbn [ms_mem]. intros a Ha Hn _.
  etransitivity; [apply KEEP; [exact Ha | tauto] | apply HK; [exact Ha | exact Hn]]. }
unfold sa_noalloc. split; [apply Permutation_refl|]. split; [reflexivity|]. exists (st_fs S). destruct S; reflexivity.
Qed.

(* ------------------------------- the loop head 0x89b08 ------------------------------- *)
Definition fnd_LH (k : nat) (regs1 : bvmap 5 word) (mem1 : word -> option byte) (md1 : Model) : Prop :=
fnd_cut regs1 mem1 md1 /\ (k < length (rc_seg rcs))%nat /\
r_find rcs nm = r_find_go (skipn k (rc_seg rcs)) nm k /\
getr regs1 8 = w64 (c + 356 * Z.of_nat k) /\ getr regs1 9 = w64 name /\
getr regs1 18 = w64 (356 * Z.of_nat k) /\ getr regs1 19 = w64 (2 ^ 64 - 1 - c) /\
getr regs1 20 = w64 (fnd_N - Z.of_nat k) /\ getr regs1 21 = w64 (32 - Z.of_nat k).

Lemma fnd_step : forall k regs1 mem1 md1,
((Datatypes.S k < length (rc_seg rcs))%nat -> forall r m d, fnd_LH (Datatypes.S k) r m d ->
  SRr SEGS W (mkCfg (mkst r (Z_to_bv 64 (BASE + FND_LH)) m (seg_rom SEGS)) d) fnd_Q) ->
fnd_LH k regs1 mem1 md1 ->
SRr SEGS W (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + FND_LH)) mem1 (seg_rom SEGS)) md1) fnd_Q.
Proof using B ASTRCMP TL LAWS RUN RUNTO BR RET ly S W regs mem md c name rcs nm HPRE HROD H10 H11 HQP.
intros k regs1 mem1 md1 NXT (HCUT & Hk & RF & R8 & R9 & R18 & R19 & R20 & R21).
pose proof HCUT as (HJ & HK & HFR & R2 & R3 & R4 & R22 & R23 & R24 & R25 & R26 & R27).
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & HQT).
pose proof fnd_sp as (Hal16 & Hslo & Hshi). pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HST : FSTK = 8256) by reflexivity. assert (Hes : ESTACK = 4096) by reflexivity.
pose proof fnd_cb as (Hc4096 & Hcceil & Hcoff & b & m & Hin & Hb & Hbm).
pose proof fnd_nfacts as [HNr HNval].
pose proof fnd_nmfacts as (Hnm1 & Hnmc & Hnm63 & Hnm32 & HNMZ & HNMT & HNMA).
assert (HkZ : 0 <= Z.of_nat k < fnd_N) by (unfold fnd_N; lia).
destruct (fnd_segname k Hk) as (SX & Hlen & TX & AX).
destruct (fnd_zrange k Hk) as [Rs Ns]. pose proof fnd_nmrange as [Rn Nn].
set (s1 := rs_name (r_seg rcs k)) in *.
assert (Usp1 : spZ regs1 = spZ regs - 64) by (unfold spZ at 1; rewrite R2; unfold w64; apply unsigned_lit_small; lia).
assert (Usp1m : spZ regs1 mod 16 = 0) by (rewrite Usp1, Zminus_mod, Hal16; reflexivity).
destruct (fnd_lh_seed B W regs1 mem1 ltac:(lia) Usp1m) as [HS SHOK].
assert (HEI : img_env VAL A_LIM (Eimg (Ereg regs1 [w64 SB]))) by apply Eimg_env.
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (Eimg (Ereg regs1 [w64 SB])) n = getr regs1 r)
  by (intros n r Hn; apply ew_Eimg_Ereg_nat; exact Hn).
pose proof (EE 2%nat 2%bv eq_refl) as E2. pose proof (EE 3%nat 3%bv eq_refl) as E3.
pose proof (EE 4%nat 4%bv eq_refl) as E4. pose proof (EE 8%nat 8%bv eq_refl) as E8.
pose proof (EE 9%nat 9%bv eq_refl) as E9. pose proof (EE 18%nat 18%bv eq_refl) as E18.
pose proof (EE 19%nat 19%bv eq_refl) as E19. pose proof (EE 20%nat 20%bv eq_refl) as E20.
pose proof (EE 21%nat 21%bv eq_refl) as E21. pose proof (EE 22%nat 22%bv eq_refl) as E22.
pose proof (EE 23%nat 23%bv eq_refl) as E23. pose proof (EE 24%nat 24%bv eq_refl) as E24.
pose proof (EE 25%nat 25%bv eq_refl) as E25. pose proof (EE 26%nat 26%bv eq_refl) as E26.
pose proof (EE 27%nat 27%bv eq_refl) as E27.
remember (Eimg (Ereg regs1 [w64 SB])) as E eqn:HE. clear HE.
assert (E2v : ew E 2 = w64 (spZ regs - 64)) by (rewrite E2; exact R2).
assert (E8v : ew E 8 = w64 (c + 356 * Z.of_nat k)) by (rewrite E8; exact R8).
assert (E9v : ew E 9 = w64 name) by (rewrite E9; exact R9).
assert (E18v : ew E 18 = w64 (356 * Z.of_nat k)) by (rewrite E18; exact R18).
assert (E19v : ew E 19 = w64 (2 ^ 64 - 1 - c)) by (rewrite E19; exact R19).
assert (E20v : ew E 20 = w64 (fnd_N - Z.of_nat k)) by (rewrite E20; exact R20).
assert (E21v : ew E 21 = w64 (32 - Z.of_nat k)) by (rewrite E21; exact R21).
assert (Usp : bv_unsigned (ew E 2) = spZ regs - 64) by (rewrite E2v; unfold w64; apply unsigned_lit_small; lia).
(* 0x89b08 beqz s5 -> the UBSan trap: 32 - k <> 0 because k < n <= 32 *)
psrr_branch_tok RUN BR HS SHOK Bspan.
{ exfalso. rewrite branch_eq_U, (U_atom E 21 (32 - Z.of_nat k) E21v), U_SLit, (zcanon_small 0) in Hc by lia.
  apply Z.eqb_eq in Hc. lia. }
clear Hc.
(* 0x89b0c bltu s3,s2 -> the UBSan trap: c + 356 k does not wrap *)
paj_run_tok RUN HS HJ SHOK Bspan.
{ awr_ok_tac; exact Usp. }
fnd_md.
fnd_keep_empty HFr KEEP0 (spZ regs - FSTK) (spZ regs - 64). clear HF HFr HG.
psrr_branch_tok RUN BR HS SHOK Bspan.
{ exfalso. rewrite branch_ltu_U, (U_atom E 19 (2 ^ 64 - 1 - c) E19v), (U_atom E 18 (356 * Z.of_nat k) E18v) in Hc by lia.
  apply Z.ltb_lt in Hc. lia. }
clear Hc.
(* 0x89b10 .. 0x89b18: a0 = c + 356 k, a1 = name, the call of the strcmp wrapper *)
paj_run_tok RUN HS HJ SHOK Bspan.
{ awr_ok_tac; exact Usp. }
fnd_md.
fnd_keep_empty HFr KEEP1 (spZ regs - FSTK) (spZ regs - 64). clear HF HFr HG.
pmkst HS.
prreg HS (1%bv : bv 5) P1. prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
prreg HS (10%bv : bv 5) P10. prreg HS (11%bv : bv 5) P11.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rT _ ?mT _) _) _ => set (rT0 := rT) in *; set (mT0 := mT) in * end.
assert (KEEP01 : kept_out (rdW W mem1) (rdW W mT0) (spZ regs - FSTK) (spZ regs - 64))
  by (apply (kept_out_trans _ _ _ _ _ _ _ KEEP0 KEEP1); lia).
assert (KEEPc : kept_out (rdW W mem) (rdW W mT0) (spZ regs - FSTK) (spZ regs))
  by (apply (kept_out_trans _ _ _ _ _ _ _ HK KEEP01); lia).
assert (HspT : spZ rT0 = spZ regs + -64)
  by (unfold spZ at 1; rewrite P2, E2v; unfold w64; rewrite unsigned_lit_small; lia).
assert (HspT' : spZ rT0 = spZ regs - 64) by lia.
assert (P3' : getr rT0 3 = w64 (as_gp B)) by (rewrite P3, E3, R3; exact Hgp).
assert (P4' : getr rT0 4 = w64 (as_tp B)) by (rewrite P4, E4, R4; exact Htp).
assert (HraT : YK0s.ret_ok (getr rT0 1)) by (rewrite P1; apply ret_ok_codeptr_v; [lia | reflexivity]).
assert (P10' : getr rT0 10 = w64 (c + 356 * Z.of_nat k)) by (rewrite P10, E8v; reflexivity).
assert (P11' : getr rT0 11 = w64 name) by (rewrite P11, E9v; reflexivity).
destruct (fnd_str_call B W mem mT0 rT0 (spZ regs - FSTK) (spZ regs) (c + 356 * Z.of_nat k) s1
  SX TX AX ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) KEEPc) as (STRa & RDa & TLa).
destruct (fnd_str_call B W mem mT0 rT0 (spZ regs - FSTK) (spZ regs) name nm
  HNMZ HNMT HNMA ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) KEEPc) as (STRb & RDb & TLb).
eapply SRr_bind.
{ eapply (aj_art_at SEGS B LAWS pa_segs_low (pal_env B TL) (2 * ESTACK) (fun _ => False)
    (SIG SS___interceptor_trampoline_strcmp)
    W rT0 mT0 FSTK (spZ regs) [] ly S W mem md [] ly S _ 0 (-64) (Z_to_bv 64 (BASE + FND_RA)) _ HJ HspT eq_refl
    ltac:(lia) ltac:(lia) ltac:(rewrite HST, Hes; lia) P1 (fun a0 (H : False) => False_ind _ H)).
  apply (ASTRCMP fx ly S W rT0 mT0 _ (c + 356 * Z.of_nat k) name (seg_spec.zb s1) (seg_spec.zb nm)).
  - exact (ecall_pre_stk_at SEGS B (2 * ESTACK) FSTK (spZ regs) [] ly S W mem md [] ly S W mT0 _ 0 rT0 (-64)
      HJ HspT eq_refl ltac:(lia) ltac:(rewrite Hes; lia) ltac:(rewrite HST, Hes; lia) HraT P3' P4').
  - exact P10'. - exact P11'. - lia. - lia.
  - exact STRa. - exact STRb. - exact RDa. - exact RDb. - exact TLa. - exact TLb.
  - exact (fnd_rom_at B SegInstB.RLO_A SegInstB.RHI_A W mem mT0 (spZ regs - FSTK) (spZ regs) HROD KEEPc
      ltac:(unfold kImgEnd; lia)). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & HQ2 & HK2).
(* back at 0x89b1c *)
jafter_call_keep_pi HS 48%nat regs2 (mrestrict (w_H W) mem2) HP2 (@nil nat) HS2.
match type of HS2 with ?t -> _ => assert (HRK : t); [|specialize (HS2 HRK); clear HRK] end.
{ apply Forall_nil. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
assert (A52 : ew (havoc E 48 (map (getr regs2) CLOB)) 52 = getr regs2 10) by reflexivity.
remember (havoc E 48 (map (getr regs2) CLOB)) as Ec eqn:HEc.
assert (HEI3 : img_env VAL A_LIM Ec) by (rewrite HEc; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLD3 : forall n, (n < 48)%nat -> ew Ec n = ew E n) by (intros n Hn; rewrite HEc; apply YN3v.ew_havoc_old; exact Hn).
clear HEc.
assert (Usp3 : bv_unsigned (ew Ec 2) = spZ regs - 64) by (rewrite OLD3 by lia; exact Usp).
assert (SHOK3 : sh_ok SEGS fnd_Bx [] Ec (mrestrict (w_H W) mem2)) by apply Forall_nil.
assert (KEEPk : kept_out (rdW W mT0) (rdW W mem2) (spZ regs - FSTK) (spZ regs - 64))
  by (intros x0 Hx0 Hn0; apply HK2; [exact Hx0 | lia | tauto]).
clear HK2. clear HJ. rename HJ2 into HJ.
assert (KEEPm : kept_out (rdW W mem1) (rdW W mem2) (spZ regs - FSTK) (spZ regs - 64))
  by (apply (kept_out_trans _ _ _ _ _ _ _ KEEP01 KEEPk); lia).
clear KEEP0 KEEP1 KEEP01 KEEPk KEEPc.
(* the model answer of the call *)
pose proof (seg_query_facts.sq_find_go_step (rc_seg rcs) nm k Hk) as RSTEP.
change (rs_name (nth k (rc_seg rcs) rseg_d)) with s1 in RSTEP.
rewrite RSTEP in RF. clear RSTEP.
(* 0x89b1c beqz a0 *)
psrr_branch_tok RUN BR HS SHOK3 Bspan.
- (* the entry's name is nm: the answer is &c->seg[k] *)
  assert (Hz : getr regs2 10 = w64 0).
  { rewrite branch_eq_U in Hc. apply Z.eqb_eq in Hc. unfold U in Hc. apply bv_eq in Hc.
    cbn [sv_denot] in Hc. rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned in Hc. rewrite A52 in Hc. exact Hc. }
  assert (HEQ : seg_spec.zb s1 = seg_spec.zb nm) by (apply HQ2; exact Hz).
  assert (HC0 : SegModel.strcmp s1 nm = 0) by (apply (fnd_zb_eq s1 nm Rs Rn Ns Nn); exact HEQ).
  rewrite HC0, Z.eqb_refl in RF.
  paj_run_to_tok RUNTO HS HJ SHOK3 Bspan FND_EPI.
  { awr_ok_tac; exact Usp3. }
  fnd_md.
  fnd_keep_empty HFr KEEP3 (spZ regs - FSTK) (spZ regs - 64). clear HF HFr HG.
  pmkst HS.
  prreg HS (2%bv : bv 5) F2. prreg HS (3%bv : bv 5) F3. prreg HS (4%bv : bv 5) F4. prreg HS (10%bv : bv 5) F10.
  prreg HS (22%bv : bv 5) G22. prreg HS (23%bv : bv 5) G23. prreg HS (24%bv : bv 5) G24.
  prreg HS (25%bv : bv 5) G25. prreg HS (26%bv : bv 5) G26. prreg HS (27%bv : bv 5) G27.
  lazymatch goal with |- SRr _ _ (mkCfg (mkst _ _ ?mF _) _) _ =>
    assert (KEEP : kept_out (rdW W mem1) (rdW W mF) (spZ regs - FSTK) (spZ regs - 64))
      by (apply (kept_out_trans _ _ _ _ _ _ _ KEEPm KEEP3); lia) end.
  apply (fnd_epi (c + 356 * Z.of_nat k)).
  + apply (fnd_cut_kept regs1 mem1 md1 _ _ _ _ _ HCUT HJ KEEP); [lia | lia
      | rewrite F2, OLD3, E2 by lia; reflexivity | rewrite F3, OLD3, E3 by lia; reflexivity
      | rewrite F4, OLD3, E4 by lia; reflexivity
      | rewrite G22, OLD3, E22 by lia; reflexivity | rewrite G23, OLD3, E23 by lia; reflexivity
      | rewrite G24, OLD3, E24 by lia; reflexivity | rewrite G25, OLD3, E25 by lia; reflexivity
      | rewrite G26, OLD3, E26 by lia; reflexivity | rewrite G27, OLD3, E27 by lia; reflexivity].
  + rewrite F10, OLD3, E8v by lia. reflexivity.
  + unfold seg_spec.find_ptr. rewrite RF. unfold seg_spec.rseg_addr, seg_spec.RSEG_SIZE. reflexivity.
- (* the entry's name is not nm *)
  assert (Hz : getr regs2 10 <> w64 0).
  { intros Heq. rewrite branch_eq_U in Hc. apply Z.eqb_neq in Hc. apply Hc. unfold U. f_equal.
    cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned, A52, Heq. reflexivity. }
  assert (HNE : SegModel.strcmp s1 nm <> 0).
  { intros Heq. apply Hz. apply HQ2. apply (fnd_zb_eq s1 nm Rs Rn Ns Nn). exact Heq. }
  replace (SegModel.strcmp s1 nm =? 0) with false in RF by (symmetry; apply Z.eqb_neq; exact HNE).
  clear Hc.
  (* 0x89b20 .. 0x89b30: s4 -= 1, s0 += 356, s2 += 356, s5 -= 1, bnez s4 *)
  paj_run_tok RUN HS HJ SHOK3 Bspan.
  { awr_ok_tac; exact Usp3. }
  fnd_md.
  fnd_keep_empty HFr KEEP3 (spZ regs - FSTK) (spZ regs - 64). clear HF HFr HG.
  assert (E20c : ew Ec 20 = w64 (fnd_N - Z.of_nat k)) by (rewrite OLD3 by lia; exact E20v).
  psrr_branch_tok RUN BR HS SHOK3 Bspan.
  + (* entries left: back to the loop head with k + 1 *)
    assert (HkS : (Datatypes.S k < length (rc_seg rcs))%nat).
    { rewrite branch_ne_U, (U_atom_off Ec 20 (fnd_N - Z.of_nat k) (-1) E20c) in Hc by lia.
      rewrite U_SLit, (zcanon_small 0) in Hc by lia. apply negb_true_iff, Z.eqb_neq in Hc.
      unfold fnd_N in Hc. lia. }
    paj_run_to_tok RUNTO HS HJ SHOK3 Bspan FND_LH.
    { awr_ok_tac; exact Usp3. }
    fnd_md.
    fnd_keep_empty HFr KEEP4 (spZ regs - FSTK) (spZ regs - 64). clear HF HFr HG.
    pmkst HS.
    prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4. prreg HS (8%bv : bv 5) Q8.
    prreg HS (9%bv : bv 5) Q9. prreg HS (18%bv : bv 5) Q18. prreg HS (19%bv : bv 5) Q19.
    prreg HS (20%bv : bv 5) Q20. prreg HS (21%bv : bv 5) Q21.
    prreg HS (22%bv : bv 5) Q22. prreg HS (23%bv : bv 5) Q23. prreg HS (24%bv : bv 5) Q24.
    prreg HS (25%bv : bv 5) Q25. prreg HS (26%bv : bv 5) Q26. prreg HS (27%bv : bv 5) Q27.
    rewrite ?OLD3 in Q2, Q3, Q4, Q8, Q9, Q18, Q19, Q20, Q21, Q22, Q23, Q24, Q25, Q26, Q27 by lia.
    lazymatch goal with |- SRr _ _ (mkCfg (mkst _ _ ?mF _) _) _ =>
      assert (KEEP : kept_out (rdW W mem1) (rdW W mF) (spZ regs - FSTK) (spZ regs - 64))
        by (apply (kept_out_trans _ _ _ _ _ _ _ (kept_out_trans _ _ _ _ _ _ _ KEEPm KEEP3 ltac:(lia) ltac:(lia)) KEEP4); lia) end.
    apply NXT; [exact HkS|]. split; [|split; [exact HkS|]].
    { apply (fnd_cut_kept regs1 mem1 md1 _ _ _ _ _ HCUT HJ KEEP); [lia | lia
        | rewrite Q2, E2; reflexivity | rewrite Q3, E3; reflexivity | rewrite Q4, E4; reflexivity
        | rewrite Q22, E22; reflexivity | rewrite Q23, E23; reflexivity | rewrite Q24, E24; reflexivity
        | rewrite Q25, E25; reflexivity | rewrite Q26, E26; reflexivity | rewrite Q27, E27; reflexivity]. }
    split; [exact RF|].
    split; [rewrite Q8, E8v; unfold w64; rewrite unsigned_lit_small by lia; f_equal; lia|].
    split; [rewrite Q9, E9v; reflexivity|].
    split; [rewrite Q18, E18v; unfold w64; rewrite unsigned_lit_small by lia; f_equal; lia|].
    split; [rewrite Q19, E19v; reflexivity|].
    split; [rewrite Q20, E20v; unfold w64; rewrite unsigned_lit_small by lia; f_equal; lia|].
    rewrite Q21, E21v; unfold w64; rewrite unsigned_lit_small by lia; f_equal; lia.
  + (* that was the last entry: the answer is NULL *)
    assert (HkS : Datatypes.S k = length (rc_seg rcs)).
    { rewrite branch_ne_U, (U_atom_off Ec 20 (fnd_N - Z.of_nat k) (-1) E20c) in Hc by lia.
      rewrite U_SLit, (zcanon_small 0) in Hc by lia. apply negb_false_iff, Z.eqb_eq in Hc.
      unfold fnd_N in Hc. lia. }
    rewrite HkS, seg_query_facts.sq_find_go_end in RF.
    paj_run_to_tok RUNTO HS HJ SHOK3 Bspan FND_EPI.
    { awr_ok_tac; exact Usp3. }
    fnd_md.
    fnd_keep_empty HFr KEEP4 (spZ regs - FSTK) (spZ regs - 64). clear HF HFr HG.
    pmkst HS.
    prreg HS (2%bv : bv 5) F2. prreg HS (3%bv : bv 5) F3. prreg HS (4%bv : bv 5) F4. prreg HS (10%bv : bv 5) F10.
    prreg HS (22%bv : bv 5) G22. prreg HS (23%bv : bv 5) G23. prreg HS (24%bv : bv 5) G24.
    prreg HS (25%bv : bv 5) G25. prreg HS (26%bv : bv 5) G26. prreg HS (27%bv : bv 5) G27.
    rewrite ?OLD3 in F2, F3, F4, G22, G23, G24, G25, G26, G27 by lia.
    lazymatch goal with |- SRr _ _ (mkCfg (mkst _ _ ?mF _) _) _ =>
      assert (KEEP : kept_out (rdW W mem1) (rdW W mF) (spZ regs - FSTK) (spZ regs - 64))
        by (apply (kept_out_trans _ _ _ _ _ _ _ (kept_out_trans _ _ _ _ _ _ _ KEEPm KEEP3 ltac:(lia) ltac:(lia)) KEEP4); lia) end.
    apply (fnd_epi 0).
    * apply (fnd_cut_kept regs1 mem1 md1 _ _ _ _ _ HCUT HJ KEEP); [lia | lia
        | rewrite F2, E2; reflexivity | rewrite F3, E3; reflexivity | rewrite F4, E4; reflexivity
        | rewrite G22, E22; reflexivity | rewrite G23, E23; reflexivity | rewrite G24, E24; reflexivity
        | rewrite G25, E25; reflexivity | rewrite G26, E26; reflexivity | rewrite G27, E27; reflexivity].
    * exact F10.
    * unfold seg_spec.find_ptr. rewrite RF. reflexivity.
Qed.

Lemma fnd_loop : forall dd k regs1 mem1 md1, (k + Datatypes.S dd = length (rc_seg rcs))%nat ->
  fnd_LH k regs1 mem1 md1 ->
  SRr SEGS W (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + FND_LH)) mem1 (seg_rom SEGS)) md1) fnd_Q.
Proof using B ASTRCMP TL LAWS RUN RUNTO BR RET ly S W regs mem md c name rcs nm HPRE HROD H10 H11 HQP.
induction dd as [|dd IH]; intros k regs1 mem1 md1 Hd HLH.
- apply (fnd_step k regs1 mem1 md1); [intros Hk2; lia | exact HLH].
- apply (fnd_step k regs1 mem1 md1); [|exact HLH].
  intros _ r m d HLH2. apply (IH (Datatypes.S k) r m d); [lia | exact HLH2].
Qed.

(* ------------------------------- the entry 0x89a84 .. 0x89aec ------------------------------- *)
Lemma fnd_entry : SRr SEGS W (cfg_at SEGS (BASE + AF_reac_segconf_find) regs mem md) fnd_Q.
Proof using B ASTRCMP TL LAWS RUN RUNTO BR RET ly S W regs mem md c name rcs nm HPRE HROD H10 H11 HQP.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & HQT).
pose proof fnd_sp as (Hal16 & Hslo & Hshi). pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HST : FSTK = 8256) by reflexivity.
pose proof fnd_cb as (Hc4096 & Hcceil & Hcoff & b & m & Hin & Hb & Hbm).
pose proof fnd_nfacts as [HNr HNval].
pose proof fnd_nmfacts as (Hnm1 & Hnmc & Hnm63 & Hnm32 & HNMZ & HNMT & HNMA).
destruct HQP as (Hc0 & Hc16 & _).
destruct (fnd_entry_seed B TL W ly S regs mem md c name fnd_N HPRE H10 H11 ltac:(lia) ltac:(lia) Hc16 Hcoff
  ltac:(lia) HNval ltac:(lia)) as [HS SHOK].
pose proof (ajournal_init_na SEGS B FSTK [] ly S W regs mem md HPRE) as HJ.
assert (HEI : img_env VAL A_LIM (Eimg (Ereg regs (fnd_extra0 fnd_N)))) by apply Eimg_env.
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (Eimg (Ereg regs (fnd_extra0 fnd_N))) n = getr regs r)
  by (intros n r Hn; apply ew_Eimg_Ereg_nat; exact Hn).
assert (E32 : ew (Eimg (Ereg regs (fnd_extra0 fnd_N))) 32 = w64 SB)
  by (rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew (Eimg (Ereg regs (fnd_extra0 fnd_N))) 33 = w64 fnd_N)
  by (rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
remember (Eimg (Ereg regs (fnd_extra0 fnd_N))) as E eqn:HE. clear HE.
pose proof (EE 2%nat 2%bv eq_refl) as E2. pose proof (EE 3%nat 3%bv eq_refl) as E3.
pose proof (EE 4%nat 4%bv eq_refl) as E4. pose proof (EE 10%nat 10%bv eq_refl) as E10e.
pose proof (EE 11%nat 11%bv eq_refl) as E11e.
pose proof (EE 22%nat 22%bv eq_refl) as E22. pose proof (EE 23%nat 23%bv eq_refl) as E23.
pose proof (EE 24%nat 24%bv eq_refl) as E24. pose proof (EE 25%nat 25%bv eq_refl) as E25.
pose proof (EE 26%nat 26%bv eq_refl) as E26. pose proof (EE 27%nat 27%bv eq_refl) as E27.
rewrite H10 in E10e. rewrite H11 in E11e.
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (UB : U E fnd_Bx = SHADOW_OFF)
  by (unfold fnd_Bx; rewrite (U_atom E 32 SB E32) by (unfold SB; lia); reflexivity).
unfold cfg_at. change (w64 (BASE + AF_reac_segconf_find)) with (Z_to_bv 64 (BASE + AF_reac_segconf_find)).
(* 0x89a84 .. 0x89aec: the frame, the three refuted arms, the shadow check of c->n, lw a0, blez a0 *)
paj_run_tok RUN HS HJ SHOK Bspan.
{ cbn [ms_mem mkst]. rewrite (U_atom_off E 10 c 11392 E10e) by lia.
  apply (obl_of_block SEGS B LAWS ly S W mem md E fnd_Bx _ 4 b m HAR Hin UB); lia. }
{ awr_ok_tac. exact Usp. }
fnd_md.
fnd_keep_win HFr KEEP0 (spZ regs - FSTK) (spZ regs) Usp. clear HF HFr HG.
(* the run left two fresh atoms (the GOT word and the shadow byte): carry the entry's atom facts *)
lazymatch goal with HSx : st_ok_pi _ _ ?En _ _ |- _ =>
  assert (HAG : forall nn, (nn < 1024)%nat -> ew En nn = ew E nn)
    by (intros nn Hnn; cbn [extK]; first [apply ew_havoc_old; lia | rewrite ?ew_ewset_other by lia; reflexivity]);
  assert (EE2 : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew En n = getr regs r)
    by (intros n r Hn; pose proof (bv_unsigned_in_range 5 r) as Hr5; change (bv_modulus 5) with 32 in Hr5;
        rewrite HAG by lia; exact (EE n r Hn));
  assert (K32 : ew En 32 = w64 SB) by (rewrite HAG by lia; exact E32);
  assert (K33 : ew En 33 = w64 fnd_N) by (rewrite HAG by lia; exact E33);
  assert (K10 : ew En 10 = w64 c) by (rewrite HAG by lia; exact E10e);
  assert (K11 : ew En 11 = w64 name) by (rewrite HAG by lia; exact E11e);
  assert (Usp2 : bv_unsigned (ew En 2) = spZ regs) by (rewrite (EE2 2%nat 2%bv eq_refl); reflexivity)
end.
psrr_branch_tok RUN BR HS SHOK Bspan.
- (* n = 0: the answer is NULL *)
  assert (HN0 : fnd_N = 0).
  { rewrite (fnd_bge0 _ 33 fnd_N K33) in Hc by lia. apply Z.leb_le in Hc. lia. }
  assert (HF0 : seg_spec.find_ptr c rcs nm = 0).
  { unfold seg_spec.find_ptr, r_find. destruct (rc_seg rcs) as [|e l] eqn:Eq; [reflexivity|].
    exfalso. unfold fnd_N in HN0. rewrite Eq in HN0. cbn [length] in HN0. lia. }
  paj_run_to_tok RUNTO HS HJ SHOK Bspan FND_EPI.
  { awr_ok_tac. exact Usp2. }
  fnd_md.
  fnd_keep_win HFr KEEP1 (spZ regs - FSTK) (spZ regs) Usp2. clear HF HFr HG.
  pmkst HS.
  lazymatch type of HS with st_ok_pi _ _ _ ?ssx (restrict _ ?msx) =>
    let r := eval vm_compute in (nth 0 (ss_mem ssx) (stack_region 0)) in
    pose proof (st_ok_pi_region_nth _ ssx (restrict _ msx) 0 r HS ltac:(vm_compute; reflexivity)) as HRg;
    cbn [ms_mem restrict] in HRg end.
  prreg HS (2%bv : bv 5) F2. prreg HS (3%bv : bv 5) F3. prreg HS (4%bv : bv 5) F4. prreg HS (10%bv : bv 5) F10.
  prreg HS (22%bv : bv 5) G22. prreg HS (23%bv : bv 5) G23. prreg HS (24%bv : bv 5) G24.
  prreg HS (25%bv : bv 5) G25. prreg HS (26%bv : bv 5) G26. prreg HS (27%bv : bv 5) G27.
  apply (fnd_epi 0); [|exact F10 | symmetry; exact HF0].
  split; [exact HJ|]. split; [apply (kept_out_trans _ _ _ _ _ _ _ KEEP0 KEEP1); lia|].
  split.
  { apply (fnd_frame_of_region _ _ _ _ HRg Usp2 EE2). intros j r Hr.
    do 7 (destruct j as [|j]; [cbn in Hr; injection Hr as <-; vm_compute; repeat first [left; reflexivity | right] |]).
    cbn in Hr; destruct j; discriminate Hr. }
  split; [rewrite F2, Usp; unfold spZ, w64; f_equal; lia|].
  split; [rewrite F3, E3; reflexivity|]. split; [rewrite F4, E4; reflexivity|].
  split; [rewrite G22, E22; reflexivity|]. split; [rewrite G23, E23; reflexivity|].
  split; [rewrite G24, E24; reflexivity|]. split; [rewrite G25, E25; reflexivity|].
  split; [rewrite G26, E26; reflexivity | rewrite G27, E27; reflexivity].
- (* n > 0: the loop, from k = 0 *)
  assert (HN0 : 0 < fnd_N).
  { rewrite (fnd_bge0 _ 33 fnd_N K33) in Hc by lia. apply Z.leb_gt in Hc. lia. }
  paj_run_to_tok RUNTO HS HJ SHOK Bspan FND_LH.
  { awr_ok_tac. exact Usp2. }
  fnd_md.
  fnd_keep_win HFr KEEP1 (spZ regs - FSTK) (spZ regs) Usp2. clear HF HFr HG.
  pmkst HS.
  lazymatch type of HS with st_ok_pi _ _ _ ?ssx (restrict _ ?msx) =>
    let r := eval vm_compute in (nth 0 (ss_mem ssx) (stack_region 0)) in
    pose proof (st_ok_pi_region_nth _ ssx (restrict _ msx) 0 r HS ltac:(vm_compute; reflexivity)) as HRg;
    cbn [ms_mem restrict] in HRg end.
  prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4. prreg HS (8%bv : bv 5) Q8.
  prreg HS (9%bv : bv 5) Q9. prreg HS (18%bv : bv 5) Q18. prreg HS (19%bv : bv 5) Q19.
  prreg HS (20%bv : bv 5) Q20. prreg HS (21%bv : bv 5) Q21.
  prreg HS (22%bv : bv 5) Q22. prreg HS (23%bv : bv 5) Q23. prreg HS (24%bv : bv 5) Q24.
  prreg HS (25%bv : bv 5) Q25. prreg HS (26%bv : bv 5) Q26. prreg HS (27%bv : bv 5) Q27.
  apply (fnd_loop (Z.to_nat fnd_N - 1)%nat 0%nat); [unfold fnd_N in *; lia|].
  split; [|split; [unfold fnd_N in HN0; lia|]].
  { split; [exact HJ|]. split; [apply (kept_out_trans _ _ _ _ _ _ _ KEEP0 KEEP1); lia|].
    split.
    { apply (fnd_frame_of_region _ _ _ _ HRg Usp2 EE2). intros j r Hr.
      do 7 (destruct j as [|j]; [cbn in Hr; injection Hr as <-; vm_compute; repeat first [left; reflexivity | right] |]).
      cbn in Hr; destruct j; discriminate Hr. }
    split; [rewrite Q2, Usp; unfold spZ, w64; f_equal; lia|].
    split; [rewrite Q3, E3; reflexivity|]. split; [rewrite Q4, E4; reflexivity|].
    split; [rewrite Q22, E22; reflexivity|]. split; [rewrite Q23, E23; reflexivity|].
    split; [rewrite Q24, E24; reflexivity|]. split; [rewrite Q25, E25; reflexivity|].
    split; [rewrite Q26, E26; reflexivity | rewrite Q27, E27; reflexivity]. }
  split; [reflexivity|].
  split; [rewrite Q8, E10e; unfold w64; f_equal; lia|].
  split; [rewrite Q9, E11e; reflexivity|].
  split; [rewrite Q18; unfold w64; f_equal; lia|].
  split; [rewrite Q19, E10e; apply fnd_xor_m1; lia|].
  split; [rewrite Q20, E33; unfold w64; rewrite fnd_s4 by lia; f_equal; lia|].
  rewrite Q21; unfold w64; f_equal; lia.
Qed.
End w.

Theorem reac_segconf_find_walk :
  reac_segconf_find_contract SEGS B (BASE + AF_reac_segconf_find) SegInstB.STK_reac_segconf_find SegInstB.RLO_A
    SegInstB.RHI_A.
Proof using B ASTRCMP TL LAWS RUN RUNTO BR RET.
unfold reac_segconf_find_contract.
intros ly S W regs mem md ch c name rcs nm HPRE0 HROD H10 _ H11 _ HQP _.
exact (fnd_entry ly S W regs mem md c name rcs nm
  (afn_pre_na_of SEGS B _ _ _ _ _ _ _ _ HPRE0) HROD H10 H11 HQP).
Qed.

End e.
End d.
End b.
