(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: proofs/cgif/cgif_file_fuzzer/lib/A/AC8j.v at c8557374ad2e (st_ok_region_nth, field_of_region, as pa_i_region_nth over a restricted state and pa_i_field) and proofs/reac-pw/fuzz_role/lib/Reusable/YCbq.v at a0d3fb0309b (aj_intrin_at, as pa_i_memset_at: at OSet on rsegs, its post adds same_io from the contract's same_but_materialized); the rest of the file is new: the block lemma pa_int7 of LLVMFuzzerTestOneInput's shape-7 Int pod block and its helpers. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_role/lib/A/RPgPropIntB.v, with its module paths and module names changed; 433 of its 516 lines of code are new or changed and 416 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_headamp/lib/A/HPgW6cTail.v, with its module paths and numbers changed; 517 of its 586 lines of code are new or changed and 447 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgW5Int.v at 3e85ad4cf5dd for
   reac-pw/fuzz_rate image A: the chained piece is rate's W8 instead of role's Int-7 pod, so there are four
   engine runs and three calls instead of two and one, the calls are __asan_memcpy as well as __asan_memset,
   the post is RtPgSteps.rts_post instead of a local copy, and the source of the two copies is the frame
   object e (which asks the frame / block separation of the kernel's AR_sep_law). *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/A/RtPgW8Core.v at 8f1d7a0a9084 for the same unit's
   image B (fuzz_rate.asan-ubsan): image B calls pod_write_ent (0x83cc4) where image A inlines it, so A's runs A and B
   and the two calls between them become run P and the call of pod_write_ent through its contract
   (lib/AU/PweSpec.v pod_write_ent_specX, RtPgStepsB.rtsb_pwe_at); the record copy's source is e62 at F + 0x210 in the
   class-4 frame; the post is RtPgStepsB.rtsb_post and the statement is RtPgBW8Kit.rbw8_core_stmt. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/AU/RtPgBW8Core.v at 6c65f5a5cf5c for
   reac-pw/fuzz_role's image B (fuzz_role.asan-ubsan): module paths fuzz_rate -> fuzz_role, the segments
   lib/AU/Img0.v rsegs; the prefix rbw8_ becomes w8_, RtPgMemB's rtmb_ becomes RPgMem's rm_ and RtPgStepsB's rtsb_
   becomes RPgSteps' / RPgStepsU's rl_; the pcs, the real-frame cells and the registers are role B's and the real
   frame is 0x200 bytes; run P also sets s8, s2 and s4, so three register facts are carried to the end instead of
   rate's one; RtPgBase's rt_block_bounds has no twin in role's lib/A/RPgBase.v, so its statement and proof
   (image-independent) are copied here as w8_block_bounds. *)
(* reac-pw/fuzz_role image B (fuzz_role.asan-ubsan, pinned sha256
   b255d4935da5af137a3967dbe33380ea43be8e78bfe05d1e356e0a2be8a69ff0; every address measured on the unstripped
   twin dc791783f32962615e18a5f5cffae758ba56eb5dc87f70913c3579b101b4406a): the walk piece "write + record" of
   LLVMFuzzerTestOneInput as ONE block, J 0x818d8 -> C 0x80b54 / CL 0x81ccc, built from the four engine runs of
   lib/AU/RPgW8Kit.v and the two calls between them. Proves no function (kind: segment lemma).

   THE CHAIN. w8_core takes the four runs as hypotheses (each proved in its own file), pod_write_ent's contract at
   0x82bac and the kernel's contract of __asan_memcpy at 0x5116c, and threads:
     run P -> pod_write_ent(pp, e62) -> run C -> (first) memcpy(&pp->ent[n_ent], e62, 104) -> run D.
   pod_write_ent's post keeps the callee-saved registers, every byte outside its writes pwe_E (the pod's bytes and
   the len cell) and its stack [R - T_pwe_STK, R), and gives the pod's bytes Model.enc_pod and the new len; the
   copy's post (the kernel's aintrin_realizes through RPgSteps.rl_intrin_at) keeps the journal at the same
   layout and state. The source of the copy is the frame object e62 at F + 0x210, whose shadow the frame's pattern
   (RPgW8Kit.w8_PJ, e62 in scope) gives and whose bytes lie apart from the first block (AR_sep_law); the
   destinations lie in the first block, writable because it is not among the journal's start blocks.

   THE RESULT. At the end the first block holds Model.enc_pod of the pod at pp + len, its length word is
   len + |enc_pod|, the frame's shadow is the prologue's pattern again (e62 out of scope), and, when `first` is
   set, pp->ent[kk] holds Layout.ent_mem of the pod and pp->n_ent is kk + 1. *)
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Pod Require Import Cursor Model Layout.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.A Require Import RPgBase RPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.AU Require Import Img0 PweSpec RPgMem RPgSteps RPgStepsU RPgW8Kit.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

(* ===================================== the frame's patterns ===================================== *)
Lemma w8_PJ_len : Z.of_nat (length w8_PJ) = 88.
Proof. vm_compute. reflexivity. Qed.
Lemma w8_P0_set : w8_P0 = rm_setn w8_PJ 66 13 0xf8.
Proof. unfold w8_P0, w8_PJ. rewrite rm_sh_e62_out. reflexivity. Qed.

(* ===================================== the piece's clobber list ===================================== *)
Definition w8_csb (z : Z) : bool :=
  (z =? 2) || (z =? 3) || (z =? 4) || (z =? 8) || (z =? 9) ||
  ((18 <=? z) && (z <=? 23)) || (z =? 25) || (z =? 27).
Lemma w8_csb_ok : forall z, w8_csb z = true -> acallee_saved z.
Proof.
intros z H. unfold w8_csb in H. unfold acallee_saved.
repeat rewrite Bool.orb_true_iff in H. rewrite Bool.andb_true_iff in H.
rewrite !Z.eqb_eq, !Z.leb_le in H. lia.
Qed.
(* s2 (x18), s4 (x20) and s8 (x24) are callee-saved: the two calls keep what run P put in them *)
Lemma w8_cs18 : acallee_saved (bv_unsigned (18%bv : bv 5)).
Proof. assert (E : bv_unsigned (18%bv : bv 5) = 18) by reflexivity. rewrite E. unfold acallee_saved. lia. Qed.
Lemma w8_cs20 : acallee_saved (bv_unsigned (20%bv : bv 5)).
Proof. assert (E : bv_unsigned (20%bv : bv 5) = 20) by reflexivity. rewrite E. unfold acallee_saved. lia. Qed.
Lemma w8_cs24 : acallee_saved (bv_unsigned (24%bv : bv 5)).
Proof. assert (E : bv_unsigned (24%bv : bv 5) = 24) by reflexivity. rewrite E. unfold acallee_saved. lia. Qed.
Lemma w8_outJ : forall r : bv 5, bv_unsigned r <> 0 -> ~ In r w8_clobJ ->
acallee_saved (bv_unsigned r) /\ ~ In r w8_clobP /\ ~ In r w8_clobC /\ ~ In r w8_clobC0 /\
~ In r w8_clobD /\ ~ In r rl_caller_saved.
Proof.
intros r Hr0 Hn.
assert (HB : forallb (fun c : bv 5 => existsb (fun d => bv_eqb d c) w8_clobJ || w8_csb (bv_unsigned c))
  nz_regs = true) by (vm_compute; reflexivity).
pose proof (proj1 (forallb_forall _ _) HB r (in_nz_regs r Hr0)) as Hq. cbn beta in Hq.
assert (HS : forallb (fun c : bv 5 => existsb (fun d => bv_eqb d c) w8_clobJ ||
  (negb (existsb (fun d => bv_eqb d c) w8_clobP) && negb (existsb (fun d => bv_eqb d c) w8_clobC) &&
   negb (existsb (fun d => bv_eqb d c) w8_clobC0) && negb (existsb (fun d => bv_eqb d c) w8_clobD) &&
   negb (existsb (fun d => bv_eqb d c) rl_caller_saved))) nz_regs = true) by (vm_compute; reflexivity).
pose proof (proj1 (forallb_forall _ _) HS r (in_nz_regs r Hr0)) as Hs. cbn beta in Hs.
assert (Hin : forall l, existsb (fun d => bv_eqb d r) l = false -> ~ In r l).
{ intros l Hb Hi. assert (Ht : existsb (fun d => bv_eqb d r) l = true)
    by (apply existsb_exists; exists r; split; [exact Hi | apply bv_eqb_refl]). rewrite Hb in Ht. discriminate. }
assert (Hne : existsb (fun d => bv_eqb d r) w8_clobJ = false).
{ destruct (existsb (fun d => bv_eqb d r) w8_clobJ) eqn:Hb; [|reflexivity].
  exfalso. apply existsb_exists in Hb as (c & Hc & Hb). apply bv_eqb_eq in Hb. subst c. exact (Hn Hc). }
rewrite Hne in Hq, Hs. cbn [orb] in Hq, Hs.
repeat (apply andb_prop in Hs as [Hs ?]).
split; [apply w8_csb_ok; exact Hq|].
repeat (split; [apply Hin; apply negb_true_iff; assumption|]).
apply Hin. apply negb_true_iff. assumption.
Qed.

(* the three registers run P sets and the rest of the piece keeps (s8 = the cursor, s2 = what is left, s4 = 1) *)
Definition w8_set3 (regs regs' : bvmap 5 word) : Prop :=
getr regs' 24 = getr regs 13 /\ getr regs' 18 = getr regs 6 /\ getr regs' 20 = w64 1.
Lemma w8_set3_step : forall (regs r1 r2 : bvmap 5 word) (clob : list (bv 5)),
w8_set3 regs r1 ->
(forall r : bv 5, bv_unsigned r <> 0 -> ~ In r clob -> getr r2 r = getr r1 r) ->
~ In (24%bv : bv 5) clob -> ~ In (18%bv : bv 5) clob -> ~ In (20%bv : bv 5) clob ->
w8_set3 regs r2.
Proof.
intros regs r1 r2 clob (H24 & H18 & H20) HK N24 N18 N20. unfold w8_set3.
split; [rewrite (HK (24%bv) ltac:(vm_compute; lia) N24); exact H24|].
split; [rewrite (HK (18%bv) ltac:(vm_compute; lia) N18); exact H18|].
rewrite (HK (20%bv) ltac:(vm_compute; lia) N20). exact H20.
Qed.
Lemma w8_set3_pres : forall (regs r1 r2 : bvmap 5 word),
w8_set3 regs r1 -> aregs_preserved r1 r2 -> w8_set3 regs r2.
Proof.
intros regs r1 r2 (H24 & H18 & H20) HP. unfold w8_set3.
split; [rewrite (w8_pres r1 r2 (24%bv) HP w8_cs24); exact H24|].
split; [rewrite (w8_pres r1 r2 (18%bv) HP w8_cs18); exact H18|].
rewrite (w8_pres r1 r2 (20%bv) HP w8_cs20). exact H20.
Qed.

(* ===================================== the frame and the first block ===================================== *)
Section g. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Hypothesis LAWS : AR_laws rsegs B.
(* lib/A/RPgBase.v has no twin of fuzz_rate's rt_block_bounds: its statement and proof, image-independent *)
Lemma w8_block_bounds : forall ly S W mem md p n, AR rsegs B ly S W mem md -> In (p, n) (ablocks B ly S) ->
0 < p /\ p mod 16 = 0 /\ p + n <= 2 ^ 63.
Proof.
intros ly S W mem md p n HAR Hin.
destruct (al_blocks _ _ LAWS ly S W mem md p n HAR Hin) as (H16 & H4096 & Hc & _).
pose proof (@YM05.alloc_ceiling_lt rc) as Hc0. unfold req_size in Hc.
destruct (Z.eqb_spec n 0); lia.
Qed.
(* the frame for locals is apart from the first block (the kernel's AR_sep_law) *)
Lemma w8_sep : forall ly S W mem md pp F pos,
AR rsegs B ly S W mem md -> In (pp, Layout.PP_SIZE) (ablocks B ly S) -> In (4, pos) (frames S) ->
F = frame_addr ly 4 pos -> pp + Layout.PP_SIZE <= F \/ F + 1024 <= pp.
Proof.
intros ly S W mem md pp F pos HAR Hb Hf ->.
pose proof (sep_block_frame rsegs B LAWS ly S W mem md pp Layout.PP_SIZE 4 pos HAR Hb Hf) as HD.
unfold zdisjoint in HD. cbn [fst snd] in HD.
change (req_size Layout.PP_SIZE) with Layout.PP_SIZE in HD.
change (fs_frame_bytes 4) with 1024 in HD. exact HD.
Qed.
(* the shadow hull of a range inside e62 lies in the frame's own 128 shadow bytes *)
Lemma w8_hull_e62 : forall (rd : reader) F o n, F mod 32 = 0 -> 0 <= F -> 0x210 <= o -> o + n <= 0x278 ->
0 < n -> (forall i, 0 <= i < 128 -> rd (shadow_addr F + i) <> None) -> shadow_hull_vis rd (F + o) n.
Proof.
intros rd F o n HF H0 Ho Hn Hn0 Hsh s Hs.
assert (E1 : forall c, 0 <= c -> shadow_addr (F + c) = shadow_addr F + c / 8).
{ intros c Hc. unfold shadow_addr.
  destruct (proj1 (Z.mod_divide F 32 ltac:(lia)) HF) as [q Hq]. rewrite Hq.
  replace (q * 32 + c) with (c + (4 * q) * 8) by lia. rewrite Z.div_add by lia.
  replace (q * 32) with ((4 * q) * 8) by lia. rewrite Z.div_mul by lia. lia. }
replace (F + o + n - 1) with (F + (o + n - 1)) in Hs by lia.
rewrite (E1 o) in Hs by lia. rewrite (E1 (o + n - 1)) in Hs by lia.
set (X := shadow_addr F) in *.
assert (A1 : 66 <= o / 8) by (apply Z.div_le_lower_bound; lia).
assert (A2 : (o + n - 1) / 8 < 79) by (apply Z.div_lt_upper_bound; lia).
pose proof (Z.div_mod (X + o / 8) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (X + o / 8) 8 ltac:(lia)).
pose proof (Z.div_mod (X + (o + n - 1) / 8) 8 ltac:(lia)).
pose proof (Z.mod_pos_bound (X + (o + n - 1) / 8) 8 ltac:(lia)).
replace s with (X + (s - X)) by lia. apply Hsh. lia.
Qed.
(* frame_addr reads only ly_F, which every journal's layout_le keeps *)
Lemma w8_lyF : forall n ly ly', layout_le n ly ly' ->
forall cid pos, frame_addr ly' cid pos = frame_addr ly cid pos.
Proof.
intros n ly ly' H cid pos. unfold frame_addr.
destruct H as (_ & _ & _ & _ & _ & HFF & _). rewrite HFF. reflexivity.
Qed.
Lemma w8_geo_step : forall STK sp0 own lyc ly1 R F pos nsec ly,
w8_geo STK sp0 own lyc R F pos -> layout_le nsec ly lyc -> layout_le nsec ly ly1 ->
w8_geo STK sp0 own ly1 R F pos.
Proof.
intros STK sp0 own lyc ly1 R F pos nsec ly (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8) Hc H1.
unfold w8_geo. repeat (split; [assumption|]). split; [|split; assumption].
rewrite (w8_lyF nsec ly ly1 H1 4 pos), <- (w8_lyF nsec ly lyc Hc 4 pos). exact G6.
Qed.
Lemma w8_F8 : forall F, F mod 32 = 0 -> F mod 8 = 0.
Proof.
intros F HF. destruct (proj1 (Z.mod_divide F 32 ltac:(lia)) HF) as [q Hq]. rewrite Hq.
replace (q * 32) with ((4 * q) * 8) by lia. apply Z_mod_mult.
Qed.
End g.

(* ===================================== the record copy =====================================
   RPgSteps.rl_intrin_at with the copy's obligations discharged once: the destination is inside the first block
   (writable because the block is not among the journal's start blocks, its shadow from the block), the source
   inside the frame object e62 (its shadow from the frame's pattern w8_PJ, its bytes present by the frame law). *)
Section ca. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Hypothesis LAWS : AR_laws rsegs B.

Lemma w8_cpy : forall pc raz STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
  (R pp F pos d x n : Z),
aintrin_realizes rsegs B OCpy pc ->
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
w8_geo STK sp0 own lyc R F pos ->
In (pp, Layout.PP_SIZE) (ablocks B lyc Sc) -> ~ In (pp, Layout.PP_SIZE) (ablocks B ly S) ->
getr regs 1 = w64 raz -> YK0s.ret_ok (w64 raz) ->
getr regs 2 = w64 R -> getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
getr regs 10 = w64 d -> getr regs 11 = w64 x -> getr regs 12 = w64 n ->
pp <= d -> d + n <= pp + Layout.PP_SIZE -> 0 <= n ->
F + 0x210 <= x -> x + n <= F + 0x278 -> rl_fsh rsegs (w_H W) memc F w8_PJ ->
SRr rsegs W (cfg_at rsegs pc regs memc mdc)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
  c2 = cfg_at rsegs raz regs2 mem2 md2 /\
  ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem2 md2 k /\
  same_io mdc md2 /\ aregs_preserved regs regs2 /\
  (forall i, 0 <= i < n -> aview rsegs (w_H W) mem2 (d + i) = aview rsegs (w_H W) memc (x + i)) /\
  (forall a, 0 <= a < 2 ^ 64 -> ~ (d <= a < d + n) -> ~ (R - ESTACK <= a < R) ->
     aview rsegs (w_H W) mem2 a = aview rsegs (w_H W) memc a)).
Proof using LAWS.
intros pc raz STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs R pp F pos d x n
  AI HJ HG Hpp Hfresh H1 Hret H2 H3 H4 H10 H11 H12 Hd1 Hd2 Hn0 Hx1 Hx2 Hfsh.
pose proof HG as (HR16 & HSTK & HRS & HRk & Hown & HF & HFapp & HF32).
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hsp0al & HSTK0 & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof alloc_ceiling_lt as Hc2.
assert (Hes : ESTACK = 4096) by reflexivity.
assert (Hrq : req_size Layout.PP_SIZE = Layout.PP_SIZE) by reflexivity.
assert (HPS : Layout.PP_SIZE = 19744) by reflexivity.
destruct (al_blocks _ _ LAWS _ _ _ _ _ pp Layout.PP_SIZE HAR Hpp) as (Hp16 & Hp4096 & Hpceil & Happ & Hppres & _).
rewrite Hrq, HPS in Hpceil, Hppres, Happ.
assert (Hin4 : In (4, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; left; exact Hown).
destruct (frames_bounds rsegs B LAWS lyc Sc W memc mdc 4 pos HAR Hin4) as (HF4096 & HFceil & _).
change (fs_frame_bytes 4) with 1024 in HF4096, HFceil. rewrite <- HF in HF4096, HFceil.
unfold T_SEG_STK, ASTACK in HSTK, HRk.
assert (HspR : spZ regs = R)
  by (unfold spZ; rewrite H2; unfold w64; apply unsigned_lit_small; unfold kHighMemBeg in HRk; lia).
assert (Hn32 : 0 <= n < 2 ^ 32) by (unfold Layout.PP_SIZE in *; lia).
destruct (al_frames _ _ LAWS lyc Sc W memc mdc 4 pos HAR Hin4) as (_ & _ & Hfb & Hfs).
change (fs_frame_bytes 4 / 8) with 128 in Hfs. change (fs_frame_bytes 4) with 1024 in Hfb.
rewrite <- HF in Hfs, Hfb.
pose proof (w8_sep B LAWS lyc Sc W memc mdc pp F pos HAR Hpp Hin4 HF) as Hsep. rewrite HPS in Hsep.
destruct (rl_fbounds F HF32 HFapp) as (_ & _ & _ & _ & _ & Hamrf).
eapply SRr_mono.
{ eapply (rl_intrin_at B LAWS OCpy pc AI W regs memc STK sp0 FP ly S W0 mem0 md0 own lyc Sc mdc k d x n
    (R - sp0) (w64 raz) HJ H10 H11 H12 Hn32).
  - lia.
  - destruct (w8_block_bounds B LAWS _ _ _ _ _ pp Layout.PP_SIZE HAR Hpp) as (_ & _ & Hb63).
    unfold Layout.PP_SIZE in *; lia.
  - rewrite HspR. lia.
  - rewrite Zminus_mod, HR16, Hsp0al. reflexivity.
  - lia.
  - rewrite Hes. lia.
  - exact H3.
  - exact H4.
  - exact H1.
  - exact Hret.
  - intros a Ha. split.
    + replace a with (pp + (a - pp)) by lia.
      apply (rl_fresh_awr _ _ _ _ _ _ _ pp Layout.PP_SIZE); [exact Hpp | exact Hfresh | rewrite Hrq, HPS; lia].
    + rewrite Hes. unfold kHighMemBeg in HRk. lia.
  - apply (amem_range_of_block rsegs B LAWS lyc Sc W memc mdc pp Layout.PP_SIZE); [exact HAR | exact Hpp | lia | rewrite Hrq, HPS; lia].
  - exact (proj1 (rm_blk_ra rsegs B lyc Sc W memc mdc pp Layout.PP_SIZE d n HAR Hpp ltac:(lia) ltac:(rewrite Hrq, HPS; lia))).
  - exact (proj2 (rm_blk_ra rsegs B lyc Sc W memc mdc pp Layout.PP_SIZE d n HAR Hpp ltac:(lia) ltac:(rewrite Hrq, HPS; lia))).
  - cbv iota.
    split; [lia|]. split; [lia|]. split.
    { intros a Ha. split.
      - apply (aview_some_of_apresent rsegs). exact (proj1 (Hfb a ltac:(lia))).
      - rewrite HspR, Hes. unfold kHighMemBeg in HRk. lia. }
    split; [lia|].
    split; [replace x with (F + (x - F)) by lia; apply Hamrf; lia|].
    split.
    { replace x with (F + RM_E62 + (x - F - 0x210)) by (unfold RM_E62; lia).
      apply (rm_B_ra_e62 rsegs _ _ F false false false false false false (x - F - 0x210) n);
      [exact Hfsh | apply (w8_F8 F); exact HF32 | lia | lia]. }
    { intros Hn. replace x with (F + (x - F)) by lia.
      apply (w8_hull_e62 _ F (x - F) n HF32 ltac:(lia) ltac:(lia) ltac:(lia) Hn).
      intros i Hi. apply (aview_some_of_apresent rsegs). exact (proj1 (Hfs i Hi)). } }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & Hc & HJ2 & HP & Hsame & _ & Heff & Hfr).
split; [reflexivity|]. exists regs2, mem2, md2.
split; [rewrite Hc; unfold cfg_at; reflexivity|].
split; [exact HJ2|]. split; [exact (same_io_materialized _ _ Hsame)|]. split; [exact HP|].
split; [exact Heff|].
intros a Ha Hn1 Hn2. apply (Hfr a Ha Hn1). lia.
Qed.
End ca.

Local Ltac w8_notin :=
  try unfold w8_clobP; try unfold w8_clobC; try unfold w8_clobC0; try unfold w8_clobD;
  try unfold w8_clobJ; try unfold rl_caller_saved;
  let H := fresh "H" in intros H; cbn [In] in H;
  repeat (destruct H as [H|H]; [apply (f_equal (@bv_unsigned 5)) in H; vm_compute in H; discriminate H|]);
  exact H.
Local Ltac w8_nz := vm_compute; lia.

(* ===================================== the piece as one block ===================================== *)
Section p. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis LAWS : AR_laws rsegs B.
Hypothesis AMEMCPY : aintrin_realizes rsegs B OCpy W8_CPY.
Hypothesis PWE : pod_write_ent_specX rsegs B MT W8_PWE.
Hypothesis RUNP : w8_runP_stmt B MT.
Hypothesis RUNC1 : w8_runC1_stmt B MT.
Hypothesis RUNC0 : w8_runC0_stmt B MT.
Hypothesis RUND : w8_runD_stmt B MT.

Lemma w8_core : w8_core_stmt B MT.
Proof using MTL LAWS AMEMCPY PWE RUNP RUNC1 RUNC0 RUND.
unfold w8_core_stmt.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs R pp F pos len cnt kk fsv ed
  HJ Hev HG Hpp Hfresh H2 H3 H4 H9 H15 H19 H22 H27
  Vd8 Ve0 Ve8 V120 V128 V138 V148 V150 V158 Vlen Vnent Hent Hfsh
  Hwf Hlen1 Hlen2 Hlen8 Hcnt Hkk Hfsv.
pose proof HG as (HR16 & HSTK & HRS & HRk & Hown & HF & HFapp & HF32).
pose proof HJ as (HAR & Hlyc & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hsp0al & HSTK0 & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof alloc_ceiling_lt as Hc2.
assert (Hes : ESTACK = 4096) by reflexivity.
assert (HTS : T_SEG_STK = 16384) by reflexivity.
assert (HTP : T_pwe_STK = 4144) by reflexivity.
assert (Hrq : req_size Layout.PP_SIZE = Layout.PP_SIZE) by reflexivity.
assert (HPS : Layout.PP_SIZE = 19744) by reflexivity.
destruct (al_blocks _ _ LAWS _ _ _ _ _ pp Layout.PP_SIZE HAR Hpp) as (Hp16 & Hp4096 & Hpceil & Happ & Hppres & _).
rewrite Hrq, HPS in Hpceil, Hppres, Happ.
assert (Hin4 : In (4, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; left; exact Hown).
destruct (frames_bounds rsegs B LAWS lyc Sc W memc mdc 4 pos HAR Hin4) as (HF4096 & HFceil & _).
change (fs_frame_bytes 4) with 1024 in HF4096, HFceil. rewrite <- HF in HF4096, HFceil.
unfold T_SEG_STK, ASTACK in HSTK, HRk. unfold kHighMemBeg in HRk.
pose proof (w8_sep B LAWS lyc Sc W memc mdc pp F pos HAR Hpp Hin4 HF) as Hsep. rewrite HPS in Hsep.
destruct (rl_pwe_len_of_wf ed Hwf) as ([Hn0 Hn56] & Hbl & Hsz & Hty).
assert (Hsz96 : e_size ed <= 96) by (unfold Layout.ENT_SIZE in Hsz; lia).
assert (HspR : spZ regs = R) by (unfold spZ; rewrite H2; unfold w64; apply unsigned_lit_small; lia).
assert (HFd : 0 <= F / 8 <= 17592184995840)
  by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
assert (HsFb : 2147450880 <= shadow_addr F /\ shadow_addr F + 128 <= 17594332446912)
  by (unfold shadow_addr, SHADOW_OFF; lia).
(* the frame's shadow lies apart from the first block and from the callees' stack, and so does e62 *)
assert (Hshd : forall i, 0 <= i < 128 ->
  ~ (pp <= shadow_addr F + i < pp + 19744) /\ ~ (R - T_pwe_STK <= shadow_addr F + i < R)).
{ intros i Hi. rewrite HTP.
  unfold in_app in Happ. rewrite C3 in *. unfold kLowShadowBeg, SHADOW_OFF, kLowMemEnd in *.
  split; lia. }
assert (Hepp : forall a, F + 0x210 <= a < F + 0x278 -> ~ (pp <= a < pp + 19744) /\ ~ (R - T_pwe_STK <= a < R))
  by (intros a Ha; rewrite HTP; split; lia).
(* the write set of the whole piece *)
set (WRA := fun a : Z =>
  (pp + len <= a < pp + len + pwe_len ed) \/
  (pp + 0x4000 <= a < pp + 0x4008) \/
  (fsv = 1 /\ pp + 0x4d14 <= a < pp + 0x4d18) \/
  (fsv = 1 /\ pp + 0x4014 + 104 * kk <= a < pp + 0x4014 + 104 * kk + 104) \/
  (shadow_addr F + 66 <= a < shadow_addr F + 79) \/
  (R - T_pwe_STK <= a < R)) in *.
lazymatch goal with |- SRr _ _ _ ?P => set (POST := P) end.
assert (HnWR : forall x, R <= x < R + 0x200 -> ~ WRA x).
{ intros x Hx HX. destruct HX as [X|[X|[[_ X]|[[_ X]|[X|X]]]]]; rewrite ?HTP in X; lia. }
assert (HnWS : forall y i, pp <= y < pp + 19744 -> 0 <= i < 128 -> y <> shadow_addr F + i).
{ intros y i Hy Hi Heq. apply (proj1 (Hshd i Hi)). lia. }
(* ================================ run P ================================ *)
eapply SRr_bind.
{ exact (RUNP STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs R pp F pos len
    HJ HG Hpp H2 H9 H15 H22 V148 V158 Vlen ltac:(lia)). }
cbv beta. intros W1 c1 Hw1 (ly1 & S1 & regs1 & mem1 & md1 & -> & HJ1 & Hk1 & Hfr1 & Hperm1 & Hio1 & Hmo1 & Hm1
  & (A1 & A10 & A11 & A24 & A18 & A20)).
assert (KA : forall a, 0 <= a < 2 ^ 64 -> aview rsegs (w_H W1) mem1 a = aview rsegs (w_H W) memc a)
  by (intros a Ha; apply Hm1; [exact Ha | intros X; exact X]).
assert (Hpp1 : In (pp, Layout.PP_SIZE) (ablocks B ly1 S1))
  by exact (Permutation_in _ (Permutation_sym Hperm1) Hpp).
assert (Hin41 : In (4, pos) (frames S1)) by (rewrite Hfr1; exact Hin4).
assert (HG1 : w8_geo STK sp0 own ly1 R F pos).
{ pose proof HJ1 as (_ & Hly1 & _). exact (w8_geo_step STK sp0 own lyc ly1 R F pos _ ly HG Hlyc Hly1). }
pose proof HJ1 as (HAR1 & _).
assert (Hset1 : w8_set3 regs regs1) by (split; [exact A24|]; split; [exact A18 | exact A20]).
assert (R1_2 : getr regs1 2 = w64 R) by (rewrite (Hk1 (2%bv) ltac:(w8_nz) ltac:(w8_notin)); exact H2).
assert (R1_3 : getr regs1 3 = w64 (as_gp B)) by (rewrite (Hk1 (3%bv) ltac:(w8_nz) ltac:(w8_notin)); exact H3).
assert (R1_4 : getr regs1 4 = w64 (as_tp B)) by (rewrite (Hk1 (4%bv) ltac:(w8_nz) ltac:(w8_notin)); exact H4).
assert (HspR1 : spZ regs1 = R) by (unfold spZ; rewrite R1_2; unfold w64; apply unsigned_lit_small; lia).
assert (Hfsh1 : rl_fsh rsegs (w_H W1) mem1 F w8_PJ).
{ intros i Hi. pose proof Hi as Hi'. rewrite w8_PJ_len in Hi'.
  rewrite (KA (shadow_addr F + i)) by lia. apply Hfsh. exact Hi. }
assert (Hent1 : rm_bytes rsegs (w_H W1) mem1 (F + 0x210) (ent_mem ed)).
{ eapply rm_bytes_kept; [exact Hent|]. intros y Hy. rewrite length_ent_mem in Hy by lia. apply KA. lia. }
assert (Vlen1 : val_mem rsegs (mrestrict (w_H W1) mem1) (pp + Layout.OFF_LEN) 8 len).
{ apply (w8_val_kept (w_H W) memc); [exact Vlen|]. intros y Hy. unfold Layout.OFF_LEN in Hy. apply KA. lia. }
destruct (al_frames _ _ LAWS ly1 S1 W1 mem1 md1 4 pos HAR1 Hin41) as (_ & _ & _ & Hfs1).
change (fs_frame_bytes 4 / 8) with 128 in Hfs1.
pose proof HG1 as (_ & _ & _ & _ & _ & HF1 & _). rewrite <- HF1 in Hfs1.
(* ================================ the call pod_write_ent(pp, e62) ================================ *)
destruct (rl_pwe_site_81908 F pp R len ed HF32 HFapp ltac:(lia) ltac:(rewrite HTP; left; lia) ltac:(lia)
  ltac:(unfold Layout.POD_BUF_MAX; lia) Hwf)
  as (Hq0 & Hq8 & Hqamr & Hqsep & Hqstk & Hlenmax & _).
unfold PWE_OFF_E62 in Hq0, Hq8, Hqamr, Hqsep, Hqstk.
destruct (pwe_pp_of_block rsegs B ly1 S1 W1 mem1 md1 pp HAR1 Hpp1) as (Hpp0 & Hpp8 & Hpp63 & Hppamr & Hppra & Hpphull).
eapply SRr_bind.
{ eapply (rl_pwe_at B MT STK sp0 FP ly S W0 mem0 md0 own k regs1 ly1 S1 W1 mem1 md1 pp len W8_RA1 (R - sp0) ed).
  - exact A1.
  - rewrite HspR1. lia.
  - exact (PWE STK sp0 FP ly S W0 mem0 md0 own ly1 S1 W1 mem1 md1 k regs1 pp (F + 0x210) len ed
      ltac:(split; [exact HJ1|]; split; [rewrite A1; exact w8_ret1|];
            split; [unfold raZ; rewrite A1; unfold w64, W8_RA1; rewrite unsigned_lit_small by lia; lia|];
            split; [exact R1_3|]; split; [exact R1_4|];
            rewrite HspR1, HTP; split; [exact HR16|]; split; [lia|]; split; [lia | exact Hev])
      A10 A11 Hpp0 Hpp8 Hpp63 Hppamr Hppra Hpphull
      (pwe_awr_fresh B STK sp0 FP ly S ly1 S1 own pp len ed Hpp1 Hfresh ltac:(lia) Hlenmax)
      ltac:(rewrite HspR1, HTP; left; unfold Layout.PP_SIZE; lia)
      Vlen1 ltac:(lia) Hlen8 Hlenmax Hq0 Hq8 Hqamr Hbl Hsz Hty Hent1
      ltac:(replace (F + 0x210) with (F + RM_E62 + 0) by (unfold RM_E62; lia);
            exact (rm_B_ra_e62 rsegs _ _ F false false false false false false 0 104 Hfsh1
              (w8_F8 F HF32) ltac:(lia) ltac:(lia)))
      ltac:(exact (w8_hull_e62 _ F 0x210 104 HF32 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
              (fun i Hi => aview_some_of_apresent rsegs _ _ _ (proj1 (Hfs1 i Hi)))))
      Hqsep ltac:(rewrite HspR1; exact Hqstk)). }
cbv beta. intros W2 c2 Hw2 (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & Hk2 & Hfr2 & Hperm2 & Hio2 & Hmo2 & Hm2
  & (Genc & Glen & Gsh & _ & _)).
assert (K2 : forall a, 0 <= a < 2 ^ 64 -> ~ pwe_E pp len ed a -> ~ (R - T_pwe_STK <= a < R) ->
  aview rsegs (w_H W2) mem2 a = aview rsegs (w_H W) memc a).
{ intros a Ha Hn1 Hn2. rewrite (Hm2 a Ha ltac:(intros [X|X]; [exact (Hn1 X) | apply Hn2; lia])). apply KA. exact Ha. }
assert (KC2 : forall a, 0 <= a < 2 ^ 64 -> ~ (pp <= a < pp + 19744) -> ~ (R - T_pwe_STK <= a < R) ->
  aview rsegs (w_H W2) mem2 a = aview rsegs (w_H W) memc a).
{ intros a Ha Hn1 Hn2. apply K2; [exact Ha | | exact Hn2].
  unfold pwe_E, Layout.OFF_LEN. intros [X|X]; apply Hn1; lia. }
assert (HW2 : forall a, 0 <= a < 2 ^ 64 -> ~ WRA a -> aview rsegs (w_H W2) mem2 a = aview rsegs (w_H W) memc a).
{ intros a Ha Hn. apply K2; [exact Ha | | intros X; apply Hn; right; right; right; right; right; exact X].
  unfold pwe_E, Layout.OFF_LEN. intros [X|X]; apply Hn; [left; exact X | right; left; lia]. }
assert (Hpp2 : In (pp, Layout.PP_SIZE) (ablocks B ly2 S2))
  by exact (Permutation_in _ (Permutation_sym Hperm2) Hpp1).
assert (HG2 : w8_geo STK sp0 own ly2 R F pos).
{ pose proof HJ2 as (_ & Hly2 & _). exact (w8_geo_step STK sp0 own lyc ly2 R F pos _ ly HG Hlyc Hly2). }
assert (Hfsh2 : rl_fsh rsegs (w_H W2) mem2 F w8_PJ).
{ intros i Hi. rewrite w8_PJ_len in Hi.
  rewrite (KC2 (shadow_addr F + i) ltac:(lia) (proj1 (Hshd i ltac:(lia))) (proj2 (Hshd i ltac:(lia)))).
  apply Hfsh. rewrite w8_PJ_len. exact Hi. }
assert (Hent2 : rm_bytes rsegs (w_H W2) mem2 (F + 0x210) (ent_mem ed)).
{ eapply rm_bytes_kept; [exact Hent|]. intros y Hy. rewrite length_ent_mem in Hy by lia.
  apply KC2; [lia | exact (proj1 (Hepp y ltac:(lia))) | exact (proj2 (Hepp y ltac:(lia)))]. }
assert (Vcell2 : forall o v, 0 <= o -> o + 8 <= 0x200 -> val_mem rsegs (mrestrict (w_H W) memc) (R + o) 8 v ->
  val_mem rsegs (mrestrict (w_H W2) mem2) (R + o) 8 v).
{ intros o v Ho1 Ho2 Hv. apply (w8_val_kept (w_H W) memc); [exact Hv|].
  intros y Hy. apply HW2; [lia | apply HnWR; lia]. }
assert (RK2 : forall r : bv 5, bv_unsigned r <> 0 -> ~ In r w8_clobJ -> getr regs2 r = getr regs r).
{ intros r Hr0 Hn. destruct (w8_outJ r Hr0 Hn) as (Hcs & HnP & _ & _ & _ & Hnc).
  rewrite (Hk2 r Hr0 ltac:(intros X; apply Hnc; exact X)), (Hk1 r Hr0 HnP). reflexivity. }
assert (R2_2 : getr regs2 2 = w64 R) by (rewrite (RK2 (2%bv) ltac:(w8_nz) ltac:(w8_notin)); exact H2).
assert (R2_3 : getr regs2 3 = w64 (as_gp B)) by (rewrite (RK2 (3%bv) ltac:(w8_nz) ltac:(w8_notin)); exact H3).
assert (R2_4 : getr regs2 4 = w64 (as_tp B)) by (rewrite (RK2 (4%bv) ltac:(w8_nz) ltac:(w8_notin)); exact H4).
assert (R2_9 : getr regs2 9 = w64 R) by (rewrite (RK2 (9%bv) ltac:(w8_nz) ltac:(w8_notin)); exact H9).
assert (R2_19 : getr regs2 19 = w64 (shadow_addr F))
  by (rewrite (RK2 (19%bv) ltac:(w8_nz) ltac:(w8_notin)); exact H19).
assert (R2_27 : getr regs2 27 = w64 SHADOW_OFF) by (rewrite (RK2 (27%bv) ltac:(w8_nz) ltac:(w8_notin)); exact H27).
assert (Hset2 : w8_set3 regs regs2).
{ apply (w8_set3_step regs regs1 regs2 rl_caller_saved Hset1);
  [ intros r Hr0 Hn; exact (Hk2 r Hr0 Hn) | w8_notin | w8_notin | w8_notin ]. }
assert (Hfr02 : frames S2 = frames Sc) by (rewrite Hfr2, Hfr1; reflexivity).
assert (Hperm02 : Permutation (ablocks B ly2 S2) (ablocks B lyc Sc))
  by (eapply Permutation_trans; [exact Hperm2 | exact Hperm1]).
assert (Hio02 : same_io mdc md2) by (eapply same_io_trans; [exact Hio1 | exact Hio2]).
assert (Hmo02 : mo_le MT Sc S2 0).
{ pose proof (mle_station MT Sc S1 S2 0 0 MTL Hmo1 Hmo2) as HM. rewrite Z.add_0_r in HM. exact HM. }
assert (Genc' : rm_bytes rsegs (w_H W2) mem2 (pp + len) (enc_pod ed)) by exact Genc.
assert (Glen' : val_mem rsegs (mrestrict (w_H W2) mem2) (pp + 0x4000) 8 (len + pwe_len ed)) by exact Glen.
(* ================================ the last run and the piece's end state ================================ *)
assert (TAIL : forall ly5 S5 (W5 : world rsegs) regs5 mem5 md5 pc0,
  ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own ly5 S5 W5 mem5 md5 k ->
  (pc0 = W8_RA2 \/ pc0 = W8_T0) -> (pc0 = W8_T0 -> getr regs5 11 = w64 kk) ->
  frames S5 = frames Sc -> Permutation (ablocks B ly5 S5) (ablocks B lyc Sc) ->
  same_io mdc md5 -> mo_le MT Sc S5 0 ->
  (forall r : bv 5, bv_unsigned r <> 0 -> ~ In r w8_clobJ -> getr regs5 r = getr regs r) ->
  w8_set3 regs regs5 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ WRA a -> aview rsegs (w_H W5) mem5 a = aview rsegs (w_H W) memc a) ->
  val_mem rsegs (mrestrict (w_H W5) mem5) (pp + 0x4000) 8 (len + pwe_len ed) ->
  rm_bytes rsegs (w_H W5) mem5 (pp + len) (enc_pod ed) ->
  (fsv = 1 -> rm_bytes rsegs (w_H W5) mem5 (pp + 0x4014 + 104 * kk) (ent_mem ed) /\
              val_mem rsegs (mrestrict (w_H W5) mem5) (pp + 0x4d14) 4 (kk + 1)) ->
  rl_fsh rsegs (w_H W5) mem5 F w8_PJ ->
  SRr rsegs W5 (cfg_at rsegs pc0 regs5 mem5 md5) POST).
{ intros ly5 S5 W5 regs5 mem5 md5 pc0 HJ5 Hpc0 Ha1 Hfr5 Hperm5 Hio5 Hmo5 RK5 Hset5 HW5 Vlen5 Henc5 Hrec5 Hfsh5.
  assert (HG5 : w8_geo STK sp0 own ly5 R F pos).
  { pose proof HJ5 as (_ & Hly5 & _). exact (w8_geo_step STK sp0 own lyc ly5 R F pos _ ly HG Hlyc Hly5). }
  assert (R5_2 : getr regs5 2 = w64 R) by (rewrite (RK5 (2%bv) ltac:(w8_nz) ltac:(w8_notin)); exact H2).
  assert (R5_9 : getr regs5 9 = w64 R) by (rewrite (RK5 (9%bv) ltac:(w8_nz) ltac:(w8_notin)); exact H9).
  assert (R5_19 : getr regs5 19 = w64 (shadow_addr F))
    by (rewrite (RK5 (19%bv) ltac:(w8_nz) ltac:(w8_notin)); exact H19).
  assert (V1285 : val_mem rsegs (mrestrict (w_H W5) mem5) (R + 0x128) 8 cnt).
  { apply (w8_val_kept (w_H W) memc); [exact V128|]. intros x Hx. apply HW5; [lia | apply HnWR; lia]. }
  assert (V1505 : val_mem rsegs (mrestrict (w_H W5) mem5) (R + 0x150) 8 kk).
  { apply (w8_val_kept (w_H W) memc); [exact V150|]. intros x Hx. apply HW5; [lia | apply HnWR; lia]. }
  eapply SRr_mono.
  { exact (RUND STK sp0 FP ly S W0 mem0 md0 own ly5 S5 W5 mem5 md5 k regs5 R F pos cnt kk pc0
      HJ5 HG5 Hpc0 Ha1 R5_2 R5_9 R5_19 V1285 V1505 Hcnt Hkk). }
  intros W7 c7 Hw7 (ly7 & S7 & regs7 & mem7 & md7 & -> & HJ7 & Hk7 & Hfr7 & Hperm7 & Hio7 & Hmo7 & Hm7
    & (D11 & D26 & D13)).
  unfold POST, rl_wpost. exists ly7, S7, regs7, mem7, md7.
  split; [reflexivity|]. split; [exact HJ7|].
  split.
  { intros r Hr0 Hn. destruct (w8_outJ r Hr0 Hn) as (_ & _ & _ & _ & HnD & _).
    rewrite (Hk7 r Hr0 HnD). exact (RK5 r Hr0 Hn). }
  split; [rewrite Hfr7; exact Hfr5|].
  split; [eapply Permutation_trans; [exact Hperm7 | exact Hperm5]|].
  split; [eapply same_io_trans; [exact Hio5 | exact Hio7]|].
  split; [pose proof (mle_station MT Sc S5 S7 0 0 MTL Hmo5 Hmo7) as HM; rewrite Z.add_0_r in HM; exact HM|].
  split.
  { intros a Ha Hn. rewrite (Hm7 a Ha ltac:(intros X; apply Hn; right; right; right; right; left; exact X)).
    apply HW5; assumption. }
  cbv beta.
  destruct (w8_set3_step regs regs5 regs7 w8_clobD Hset5
    ltac:(intros r Hr0 Hn; exact (Hk7 r Hr0 Hn)) ltac:(w8_notin) ltac:(w8_notin) ltac:(w8_notin))
    as (S24 & S18 & S20).
  split; [exact D11|].
  split; [exact D26|].
  split; [exact S24|]. split; [exact S18|]. split; [exact S20|].
  split.
  { apply (w8_val_kept (w_H W5) mem5); [exact Vlen5|]. intros x Hx.
    apply Hm7; [lia | intros X; apply (HnWS x (x - shadow_addr F)); lia]. }
  split.
  { eapply rm_bytes_kept; [exact Henc5|]. intros y Hy. fold (pwe_len ed) in Hy.
    apply Hm7; [lia | intros X; apply (HnWS y (y - shadow_addr F)); lia]. }
  split.
  { intros Hf. destruct (Hrec5 Hf) as [Hr1 Hr2]. split.
    - eapply rm_bytes_kept; [exact Hr1|]. intros y Hy. rewrite length_ent_mem in Hy by lia.
      apply Hm7; [lia | intros X; apply (HnWS y (y - shadow_addr F)); lia].
    - apply (w8_val_kept (w_H W5) mem5); [exact Hr2|]. intros x Hx.
      apply Hm7; [lia | intros X; apply (HnWS x (x - shadow_addr F)); lia]. }
  rewrite w8_P0_set.
  apply (rm_fsh_set rsegs (w_H W5) mem5 (w_H W7) mem7 F w8_PJ 66 13 0xf8 Hfsh5).
  - intros i Hi. cbn in Hi. replace (shadow_addr F + i) with (shadow_addr F + 66 + (i - 66)) by lia.
    apply D13. lia.
  - intros i Hi Hn. rewrite w8_PJ_len in Hi. cbn in Hn. apply Hm7; [lia | lia]. }
(* ================================ run C, by `first` ================================ *)
destruct Hfsv as [Hf | Hf]; subst fsv.
- (* first clear: run C0, then the last run from 0x81978 *)
  eapply SRr_bind.
  { exact (RUNC0 STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 mem2 md2 k regs2 R F pos kk
      HJ2 HG2 R2_2 R2_9 (Vcell2 0x138 0 ltac:(lia) ltac:(lia) V138) (Vcell2 0x150 kk ltac:(lia) ltac:(lia) V150) Hkk). }
  cbv beta. intros W5 c5 Hw5 (ly5 & S5 & regs5 & mem5 & md5 & -> & HJ5 & Hk5 & Hfr5 & Hperm5 & Hio5 & Hmo5 & Hm5 & C11).
  apply (TAIL ly5 S5 W5 regs5 mem5 md5 W8_T0 HJ5 (or_intror eq_refl) (fun _ => C11)).
  + rewrite Hfr5. exact Hfr02.
  + eapply Permutation_trans; [exact Hperm5 | exact Hperm02].
  + eapply same_io_trans; [exact Hio02 | exact Hio5].
  + pose proof (mle_station MT Sc S2 S5 0 0 MTL Hmo02 Hmo5) as HM. rewrite Z.add_0_r in HM. exact HM.
  + intros r Hr0 Hn. destruct (w8_outJ r Hr0 Hn) as (_ & _ & _ & HnC0 & _ & _).
    rewrite (Hk5 r Hr0 HnC0). exact (RK2 r Hr0 Hn).
  + apply (w8_set3_step regs regs2 regs5 w8_clobC0 Hset2);
    [ intros r Hr0 Hn; exact (Hk5 r Hr0 Hn) | w8_notin | w8_notin | w8_notin ].
  + intros a Ha Hn. rewrite (Hm5 a Ha ltac:(intros X; exact X)). apply HW2; assumption.
  + apply (w8_val_kept (w_H W2) mem2); [exact Glen'|]. intros x Hx. apply Hm5; [lia | intros X; exact X].
  + eapply rm_bytes_kept; [exact Genc'|]. intros y Hy. fold (pwe_len ed) in Hy.
    apply Hm5; [lia | intros X; exact X].
  + intros X. lia.
  + intros i Hi. pose proof Hi as Hi'. rewrite w8_PJ_len in Hi'.
    rewrite (Hm5 (shadow_addr F + i) ltac:(lia) ltac:(intros X; exact X)). apply Hfsh2. exact Hi.
- (* first set: run C1, the record copy, then the last run from 0x81974 *)
  assert (Vnent2 : val_mem rsegs (mrestrict (w_H W2) mem2) (pp + 0x4d14) 4 kk).
  { apply (w8_val_kept (w_H W) memc); [exact (Vnent eq_refl)|].
    intros x Hx. apply K2; [lia | unfold pwe_E, Layout.OFF_LEN; intros [X|X]; lia | lia]. }
  eapply SRr_bind.
  { exact (RUNC1 STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 mem2 md2 k regs2 R pp F pos kk
      HJ2 HG2 Hpp2 Hfresh R2_2 R2_9 R2_27
      (Vcell2 0xd8 _ ltac:(lia) ltac:(lia) Vd8) (Vcell2 0xe0 _ ltac:(lia) ltac:(lia) Ve0)
      (Vcell2 0xe8 _ ltac:(lia) ltac:(lia) Ve8) (Vcell2 0x120 _ ltac:(lia) ltac:(lia) V120)
      (Vcell2 0x138 1 ltac:(lia) ltac:(lia) V138) (Vcell2 0x150 kk ltac:(lia) ltac:(lia) V150)
      (Vcell2 0x158 _ ltac:(lia) ltac:(lia) V158)
      Vnent2 Hkk). }
  cbv beta. intros W5 c5 Hw5 (ly5 & S5 & regs5 & mem5 & md5 & -> & HJ5 & Hk5 & Hfr5 & Hperm5 & Hio5 & Hmo5 & Hm5
    & (E1 & E10 & E11 & E12 & Enent)).
  assert (Hpp5 : In (pp, Layout.PP_SIZE) (ablocks B ly5 S5))
    by exact (Permutation_in _ (Permutation_sym Hperm5) Hpp2).
  assert (HG5 : w8_geo STK sp0 own ly5 R F pos).
  { pose proof HJ5 as (_ & Hly5 & _). exact (w8_geo_step STK sp0 own lyc ly5 R F pos _ ly HG Hlyc Hly5). }
  assert (K5 : forall a, 0 <= a < 2 ^ 64 -> ~ (pp <= a < pp + 19744) ->
    aview rsegs (w_H W5) mem5 a = aview rsegs (w_H W2) mem2 a)
    by (intros a Ha Hn; apply Hm5; [exact Ha | lia]).
  assert (Hfsh5 : rl_fsh rsegs (w_H W5) mem5 F w8_PJ).
  { intros i Hi. rewrite w8_PJ_len in Hi.
    rewrite (K5 (shadow_addr F + i) ltac:(lia) (proj1 (Hshd i ltac:(lia)))).
    apply Hfsh2. rewrite w8_PJ_len. exact Hi. }
  assert (Hent5 : rm_bytes rsegs (w_H W5) mem5 (F + 0x210) (ent_mem ed)).
  { eapply rm_bytes_kept; [exact Hent2|]. intros y Hy. rewrite length_ent_mem in Hy by lia.
    apply K5; [lia | exact (proj1 (Hepp y ltac:(lia)))]. }
  assert (RK5 : forall r : bv 5, bv_unsigned r <> 0 -> ~ In r w8_clobJ -> getr regs5 r = getr regs r).
  { intros r Hr0 Hn. destruct (w8_outJ r Hr0 Hn) as (_ & _ & HnC & _ & _ & _).
    rewrite (Hk5 r Hr0 HnC). exact (RK2 r Hr0 Hn). }
  assert (Hset5 : w8_set3 regs regs5).
  { apply (w8_set3_step regs regs2 regs5 w8_clobC Hset2);
    [ intros r Hr0 Hn; exact (Hk5 r Hr0 Hn) | w8_notin | w8_notin | w8_notin ]. }
  assert (R5_2 : getr regs5 2 = w64 R) by (rewrite (RK5 (2%bv) ltac:(w8_nz) ltac:(w8_notin)); exact H2).
  assert (R5_3 : getr regs5 3 = w64 (as_gp B)) by (rewrite (RK5 (3%bv) ltac:(w8_nz) ltac:(w8_notin)); exact H3).
  assert (R5_4 : getr regs5 4 = w64 (as_tp B)) by (rewrite (RK5 (4%bv) ltac:(w8_nz) ltac:(w8_notin)); exact H4).
  eapply SRr_bind.
  { eapply (w8_cpy B LAWS W8_CPY W8_RA2 STK sp0 FP ly S W0 mem0 md0 own ly5 S5 W5 mem5 md5 k regs5
      R pp F pos (pp + 0x4014 + 104 * kk) (F + 0x210) 104).
    - exact AMEMCPY.
    - exact HJ5.
    - exact HG5.
    - exact Hpp5.
    - exact Hfresh.
    - exact E1.
    - exact w8_ret2.
    - exact R5_2.
    - exact R5_3.
    - exact R5_4.
    - exact E10.
    - exact E11.
    - exact E12.
    - lia.
    - unfold Layout.PP_SIZE; lia.
    - lia.
    - lia.
    - lia.
    - exact Hfsh5. }
  cbv beta. intros Wr6 cr6 _ (-> & regs6 & mem6 & md6 & -> & HJ6 & Hio6 & HP6 & Heff6 & Hkp6).
  apply (TAIL ly5 S5 W5 regs6 mem6 md6 W8_RA2 HJ6 (or_introl eq_refl)
    ltac:(unfold W8_RA2, W8_T0; intros X; lia)).
  + rewrite Hfr5. exact Hfr02.
  + eapply Permutation_trans; [exact Hperm5 | exact Hperm02].
  + eapply same_io_trans; [exact Hio02|]. eapply same_io_trans; [exact Hio5 | exact Hio6].
  + pose proof (mle_station MT Sc S2 S5 0 0 MTL Hmo02 Hmo5) as HM. rewrite Z.add_0_r in HM. exact HM.
  + intros r Hr0 Hn. destruct (w8_outJ r Hr0 Hn) as (Hcs & _ & _ & _ & _ & _).
    rewrite (w8_pres regs5 regs6 r HP6 Hcs). exact (RK5 r Hr0 Hn).
  + exact (w8_set3_pres regs regs5 regs6 Hset5 HP6).
  + intros a Ha Hn.
    rewrite (Hkp6 a Ha ltac:(intros X; apply Hn; right; right; right; left; split; [reflexivity | lia])
      ltac:(intros X; apply Hn; right; right; right; right; right; rewrite HTP; lia)).
    rewrite (Hm5 a Ha ltac:(intros X; apply Hn; right; right; left; split; [reflexivity | exact X])).
    apply HW2; assumption.
  + apply (w8_val_kept (w_H W5) mem5); [|intros x Hx; apply Hkp6; [lia | lia | lia]].
    apply (w8_val_kept (w_H W2) mem2); [exact Glen'|]. intros x Hx. apply Hm5; [lia | lia].
  + eapply rm_bytes_kept; [exact Genc'|]. intros y Hy. fold (pwe_len ed) in Hy.
    rewrite (Hkp6 y ltac:(lia) ltac:(lia) ltac:(lia)). apply Hm5; [lia | lia].
  + intros _. split.
    * apply (rm_memcpy_bytes rsegs (w_H W5) mem5 (w_H W5) mem6 (F + 0x210) (pp + 0x4014 + 104 * kk) (ent_mem ed) Hent5).
      intros i Hi. rewrite length_ent_mem in Hi by lia. apply Heff6. lia.
    * apply (w8_val_kept (w_H W5) mem5); [exact Enent|]. intros x Hx. apply Hkp6; [lia | lia | lia].
  + intros i Hi. rewrite w8_PJ_len in Hi.
    rewrite (Hkp6 (shadow_addr F + i) ltac:(lia) ltac:(intros X; apply (proj1 (Hshd i ltac:(lia))); lia)
      ltac:(intros X; apply (proj2 (Hshd i ltac:(lia))); rewrite HTP; lia)).
    apply Hfsh5. rewrite w8_PJ_len. exact Hi.
Qed.
End p.
