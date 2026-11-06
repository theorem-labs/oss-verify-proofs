(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/Reusable/YCbq.v aj_intrin_at at 28fdc66416e (the call of
   __asan_memcpy in the journal) restated as hd_memcpy with the wrapper's same_but_materialized kept in the post as
   same_io, and proofs/reac-pw/fuzz_role/lib/A/RPgM02Base.v at 9e73ed57244 (m2_img_zone, m2_cstr_kept, the .rodata
   zone of m2_szone) restated as hd_img_zone / hd_cstr_kept / hd_szone for the .rodata range only; the rest of the
   file is new. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_role/lib/A/RPgScanHead.v, with its module paths and module names changed; 428 of its 517 lines of code are new or changed and 925 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_role/lib/A/RPgW6cTail.v, with its module paths changed; 758 of its 829 lines of code are new or changed and 446 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgW5Int.v at 3e85ad4cf5dd for
   reac-pw/fuzz_rate image A: the chained piece is rate's W8 instead of role's Int-7 pod, so there are four
   engine runs and three calls instead of two and one, the calls are __asan_memcpy as well as __asan_memset,
   the post is RtPgSteps.rts_post instead of a local copy, and the source of the two copies is the frame
   object e (which asks the frame / block separation of the kernel's AR_sep_law). *)
(* reac-pw/fuzz_rate image A (fuzz_rate.asan, pinned sha256
   22bc8613d780c9a99353dc86368f9401311ef5c8358882651217836298529b6a; every address measured on the unstripped
   twin 0d508f2c65c249840b6c8fe3c1960824f2548b175c23583632f06bb7956458c3): the walk piece "write + record" of
   LLVMFuzzerTestOneInput as ONE block, J 0x81e00 -> C 0x8127c / CL 0x82484, built from the four engine runs of
   lib/A/RtPgW8Kit.v and the three runtime calls between them. Proves no function (kind: segment lemma).

   THE CHAIN. rw8_core takes the four runs as hypotheses (each lane proves one) and the kernel's contracts of
   the two intrinsics (aintrin_realizes at __asan_memcpy 0x51860 and __asan_memset 0x51cfc), and threads:
     run A -> memcpy(pp + len + 8, e.body, e.size) -> run B -> memset(pp + len + 8 + size, 0, pad)
           -> run C -> (first) memcpy(&pp->ent[n_ent], e, 104) -> run D.
   What is carried across a call is the kernel's post (YG0d aintrin_realizes through RtPgSteps.rts_intrin_at):
   the journal at the SAME layout and state, the callee-saved registers, the n bytes written and every other
   byte outside the callee's stack [R - ESTACK, R). The source of both copies is the frame object e at F+0xf0,
   whose shadow the frame's pattern rs_PJ gives (e in scope) and whose bytes are apart from the first block by
   AR_sep_law; the destinations lie in the first block, writable because it is not among the journal's start
   blocks (RtPgBase.rt_fresh_awr).

   THE RESULT. At the end the first block holds Model.enc_pod of the pod at pp + len, its length word is
   len + |enc_pod|, the frame's shadow is the prologue's pattern again (e out of scope), and, when `first` is
   set, pp->ent[kk] holds Layout.ent_mem of the pod and pp->n_ent is kk + 1. *)
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Import Cursor Model Layout.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import RtPgBase RtPgCSpec RtPgMem RtPgSteps RtPgSeg RtPgW8Kit.
Require OSSVerify.reac_pw.fuzz_rate.images.Asan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

Local Abbreviation rsegs := OSSVerify.reac_pw.fuzz_rate.images.Asan.M.loaded_segments.

(* ===================================== byte lists of the model ===================================== *)
(* e's four fields as the code reads them: the type word, the size word, the body and its zero tail. *)
Lemma rw8_ent_mem_split : forall ed, ent_mem ed =
  Z_to_le_bytes 4 (e_type ed) ++ Z_to_le_bytes 4 (e_size ed) ++ (e_body ed ++ zeros (96 - length (e_body ed))).
Proof. intros ed. reflexivity. Qed.
Lemma rw8_enc_pod_split : forall ed, enc_pod ed =
  (Z_to_le_bytes 4 (e_size ed) ++ Z_to_le_bytes 4 (e_type ed)) ++ e_body ed ++ repeat NUL (Z.to_nat (pad8 (e_size ed))).
Proof. intros ed. unfold enc_pod, le32, zeros. rewrite <- app_assoc. reflexivity. Qed.
Lemma rw8_len_body : forall ed, ent_wf ed -> Z.of_nat (length (e_body ed)) = e_size ed.
Proof. intros ed (_ & Hb & Hs). rewrite Hb. lia. Qed.
(* the pad of a pod written at an 8-aligned length *)
Lemma rw8_pad_shift : forall l s, l mod 8 = 0 -> pad8 (l + 8 + s) = pad8 s.
Proof.
intros l s Hl. unfold pad8.
replace ((l + 8 + s) mod 8) with (s mod 8); [reflexivity|].
replace (l + 8 + s) with (s + (l / 8 + 1) * 8) by (pose proof (Z.div_mod l 8 ltac:(lia)); lia).
symmetry. apply Z_mod_plus_full.
Qed.
Lemma rw8_PJ_sh : rs_PJ = rtm_sh false false false true false false false.
Proof. vm_compute. reflexivity. Qed.
Lemma rw8_PJ_len : Z.of_nat (length rs_PJ) = 56.
Proof. vm_compute. reflexivity. Qed.
Lemma rw8_P0_sh : rs_P0 = rtm_sh false false false false false false false.
Proof. vm_compute. reflexivity. Qed.

(* ===================================== the piece's clobber list ===================================== *)
Definition rw8_clobJ : list (bv 5) :=
  [1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 24; 26; 28; 29; 30; 31]%bv.
Definition rw8_csb (z : Z) : bool :=
  (z =? 2) || (z =? 3) || (z =? 4) || (z =? 8) || (z =? 9) ||
  ((18 <=? z) && (z <=? 23)) || (z =? 25) || (z =? 27).
Lemma rw8_csb_ok : forall z, rw8_csb z = true -> acallee_saved z.
Proof.
intros z H. unfold rw8_csb in H. unfold acallee_saved.
repeat rewrite Bool.orb_true_iff in H. rewrite Bool.andb_true_iff in H.
rewrite !Z.eqb_eq, !Z.leb_le in H. lia.
Qed.
Lemma rw8_outJ : forall r : bv 5, bv_unsigned r <> 0 -> ~ In r rw8_clobJ ->
acallee_saved (bv_unsigned r) /\ ~ In r rw8_clobA /\ ~ In r rw8_clobB /\ ~ In r rw8_clobC /\ ~ In r rw8_clobD
/\ ~ In r rts_caller_saved.
Proof.
intros r Hr0 Hn.
assert (HB : forallb (fun c : bv 5 => existsb (fun d => bv_eqb d c) rw8_clobJ || rw8_csb (bv_unsigned c))
  nz_regs = true) by (vm_compute; reflexivity).
pose proof (proj1 (forallb_forall _ _) HB r (in_nz_regs r Hr0)) as Hq. cbn beta in Hq.
assert (HS : forallb (fun c : bv 5 => existsb (fun d => bv_eqb d c) rw8_clobJ ||
  (negb (existsb (fun d => bv_eqb d c) rw8_clobA) && negb (existsb (fun d => bv_eqb d c) rw8_clobB) &&
   negb (existsb (fun d => bv_eqb d c) rw8_clobC) && negb (existsb (fun d => bv_eqb d c) rw8_clobD) &&
   negb (existsb (fun d => bv_eqb d c) rts_caller_saved))) nz_regs = true) by (vm_compute; reflexivity).
pose proof (proj1 (forallb_forall _ _) HS r (in_nz_regs r Hr0)) as Hs. cbn beta in Hs.
assert (Hin : forall l, existsb (fun d => bv_eqb d r) l = false -> ~ In r l).
{ intros l Hb Hi. assert (Ht : existsb (fun d => bv_eqb d r) l = true)
    by (apply existsb_exists; exists r; split; [exact Hi | apply bv_eqb_refl]). rewrite Hb in Ht. discriminate. }
assert (Hne : existsb (fun d => bv_eqb d r) rw8_clobJ = false).
{ destruct (existsb (fun d => bv_eqb d r) rw8_clobJ) eqn:Hb; [|reflexivity].
  exfalso. apply existsb_exists in Hb as (c & Hc & Hb). apply bv_eqb_eq in Hb. subst c. exact (Hn Hc). }
rewrite Hne in Hq, Hs. cbn [orb] in Hq, Hs.
repeat (apply andb_prop in Hs as [Hs ?]).
split; [apply rw8_csb_ok; exact Hq|].
repeat (split; [apply Hin; apply negb_true_iff; assumption|]).
apply Hin. apply negb_true_iff. assumption.
Qed.

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.

(* ===================================== the statement ===================================== *)
(* The piece's start state as explicit facts (RtPgW8.v turns RtPgSeg's cut J into them) and its end state as
   the bytes the model asks for. The write set is the pod's bytes in the first block, its length word, the
   record and the count word when `first` is set, the thirteen shadow bytes of e, and the callees' stack. *)
Definition rw8_core_stmt : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
  (R pp F pos len cnt kk rl fsv : Z) (ed : ent),
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
rw8_geo STK sp0 own lyc R F pos ->
In (pp, Layout.PP_SIZE) (ablocks B lyc Sc) -> ~ In (pp, Layout.PP_SIZE) (ablocks B ly S) ->
getr regs 2 = w64 R -> getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
getr regs 9 = w64 R -> getr regs 18 = w64 SHADOW_OFF -> getr regs 19 = w64 (F + 0xe0) ->
getr regs 20 = w64 (shadow_addr F) -> getr regs 22 = w64 (shadow_addr (pp + 0x4000)) ->
getr regs 23 = w64 (pp + 0x4000) -> getr regs 24 = w64 rl ->
getr regs 26 = w64 ((- 0x4001) mod 2 ^ 64) -> getr regs 27 = w64 pp ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0xa0) 8 (pp + 0x4014) ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0xa8) 8 (Z.shiftr (pp + 0x4d14) 3) ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0xb8) 8 (pp + 0x4d14) ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0xf0) 8 cnt ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x108) 8 (F + 0xf8) ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x110) 8 fsv ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x118) 8 ((- 0x4001) mod 2 ^ 64) ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x128) 8 kk ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x130) 8 ((- 0x3ffd) mod 2 ^ 64) ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x138) 8 (F + 0xf0) ->
val_mem rsegs (mrestrict (w_H W) memc) (pp + 0x4000) 8 len ->
(fsv = 1 -> val_mem rsegs (mrestrict (w_H W) memc) (pp + 0x4d14) 4 kk) ->
rtm_bytes rsegs (w_H W) memc (F + 0xf0) (ent_mem ed) ->
rt_fsh rsegs (w_H W) memc F rs_PJ ->
ent_wf ed -> 32 <= len -> len + 56 <= 5440 -> len mod 8 = 0 ->
1 <= cnt <= 32 -> 0 <= kk <= 31 -> (fsv = 0 \/ fsv = 1) -> 0 <= rl < 2 ^ 64 ->
SRr rsegs W (cfg_at rsegs RW8_J regs memc mdc)
(rts_post B MT STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc
  (if kk + 1 =? cnt then RW8_CL else RW8_C) rw8_clobJ
  (fun a => (pp + len <= a < pp + len + Z.of_nat (length (enc_pod ed))) \/
            (pp + 0x4000 <= a < pp + 0x4008) \/
            (fsv = 1 /\ pp + 0x4d14 <= a < pp + 0x4d18) \/
            (fsv = 1 /\ pp + 0x4014 + 104 * kk <= a < pp + 0x4014 + 104 * kk + 104) \/
            (shadow_addr F + 0x1e <= a < shadow_addr F + 0x2b) \/
            (R - ESTACK <= a < R))
  (fun W2 regs2 mem2 =>
     getr regs2 11 = w64 (kk + 1) /\
     getr regs2 24 = w64 rl /\ getr regs2 26 = w64 ((- 0x4001) mod 2 ^ 64) /\
     val_mem rsegs (mrestrict (w_H W2) mem2) (pp + 0x4000) 8 (len + Z.of_nat (length (enc_pod ed))) /\
     rtm_bytes rsegs (w_H W2) mem2 (pp + len) (enc_pod ed) /\
     (fsv = 1 -> rtm_bytes rsegs (w_H W2) mem2 (pp + 0x4014 + 104 * kk) (ent_mem ed) /\
                 val_mem rsegs (mrestrict (w_H W2) mem2) (pp + 0x4d14) 4 (kk + 1)) /\
     rt_fsh rsegs (w_H W2) mem2 F rs_P0)).
End c.

(* ===================================== the frame and the first block ===================================== *)
Section g. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Hypothesis LAWS : AR_laws rsegs B.
(* the frame for locals is apart from the first block (the kernel's AR_sep_law) *)
Lemma rw8_sep : forall ly S W mem md pp F pos,
AR rsegs B ly S W mem md -> In (pp, Layout.PP_SIZE) (ablocks B ly S) -> In (3, pos) (frames S) ->
F = frame_addr ly 3 pos -> pp + Layout.PP_SIZE <= F \/ F + 512 <= pp.
Proof.
intros ly S W mem md pp F pos HAR Hb Hf ->.
pose proof (sep_block_frame rsegs B LAWS ly S W mem md pp Layout.PP_SIZE 3 pos HAR Hb Hf) as HD.
unfold zdisjoint in HD. cbn [fst snd] in HD.
change (req_size Layout.PP_SIZE) with Layout.PP_SIZE in HD.
change (fs_frame_bytes 3) with 512 in HD. exact HD.
Qed.
(* the shadow hull of a range inside e lies in the frame's own 64 shadow bytes *)
Lemma rw8_hull_e : forall (rd : reader) F o n, F mod 32 = 0 -> 0 <= F -> 0xf0 <= o -> o + n <= 0x158 -> 0 < n ->
(forall i, 0 <= i < 64 -> rd (shadow_addr F + i) <> None) -> shadow_hull_vis rd (F + o) n.
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
assert (A1 : 30 <= o / 8) by (apply Z.div_le_lower_bound; lia).
assert (A2 : (o + n - 1) / 8 < 43) by (apply Z.div_lt_upper_bound; lia).
pose proof (Z.div_mod (X + o / 8) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (X + o / 8) 8 ltac:(lia)).
pose proof (Z.div_mod (X + (o + n - 1) / 8) 8 ltac:(lia)).
pose proof (Z.mod_pos_bound (X + (o + n - 1) / 8) 8 ltac:(lia)).
replace s with (X + (s - X)) by lia. apply Hsh. lia.
Qed.
(* frame_addr reads only ly_F, which every journal's layout_le keeps *)
Lemma rw8_lyF : forall n ly ly', layout_le n ly ly' ->
forall cid pos, frame_addr ly' cid pos = frame_addr ly cid pos.
Proof.
intros n ly ly' H cid pos. unfold frame_addr.
destruct H as (_ & _ & _ & _ & _ & HFF & _). rewrite HFF. reflexivity.
Qed.
Lemma rw8_geo_step : forall STK sp0 own lyc ly1 R F pos nsec ly,
rw8_geo STK sp0 own lyc R F pos -> layout_le nsec ly lyc -> layout_le nsec ly ly1 ->
rw8_geo STK sp0 own ly1 R F pos.
Proof.
intros STK sp0 own lyc ly1 R F pos nsec ly (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8) Hc H1.
unfold rw8_geo. repeat (split; [assumption|]). split; [|split; assumption].
rewrite (rw8_lyF nsec ly ly1 H1 3 pos), <- (rw8_lyF nsec ly lyc Hc 3 pos). exact G6.
Qed.
Lemma rw8_F8 : forall F, F mod 32 = 0 -> F mod 8 = 0.
Proof.
intros F HF. destruct (proj1 (Z.mod_divide F 32 ltac:(lia)) HF) as [q Hq]. rewrite Hq.
replace (q * 32) with ((4 * q) * 8) by lia. apply Z_mod_mult.
Qed.
End g.

(* ===================================== one runtime call of the piece =====================================
   The three calls differ only in the operation, the destination (always inside the first block) and, for a
   copy, the source (always inside the frame object e). rw8_call is RtPgSteps.rts_intrin_at with those
   obligations discharged once: the destination is writable because the first block is not among the
   journal's start blocks, its shadow comes from the block, and the source's shadow from e's granules. *)
Section ca. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Hypothesis LAWS : AR_laws rsegs B.

Lemma rw8_call : forall op pc raz STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
  (R pp F pos d x n : Z),
aintrin_realizes rsegs B op pc ->
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
rw8_geo STK sp0 own lyc R F pos ->
In (pp, Layout.PP_SIZE) (ablocks B lyc Sc) -> ~ In (pp, Layout.PP_SIZE) (ablocks B ly S) ->
getr regs 1 = w64 raz -> YK0s.ret_ok (w64 raz) ->
getr regs 2 = w64 R -> getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
getr regs 10 = w64 d -> getr regs 11 = w64 x -> getr regs 12 = w64 n ->
pp <= d -> d + n <= pp + Layout.PP_SIZE -> 0 <= n ->
(match op with
 | OCpy => F + 0xf0 <= x /\ x + n <= F + 0x158 /\ rt_fsh rsegs (w_H W) memc F rs_PJ /\
           (forall a, F + 0xf0 <= a < F + 0x158 -> aview rsegs (w_H W) memc a <> None)
 | OSet => True end) ->
SRr rsegs W (cfg_at rsegs pc regs memc mdc)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
  c2 = cfg_at rsegs raz regs2 mem2 md2 /\
  ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem2 md2 k /\
  same_io mdc md2 /\ aregs_preserved regs regs2 /\
  (forall i, 0 <= i < n -> aview rsegs (w_H W) mem2 (d + i) =
     match op with OCpy => aview rsegs (w_H W) memc (x + i) | OSet => Some (x mod 256) end) /\
  (forall a, 0 <= a < 2 ^ 64 -> ~ (d <= a < d + n) -> ~ (R - ESTACK <= a < R) ->
     aview rsegs (w_H W) mem2 a = aview rsegs (w_H W) memc a)).
Proof using LAWS.
intros op pc raz STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs R pp F pos d x n
  AI HJ HG Hpp Hfresh H1 Hret H2 H3 H4 H10 H11 H12 Hd1 Hd2 Hn0 Hsrc.
pose proof HG as (HR16 & HSTK & HRS & HRk & Hown & HF & HFapp & HF32).
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hsp0al & HSTK0 & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof alloc_ceiling_value as (Hc1 & _). pose proof alloc_ceiling_lt as Hc2.
assert (Hes : ESTACK = 4096) by reflexivity.
assert (HTS : T_SEG_STK = 16384) by reflexivity.
assert (Hrq : req_size Layout.PP_SIZE = Layout.PP_SIZE) by reflexivity.
assert (HPS : Layout.PP_SIZE = 19744) by reflexivity.
destruct (al_blocks _ _ LAWS _ _ _ _ _ pp Layout.PP_SIZE HAR Hpp) as (Hp16 & Hp4096 & Hpceil & Happ & Hppres & _).
rewrite Hrq, HPS in Hpceil, Hppres, Happ.
assert (Hin3 : In (3, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; left; exact Hown).
destruct (frames_bounds rsegs B LAWS lyc Sc W memc mdc 3 pos HAR Hin3) as (HF4096 & HFceil & _).
change (fs_frame_bytes 3) with 512 in HF4096, HFceil. rewrite <- HF in HF4096, HFceil.
unfold T_SEG_STK, ASTACK in HSTK, HRk.
assert (HspR : spZ regs = R)
  by (unfold spZ; rewrite H2; unfold w64; apply unsigned_lit_small; unfold kHighMemBeg in HRk; lia).
assert (Hn32 : 0 <= n < 2 ^ 32) by (unfold Layout.PP_SIZE in *; lia).
eapply SRr_mono.
{ eapply (rts_intrin_at B LAWS op pc AI W regs memc STK sp0 FP ly S W0 mem0 md0 own lyc Sc mdc k d x n
    (R - sp0) (w64 raz) HJ H10 H11 H12 Hn32).
  - unfold Layout.PP_SIZE in *; lia.
  - destruct (rt_block_bounds rsegs B LAWS _ _ _ _ _ pp Layout.PP_SIZE HAR Hpp) as (_ & _ & Hb63).
    unfold Layout.PP_SIZE in *; lia.
  - rewrite HspR. lia.
  - rewrite Zminus_mod, HR16, Hsp0al. reflexivity.
  - lia.
  - unfold kHighMemBeg in HRk. lia.
  - exact H3.
  - exact H4.
  - exact H1.
  - exact Hret.
  - intros a Ha. split.
    + replace a with (pp + (a - pp)) by lia.
      apply (rt_fresh_awr _ _ _ _ _ _ _ pp Layout.PP_SIZE); [exact Hpp | exact Hfresh | rewrite Hrq; lia].
    + unfold kHighMemBeg in HRk. unfold Layout.PP_SIZE in *. lia.
  - apply (amem_range_of_block rsegs B LAWS lyc Sc W memc mdc pp Layout.PP_SIZE); [exact HAR | exact Hpp | lia | rewrite Hrq; lia].
  - exact (proj1 (rtm_blk_ra rsegs B lyc Sc W memc mdc pp Layout.PP_SIZE d n HAR Hpp ltac:(lia) ltac:(rewrite Hrq; lia))).
  - exact (proj2 (rtm_blk_ra rsegs B lyc Sc W memc mdc pp Layout.PP_SIZE d n HAR Hpp ltac:(lia) ltac:(rewrite Hrq; lia))).
  - destruct op; [|exact I]. cbv iota in Hsrc |- *.
    destruct Hsrc as (Hx1 & Hx2 & Hfsh & Hpr).
    destruct (al_frames _ _ LAWS lyc Sc W memc mdc 3 pos HAR Hin3) as (_ & _ & _ & Hfs).
    change (fs_frame_bytes 3 / 8) with 64 in Hfs. rewrite <- HF in Hfs.
    destruct (rts_fbounds F HF32 HFapp) as (_ & _ & _ & _ & _ & Hamrf).
    split; [lia|]. split; [lia|]. split.
    { intros a Ha. split; [exact (Hpr a ltac:(lia))|]. rewrite HspR. unfold kHighMemBeg in HRk. lia. }
    split.
    { destruct (rw8_sep B LAWS lyc Sc W memc mdc pp F pos HAR Hpp Hin3 HF) as [Hs|Hs];
      [left | right]; unfold Layout.PP_SIZE in *; lia. }
    split.
    { replace x with (F + (x - F)) by lia. apply Hamrf; lia. }
    split.
    { replace x with (F + 0xf0 + (x - F - 0xf0)) by lia.
      replace (F + 0xf0 + (x - F - 0xf0)) with (F + RTM_E + (x - F - 0xf0)) by (unfold RTM_E; lia).
      apply (rtm_A_ra_e rsegs _ _ F false false false false false false (x - F - 0xf0) n);
      [rewrite <- rw8_PJ_sh; exact Hfsh | apply (rw8_F8 F); exact HF32 | lia | lia]. }
    { intros Hn. replace x with (F + (x - F)) by lia.
      apply (rw8_hull_e _ F (x - F) n HF32 ltac:(lia) ltac:(lia) ltac:(lia) Hn).
      intros i Hi. apply (aview_some_of_apresent rsegs). exact (proj1 (Hfs i Hi)). } }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & Hc & HJ2 & HP & Hsame & Ha0 & Heff & Hfr).
split; [reflexivity|]. exists regs2, mem2, md2.
split; [rewrite Hc; unfold cfg_at; reflexivity|].
split; [exact HJ2|]. split; [exact (same_io_materialized _ _ Hsame)|]. split; [exact HP|].
split; [exact Heff|].
intros a Ha Hn1 Hn2. apply (Hfr a Ha Hn1). rewrite Hes. lia.
Qed.
End ca.

Local Ltac rw8_notin :=
  try unfold rw8_clobA; try unfold rw8_clobB; try unfold rw8_clobC; try unfold rw8_clobD; try unfold rw8_clobJ;
  let H := fresh "H" in intros H; cbn [In] in H;
  repeat (destruct H as [H|H]; [apply (f_equal (@bv_unsigned 5)) in H; vm_compute in H; discriminate H|]);
  exact H.
Local Ltac rw8_nz := vm_compute; lia.

(* ===================================== the piece as one block ===================================== *)
Section p. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis LAWS : AR_laws rsegs B.
Hypothesis AMEMCPY : aintrin_realizes rsegs B OCpy RW8_CPY.
Hypothesis AMEMSET : aintrin_realizes rsegs B OSet RW8_SET.
Hypothesis RUNA : rw8_runA_stmt B MT.
Hypothesis RUNB : rw8_runB_stmt B MT.
Hypothesis RUNC1 : rw8_runC1_stmt B MT.
Hypothesis RUNC0 : rw8_runC0_stmt B MT.
Hypothesis RUND : rw8_runD_stmt B MT.

Lemma rw8_core : rw8_core_stmt B MT.
Proof using MTL LAWS AMEMCPY AMEMSET RUNA RUNB RUNC1 RUNC0 RUND.
unfold rw8_core_stmt.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs R pp F pos len cnt kk rl fsv ed
  HJ HG Hpp Hfresh H2 H3 H4 H9 H18 H19 H20 H22 H23 H24 H26 H27
  Va0 Va8 Vb8 Vf0 V108 V110 V118 V128 V130 V138 Vlen Vnent Hent Hfsh
  Hwf Hlen1 Hlen2 Hlen8 Hcnt Hkk Hfsv Hrl.
pose proof HG as (HR16 & HSTK & HRS & HRk & Hown & HF & HFapp & HF32).
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hsp0al & HSTK0 & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof alloc_ceiling_value as (Hc1 & _). pose proof alloc_ceiling_lt as Hc2.
assert (Hes : ESTACK = 4096) by reflexivity.
assert (HTS : T_SEG_STK = 16384) by reflexivity.
assert (Hrq : req_size Layout.PP_SIZE = Layout.PP_SIZE) by reflexivity.
assert (HPS : Layout.PP_SIZE = 19744) by reflexivity.
destruct (al_blocks _ _ LAWS _ _ _ _ _ pp Layout.PP_SIZE HAR Hpp) as (Hp16 & Hp4096 & Hpceil & Happ & Hppres & _).
rewrite Hrq, HPS in Hpceil, Hppres, Happ.
assert (Hin3 : In (3, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; left; exact Hown).
destruct (frames_bounds rsegs B LAWS lyc Sc W memc mdc 3 pos HAR Hin3) as (HF4096 & HFceil & _).
change (fs_frame_bytes 3) with 512 in HF4096, HFceil. rewrite <- HF in HF4096, HFceil.
unfold T_SEG_STK, ASTACK in HSTK, HRk. unfold kHighMemBeg in HRk.
pose proof (rw8_sep B LAWS lyc Sc W memc mdc pp F pos HAR Hpp Hin3 HF) as Hsep.
rewrite HPS in Hsep.
pose proof Hwf as (Hty & Hbl & Hsz).
assert (Hbody : Z.of_nat (length (e_body ed)) = e_size ed) by (apply rw8_len_body; exact Hwf).
assert (Hpd : 0 <= pad8 (e_size ed) < 8) by apply pad8_bound.
assert (Henc : Z.of_nat (length (enc_pod ed)) = 8 + e_size ed + pad8 (e_size ed))
  by (apply zlen_enc_pod; exact Hwf).
(* e's two header words and its body, read out of the object's bytes *)
assert (Hent0 := Hent).
rewrite rw8_ent_mem_split in Hent.
apply (proj1 (rtm_bytes_app rsegs _ _ _ _ _)) in Hent as [Hty4 Hent].
rewrite length_Z_to_le_bytes in Hent.
apply (proj1 (rtm_bytes_app rsegs _ _ _ _ _)) in Hent as [Hsz4 Hbdy].
rewrite length_Z_to_le_bytes in Hbdy.
assert (Vty : val_mem rsegs (mrestrict (w_H W) memc) (F + 0xf0) 4 (e_type ed))
  by (apply rtm_val_of_bytes; exact Hty4).
assert (Vsz : val_mem rsegs (mrestrict (w_H W) memc) (F + 0xf4) 4 (e_size ed)).
{ apply rtm_val_of_bytes. replace (F + 0xf4) with (F + 0xf0 + Z.of_nat 4) by (cbn; lia). exact Hsz4. }
(* the bytes of e are present (the source of the two copies) *)
assert (Hepr : forall a, F + 0xf0 <= a < F + 0x158 -> aview rsegs (w_H W) memc a <> None).
{ intros a Ha.
  destruct (al_frames _ _ LAWS lyc Sc W memc mdc 3 pos HAR Hin3) as (_ & _ & Hfb & _).
  change (fs_frame_bytes 3) with 512 in Hfb. rewrite <- HF in Hfb.
  apply (aview_some_of_apresent rsegs). exact (proj1 (Hfb a ltac:(lia))). }
(* the write set of the whole piece *)
set (WRA := fun a : Z =>
  (pp + len <= a < pp + len + Z.of_nat (length (enc_pod ed))) \/
  (pp + 0x4000 <= a < pp + 0x4008) \/
  (fsv = 1 /\ pp + 0x4d14 <= a < pp + 0x4d18) \/
  (fsv = 1 /\ pp + 0x4014 + 104 * kk <= a < pp + 0x4014 + 104 * kk + 104) \/
  (shadow_addr F + 0x1e <= a < shadow_addr F + 0x2b) \/
  (R - ESTACK <= a < R)) in *.
lazymatch goal with |- SRr _ _ _ ?P => set (POST := P) end.
assert (Hsp48 : e_size ed + pad8 (e_size ed) <= 48).
{ rewrite pad8_eq. assert ((e_size ed + 7) / 8 < 7) by (apply Z.div_lt_upper_bound; lia). lia. }
assert (HWR1 : forall a, pp + len <= a < pp + len + Z.of_nat (length (enc_pod ed)) -> WRA a)
  by (intros a Ha; left; lia).
assert (HWR2 : forall a, pp + 0x4000 <= a < pp + 0x4008 -> WRA a) by (intros a Ha; right; left; lia).
assert (HWRs : forall a, R - ESTACK <= a < R -> WRA a)
  by (intros a Ha; right; right; right; right; right; lia).
assert (HWRf : forall a, shadow_addr F + 0x1e <= a < shadow_addr F + 0x2b -> WRA a)
  by (intros a Ha; right; right; right; right; left; lia).
(* ================================ run A ================================ *)
eapply SRr_bind.
{ exact (RUNA STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs R pp F pos len (e_size ed)
    (e_type ed) rl HJ HG Hpp Hfresh H2 H9 H18 H19 H22 H23 H24 H26 H27 V108 V130 V138 Vlen Vty Vsz
    Hrl Hlen1 Hlen2 Hlen8 Hsz Hty). }
cbv beta. intros W1 c1 Hw1 (ly1 & S1 & regs1 & mem1 & md1 & -> & HJ1 & Hk1 & Hfr1 & Hperm1 & Hio1 & Hmo1 & Hm1
  & (A1 & A10 & A11 & A12 & A24 & A26 & Alen & Abytes)).
assert (Hpp1 : In (pp, Layout.PP_SIZE) (ablocks B ly1 S1))
  by exact (Permutation_in _ (Permutation_sym Hperm1) Hpp).
assert (Hin31 : In (3, pos) (frames S1)) by (rewrite Hfr1; exact Hin3).
assert (HG1 : rw8_geo STK sp0 own ly1 R F pos).
{ pose proof HJ as (_ & Hlyc & _). pose proof HJ1 as (_ & Hly1 & _).
  exact (rw8_geo_step STK sp0 own lyc ly1 R F pos _ ly HG Hlyc Hly1). }
(* the frame's shadow and the object e lie apart from everything the piece writes *)
assert (Hshd : forall i, 0 <= i < 64 ->
  ~ (pp <= shadow_addr F + i < pp + 19744) /\ ~ (R - ESTACK <= shadow_addr F + i < R)).
{ intros i Hi. unfold shadow_addr.
  assert (HFd : 0 <= F / 8 <= 17592184995840) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
  unfold in_app in Happ. rewrite C3 in *. unfold kLowShadowBeg, SHADOW_OFF, kLowMemEnd in *.
  split; lia. }
assert (HsFb : 2147450880 <= shadow_addr F /\ shadow_addr F + 64 <= 17594332446784).
{ unfold shadow_addr.
  assert (HFd : 0 <= F / 8 <= 17592184995840) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
  unfold SHADOW_OFF. lia. }
assert (Hepp : forall a, F + 0xf0 <= a < F + 0x158 -> ~ (pp <= a < pp + 19744) /\ ~ (R - ESTACK <= a < R))
  by (intros a Ha; split; lia).
(* the body bytes of e, the source of the first copy *)
assert (Hbd8 : rtm_bytes rsegs (w_H W) memc (F + 0xf8) (e_body ed)).
{ apply (proj1 (rtm_bytes_app rsegs _ _ _ _ _)) in Hbdy as [Hb1 _].
  replace (F + 0xf8) with (F + 0xf0 + Z.of_nat 4 + Z.of_nat 4) by (cbn; lia). exact Hb1. }
(* ================================ after run A ================================ *)
assert (KA : forall a, 0 <= a < 2 ^ 64 -> ~ (pp <= a < pp + 19744) ->
  aview rsegs (w_H W1) mem1 a = aview rsegs (w_H W) memc a).
{ intros a Ha Hn. apply Hm1; [exact Ha|]. cbv beta. intros [X|X]; apply Hn; unfold Layout.PP_SIZE in *; lia. }
assert (Hfsh1 : rt_fsh rsegs (w_H W1) mem1 F rs_PJ).
{ intros i Hi. rewrite rw8_PJ_len in Hi.
  assert (Hq : aview rsegs (w_H W1) mem1 (shadow_addr F + i) = aview rsegs (w_H W) memc (shadow_addr F + i))
    by (apply KA; [lia | exact (proj1 (Hshd i ltac:(lia)))]).
  rewrite Hq. apply Hfsh. rewrite rw8_PJ_len. lia. }
assert (Hepr1 : forall a, F + 0xf0 <= a < F + 0x158 -> aview rsegs (w_H W1) mem1 a <> None).
{ intros a Ha.
  assert (Hq : aview rsegs (w_H W1) mem1 a = aview rsegs (w_H W) memc a)
    by (apply KA; [lia | exact (proj1 (Hepp a Ha))]).
  rewrite Hq. exact (Hepr a Ha). }
assert (Hbd81 : rtm_bytes rsegs (w_H W1) mem1 (F + 0xf8) (e_body ed)).
{ eapply rtm_bytes_kept; [exact Hbd8|]. intros y Hy. rewrite Hbody in Hy.
  apply KA; [lia | exact (proj1 (Hepp y ltac:(lia)))]. }
assert (Hent1 : rtm_bytes rsegs (w_H W1) mem1 (F + 0xf0) (ent_mem ed)).
{ eapply rtm_bytes_kept; [exact Hent0|].
  intros y Hy. rewrite length_ent_mem in Hy by lia.
  apply KA; [lia | exact (proj1 (Hepp y ltac:(lia)))]. }
assert (R1_2 : getr regs1 2 = w64 R) by (rewrite (Hk1 (2%bv) ltac:(rw8_nz) ltac:(rw8_notin)); exact H2).
assert (R1_3 : getr regs1 3 = w64 (as_gp B)) by (rewrite (Hk1 (3%bv) ltac:(rw8_nz) ltac:(rw8_notin)); exact H3).
assert (R1_4 : getr regs1 4 = w64 (as_tp B)) by (rewrite (Hk1 (4%bv) ltac:(rw8_nz) ltac:(rw8_notin)); exact H4).
assert (R1_9 : getr regs1 9 = w64 R) by (rewrite (Hk1 (9%bv) ltac:(rw8_nz) ltac:(rw8_notin)); exact H9).
assert (R1_18 : getr regs1 18 = w64 SHADOW_OFF) by (rewrite (Hk1 (18%bv) ltac:(rw8_nz) ltac:(rw8_notin)); exact H18).
assert (R1_19 : getr regs1 19 = w64 (F + 0xe0)) by (rewrite (Hk1 (19%bv) ltac:(rw8_nz) ltac:(rw8_notin)); exact H19).
assert (R1_20 : getr regs1 20 = w64 (shadow_addr F)) by (rewrite (Hk1 (20%bv) ltac:(rw8_nz) ltac:(rw8_notin)); exact H20).
assert (R1_22 : getr regs1 22 = w64 (shadow_addr (pp + 0x4000))) by (rewrite (Hk1 (22%bv) ltac:(rw8_nz) ltac:(rw8_notin)); exact H22).
assert (R1_23 : getr regs1 23 = w64 (pp + 0x4000)) by (rewrite (Hk1 (23%bv) ltac:(rw8_nz) ltac:(rw8_notin)); exact H23).
assert (R1_25 : getr regs1 25 = getr regs 25) by (apply Hk1; [rw8_nz | rw8_notin]).
assert (R1_27 : getr regs1 27 = w64 pp) by (rewrite (Hk1 (27%bv) ltac:(rw8_nz) ltac:(rw8_notin)); exact H27).
(* ================================ the body copy ================================ *)
eapply SRr_bind.
{ eapply (rw8_call B LAWS OCpy RW8_CPY RW8_RA1 STK sp0 FP ly S W0 mem0 md0 own ly1 S1 W1 mem1 md1 k regs1
    R pp F pos (pp + len + 8) (F + 0xf8) (e_size ed)).
  - exact AMEMCPY.
  - exact HJ1.
  - exact HG1.
  - exact Hpp1.
  - exact Hfresh.
  - exact A1.
  - exact rw8_ret1.
  - exact R1_2.
  - exact R1_3.
  - exact R1_4.
  - exact A10.
  - exact A11.
  - exact A12.
  - lia.
  - unfold Layout.PP_SIZE; lia.
  - lia.
  - cbv iota. split; [lia|]. split; [lia|]. split; [exact Hfsh1 | exact Hepr1]. }
cbv beta. intros Wq cq _ (-> & regs2 & mem2 & md2 & -> & HJ2 & Hio2 & HP2 & Heff2 & Hkp2).
assert (HW1 : forall a, 0 <= a < 2 ^ 64 -> ~ WRA a -> aview rsegs (w_H W1) mem1 a = aview rsegs (w_H W) memc a).
{ intros a Ha Hn. apply Hm1; [exact Ha|]. cbv beta. intros [X|X]; apply Hn; [apply HWR1; lia | apply HWR2; lia]. }
assert (K2 : forall a, 0 <= a < 2 ^ 64 -> ~ (pp <= a < pp + 19744) -> ~ (R - ESTACK <= a < R) ->
  aview rsegs (w_H W1) mem2 a = aview rsegs (w_H W1) mem1 a)
  by (intros a Ha Hn1 Hn2; apply Hkp2; [exact Ha | unfold Layout.PP_SIZE in *; lia | lia]).
assert (KC2 : forall a, 0 <= a < 2 ^ 64 -> ~ (pp <= a < pp + 19744) -> ~ (R - ESTACK <= a < R) ->
  aview rsegs (w_H W1) mem2 a = aview rsegs (w_H W) memc a)
  by (intros a Ha H1' H2'; rewrite (K2 a Ha H1' H2'); apply KA; assumption).
assert (HW2 : forall a, 0 <= a < 2 ^ 64 -> ~ WRA a -> aview rsegs (w_H W1) mem2 a = aview rsegs (w_H W) memc a).
{ intros a Ha Hn. rewrite (Hkp2 a Ha ltac:(intros X; apply Hn; apply HWR1; lia)
    ltac:(intros X; apply Hn; apply HWRs; lia)). apply HW1; assumption. }
assert (Hfsh2 : rt_fsh rsegs (w_H W1) mem2 F rs_PJ).
{ intros i Hi. rewrite rw8_PJ_len in Hi.
  assert (Hq : aview rsegs (w_H W1) mem2 (shadow_addr F + i) = aview rsegs (w_H W) memc (shadow_addr F + i))
    by (apply KC2; [lia | exact (proj1 (Hshd i ltac:(lia))) | exact (proj2 (Hshd i ltac:(lia)))]).
  rewrite Hq. apply Hfsh. rewrite rw8_PJ_len. lia. }
assert (Hent2 : rtm_bytes rsegs (w_H W1) mem2 (F + 0xf0) (ent_mem ed)).
{ eapply rtm_bytes_kept; [exact Hent1|]. intros y Hy. rewrite length_ent_mem in Hy by lia.
  apply K2; [lia | exact (proj1 (Hepp y ltac:(lia))) | exact (proj2 (Hepp y ltac:(lia)))]. }
assert (Hepr2 : forall a, F + 0xf0 <= a < F + 0x158 -> aview rsegs (w_H W1) mem2 a <> None).
{ intros a Ha.
  assert (Hq : aview rsegs (w_H W1) mem2 a = aview rsegs (w_H W) memc a)
    by (apply KC2; [lia | exact (proj1 (Hepp a Ha)) | exact (proj2 (Hepp a Ha))]).
  rewrite Hq. exact (Hepr a Ha). }
(* the two header words and the body now sit in the first block *)
assert (Abytes2 : rtm_bytes rsegs (w_H W1) mem2 (pp + len)
  (Z_to_le_bytes 4 (e_size ed) ++ Z_to_le_bytes 4 (e_type ed))).
{ eapply rtm_bytes_kept; [exact Abytes|]. intros y Hy.
  rewrite length_app, !length_Z_to_le_bytes in Hy. apply Hkp2; [lia | lia | lia]. }
assert (Hbdy2 : rtm_bytes rsegs (w_H W1) mem2 (pp + len + 8) (e_body ed)).
{ apply (rtm_memcpy_bytes rsegs (w_H W1) mem1 (w_H W1) mem2 (F + 0xf8) (pp + len + 8) (e_body ed) Hbd81).
  intros i Hi. rewrite Hbody in Hi. apply Heff2. lia. }
assert (Alen2 : val_mem rsegs (mrestrict (w_H W1) mem2) (pp + 0x4000) 8 (len + 8)).
{ apply (rw8_val_kept (w_H W1) mem1); [exact Alen|]. intros x Hx. apply Hkp2; [lia | lia | lia]. }
assert (R2_2 : getr regs2 2 = w64 R) by exact (eq_trans (HP2 2 ltac:(unfold acallee_saved; lia)) R1_2).
assert (R2_3 : getr regs2 3 = w64 (as_gp B)) by exact (eq_trans (HP2 3 ltac:(unfold acallee_saved; lia)) R1_3).
assert (R2_4 : getr regs2 4 = w64 (as_tp B)) by exact (eq_trans (HP2 4 ltac:(unfold acallee_saved; lia)) R1_4).
assert (R2_9 : getr regs2 9 = w64 R) by exact (eq_trans (HP2 9 ltac:(unfold acallee_saved; lia)) R1_9).
assert (R2_18 : getr regs2 18 = w64 SHADOW_OFF) by exact (eq_trans (HP2 18 ltac:(unfold acallee_saved; lia)) R1_18).
assert (R2_19 : getr regs2 19 = w64 (F + 0xe0)) by exact (eq_trans (HP2 19 ltac:(unfold acallee_saved; lia)) R1_19).
assert (R2_20 : getr regs2 20 = w64 (shadow_addr F)) by exact (eq_trans (HP2 20 ltac:(unfold acallee_saved; lia)) R1_20).
assert (R2_22 : getr regs2 22 = w64 (shadow_addr (pp + 0x4000)))
  by exact (eq_trans (HP2 22 ltac:(unfold acallee_saved; lia)) R1_22).
assert (R2_23 : getr regs2 23 = w64 (pp + 0x4000)) by exact (eq_trans (HP2 23 ltac:(unfold acallee_saved; lia)) R1_23).
assert (R2_24 : getr regs2 24 = w64 (e_size ed)) by exact (eq_trans (HP2 24 ltac:(unfold acallee_saved; lia)) A24).
assert (R2_26 : getr regs2 26 = w64 rl) by exact (eq_trans (HP2 26 ltac:(unfold acallee_saved; lia)) A26).
assert (R2_27 : getr regs2 27 = w64 pp) by exact (eq_trans (HP2 27 ltac:(unfold acallee_saved; lia)) R1_27).
assert (R2_25 : getr regs2 25 = getr regs 25) by exact (eq_trans (HP2 25 ltac:(unfold acallee_saved; lia)) R1_25).
(* ================================ run B ================================ *)
eapply SRr_bind.
{ exact (RUNB STK sp0 FP ly S W0 mem0 md0 own ly1 S1 W1 mem2 md2 k regs2 R pp F pos (len + 8) (e_size ed)
    HJ2 HG1 Hpp1 Hfresh R2_2 R2_18 R2_22 R2_23 R2_24 R2_27 Alen2 ltac:(lia) ltac:(lia) Hsz). }
cbv beta. intros W3 c3 Hw3 (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ3 & Hk3 & Hfr3 & Hperm3 & Hio3 & Hmo3 & Hm3
  & (B1 & B10 & B11 & B12 & B24 & Blen)).
rewrite (rw8_pad_shift len (e_size ed) Hlen8) in B12, B24.
assert (Hpp3 : In (pp, Layout.PP_SIZE) (ablocks B ly3 S3))
  by exact (Permutation_in _ (Permutation_sym Hperm3) Hpp1).
assert (Hin33 : In (3, pos) (frames S3)) by (rewrite Hfr3; exact Hin31).
assert (HG3 : rw8_geo STK sp0 own ly3 R F pos).
{ pose proof HJ as (_ & Hlyc & _). pose proof HJ3 as (_ & Hly3 & _).
  exact (rw8_geo_step STK sp0 own lyc ly3 R F pos _ ly HG Hlyc Hly3). }
assert (K3 : forall a, 0 <= a < 2 ^ 64 -> ~ (pp <= a < pp + 19744) -> ~ (R - ESTACK <= a < R) ->
  aview rsegs (w_H W3) mem3 a = aview rsegs (w_H W1) mem2 a)
  by (intros a Ha Hn1 Hn2; apply Hm3; [exact Ha | cbv beta; lia]).
assert (KC3 : forall a, 0 <= a < 2 ^ 64 -> ~ (pp <= a < pp + 19744) -> ~ (R - ESTACK <= a < R) ->
  aview rsegs (w_H W3) mem3 a = aview rsegs (w_H W) memc a)
  by (intros a Ha H1' H2'; rewrite (K3 a Ha H1' H2'); apply KC2; assumption).
assert (HW3 : forall a, 0 <= a < 2 ^ 64 -> ~ WRA a -> aview rsegs (w_H W3) mem3 a = aview rsegs (w_H W) memc a).
{ intros a Ha Hn. rewrite (Hm3 a Ha ltac:(cbv beta; intros X; apply Hn; apply HWR2; lia)).
  apply HW2; assumption. }
assert (Hfsh3 : rt_fsh rsegs (w_H W3) mem3 F rs_PJ).
{ intros i Hi. rewrite rw8_PJ_len in Hi.
  assert (Hq : aview rsegs (w_H W3) mem3 (shadow_addr F + i) = aview rsegs (w_H W) memc (shadow_addr F + i))
    by (apply KC3; [lia | exact (proj1 (Hshd i ltac:(lia))) | exact (proj2 (Hshd i ltac:(lia)))]).
  rewrite Hq. apply Hfsh. rewrite rw8_PJ_len. lia. }
assert (Hent3 : rtm_bytes rsegs (w_H W3) mem3 (F + 0xf0) (ent_mem ed)).
{ eapply rtm_bytes_kept; [exact Hent2|]. intros y Hy. rewrite length_ent_mem in Hy by lia.
  apply K3; [lia | exact (proj1 (Hepp y ltac:(lia))) | exact (proj2 (Hepp y ltac:(lia)))]. }
assert (Hepr3 : forall a, F + 0xf0 <= a < F + 0x158 -> aview rsegs (w_H W3) mem3 a <> None).
{ intros a Ha.
  assert (Hq : aview rsegs (w_H W3) mem3 a = aview rsegs (w_H W) memc a)
    by (apply KC3; [lia | exact (proj1 (Hepp a Ha)) | exact (proj2 (Hepp a Ha))]).
  rewrite Hq. exact (Hepr a Ha). }
assert (Abytes3 : rtm_bytes rsegs (w_H W3) mem3 (pp + len)
  (Z_to_le_bytes 4 (e_size ed) ++ Z_to_le_bytes 4 (e_type ed))).
{ eapply rtm_bytes_kept; [exact Abytes2|]. intros y Hy.
  rewrite length_app, !length_Z_to_le_bytes in Hy. apply Hm3; [lia | cbv beta; lia]. }
assert (Hbdy3 : rtm_bytes rsegs (w_H W3) mem3 (pp + len + 8) (e_body ed)).
{ eapply rtm_bytes_kept; [exact Hbdy2|]. intros y Hy. rewrite Hbody in Hy.
  apply Hm3; [lia | cbv beta; lia]. }
assert (R3_2 : getr regs3 2 = w64 R) by (rewrite (Hk3 (2%bv) ltac:(rw8_nz) ltac:(rw8_notin)); exact R2_2).
assert (R3_3 : getr regs3 3 = w64 (as_gp B)) by (rewrite (Hk3 (3%bv) ltac:(rw8_nz) ltac:(rw8_notin)); exact R2_3).
assert (R3_4 : getr regs3 4 = w64 (as_tp B)) by (rewrite (Hk3 (4%bv) ltac:(rw8_nz) ltac:(rw8_notin)); exact R2_4).
assert (R3_9 : getr regs3 9 = w64 R) by (rewrite (Hk3 (9%bv) ltac:(rw8_nz) ltac:(rw8_notin)); exact R2_9).
assert (R3_18 : getr regs3 18 = w64 SHADOW_OFF) by (rewrite (Hk3 (18%bv) ltac:(rw8_nz) ltac:(rw8_notin)); exact R2_18).
assert (R3_19 : getr regs3 19 = w64 (F + 0xe0)) by (rewrite (Hk3 (19%bv) ltac:(rw8_nz) ltac:(rw8_notin)); exact R2_19).
assert (R3_20 : getr regs3 20 = w64 (shadow_addr F)) by (rewrite (Hk3 (20%bv) ltac:(rw8_nz) ltac:(rw8_notin)); exact R2_20).
assert (R3_22 : getr regs3 22 = w64 (shadow_addr (pp + 0x4000)))
  by (rewrite (Hk3 (22%bv) ltac:(rw8_nz) ltac:(rw8_notin)); exact R2_22).
assert (R3_23 : getr regs3 23 = w64 (pp + 0x4000)) by (rewrite (Hk3 (23%bv) ltac:(rw8_nz) ltac:(rw8_notin)); exact R2_23).
assert (R3_25 : getr regs3 25 = getr regs 25)
  by (rewrite (Hk3 (25%bv) ltac:(rw8_nz) ltac:(rw8_notin)); exact R2_25).
assert (R3_26 : getr regs3 26 = w64 rl) by (rewrite (Hk3 (26%bv) ltac:(rw8_nz) ltac:(rw8_notin)); exact R2_26).
assert (R3_27 : getr regs3 27 = w64 pp) by (rewrite (Hk3 (27%bv) ltac:(rw8_nz) ltac:(rw8_notin)); exact R2_27).
(* ================================ the pad fill ================================ *)
eapply SRr_bind.
{ eapply (rw8_call B LAWS OSet RW8_SET RW8_RA2 STK sp0 FP ly S W0 mem0 md0 own ly3 S3 W3 mem3 md3 k regs3
    R pp F pos (pp + (len + 8 + e_size ed)) 0 (pad8 (e_size ed))).
  - exact AMEMSET.
  - exact HJ3.
  - exact HG3.
  - exact Hpp3.
  - exact Hfresh.
  - exact B1.
  - exact rw8_ret2.
  - exact R3_2.
  - exact R3_3.
  - exact R3_4.
  - exact B10.
  - exact B11.
  - exact B12.
  - lia.
  - unfold Layout.PP_SIZE; lia.
  - lia.
  - exact I. }
cbv beta. intros Wr4 cr4 _ (-> & regs4 & mem4 & md4 & -> & HJ4 & Hio4 & HP4 & Heff4 & Hkp4).
(* the cells of the first block that the piece has not written yet *)
assert (HU1 : forall a, 0 <= a < 2 ^ 64 ->
  ~ (pp + len <= a < pp + len + Z.of_nat (length (enc_pod ed))) -> ~ (pp + 0x4000 <= a < pp + 0x4008) ->
  ~ (R - ESTACK <= a < R) -> aview rsegs (w_H W1) mem1 a = aview rsegs (w_H W) memc a)
  by (intros a Ha U1 U2 U3; apply Hm1; [exact Ha | cbv beta; intros [X|X]; [apply U1; lia | apply U2; lia]]).
assert (HU2 : forall a, 0 <= a < 2 ^ 64 ->
  ~ (pp + len <= a < pp + len + Z.of_nat (length (enc_pod ed))) -> ~ (pp + 0x4000 <= a < pp + 0x4008) ->
  ~ (R - ESTACK <= a < R) -> aview rsegs (w_H W1) mem2 a = aview rsegs (w_H W) memc a)
  by (intros a Ha U1 U2 U3; rewrite (Hkp2 a Ha ltac:(lia) ltac:(lia)); apply HU1; assumption).
assert (HU3 : forall a, 0 <= a < 2 ^ 64 ->
  ~ (pp + len <= a < pp + len + Z.of_nat (length (enc_pod ed))) -> ~ (pp + 0x4000 <= a < pp + 0x4008) ->
  ~ (R - ESTACK <= a < R) -> aview rsegs (w_H W3) mem3 a = aview rsegs (w_H W) memc a)
  by (intros a Ha U1 U2 U3; rewrite (Hm3 a Ha ltac:(cbv beta; lia)); apply HU2; assumption).
assert (HU4 : forall a, 0 <= a < 2 ^ 64 ->
  ~ (pp + len <= a < pp + len + Z.of_nat (length (enc_pod ed))) -> ~ (pp + 0x4000 <= a < pp + 0x4008) ->
  ~ (R - ESTACK <= a < R) -> aview rsegs (w_H W3) mem4 a = aview rsegs (w_H W) memc a)
  by (intros a Ha U1 U2 U3; rewrite (Hkp4 a Ha ltac:(lia) ltac:(lia)); apply HU3; assumption).
assert (HW4 : forall a, 0 <= a < 2 ^ 64 -> ~ WRA a -> aview rsegs (w_H W3) mem4 a = aview rsegs (w_H W) memc a).
{ intros a Ha Hn. rewrite (Hkp4 a Ha ltac:(intros X; apply Hn; apply HWR1; lia)
    ltac:(intros X; apply Hn; apply HWRs; lia)). apply HW3; assumption. }
assert (KC4 : forall a, 0 <= a < 2 ^ 64 -> ~ (pp <= a < pp + 19744) -> ~ (R - ESTACK <= a < R) ->
  aview rsegs (w_H W3) mem4 a = aview rsegs (w_H W) memc a)
  by (intros a Ha U1 U2; apply HU4; [exact Ha | lia | lia | exact U2]).
assert (Hfsh4 : rt_fsh rsegs (w_H W3) mem4 F rs_PJ).
{ intros i Hi. rewrite rw8_PJ_len in Hi.
  assert (Hq : aview rsegs (w_H W3) mem4 (shadow_addr F + i) = aview rsegs (w_H W) memc (shadow_addr F + i))
    by (apply KC4; [lia | exact (proj1 (Hshd i ltac:(lia))) | exact (proj2 (Hshd i ltac:(lia)))]).
  rewrite Hq. apply Hfsh. rewrite rw8_PJ_len. lia. }
assert (Hent4 : rtm_bytes rsegs (w_H W3) mem4 (F + 0xf0) (ent_mem ed)).
{ eapply rtm_bytes_kept; [exact Hent3|]. intros y Hy. rewrite length_ent_mem in Hy by lia.
  apply Hkp4; [lia | lia | lia]. }
assert (Hepr4 : forall a, F + 0xf0 <= a < F + 0x158 -> aview rsegs (w_H W3) mem4 a <> None).
{ intros a Ha.
  assert (Hq : aview rsegs (w_H W3) mem4 a = aview rsegs (w_H W) memc a)
    by (apply KC4; [lia | exact (proj1 (Hepp a Ha)) | exact (proj2 (Hepp a Ha))]).
  rewrite Hq. exact (Hepr a Ha). }
assert (Abytes4 : rtm_bytes rsegs (w_H W3) mem4 (pp + len)
  (Z_to_le_bytes 4 (e_size ed) ++ Z_to_le_bytes 4 (e_type ed))).
{ eapply rtm_bytes_kept; [exact Abytes3|]. intros y Hy.
  rewrite length_app, !length_Z_to_le_bytes in Hy. apply Hkp4; [lia | lia | lia]. }
assert (Hbdy4 : rtm_bytes rsegs (w_H W3) mem4 (pp + len + 8) (e_body ed)).
{ eapply rtm_bytes_kept; [exact Hbdy3|]. intros y Hy. rewrite Hbody in Hy. apply Hkp4; [lia | lia | lia]. }
assert (Hpad4 : rtm_bytes rsegs (w_H W3) mem4 (pp + len + 8 + e_size ed)
  (repeat NUL (Z.to_nat (pad8 (e_size ed))))).
{ apply (rtm_memset_bytes rsegs (w_H W3) mem4 (pp + len + 8 + e_size ed) 0 (Z.to_nat (pad8 (e_size ed)))).
  intros i Hi. rewrite Z2Nat.id in Hi by lia.
  replace (pp + len + 8 + e_size ed + i) with (pp + (len + 8 + e_size ed) + i) by lia.
  rewrite (Heff4 i ltac:(lia)). reflexivity. }
assert (Alen4 : val_mem rsegs (mrestrict (w_H W3) mem4) (pp + 0x4000) 8 (len + 8 + e_size ed)).
{ apply (rw8_val_kept (w_H W3) mem3); [exact Blen|]. intros x Hx. apply Hkp4; [lia | lia | lia]. }
assert (Vnent4 : fsv = 1 -> val_mem rsegs (mrestrict (w_H W3) mem4) (pp + 0x4d14) 4 kk).
{ intros Hf1. apply (rw8_val_kept (w_H W) memc); [exact (Vnent Hf1)|].
  intros x Hx. apply HU4; [lia | lia | lia | lia]. }
assert (Vcell4 : forall o v, 0xa0 <= o <= 0x138 -> val_mem rsegs (mrestrict (w_H W) memc) (R + o) 8 v ->
  val_mem rsegs (mrestrict (w_H W3) mem4) (R + o) 8 v).
{ intros o v Ho Hv. apply (rw8_val_kept (w_H W) memc); [exact Hv|].
  intros x Hx. apply HU4; [lia | lia | lia | lia]. }
assert (R4_2 : getr regs4 2 = w64 R) by exact (eq_trans (HP4 2 ltac:(unfold acallee_saved; lia)) R3_2).
assert (R4_3 : getr regs4 3 = w64 (as_gp B)) by exact (eq_trans (HP4 3 ltac:(unfold acallee_saved; lia)) R3_3).
assert (R4_4 : getr regs4 4 = w64 (as_tp B)) by exact (eq_trans (HP4 4 ltac:(unfold acallee_saved; lia)) R3_4).
assert (R4_9 : getr regs4 9 = w64 R) by exact (eq_trans (HP4 9 ltac:(unfold acallee_saved; lia)) R3_9).
assert (R4_18 : getr regs4 18 = w64 SHADOW_OFF) by exact (eq_trans (HP4 18 ltac:(unfold acallee_saved; lia)) R3_18).
assert (R4_19 : getr regs4 19 = w64 (F + 0xe0)) by exact (eq_trans (HP4 19 ltac:(unfold acallee_saved; lia)) R3_19).
assert (R4_20 : getr regs4 20 = w64 (shadow_addr F)) by exact (eq_trans (HP4 20 ltac:(unfold acallee_saved; lia)) R3_20).
assert (R4_22 : getr regs4 22 = w64 (shadow_addr (pp + 0x4000)))
  by exact (eq_trans (HP4 22 ltac:(unfold acallee_saved; lia)) R3_22).
assert (R4_23 : getr regs4 23 = w64 (pp + 0x4000)) by exact (eq_trans (HP4 23 ltac:(unfold acallee_saved; lia)) R3_23).
assert (R4_24 : getr regs4 24 = w64 (pad8 (e_size ed))) by exact (eq_trans (HP4 24 ltac:(unfold acallee_saved; lia)) B24).
assert (R4_25 : getr regs4 25 = getr regs 25) by exact (eq_trans (HP4 25 ltac:(unfold acallee_saved; lia)) R3_25).
assert (R4_26 : getr regs4 26 = w64 rl) by exact (eq_trans (HP4 26 ltac:(unfold acallee_saved; lia)) R3_26).
assert (R4_27 : getr regs4 27 = w64 pp) by exact (eq_trans (HP4 27 ltac:(unfold acallee_saved; lia)) R3_27).
assert (RK4 : forall r : bv 5, bv_unsigned r <> 0 -> ~ In r rw8_clobJ -> getr regs4 r = getr regs r).
{ intros r Hr0 Hn. destruct (rw8_outJ r Hr0 Hn) as (Hcs & HnA & HnB & HnC & HnD & Hnc).
  rewrite (rw8_pres regs3 regs4 r HP4 Hcs), (Hk3 r Hr0 HnB), (rw8_pres regs1 regs2 r HP2 Hcs), (Hk1 r Hr0 HnA).
  reflexivity. }
assert (Hfr34 : frames S3 = frames Sc) by (rewrite Hfr3, Hfr1; reflexivity).
assert (Hperm34 : Permutation (ablocks B ly3 S3) (ablocks B lyc Sc))
  by (eapply Permutation_trans; [exact Hperm3 | exact Hperm1]).
assert (Hio_4 : same_io mdc md4).
{ eapply same_io_trans; [exact Hio1|]. eapply same_io_trans; [exact Hio2|].
  eapply same_io_trans; [exact Hio3 | exact Hio4]. }
assert (Hmo_4 : mo_le MT Sc S3 0).
{ pose proof (mle_station MT Sc S1 S3 0 0 MTL Hmo1 Hmo3) as HM. rewrite Z.add_0_r in HM. exact HM. }
assert (Henc4 : rtm_bytes rsegs (w_H W3) mem4 (pp + len) (enc_pod ed)).
{ rewrite rw8_enc_pod_split. apply (proj2 (rtm_bytes_app rsegs _ _ _ _ _)). split; [exact Abytes4|].
  rewrite length_app, !length_Z_to_le_bytes.
  apply (proj2 (rtm_bytes_app rsegs _ _ _ _ _)). split.
  - replace (pp + len + Z.of_nat (4 + 4)) with (pp + len + 8) by lia. exact Hbdy4.
  - replace (pp + len + Z.of_nat (4 + 4) + Z.of_nat (length (e_body ed))) with (pp + len + 8 + e_size ed)
      by lia. exact Hpad4. }
assert (HnWR : forall x, R <= x < R + 0x140 -> ~ WRA x).
{ intros x Hx. unfold WRA. intros [X|[X|[X|[X|[X|X]]]]]; lia. }
assert (HnWS : forall y i, pp <= y < pp + 19744 -> 0x1e <= i < 0x2b -> y <> shadow_addr F + i).
{ intros y i Hy Hi Heq. apply (proj1 (Hshd i ltac:(lia))). lia. }
(* ================================ the last run and the piece's end state ================================ *)
assert (TAIL : forall ly5 S5 (W5 : world rsegs) regs5 mem5 md5 pc0,
  ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own ly5 S5 W5 mem5 md5 k ->
  (pc0 = RW8_RA3 \/ pc0 = RW8_T0) -> (pc0 = RW8_T0 -> getr regs5 11 = w64 kk) ->
  frames S5 = frames Sc -> Permutation (ablocks B ly5 S5) (ablocks B lyc Sc) ->
  same_io mdc md5 -> mo_le MT Sc S5 0 ->
  (forall r : bv 5, bv_unsigned r <> 0 -> ~ In r rw8_clobJ -> getr regs5 r = getr regs r) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ WRA a -> aview rsegs (w_H W5) mem5 a = aview rsegs (w_H W) memc a) ->
  getr regs5 24 = w64 rl -> getr regs5 26 = w64 ((- 0x4001) mod 2 ^ 64) ->
  val_mem rsegs (mrestrict (w_H W5) mem5) (pp + 0x4000) 8 (len + Z.of_nat (length (enc_pod ed))) ->
  rtm_bytes rsegs (w_H W5) mem5 (pp + len) (enc_pod ed) ->
  (fsv = 1 -> rtm_bytes rsegs (w_H W5) mem5 (pp + 0x4014 + 104 * kk) (ent_mem ed) /\
              val_mem rsegs (mrestrict (w_H W5) mem5) (pp + 0x4d14) 4 (kk + 1)) ->
  rt_fsh rsegs (w_H W5) mem5 F rs_PJ ->
  SRr rsegs W5 (cfg_at rsegs pc0 regs5 mem5 md5) POST).
{ intros ly5 S5 W5 regs5 mem5 md5 pc0 HJ5 Hpc0 Ha1 Hfr5 Hperm5 Hio5 Hmo5 RK5 HW5 R5_24 R5_26 Vlen5 Henc5 Hrec5 Hfsh5.
  assert (HG5 : rw8_geo STK sp0 own ly5 R F pos).
  { pose proof HJ as (_ & Hlyc & _). pose proof HJ5 as (_ & Hly5 & _).
    exact (rw8_geo_step STK sp0 own lyc ly5 R F pos _ ly HG Hlyc Hly5). }
  assert (R5_2 : getr regs5 2 = w64 R) by (rewrite (RK5 (2%bv) ltac:(rw8_nz) ltac:(rw8_notin)); exact H2).
  assert (R5_9 : getr regs5 9 = w64 R) by (rewrite (RK5 (9%bv) ltac:(rw8_nz) ltac:(rw8_notin)); exact H9).
  assert (R5_20 : getr regs5 20 = w64 (shadow_addr F)) by (rewrite (RK5 (20%bv) ltac:(rw8_nz) ltac:(rw8_notin)); exact H20).
  assert (Vf05 : val_mem rsegs (mrestrict (w_H W5) mem5) (R + 0xf0) 8 cnt).
  { apply (rw8_val_kept (w_H W) memc); [exact Vf0|]. intros x Hx. apply HW5; [lia | apply HnWR; lia]. }
  assert (V1285 : val_mem rsegs (mrestrict (w_H W5) mem5) (R + 0x128) 8 kk).
  { apply (rw8_val_kept (w_H W) memc); [exact V128|]. intros x Hx. apply HW5; [lia | apply HnWR; lia]. }
  eapply SRr_mono.
  { exact (RUND STK sp0 FP ly S W0 mem0 md0 own ly5 S5 W5 mem5 md5 k regs5 R F pos cnt kk pc0
      HJ5 HG5 Hpc0 Ha1 R5_2 R5_9 R5_20 Vf05 V1285 ltac:(lia) Hkk). }
  intros W7 c7 Hw7 (ly7 & S7 & regs7 & mem7 & md7 & -> & HJ7 & Hk7 & Hfr7 & Hperm7 & Hio7 & Hmo7 & Hm7 & (D11 & D13)).
  unfold POST, rts_post. exists ly7, S7, regs7, mem7, md7.
  split; [reflexivity|]. split; [exact HJ7|].
  split.
  { intros r Hr0 Hn. destruct (rw8_outJ r Hr0 Hn) as (_ & _ & _ & _ & HnD & _).
    rewrite (Hk7 r Hr0 HnD). exact (RK5 r Hr0 Hn). }
  split; [rewrite Hfr7; exact Hfr5|].
  split; [eapply Permutation_trans; [exact Hperm7 | exact Hperm5]|].
  split; [eapply same_io_trans; [exact Hio5 | exact Hio7]|].
  split; [pose proof (mle_station MT Sc S5 S7 0 0 MTL Hmo5 Hmo7) as HM; rewrite Z.add_0_r in HM; exact HM|].
  split.
  { intros a Ha Hn. rewrite (Hm7 a Ha ltac:(cbv beta; intros X; apply Hn; apply HWRf; exact X)).
    apply HW5; assumption. }
  cbv beta.
  split; [exact D11|].
  split; [rewrite (Hk7 (24%bv) ltac:(rw8_nz) ltac:(rw8_notin)); exact R5_24|].
  split; [rewrite (Hk7 (26%bv) ltac:(rw8_nz) ltac:(rw8_notin)); exact R5_26|].
  split.
  { apply (rw8_val_kept (w_H W5) mem5); [exact Vlen5|]. intros x Hx.
    apply Hm7; [lia | cbv beta; intros X; apply (HnWS x (x - shadow_addr F)); lia]. }
  split.
  { eapply rtm_bytes_kept; [exact Henc5|]. intros y Hy. rewrite Henc in Hy.
    apply Hm7; [lia | cbv beta; intros X; apply (HnWS y (y - shadow_addr F)); lia]. }
  split.
  { intros Hf. destruct (Hrec5 Hf) as [Hr1 Hr2]. split.
    - eapply rtm_bytes_kept; [exact Hr1|]. intros y Hy. rewrite length_ent_mem in Hy by lia.
      apply Hm7; [lia | cbv beta; intros X; apply (HnWS y (y - shadow_addr F)); lia].
    - apply (rw8_val_kept (w_H W5) mem5); [exact Hr2|]. intros x Hx.
      apply Hm7; [lia | cbv beta; intros X; apply (HnWS x (x - shadow_addr F)); lia]. }
  replace rs_P0 with (rtm_setn rs_PJ 30 13 0xf8) by (vm_compute; reflexivity).
  apply (rtm_fsh_set rsegs (w_H W5) mem5 (w_H W7) mem7 F rs_PJ 30 13 0xf8 Hfsh5).
  - intros i Hi. cbn in Hi. replace (shadow_addr F + i) with (shadow_addr F + 0x1e + (i - 30)) by lia.
    apply D13. lia.
  - intros i Hi Hn. rewrite rw8_PJ_len in Hi. cbn in Hn. apply Hm7; [lia | cbv beta; lia]. }
(* ================================ run C, by `first` ================================ *)
destruct Hfsv as [Hf | Hf]; subst fsv.
- (* first clear: run C0, then the last run from 0x81ffc *)
  eapply SRr_bind.
  { exact (RUNC0 STK sp0 FP ly S W0 mem0 md0 own ly3 S3 W3 mem4 md4 k regs4 R pp F pos (len + 8 + e_size ed)
      (pad8 (e_size ed)) kk rl HJ4 HG3 Hpp3 Hfresh R4_2 R4_9 R4_18 R4_22 R4_23 R4_24 R4_26 R4_27
      (Vcell4 0x110 0 ltac:(lia) V110) (Vcell4 0x118 _ ltac:(lia) V118) (Vcell4 0x128 kk ltac:(lia) V128) Alen4
      ltac:(lia) ltac:(lia) ltac:(lia) Hkk Hrl). }
  cbv beta. intros W5 c5 Hw5 (ly5 & S5 & regs5 & mem5 & md5 & -> & HJ5 & Hk5 & Hfr5 & Hperm5 & Hio5 & Hmo5 & Hm5
    & (C11 & C24 & C26 & Clen)).
  apply (TAIL ly5 S5 W5 regs5 mem5 md5 RW8_T0 HJ5 (or_intror eq_refl) (fun _ => C11)).
  + rewrite Hfr5. exact Hfr34.
  + eapply Permutation_trans; [exact Hperm5 | exact Hperm34].
  + eapply same_io_trans; [exact Hio_4 | exact Hio5].
  + pose proof (mle_station MT Sc S3 S5 0 0 MTL Hmo_4 Hmo5) as HM. rewrite Z.add_0_r in HM. exact HM.
  + intros r Hr0 Hn. destruct (rw8_outJ r Hr0 Hn) as (_ & _ & _ & HnC & _ & _).
    rewrite (Hk5 r Hr0 HnC). exact (RK4 r Hr0 Hn).
  + intros a Ha Hn. rewrite (Hm5 a Ha ltac:(cbv beta; intros X; apply Hn; apply HWR2; exact X)).
    apply HW4; assumption.
  + exact C24.
  + exact C26.
  + rewrite Henc. replace (len + (8 + e_size ed + pad8 (e_size ed))) with (len + 8 + e_size ed + pad8 (e_size ed))
      by lia. exact Clen.
  + eapply rtm_bytes_kept; [exact Henc4|]. intros y Hy. rewrite Henc in Hy. apply Hm5; [lia | cbv beta; lia].
  + intros X. lia.
  + intros i Hi. rewrite rw8_PJ_len in Hi.
    rewrite (Hm5 (shadow_addr F + i) ltac:(lia) ltac:(cbv beta; intros X; apply (proj1 (Hshd i ltac:(lia))); lia)).
    apply Hfsh4. rewrite rw8_PJ_len. lia.
- (* first set: run C1, the record copy, then the last run from 0x81ff8 *)
  eapply SRr_bind.
  { exact (RUNC1 STK sp0 FP ly S W0 mem0 md0 own ly3 S3 W3 mem4 md4 k regs4 R pp F pos (len + 8 + e_size ed)
      (pad8 (e_size ed)) kk rl HJ4 HG3 Hpp3 Hfresh R4_2 R4_9 R4_18 R4_19 R4_22 R4_23 R4_24 R4_26 R4_27
      (Vcell4 0xa0 _ ltac:(lia) Va0) (Vcell4 0xa8 _ ltac:(lia) Va8) (Vcell4 0xb8 _ ltac:(lia) Vb8)
      (Vcell4 0x110 1 ltac:(lia) V110) (Vcell4 0x118 _ ltac:(lia) V118) (Vcell4 0x138 _ ltac:(lia) V138)
      Alen4 (Vnent4 eq_refl) ltac:(lia) ltac:(lia) ltac:(lia) Hkk Hrl). }
  cbv beta. intros W5 c5 Hw5 (ly5 & S5 & regs5 & mem5 & md5 & -> & HJ5 & Hk5 & Hfr5 & Hperm5 & Hio5 & Hmo5 & Hm5
    & (E1 & E10 & E11 & E12 & E24 & E26 & Elen & Enent)).
  assert (Hpp5 : In (pp, Layout.PP_SIZE) (ablocks B ly5 S5))
    by exact (Permutation_in _ (Permutation_sym Hperm5) Hpp3).
  assert (HG5 : rw8_geo STK sp0 own ly5 R F pos).
  { pose proof HJ as (_ & Hlyc & _). pose proof HJ5 as (_ & Hly5 & _).
    exact (rw8_geo_step STK sp0 own lyc ly5 R F pos _ ly HG Hlyc Hly5). }
  assert (K5 : forall a, 0 <= a < 2 ^ 64 -> ~ (pp <= a < pp + 19744) ->
    aview rsegs (w_H W5) mem5 a = aview rsegs (w_H W3) mem4 a)
    by (intros a Ha Hn; apply Hm5; [exact Ha | cbv beta; lia]).
  assert (Hfsh5 : rt_fsh rsegs (w_H W5) mem5 F rs_PJ).
  { intros i Hi. rewrite rw8_PJ_len in Hi.
    rewrite (K5 (shadow_addr F + i) ltac:(lia) (proj1 (Hshd i ltac:(lia)))).
    apply Hfsh4. rewrite rw8_PJ_len. lia. }
  assert (Hent5 : rtm_bytes rsegs (w_H W5) mem5 (F + 0xf0) (ent_mem ed)).
  { eapply rtm_bytes_kept; [exact Hent4|]. intros y Hy. rewrite length_ent_mem in Hy by lia.
    apply K5; [lia | exact (proj1 (Hepp y ltac:(lia)))]. }
  assert (Hepr5 : forall a, F + 0xf0 <= a < F + 0x158 -> aview rsegs (w_H W5) mem5 a <> None).
  { intros a Ha. rewrite (K5 a ltac:(lia) (proj1 (Hepp a Ha))). exact (Hepr4 a Ha). }
  assert (RK5 : forall r : bv 5, bv_unsigned r <> 0 -> ~ In r rw8_clobJ -> getr regs5 r = getr regs r).
  { intros r Hr0 Hn. destruct (rw8_outJ r Hr0 Hn) as (_ & _ & _ & HnC & _ & _).
    rewrite (Hk5 r Hr0 HnC). exact (RK4 r Hr0 Hn). }
  assert (R5_2 : getr regs5 2 = w64 R) by (rewrite (RK5 (2%bv) ltac:(rw8_nz) ltac:(rw8_notin)); exact H2).
  assert (R5_3 : getr regs5 3 = w64 (as_gp B)) by (rewrite (RK5 (3%bv) ltac:(rw8_nz) ltac:(rw8_notin)); exact H3).
  assert (R5_4 : getr regs5 4 = w64 (as_tp B)) by (rewrite (RK5 (4%bv) ltac:(rw8_nz) ltac:(rw8_notin)); exact H4).
  eapply SRr_bind.
  { eapply (rw8_call B LAWS OCpy RW8_CPY RW8_RA3 STK sp0 FP ly S W0 mem0 md0 own ly5 S5 W5 mem5 md5 k regs5
      R pp F pos (pp + 0x4014 + 104 * kk) (F + 0xf0) 104).
    - exact AMEMCPY.
    - exact HJ5.
    - exact HG5.
    - exact Hpp5.
    - exact Hfresh.
    - exact E1.
    - exact rw8_ret3.
    - exact R5_2.
    - exact R5_3.
    - exact R5_4.
    - exact E10.
    - exact E11.
    - exact E12.
    - lia.
    - unfold Layout.PP_SIZE; lia.
    - lia.
    - cbv iota. split; [lia|]. split; [lia|]. split; [exact Hfsh5 | exact Hepr5]. }
  cbv beta. intros Wr6 cr6 _ (-> & regs6 & mem6 & md6 & -> & HJ6 & Hio6 & HP6 & Heff6 & Hkp6).
  apply (TAIL ly5 S5 W5 regs6 mem6 md6 RW8_RA3 HJ6 (or_introl eq_refl)
    ltac:(unfold RW8_RA3, RW8_T0; intros X; lia)).
  + rewrite Hfr5. exact Hfr34.
  + eapply Permutation_trans; [exact Hperm5 | exact Hperm34].
  + eapply same_io_trans; [exact Hio_4|]. eapply same_io_trans; [exact Hio5 | exact Hio6].
  + pose proof (mle_station MT Sc S3 S5 0 0 MTL Hmo_4 Hmo5) as HM. rewrite Z.add_0_r in HM. exact HM.
  + intros r Hr0 Hn. destruct (rw8_outJ r Hr0 Hn) as (Hcs & _ & _ & _ & _ & _).
    rewrite (rw8_pres regs5 regs6 r HP6 Hcs). exact (RK5 r Hr0 Hn).
  + intros a Ha Hn.
    rewrite (Hkp6 a Ha ltac:(intros X; apply Hn; right; right; right; left; split; [reflexivity | lia])
      ltac:(intros X; apply Hn; apply HWRs; exact X)).
    rewrite (Hm5 a Ha ltac:(cbv beta; intros [X|X]; apply Hn; [apply HWR2; exact X | right; right; left; split; [reflexivity | exact X]])).
    apply HW4; assumption.
  + exact (eq_trans (HP6 24 ltac:(unfold acallee_saved; lia)) E24).
  + exact (eq_trans (HP6 26 ltac:(unfold acallee_saved; lia)) E26).
  + apply (rw8_val_kept (w_H W5) mem5); [|intros x Hx; apply Hkp6; [lia | lia | lia]].
    rewrite Henc. replace (len + (8 + e_size ed + pad8 (e_size ed))) with (len + 8 + e_size ed + pad8 (e_size ed))
      by lia. exact Elen.
  + eapply rtm_bytes_kept; [exact Henc4|]. intros y Hy. rewrite Henc in Hy.
    rewrite (Hkp6 y ltac:(lia) ltac:(lia) ltac:(lia)). apply Hm5; [lia | cbv beta; lia].
  + intros _. split.
    * apply (rtm_memcpy_bytes rsegs (w_H W5) mem5 (w_H W5) mem6 (F + 0xf0) (pp + 0x4014 + 104 * kk) (ent_mem ed) Hent5).
      intros i Hi. rewrite length_ent_mem in Hi by lia. apply Heff6. lia.
    * apply (rw8_val_kept (w_H W5) mem5); [exact Enent|]. intros x Hx. apply Hkp6; [lia | lia | lia].
  + intros i Hi. rewrite rw8_PJ_len in Hi.
    rewrite (Hkp6 (shadow_addr F + i) ltac:(lia) ltac:(intros X; apply (proj1 (Hshd i ltac:(lia))); lia)
      (proj2 (Hshd i ltac:(lia)))).
    apply Hfsh5. rewrite rw8_PJ_len. lia.
Qed.
End p.

Print Assumptions rw8_core.
