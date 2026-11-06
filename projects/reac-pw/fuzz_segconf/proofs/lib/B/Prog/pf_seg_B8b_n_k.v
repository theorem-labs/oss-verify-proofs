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
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/check_round_trip.v, with its module paths and module names changed; 521 of its 608 lines of code are new or changed and 4966 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/pf_seg_B8b_s.v, with its module names changed; 381 of its 478 lines of code are new or changed and 511 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, image B (fuzz_segconf.asan-ubsan, pin c3796c0b38f3, twin 80e82127e8ca): the kit of the NEW
   sub-walk of segment B8b of reac_segconf_parse_file's walk (lib/B/Prog/pf_seg_B8b_n.v, pb8b_new_holds : NEW
   0x88e54 -> JOIN 0x88f00). A B8b sub-lane of the image-B G3 walk owner, 2026-10-30.
   proves no function (kind: segment kit: closed arithmetic, byte-splice and fact-transport lemmas; no instruction
   is walked here). Reuse search and CONFIRM: the rule-24 lookup record (verdict none).
   ADAPTED from a working branch's lib/A/Prog/pf_a8b_m.v / pf_a8b_k.v (the byte splices and the keep clause,
   here over pf_seg_B8b_m.v), the image-B G3 walk owner's lib/B/Prog/pf_seg_B9_c.v (commit 47521c589cf3: the
   addressability of buf from the frame's shadow cells, b9_addr_cells / b9_sa_addr_sub / b9_hull_sub) and
   lib/B/Prog/pf_seg_B10b_j.v (commit 961c19ce3f65: the keep lemmas of a cut's objects), re-stated
   for NEW's write set.

   WHAT NEW WRITES (the whole path NEW -> JOIN): c->n (4 bytes at c + RC_N, the `sw` at 0x88e64), c->seg[n] (356
   bytes, checked_memset 0x88e90, then the name and its NUL, wrapper_snprintf 0x88ea8), and the two callees' stack
   windows below s1 (memset ESTACK, snprintf CMD_SNP_K = 2 * ESTACK). pb8bn_Wr is that set; pb8bn_kept says a reader
   agrees with another outside it. Every object a cut names lies outside it: the text (apart from c by reader_pre's
   sa_disj), c's shadow and the frame's shadow cells (the shadow band, below kHighMemBeg <= alloc_ceiling), the
   image (off the block, which AR keeps off the image), the class-5 frame (apart from c, pb8b_cblk), the real-stack
   slots and the saved registers (at and above s1). The record c holds after the three writes is pb8bn_rconf_new
   (pf_seg_B8b_m.v's pb8b_rconf_newseg over a reader equal to the new one on the block). *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI00 YI04.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Mem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pf_pieces_spec pfA_facts.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaRun PaShadow PaJournal SegSyms SegList
SegAddr SegPa SegObj SegGlob.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPaLib PaDenot PaLibG PaLibF PaLibH PaSB
PaCall PaCallRun PaArt PaFx.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import refuse_c reac_segconf_parse_file_c
SegInstB pf_pieces pf_seg_B8b_d pf_seg_B8b_m.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ================================ ranges of the shadow (pf_seg_B9_c.v) ================================ *)
Lemma pb8bn_hull_sub : forall (rd : reader) q n q' n', shadow_hull_vis rd q n -> q <= q' -> 0 < n' ->
  q' + n' <= q + n -> shadow_hull_vis rd q' n'.
Proof.
  intros rd q n q' n' H Hq Hn Hle s Hs. apply H.
  pose proof (shadow_mono q q' Hq) as M1.
  pose proof (shadow_mono (q' + n' - 1) (q + n - 1) ltac:(lia)) as M2.
  assert (R8 : forall u w, u <= w -> u / 8 * 8 <= w / 8 * 8)
    by (intros u w Huw; apply Z.mul_le_mono_nonneg_r; [lia|]; apply Z.div_le_mono; lia).
  pose proof (R8 _ _ M1). pose proof (R8 _ _ M2). lia.
Qed.
Lemma pb8bn_sa_addr_sub : forall (rd : reader) q n q' n', sa_addr rd q n -> q <= q' -> 0 <= n' ->
  q' + n' <= q + n -> sa_addr rd q' n'.
Proof.
  intros rd q n q' n' (A0 & A1 & A2 & A3 & A4) Hq Hn Hle.
  split; [lia|]. split; [lia|].
  split; [unfold amem_range in *; destruct A2 as [A2|A2]; [left; lia | right; lia]|].
  split; [eapply range_addressable_sub; [exact A3 | lia | lia]|].
  intros Hn'. exact (pb8bn_hull_sub rd q n q' n' (A4 ltac:(lia)) Hq Hn' Hle).
Qed.

(* ================================ bytes ================================ *)
Lemma pb8bn_bv8 : forall z, 0 <= z < 256 -> bv_unsigned (Z_to_bv 8 z) = z.
Proof.
  intros z Hz. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus.
  replace (2 ^ Z.of_N 8) with 256 by reflexivity. lia.
Qed.
(* the 4 little-endian bytes of a count 0 .. 32 (B4's pb4_n_bytes) *)
Lemma pb8bn_u32_bytes : forall (m : nat), (m <= 32)%nat -> forall nb, seg_spec.u32_enc (Z.of_nat m) nb ->
  forall k, (k < 4)%nat -> bv_unsigned (nth k nb ZB0) = le_byte (Z.of_nat m) 4 k.
Proof.
intros m Hm nb [_ ->] k Hk.
do 33 (destruct m as [|m]; [destruct k as [|[|[|[|k]]]]; [vm_compute; reflexivity .. | lia] |]). lia.
Qed.
Lemma pb8bn_nth_rng : forall name k, Forall (fun z => 0 <= z < 256) name -> 0 <= nth k (name ++ [0]) 0 < 256.
Proof.
intros name k H.
destruct (Nat.lt_ge_cases k (length (name ++ [0]))) as [Hk|Hk]; [|rewrite nth_overflow by exact Hk; lia].
assert (H0 : Forall (fun z => 0 <= z < 256) (name ++ [0]))
  by (apply Forall_app; split; [exact H | constructor; [lia | constructor]]).
rewrite Forall_forall in H0. apply H0. apply nth_In. exact Hk.
Qed.
(* the 356 bytes of a new entry: the name, its NUL, zeros *)
Definition pb8bn_seg_bytes (name : list Z) : list byte :=
  map (fun i => Z_to_bv 8 (nth i (name ++ [0]) 0)) (seq 0 356).
Lemma pb8bn_seg_bytes_len : forall name, length (pb8bn_seg_bytes name) = 356%nat.
Proof. intros name. unfold pb8bn_seg_bytes. rewrite length_map, length_seq. reflexivity. Qed.
Lemma pb8bn_seg_bytes_nth : forall name k d, (k < 356)%nat ->
  nth k (pb8bn_seg_bytes name) d = Z_to_bv 8 (nth k (name ++ [0]) 0).
Proof.
intros name k d Hk. unfold pb8bn_seg_bytes.
set (f := fun i : nat => Z_to_bv 8 (nth i (name ++ [0]) 0)).
rewrite (nth_indep (map f (seq 0 356)) d (f 0%nat)) by (rewrite length_map, length_seq; exact Hk).
rewrite map_nth, seq_nth by exact Hk. reflexivity.
Qed.
Lemma pb8bn_seg_bytes_name : forall name, ~ In 0 name -> (length name <= 15)%nat ->
  Forall (fun z => 0 <= z < 256) name -> seg_spec.cstr_enc 16 name (seg_spec.fld 0 16 (pb8bn_seg_bytes name)).
Proof.
intros name Hnz Hl Hr.
assert (Lf : length (seg_spec.fld 0 16 (pb8bn_seg_bytes name)) = 16%nat)
  by (rewrite pb8b_fld_len, pb8bn_seg_bytes_len; reflexivity).
split; [exact Lf|]. split; [lia|]. split; [exact Hnz|].
apply (nth_ext _ _ 0 0).
- unfold seg_spec.zs. rewrite length_firstn, length_map, Lf, length_app. cbn [length]. lia.
- intros k Hk. unfold seg_spec.zs in *. rewrite length_firstn, length_map, Lf in Hk.
  rewrite pb8b_nth_firstn by lia. rewrite pb8b_nth_map_bv by (rewrite Lf; lia).
  rewrite pb8b_fld_nth by lia. cbn [Nat.add]. rewrite pb8bn_seg_bytes_nth by lia.
  apply pb8bn_bv8. apply pb8bn_nth_rng. exact Hr.
Qed.

(* ================================ the record after NEW's three writes ================================ *)
(* c holds cf before; after: c->n = n + 1 (its 4 bytes), seg[n] = the name, its NUL and zeros (356 bytes), every
   other byte of the block as before. Then c holds cf with the new entry rseg0 (snprintf_s 16 "%s" name) (the
   model's seg_get on the NEW path, pf_seg_B8b_m.v's pb8b_seg_get_new). *)
Lemma pb8bn_rconf_new : forall (rd rdF : reader) (c : Z) (cf : rconf) (name : list Z),
  sa_rconf rd c cf -> (length (rc_seg cf) < 32)%nat -> 0 <= c ->
  ~ In 0 name -> (length name <= 15)%nat -> Forall (fun z => 0 <= z < 256) name ->
  (forall x, c <= x < c + seg_spec.SEG_C_SIZE ->
     ~ (seg_spec.rseg_addr c (length (rc_seg cf)) <= x < seg_spec.rseg_addr c (length (rc_seg cf)) + 356) ->
     ~ (c + seg_spec.RC_N <= x < c + seg_spec.RC_N + 4) -> rdF x = rd x) ->
  (forall k, (k < 4)%nat ->
     rdF (c + seg_spec.RC_N + Z.of_nat k) = Some (le_byte (Z.of_nat (length (rc_seg cf)) + 1) 4 k)) ->
  (forall i, 0 <= i < 356 ->
     rdF (seg_spec.rseg_addr c (length (rc_seg cf)) + i) = Some (nth (Z.to_nat i) (name ++ [0]) 0)) ->
  sa_rconf rdF c (r_set_segs cf (rc_seg cf ++ [rseg0 (snprintf_s 16 F_s [AS name])])).
Proof.
intros rd rdF c cf name Hs Hn Hc0 Hnz Hl Hr Hkeep Hcn Hseg.
rewrite (pb8b_snprintf_name16 name Hnz Hl).
set (n := length (rc_seg cf)) in *.
set (f := pb8bn_seg_bytes name).
set (nb := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib.Mem.le4 (Z_to_bv 64 (Z.of_nat n + 1))).
assert (Hnb : seg_spec.u32_enc (Z.of_nat n + 1) nb) by (split; [lia | reflexivity]).
pose proof (pb8b_u32_len _ _ Hnb) as Lnb.
assert (Hg : seg_spec.rseg_enc (rseg0 name) f).
{ apply pb8b_rseg0_enc.
  - apply pb8bn_seg_bytes_len.
  - intros k Hk. unfold f. rewrite pb8bn_seg_bytes_nth by lia.
    rewrite nth_overflow by (rewrite length_app; cbn [length]; lia). reflexivity.
  - exact (pb8bn_seg_bytes_name name Hnz Hl Hr). }
assert (Hd : seg_spec.rseg_addr c n + 356 <= c + seg_spec.RC_N)
  by (unfold seg_spec.rseg_addr, seg_spec.RSEG_SIZE, seg_spec.RC_N; lia).
set (rd2 := fun x => if (c <=? x) && (x <? c + seg_spec.SEG_C_SIZE) then rdF x else rd x).
assert (Hin : forall x, c <= x < c + seg_spec.SEG_C_SIZE -> rd2 x = rdF x).
{ intros x Hx. unfold rd2.
  replace ((c <=? x) && (x <? c + seg_spec.SEG_C_SIZE)) with true; [reflexivity|].
  symmetry. apply andb_true_iff. split; [apply Z.leb_le | apply Z.ltb_lt]; lia. }
assert (H2 : sa_rconf rd2 c (r_set_segs cf (rc_seg cf ++ [rseg0 name]))).
{ apply (pb8b_rconf_newseg rd rd2 c cf (rseg0 name) f nb Hs Hn Hc0 Hg Hnb).
  - intros x Hx Hns Hnc. unfold rd2.
    destruct ((c <=? x) && (x <? c + seg_spec.SEG_C_SIZE)) eqn:E; [|reflexivity].
    apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2.
    exact (Hkeep x (conj E1 E2) Hns Hnc).
  - intros i Hi. fold n. unfold f in Hi. rewrite pb8bn_seg_bytes_len in Hi.
    rewrite Hin by (unfold seg_spec.rseg_addr, seg_spec.RSEG_SIZE, seg_spec.SEG_C_SIZE, seg_spec.RC_N in *; lia).
    rewrite (Hseg (Z.of_nat i)) by lia. rewrite Nat2Z.id. unfold f. rewrite pb8bn_seg_bytes_nth by lia.
    rewrite pb8bn_bv8 by (apply pb8bn_nth_rng; exact Hr). reflexivity.
  - intros k Hk. fold n. rewrite Lnb in Hk.
    rewrite Hin by (unfold seg_spec.SEG_C_SIZE, seg_spec.RC_N; lia).
    rewrite (Hcn k Hk). f_equal. symmetry.
    replace (Z.of_nat n + 1) with (Z.of_nat (S n)) by lia.
    apply (pb8bn_u32_bytes (S n) ltac:(lia) nb); [|exact Hk].
    replace (Z.of_nat (S n)) with (Z.of_nat n + 1) by lia. exact Hnb. }
destruct H2 as (bs & Hb & He). exists bs. split; [|exact He].
pose proof (proj1 He) as L. unfold seg_spec.SEG_C_SIZE in L.
intros i Hi. rewrite <- (Hin (c + Z.of_nat i)) by (unfold seg_spec.SEG_C_SIZE; lia). exact (Hb i Hi).
Qed.

(* ================================ the cut's objects across NEW's writes ================================ *)
Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.

(* the bytes NEW may write: seg[n], c->n, the callees' windows below s1 *)
Definition pb8bn_Wr (v : pfv) (n : nat) (a : Z) : Prop :=
  (seg_spec.rseg_addr (p_c v) n <= a < seg_spec.rseg_addr (p_c v) n + 356) \/
  (p_c v + seg_spec.RC_N <= a < p_c v + seg_spec.RC_N + 4) \/
  (pf_s1 v - 2 * ESTACK <= a < pf_s1 v).
Definition pb8bn_kept (v : pfv) (n : nat) (rd rd' : reader) : Prop :=
  forall a, 0 <= a < 2 ^ 64 -> ~ pb8bn_Wr v n a -> rd' a = rd a.
Lemma pb8bn_kept_refl : forall v n rd, pb8bn_kept v n rd rd.
Proof. intros v n rd a _ _. reflexivity. Qed.
Lemma pb8bn_kept_trans : forall v n rd1 rd2 rd3, pb8bn_kept v n rd1 rd2 -> pb8bn_kept v n rd2 rd3 ->
  pb8bn_kept v n rd1 rd3.
Proof. intros v n rd1 rd2 rd3 K1 K2 a Ha Hw. rewrite (K2 a Ha Hw). exact (K1 a Ha Hw). Qed.

Section c. Context {fx : YK11.FPState}.
(* the geometry the keep lemmas use, from the cut facts *)
Definition pb8bn_G (v : pfv) (pos : Z) (n : nat) : Prop :=
  pb8b_geoP v pos /\ (n < 32)%nat /\ 4096 <= p_c v /\ p_c v + seg_spec.SEG_C_SIZE <= alloc_ceiling /\
  in_app (p_c v) seg_spec.SEG_C_SIZE /\ off_img (p_c v) seg_spec.SEG_C_SIZE /\
  (p_c v + seg_spec.SEG_C_SIZE <= pf_F v pos \/ pf_F v pos + 2048 <= p_c v) /\
  0 <= p_t v /\ p_t v + Z.of_nat (length (p_s v)) + 1 <= alloc_ceiling /\
  sa_disj (p_t v) (seg_spec.cstr_span (p_t v) (p_s v)) (p_c v) seg_spec.SEG_C_SIZE.

Lemma pb8bn_G_of : forall v pos lyc Sc Wc rX memc mdc n, pf_cx B v -> pf_fi B v pos lyc Sc Wc rX memc mdc ->
  pf_obj B v lyc Sc (rdW Wc memc) -> (n < 32)%nat -> pb8bn_G v pos n.
Proof.
intros v pos lyc Sc Wc rX memc mdc n HCX HFI HOBJ Hn.
destruct (pb8b_geo B v pos lyc Sc Wc rX memc mdc HCX HFI) as (HG & Hin & EF & Hfrs & HAR).
destruct (pb8b_cblk B v pos lyc Sc Wc rX memc mdc HCX HFI HOBJ) as (Hc0 & Hc16 & Hc4 & Hcc & _ & HCH & Hap).
destruct HCH as (b & m & Hb & Hb1 & Hb2).
destruct (al_blocks _ _ LAWS lyc Sc Wc memc mdc b m HAR Hb) as (_ & _ & Hcl & Happ & _ & _ & Hm0).
pose proof (req_size_pos m ltac:(lia)) as [_ Hrm].
pose proof (blk_off_imgP B lyc Sc Wc memc mdc b m HAR Hb) as Hoff.
pose proof HOBJ as (_ & _ & HT & _).
destruct HT as (bt & mt & Hbt & Ht1 & Ht2). unfold pf_len in Ht2.
destruct (al_blocks _ _ LAWS lyc Sc Wc memc mdc bt mt HAR Hbt) as (_ & _ & Htl & _ & _ & _ & Hmt0).
pose proof (req_size_pos mt ltac:(lia)) as [_ Hrmt].
pose proof HCX as (_ & _ & _ & _ & _ & Ht64 & _ & _ & (fe & HPRE) & _).
destruct HPRE as (HRP & _).
destruct HRP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HDJ & _).
split; [exact HG|]. split; [exact Hn|]. split; [exact Hc4|]. split; [exact Hcc|].
split; [apply (in_app_sub b (req_size m)); [exact Happ | lia | unfold seg_spec.SEG_C_SIZE; lia | lia]|].
split; [unfold off_img in *; lia|].
split; [exact Hap|]. split; [lia|]. split; [lia | exact HDJ].
Qed.

Section k.
Variable v : pfv.
Variable pos : Z.
Variable n : nat.
Hypothesis G : pb8bn_G v pos n.

Lemma pb8bn_s1_lo : alloc_ceiling + 8 <= pf_s1 v - 2 * ESTACK.
Proof.
pose proof G as ((S1 & S2 & S3 & S4 & _) & _). unfold ESTACK. lia.
Qed.
(* a byte below alloc_ceiling + 8 and outside the block c is not written *)
Lemma pb8bn_low_nw : forall x, 0 <= x -> x < alloc_ceiling + 8 ->
  (x < p_c v \/ p_c v + seg_spec.SEG_C_SIZE <= x) -> 0 <= x < 2 ^ 64 /\ ~ pb8bn_Wr v n x.
Proof.
intros x H0 H1 Hc. pose proof pb8bn_s1_lo as L. pose proof G as (_ & Hn & _).
pose proof asan_consts as (C1 & _).
split; [lia|]. unfold pb8bn_Wr, seg_spec.rseg_addr, seg_spec.RSEG_SIZE, seg_spec.RC_N, seg_spec.SEG_C_SIZE in *.
assert (Z.of_nat n <= 31) by lia. lia.
Qed.
(* a shadow byte is not written *)
Lemma pb8bn_shadow_nw : forall s, SHADOW_OFF <= s < kHighMemBeg -> 0 <= s < 2 ^ 64 /\ ~ pb8bn_Wr v n s.
Proof.
intros s Hs. pose proof G as (_ & Hn & _ & _ & Happ & _).
pose proof pb8bn_s1_lo as L. pose proof asan_consts as (C1 & _).
split; [unfold kHighMemBeg, SHADOW_OFF in Hs; lia|].
unfold pb8bn_Wr, in_app, seg_spec.rseg_addr, seg_spec.RSEG_SIZE, seg_spec.RC_N, seg_spec.SEG_C_SIZE,
  kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SHADOW_OFF in *.
assert (Z.of_nat n <= 31) by lia. lia.
Qed.
(* the frame's bytes are not written *)
Lemma pb8bn_frame_nw : forall x, pf_F v pos <= x < pf_F v pos + 2048 -> 0 <= x < 2 ^ 64 /\ ~ pb8bn_Wr v n x.
Proof.
intros x Hx. pose proof G as ((_ & _ & _ & _ & _ & _ & F1 & F2 & _) & _ & _ & _ & _ & _ & Hap & _).
apply pb8bn_low_nw; lia.
Qed.
(* an image byte is not written *)
Lemma pb8bn_img_nw : forall x, 0x10000 <= x < kImgEnd -> 0 <= x < 2 ^ 64 /\ ~ pb8bn_Wr v n x.
Proof.
intros x Hx. pose proof G as (_ & _ & _ & _ & _ & Hoff & _). pose proof asan_consts as (C1 & _).
apply pb8bn_low_nw; unfold off_img, kImgEnd in *; lia.
Qed.
(* the real stack from s1 up is not written *)
Lemma pb8bn_stack_nw : forall x, pf_s1 v <= x < 2 ^ 64 -> ~ pb8bn_Wr v n x.
Proof.
intros x Hx. pose proof pb8bn_s1_lo as L. pose proof G as (_ & Hn & _ & Hcc & _).
pose proof asan_consts as (C1 & _).
unfold pb8bn_Wr, seg_spec.rseg_addr, seg_spec.RSEG_SIZE, seg_spec.RC_N, seg_spec.SEG_C_SIZE, ESTACK in *.
assert (Z.of_nat n <= 31) by lia. lia.
Qed.

Section r.
Variables rd rd' : reader.
Hypothesis K : pb8bn_kept v n rd rd'.
Lemma pb8bn_k_at : forall x, 0 <= x < 2 ^ 64 /\ ~ pb8bn_Wr v n x -> rd' x = rd x.
Proof. intros x [H0 H1]. exact (K x H0 H1). Qed.
Lemma pb8bn_k_rdword : forall a, (forall k, 0 <= k < 8 -> 0 <= a + k < 2 ^ 64 /\ ~ pb8bn_Wr v n (a + k)) ->
  rdword rd' a = rdword rd a.
Proof.
intros a Ho. apply rdword_ext. intros k Hk. apply pb8bn_k_at. exact (Ho k Hk).
Qed.
(* a C string (bytes, NUL, slack) whose span is not written *)
Lemma pb8bn_k_str : forall p s, 0 <= p ->
  (forall x, p <= x < p + seg_spec.cstr_span p s -> 0 <= x < 2 ^ 64 /\ ~ pb8bn_Wr v n x) ->
  sa_str rd p s -> sa_str rd' p s.
Proof.
intros p s Hp Ho [[Hz Hn] Ht].
assert (Esp : p + seg_spec.cstr_span p s = p + Z.of_nat (length s) - (p + Z.of_nat (length s)) mod 8 + 8).
{ unfold seg_spec.cstr_span.
  pose proof (Z.div_mod (p + Z.of_nat (length s)) 8 ltac:(lia)) as E1.
  pose proof (Z.mod_pos_bound (p + Z.of_nat (length s)) 8 ltac:(lia)) as B1.
  rewrite <- (Z.mod_unique (- (p + Z.of_nat (length s) + 1)) 8 (- ((p + Z.of_nat (length s)) / 8) - 1)
    (7 - (p + Z.of_nat (length s)) mod 8)) by lia.
  lia. }
pose proof (Z.mod_pos_bound (p + Z.of_nat (length s)) 8 ltac:(lia)) as B1.
split; [split; [|exact Hn]|].
- intros i Hi. pose proof Hi as Hl. rewrite length_app in Hl. cbn [length] in Hl.
  rewrite (pb8bn_k_at (p + Z.of_nat i)) by (apply Ho; lia). exact (Hz i Hi).
- intros x Hx. rewrite (pb8bn_k_at x) by (apply Ho; lia). exact (Ht x Hx).
Qed.
(* sa_addr reads shadow bytes only *)
Lemma pb8bn_k_addr : forall q m, 0 <= q -> q + m <= kHighMemEnd -> sa_addr rd q m -> sa_addr rd' q m.
Proof.
intros q m H0 H1 (A0 & A1 & A2 & A3 & A4). split; [exact A0|]. split; [exact A1|]. split; [exact A2|].
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
split.
- intros x Hx. destruct (A3 x Hx) as (s & Hs & Hok). exists s. split; [|exact Hok].
  rewrite (pb8bn_k_at (shadow_of_addr SHADOW_OFF x)); [exact Hs|].
  apply pb8bn_shadow_nw. unfold shadow_of_addr, SHADOW_OFF, kHighMemBeg, kHighMemEnd in *.
  pose proof (Z.div_pos x 8 ltac:(lia) ltac:(lia)).
  assert (x / 8 < 17592186044416) by (apply Z.div_lt_upper_bound; lia). lia.
- intros Hm s Hs. rewrite (pb8bn_k_at s); [exact (A4 Hm s Hs)|]. apply pb8bn_shadow_nw.
  unfold shadow_addr, SHADOW_OFF, kHighMemBeg, kHighMemEnd in *.
  pose proof (Z.div_pos q 8 ltac:(lia) ltac:(lia)) as Dq.
  assert (Le : (q + m - 1) / 8 < 17592186044416) by (apply Z.div_lt_upper_bound; lia).
  assert (Lq : 268431360 <= (2147450880 + q / 8) / 8) by (apply Z.div_le_lower_bound; lia).
  pose proof (Z.div_mod (2147450880 + (q + m - 1) / 8) 8 ltac:(lia)) as De.
  pose proof (Z.mod_pos_bound (2147450880 + (q + m - 1) / 8) 8 ltac:(lia)) as Me.
  lia.
Qed.
Lemma pb8bn_k_lit : forall a s, sa_lit SEGS B rd a s -> sa_lit SEGS B rd' a s.
Proof.
intros a s (Ha & Hs & Hp & Hr & Hi). split; [exact Ha|]. split; [|exact (conj Hp (conj Hr Hi))].
destruct Hs as [[Hz Hn] Ht]. split; [split; [|exact Hn]|].
- intros i Hi'. pose proof Hi' as Hl. rewrite length_app in Hl. cbn [length] in Hl.
  rewrite (pb8bn_k_at (a + Z.of_nat i)); [exact (Hz i Hi')|].
  apply pb8bn_img_nw. exact (pa_img_range _ (proj1 (Hi (a + Z.of_nat i) ltac:(lia)))).
- intros x Hx. pose proof (Z.mod_pos_bound (a + Z.of_nat (length s)) 8 ltac:(lia)) as M.
  rewrite (pb8bn_k_at x); [exact (Ht x Hx)|].
  apply pb8bn_img_nw. apply pa_img_range.
  assert (Ie : in_img SEGS (a + Z.of_nat (length s))) by exact (proj1 (Hi (a + Z.of_nat (length s)) ltac:(lia))).
  pose proof (pa_segs_low _ Ie) as Re. pose proof asan_consts as (_ & _ & _ & _ & C5).
  apply (YG0s.seg_rom_in_img SEGS x); [lia | exact (Hr x Hx)].
Qed.
Lemma pb8bn_k_cat : forall cat, sa_cat SEGS B rd cat -> sa_cat SEGS B rd' cat.
Proof.
intros cat (Hp & Hi & Hrows). split; [exact Hp|]. split; [exact Hi|].
intros i Hn. destruct (Hrows i Hn) as (tp & Htp & Hl). exists tp. split; [|exact (pb8bn_k_lit tp _ Hl)].
assert (Hn' : (Z.of_nat i < 11)) by (unfold pin_spec.CAT_N in Hn; lia).
rewrite (pb8bn_k_rdword (pin_spec.row_addr cat i)); [exact Htp|].
intros k Hk. apply pb8bn_img_nw. apply pa_img_range. apply Hi.
unfold pin_spec.row_addr, pin_spec.CAT_ROW, pin_spec.CAT_BYTES. lia.
Qed.
Lemma pb8bn_k_rod : arodata_okP SEGS RLO_A RHI_A B rd -> arodata_okP SEGS RLO_A RHI_A B rd'.
Proof.
intros H a Hro Ho He. rewrite (pb8bn_k_at a); [exact (H a Hro Ho He)|].
apply pb8bn_img_nw.
destruct Hro as [(sg & Hsg & _ & Hr) | Hr].
- apply pa_img_range. exists sg. split; [exact Hsg | exact Hr].
- unfold RLO_A, RHI_A, SEG_RLO, SEG_RHI, kImgEnd in *. lia.
Qed.
Lemma pb8bn_k_ssp : sa_ssp rd gotwA guardA -> sa_ssp rd' gotwA guardA.
Proof.
intros (G1 & g & G2).
split; [rewrite (pb8bn_k_rdword gotwA); [exact G1 | intros k Hk; apply pb8bn_img_nw; unfold gotwA, kImgEnd; lia]|].
exists g. rewrite (pb8bn_k_rdword guardA); [exact G2 | intros k Hk; apply pb8bn_img_nw; unfold guardA, kImgEnd; lia].
Qed.
(* the text (reader_pre's sa_disj keeps its span off the block) *)
Lemma pb8bn_k_text : sa_str rd (p_t v) (p_s v) -> sa_str rd' (p_t v) (p_s v).
Proof.
intros H. pose proof G as (_ & _ & _ & _ & _ & _ & _ & Ht0 & Htc & HDJ).
apply (pb8bn_k_str _ _ Ht0); [|exact H].
intros x Hx. assert (Hsp : seg_spec.cstr_span (p_t v) (p_s v) <= Z.of_nat (length (p_s v)) + 8).
{ unfold seg_spec.cstr_span. pose proof (Z.mod_pos_bound (- (p_t v + Z.of_nat (length (p_s v)) + 1)) 8 ltac:(lia)). lia. }
apply pb8bn_low_nw; [lia | lia |]. unfold sa_disj in HDJ. lia.
Qed.
Lemma pb8bn_k_obj : forall lyc Sc, pf_obj B v lyc Sc rd -> pf_obj B v lyc Sc rd'.
Proof.
intros lyc Sc (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9).
pose proof G as (_ & _ & Hc4 & Hcc & _ & _ & _ & Ht0 & Htc & _). pose proof asan_consts as (C1 & _).
split; [exact (pb8bn_k_text H1)|].
split; [apply (pb8bn_k_addr _ _ Ht0); [unfold pf_len; unfold kHighMemEnd in *; lia | exact H2]|].
split; [exact H3|].
split; [apply (pb8bn_k_addr (p_c v) seg_spec.SEG_C_SIZE ltac:(lia)); [unfold kHighMemEnd, seg_spec.SEG_C_SIZE in *; lia | exact H4]|].
split; [exact H5|].
split; [exact (pb8bn_k_cat _ H6)|].
split; [intros x Hx; exact (pb8bn_k_lit _ _ (H7 x Hx))|].
split; [exact (pb8bn_k_rod H8) | exact (pb8bn_k_ssp H9)].
Qed.
Lemma pb8bn_k_saved : forall regs, pf_saved rd (pf_sp0 v) regs -> pf_saved rd' (pf_sp0 v) regs.
Proof.
intros regs H j r Hj. rewrite (pb8bn_k_rdword (pf_sp0 v - 8 - 8 * Z.of_nat j)); [exact (H j r Hj)|].
assert (Hj13 : (j < 13)%nat) by (change 13%nat with (length PF_SAVED); apply nth_error_Some; rewrite Hj; discriminate).
pose proof G as ((S1 & S2 & S3 & S4 & _) & _). pose proof asan_consts as (C1 & _).
intros k Hk. split; [lia|]. apply pb8bn_stack_nw. lia.
Qed.
Lemma pb8bn_k_flag : rdword rd (pf_F v pos + fs_frame_bytes 5 - 8) = Some (pf_FL v pos) ->
  rdword rd' (pf_F v pos + fs_frame_bytes 5 - 8) = Some (pf_FL v pos).
Proof.
intros H. rewrite (pb8bn_k_rdword _); [exact H|]. change (fs_frame_bytes 5) with 2048.
intros k Hk. apply pb8bn_frame_nw. lia.
Qed.
Lemma pb8bn_k_slot : forall off w, 0 <= off <= 0xd8 -> rdword rd (pf_s1 v + off) = Some w ->
  rdword rd' (pf_s1 v + off) = Some w.
Proof.
intros off w Ho H. rewrite (pb8bn_k_rdword _); [exact H|].
pose proof G as ((S1 & S2 & S3 & S4 & _) & _). pose proof asan_consts as (C1 & _).
intros k Hk. split; [lia|]. apply pb8bn_stack_nw. lia.
Qed.
Lemma pb8bn_k_sl : forall L, Forall (fun ov => 0 <= fst ov <= 0xd8) L -> pf_sl rd (pf_s1 v) L -> pf_sl rd' (pf_s1 v) L.
Proof.
intros L HL H. unfold pf_sl in *. rewrite Forall_forall in *. intros ov Hov.
exact (pb8bn_k_slot (fst ov) (snd ov) (HL ov Hov) (H ov Hov)).
Qed.
Lemma pb8bn_PF_SL_offs : forall pos', Forall (fun ov => 0 <= fst ov <= 0xd8) (PF_SL v pos').
Proof. intros pos'. unfold PF_SL. repeat constructor; cbn [fst]; lia. Qed.
Lemma pb8bn_k_fsh : forall sc, pf_fsh rd (pf_SH v pos) sc -> pf_fsh rd' (pf_SH v pos) sc.
Proof.
intros sc H i Hi. rewrite (pb8bn_k_at (pf_SH v pos + i)); [exact (H i Hi)|].
pose proof G as (HG & _). destruct (pb8b_SHb v pos HG) as (_ & SH1 & SH2 & _).
apply pb8bn_shadow_nw. unfold SHADOW_OFF, kHighMemBeg. lia.
Qed.
Lemma pb8bn_k_nm : forall nm, pf_nm rd (pf_F v pos + PF_O_CN) nm -> pf_nm rd' (pf_F v pos + PF_O_CN) nm.
Proof.
intros nm (f & Hb & Henc). exists f. split; [|exact Henc].
intros i Hi. destruct Henc as [Hl _]. rewrite Hl in Hi. unfold PF_O_CN.
rewrite (pb8bn_k_at (pf_F v pos + 0x20 + Z.of_nat i)); [exact (Hb i ltac:(lia))|].
apply pb8bn_frame_nw. lia.
Qed.
(* a C string in buf *)
Lemma pb8bn_k_buf : forall p s, pf_inb (pf_F v pos + PF_O_BUF) p s -> sa_str rd p s -> sa_str rd' p s.
Proof.
intros p s [Hb1 Hb2] H. pose proof G as ((_ & _ & _ & _ & _ & _ & F1 & F2 & _) & _).
unfold PF_O_BUF in *.
apply (pb8bn_k_str p s ltac:(lia)); [|exact H].
intros x Hx. assert (Hsp : seg_spec.cstr_span p s <= Z.of_nat (length s) + 8).
{ unfold seg_spec.cstr_span. pose proof (Z.mod_pos_bound (- (p + Z.of_nat (length s) + 1)) 8 ltac:(lia)). lia. }
apply pb8bn_frame_nw. lia.
Qed.
(* the block's bytes outside seg[n] and c->n *)
Lemma pb8bn_k_blk : forall x, p_c v <= x < p_c v + seg_spec.SEG_C_SIZE ->
  ~ (seg_spec.rseg_addr (p_c v) n <= x < seg_spec.rseg_addr (p_c v) n + 356) ->
  ~ (p_c v + seg_spec.RC_N <= x < p_c v + seg_spec.RC_N + 4) -> rd' x = rd x.
Proof.
intros x Hx H1 H2. apply pb8bn_k_at. pose proof G as (_ & Hn & Hc4 & Hcc & _).
pose proof pb8bn_s1_lo as L. split; [pose proof asan_consts as (C1 & _); lia|].
intros [W1 | [W2 | W3]]; [exact (H1 W1) | exact (H2 W2) | lia].
Qed.
End r.
End k.

(* ================================ buf is addressable (pf_seg_B9_c.v b9_addr_cells) ================================ *)
Lemma pb8bn_sh_cells : forall v pos (rd : reader) lo hi x, pb8b_geoP v pos -> pf_fsh rd (pf_SH v pos) PF_SC_LINE ->
  0 <= lo -> hi <= 144 -> (forall i, lo <= i < hi -> pf_shb PF_SC_LINE i = 0) ->
  pf_F v pos + 8 * lo <= x < pf_F v pos + 8 * hi ->
  rd (shadow_of_addr SHADOW_OFF x) = Some 0.
Proof.
intros v pos rd lo hi x HG HF Hlo Hhi Hz Hx.
pose proof HG as (_ & _ & _ & _ & _ & _ & H1 & H2 & H4 & _).
assert (HF8 : pf_F v pos mod 8 = 0) by (pose proof (Z.div_mod (pf_F v pos) 32 ltac:(lia)); lia).
replace x with (pf_F v pos + (x - pf_F v pos)) by lia.
rewrite (shadow_of_addr_aligned_off SHADOW_OFF (pf_F v pos) (x - pf_F v pos) HF8).
change (shadow_of_addr SHADOW_OFF (pf_F v pos)) with (pf_SH v pos).
rewrite (HF ((x - pf_F v pos) / 8)).
- f_equal. apply Hz. split; [apply Z.div_le_lower_bound; lia | apply Z.div_lt_upper_bound; lia].
- split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia].
Qed.
Lemma pb8bn_shb_line : forall i, 8 <= i < 72 -> pf_shb PF_SC_LINE i = 0.
Proof.
  intros i Hi. unfold pf_shb.
  destruct (Z.ltb_spec i 4) as [H|_]; [lia|].
  destruct (Z.ltb_spec i 6) as [H|_]; [lia|].
  destruct (Z.ltb_spec i 8) as [H|_]; [lia|].
  destruct (Z.ltb_spec i 72) as [_|H]; [reflexivity|lia].
Qed.
Lemma pb8bn_addr_buf : forall v pos (rd : reader) q m, pb8b_geoP v pos -> pf_fsh rd (pf_SH v pos) PF_SC_LINE ->
  pf_F v pos + PF_O_BUF <= q -> 0 <= m -> q + m <= pf_F v pos + PF_O_BUF + 512 -> sa_addr rd q m.
Proof.
intros v pos rd q m HG HF Hq Hm Hqm. unfold PF_O_BUF in *.
pose proof HG as (_ & _ & _ & _ & _ & _ & H1 & H2 & H4 & H3 & _).
destruct (pb8b_SHb v pos HG) as (ESH & SH1 & SH2 & F8).
assert (HF8 : pf_F v pos mod 8 = 0) by (pose proof (Z.div_mod (pf_F v pos) 32 ltac:(lia)); lia).
split; [lia|]. split; [pose proof asan_consts as (C1 & _); lia|].
split.
{ apply amem_range_high; [lia| |lia]. destruct H3 as [H3|H3]; [left; lia | right; lia]. }
split.
- intros x Hx. exists 0. split; [|left; reflexivity].
  apply (pb8bn_sh_cells v pos rd 8 72 x HG HF ltac:(lia) ltac:(lia) pb8bn_shb_line). lia.
- intros Hn0 s Hs.
  assert (E1 : shadow_addr q = pf_SH v pos + (q - pf_F v pos) / 8).
  { unfold shadow_addr. replace q with (pf_F v pos + (q - pf_F v pos)) at 1 by lia.
    change (SHADOW_OFF + (pf_F v pos + (q - pf_F v pos)) / 8)
      with (shadow_of_addr SHADOW_OFF (pf_F v pos + (q - pf_F v pos))).
    rewrite (shadow_of_addr_aligned_off SHADOW_OFF (pf_F v pos) (q - pf_F v pos) HF8). reflexivity. }
  assert (E2 : shadow_addr (q + m - 1) = pf_SH v pos + (q + m - 1 - pf_F v pos) / 8).
  { unfold shadow_addr. replace (q + m - 1) with (pf_F v pos + (q + m - 1 - pf_F v pos)) at 1 by lia.
    change (SHADOW_OFF + (pf_F v pos + (q + m - 1 - pf_F v pos)) / 8)
      with (shadow_of_addr SHADOW_OFF (pf_F v pos + (q + m - 1 - pf_F v pos))).
    rewrite (shadow_of_addr_aligned_off SHADOW_OFF (pf_F v pos) (q + m - 1 - pf_F v pos) HF8). reflexivity. }
  assert (B1 : 8 <= (q - pf_F v pos) / 8) by (apply Z.div_le_lower_bound; lia).
  assert (B2 : (q + m - 1 - pf_F v pos) / 8 < 72) by (apply Z.div_lt_upper_bound; lia).
  rewrite E1, E2 in Hs.
  pose proof (Z.div_mod (pf_SH v pos + (q - pf_F v pos) / 8) 8 ltac:(lia)) as D1.
  pose proof (Z.mod_pos_bound (pf_SH v pos + (q - pf_F v pos) / 8) 8 ltac:(lia)) as M1.
  pose proof (Z.div_mod (pf_SH v pos + (q + m - 1 - pf_F v pos) / 8) 8 ltac:(lia)) as D2.
  pose proof (Z.mod_pos_bound (pf_SH v pos + (q + m - 1 - pf_F v pos) / 8) 8 ltac:(lia)) as M2.
  replace s with (pf_SH v pos + (s - pf_SH v pos)) by lia.
  rewrite (HF (s - pf_SH v pos)) by lia. discriminate.
Qed.

(* ================================ the counters' room after the line ================================ *)
Lemma pb8bn_cnt_new : forall (cf : rconf) (s : list Z) (o : nat) g,
  (o < length s)%nat -> pf_cnt cf (length (skipn o s)) ->
  pf_cnt (r_set_segs cf (rc_seg cf ++ [g])) (length (skipn (pf_next s o) s)).
Proof.
intros cf s o g Ho H. pose proof (pf_next_skipn_lt s o Ho) as L.
assert (H' : pf_cnt (r_set_segs cf (rc_seg cf ++ [g])) (length (skipn o s)))
  by (unfold pf_cnt in *; unfold r_set_segs; cbn [rc_refused rc_overflow]; exact H).
apply (pf_cnt_mono _ (length (skipn o s))); [lia|]. exact H'.
Qed.

End c.
End e.
End f.
End d.
