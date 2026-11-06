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
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/check_round_trip.v, with its module paths and module names changed; 285 of its 337 lines of code are new or changed and 5001 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/A/Prog/pf_a11b_m.v; 725 of its 795 lines of code are new or changed and 267 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, image A (fuzz_segconf.asan): the piece A7_S_CLOSE of segment A7 of
   reac_segconf_parse_file's walk -- from the internal cut CLOSE 0x880ac to KWOK 0x882f0 or UNK 0x880e4
   (segment A7's proof, 2026-10-30).

   The code (the unit's internal record, commit dfb49d6ad789, path records/segp/dis/
   reac_segconf_parse_file.fuzz_segconf.asan.s; 14 instructions, 0x880ac .. 0x880e0, plus the inline
   check's slow block, which this piece shows is not reached):
     0x880ac srli a1,a0,3 / 0x880b0 add a1,a1,s6 / 0x880b4 lb a1,0(a1) / 0x880b8 bnez a1,0x88a4c
                                   -- inline check 13, a store1 of the ']' byte at a0 = lp + ci; the slow
                                      block 0x88a4c-0x88a54 and 0x88d18 errpath_store1 are not reached:
                                      the byte lies in buf, whose 64 shadow cells are 0 while buf is in
                                      scope (pf_shb PF_SC_LINE), so the token executor reads the literal 0
                                      and the branch is decided
     0x880bc sb zero,0(a0)          -- *close = 0: the line in buf becomes the C string slice 1 ci line
     0x880c0 addi a0,s7,1           -- a0 = lp + 1
     0x880c4 jal 0x890a8 <trim>     -- trim(line + 1), a program call (trim_contract, cl_callS_wide)
     0x880c8 mv s3,a0               -- s3 = the body = a7_body line ci at lp + 1 + trim_lead
     0x880cc auipc a0 / 0x880d0 addi a1,a0,0x3d4   -- a1 = 0x214a0 = seg_litA_rc S_segment (listing A_OBJ 41)
     0x880d4 addi a2,zero,7 / 0x880d8 mv a0,s3
     0x880dc jal 0x43a20 <wrapper_strncasecmp>     -- an interceptor (RtSeg.astrncasecmp_realizes, aj_art_at)
     0x880e0 beqz a0,0x882f0        -- the keyword matched -> KWOK; else fall into UNK 0x880e4

   The proof is three phases, each a lemma of this file, chained by a7_w2:
     w2_A  CLOSE -> the return of trim (0x880c8): the seed w2_seed1 (one writable byte region on a0, the
           shadow entry that covers it), one token run (paj_run_tok) through the check, the store and the
           two moves to the call, then trim through PaNoChain.cl_callS_wide with the call-site premises of
           pf_a7_s.v (a7_trim_site_880c4). The state after the store is pf_base again by pf_a5_k.a5_move0,
           and the line in buf is the C string slice 1 ci line by w2_cstr_close; trim's post then gives the
           body as a C string by w2_body_str and pfA_facts.L_trim_holds.
     w2_B  0x880c8 -> the return of strncasecmp (0x880e0): the seed pf_a7_q.a7_seed (bw = false: this run
           writes nothing), one plain run to the call, then PaArt.aj_art_at with the premise bundle of
           pf_a7_r.v (a7_ncase_pre_880dc); a7_keep_art carries the cut's facts across it.
     w2_C  0x880e0 -> KWOK or UNK: the seed again, the branch split (psrr_branch_pi), and each arm run to
           its cut and handed to HA_KWOK / HA_UNK. The bridge from the interceptor's answer strncase_eq to
           SegModel's strncasecmp is w2_strncase_bridge below.

   Section hypotheses: TRIM (trim_contract at image A's numbers), ANCASE (RtSeg.astrncasecmp_realizes at
   pa_sigma SS___interceptor_trampoline_strncasecmp), SIGP (seg_sig_prog), OBJ (seg_val_objs, for the
   literal's atom A_OBJ 41) and TL (PALib B, for api_env, which PaArt.aj_art_at asks). NO SSPX, NO VRO and
   NO ROMV: the transport across this piece's store, its trim call and its interceptor call is
   pf_a5_k.a5_move0 / pf_a7_r.a7_keep_art, neither of which needs one (the G3 walk owner's rule, 2026-10-30). *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI00 YI04 YI09 YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI16 YC5d YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pf_pieces_spec pfA_facts.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require RtSeg.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaRun PaShadow PaJournal SegSyms SegList
SegAddr SegPa SegObj SegGlob.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPaLib PaDenot PaLibG PaLibF PaLibH PaCall
PaCallRun PaArt PaFx PaNoChain PaSB.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import refuse_c trim_c
reac_segconf_parse_file_c SegInstA pf_pieces pf_a5_d pf_a5_k pf_a6_k pf_a7_f pf_a7_d pf_a7_m pf_a7_q
pf_a7_s pf_a7_r pf_a7_w3_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(** ** 1. The pure bridge: the interceptor's answer against SegModel's strncasecmp *)
(* RtSeg's fold and SegModel's are the same function: c + 32 = c - 65 + 97 on ['A','Z']. *)
Lemma w2_lc_lower : forall c, RtSeg.lc c = lower c.
Proof. intros c. unfold RtSeg.lc, lower. destruct ((65 <=? c) && (c <=? 90)); [lia | reflexivity]. Qed.

(* ieq_go's fold against a word, as a list equation *)
Lemma w2_ieq_go_map : forall l w, ieq_go l w = true <-> map lower l = w.
Proof.
  induction l as [|a l IH]; intros [|x w]; cbn [ieq_go map].
  - split; reflexivity.
  - split; [discriminate | intros H; discriminate H].
  - split; [discriminate | intros H; discriminate H].
  - split.
    + intros H. apply andb_true_iff in H as [H1 H2]. apply Z.eqb_eq in H1.
      rewrite H1. f_equal. apply IH. exact H2.
    + intros H. injection H as H1 H2. apply andb_true_iff. split.
      * apply Z.eqb_eq. exact H1.
      * apply IH. exact H2.
Qed.

Lemma w2_S_segment_len : length S_segment = 7%nat.
Proof. vm_compute. reflexivity. Qed.
Lemma w2_S_segment_nz : ~ In 0 S_segment.
Proof. vm_compute. intros H. repeat (destruct H as [H|H]; [discriminate H|]). exact H. Qed.
Lemma w2_S_segment_lc : map RtSeg.lc (firstn 7 (S_segment ++ [0])) = S_segment.
Proof. vm_compute. reflexivity. Qed.

(* a body shorter than the keyword puts its NUL inside the seven compared bytes *)
Lemma w2_short_has0 : forall b, (length b < 7)%nat -> In 0 (map RtSeg.lc (firstn 7 (b ++ [0]))).
Proof.
  intros b Hb. rewrite firstn_all2 by (rewrite length_app; cbn [length]; lia).
  apply in_map_iff. exists 0. split; [reflexivity|]. apply in_or_app. right. left. reflexivity.
Qed.

(* THE BRIDGE: the interceptor's post (strncase_eq over the two byte lists) and SegModel's strncasecmp
   say the same thing of a NUL-free body against the keyword "segment". *)
Lemma w2_strncase_bridge : forall b, ~ In 0 b ->
  (RtSeg.strncase_eq 7 b S_segment <-> strncasecmp b S_segment 7 = 0).
Proof.
  intros b Hb. unfold RtSeg.strncase_eq. rewrite w2_S_segment_lc.
  pose proof (strncasecmp_segment b Hb) as EQ.
  destruct (Nat.ltb_spec (length b) 7) as [Hlt|Hge].
  - split.
    + intros H. exfalso. apply w2_S_segment_nz. rewrite <- H. apply w2_short_has0. exact Hlt.
    + intros H. exfalso. apply Z.eqb_eq in H. rewrite H in EQ.
      replace ((7 <=? length b)%nat) with false in EQ by (symmetry; apply Nat.leb_gt; lia).
      cbn [andb] in EQ. discriminate EQ.
  - assert (HF : firstn 7 (b ++ [0]) = firstn 7 b)
      by (rewrite firstn_app; replace (7 - length b)%nat with 0%nat by lia; rewrite app_nil_r; reflexivity).
    rewrite HF.
    assert (HL : length (firstn 7 b) = 7%nat) by (rewrite length_firstn; lia).
    split.
    + intros H. apply Z.eqb_eq. rewrite EQ.
      replace ((7 <=? length b)%nat) with true by (symmetry; apply Nat.leb_le; lia).
      cbn [andb]. unfold ieq. rewrite HL, w2_S_segment_len, Nat.eqb_refl. cbn [andb].
      apply w2_ieq_go_map. rewrite <- H. apply map_ext. intros c. symmetry. apply w2_lc_lower.
    + intros H. apply Z.eqb_eq in H. rewrite H in EQ. symmetry in EQ.
      apply andb_true_iff in EQ as [_ EQ]. unfold ieq in EQ. apply andb_true_iff in EQ as [_ EQ].
      apply w2_ieq_go_map in EQ. rewrite <- EQ. apply map_ext. intros c. apply w2_lc_lower.
Qed.

(** ** 2. The pure memory facts of the store and of trim's answer *)
(* an index into slice 1 ci l *)
Lemma w2_nth_slice : forall (l : list Z) ci i, (i < ci - 1)%nat -> nth i (slice 1 ci l) 0 = nth (1 + i) l 0.
Proof.
  intros l ci i Hi. unfold slice. rewrite nth_firstn.
  destruct (Nat.ltb_spec i (ci - 1)) as [_|Hc]; [|lia].
  apply PaArt.nth_skipn_add.
Qed.

(* After `sb zero, 0(close)` the line in buf is the C string slice 1 ci l: the bytes 1 .. ci - 1 are
   untouched and the stored NUL ends it, because the ']' is the line's last byte (a7_close_last). *)
Lemma w2_cstr_close : forall (rd rd' : reader) lp l ci,
  sa_str rd lp l -> (1 <= ci)%nat -> strchr l RBR = Some ci -> nth (S ci) l 0 = 0 ->
  (forall x, lp <= x < lp + Z.of_nat ci -> rd' x = rd x) ->
  rd' (lp + Z.of_nat ci) = Some 0 ->
  sa_tail rd' (lp + Z.of_nat ci) ->
  sa_str rd' (lp + 1) (slice 1 ci l).
Proof.
  intros rd rd' lp l ci [[Hz Hn] _] Hci Hcl Hnth HK H0 HT.
  destruct (a7_close_last l ci Hn Hcl Hnth) as [Hlt Hlen].
  assert (HLS : length (slice 1 ci l) = (ci - 1)%nat)
    by (unfold slice; rewrite length_firstn, length_skipn; lia).
  split; [split|].
  - intros i Hi. rewrite length_app, HLS in Hi. cbn [length] in Hi.
    destruct (Nat.lt_ge_cases i (ci - 1)) as [Hik|Hik].
    + rewrite app_nth1 by lia. rewrite (w2_nth_slice l ci i Hik).
      replace (lp + 1 + Z.of_nat i) with (lp + Z.of_nat (1 + i)) by lia.
      rewrite HK by lia.
      assert (Hi' : (1 + i < length (l ++ [0%Z]))%nat) by (rewrite length_app; cbn [length]; lia).
      rewrite (Hz (1 + i)%nat Hi'). rewrite app_nth1 by lia. reflexivity.
    + assert (i = (ci - 1)%nat) as -> by lia.
      rewrite app_nth2 by lia. rewrite HLS, Nat.sub_diag. cbn [nth].
      replace (lp + 1 + Z.of_nat (ci - 1)) with (lp + Z.of_nat ci) by lia. exact H0.
  - unfold slice. apply nulfree_firstn. apply nulfree_skipn. exact Hn.
  - rewrite HLS. replace (lp + 1 + Z.of_nat (ci - 1)) with (lp + Z.of_nat ci) by lia. exact HT.
Qed.

Lemma w2_bv8 : forall z, 0 <= z < 256 -> bv_unsigned (Z_to_bv 8 z) = z.
Proof.
  intros z Hz. rewrite Z_to_bv_unsigned. apply bv_wrap_small.
  change (bv_modulus 8) with 256. lia.
Qed.

(* trim's post (the kept prefix and the NUL it stored) is the C string r_trim s at p + trim_lead s. *)
Lemma w2_body_str : forall (rd : reader) p s,
  ~ In 0 s -> (forall i, (i < length s)%nat -> 0 <= nth i s 0 < 256) ->
  sa_bytes rd p (seg_spec.zb (firstn (seg_spec.trim_lead s + length (r_trim s)) s) ++ [seg_spec.ZERO]) ->
  sa_tail rd (p + Z.of_nat (seg_spec.trim_lead s) + Z.of_nat (length (r_trim s))) ->
  sa_str rd (p + Z.of_nat (seg_spec.trim_lead s)) (r_trim s).
Proof.
  intros rd p s Hn HR HB HT.
  destruct (L_trim_holds s Hn) as (Hle & Heq & Hnf).
  set (k := seg_spec.trim_lead s) in *. set (m := length (r_trim s)) in *.
  assert (HLF : length (seg_spec.zb (firstn (k + m) s)) = (k + m)%nat)
    by (unfold seg_spec.zb; rewrite length_map, length_firstn; lia).
  split; [split|].
  - intros i Hi. rewrite length_app in Hi. cbn [length] in Hi.
    destruct (Nat.lt_ge_cases i m) as [Him|Him].
    + rewrite app_nth1 by lia.
      assert (Hidx : nth i (r_trim s) 0 = nth (k + i) s 0).
      { rewrite Heq at 1. rewrite nth_firstn.
        destruct (Nat.ltb_spec i m) as [_|Hc]; [|lia]. apply PaArt.nth_skipn_add. }
      rewrite Hidx.
      replace (p + Z.of_nat k + Z.of_nat i) with (p + Z.of_nat (k + i)) by lia.
      rewrite (HB (k + i)%nat ltac:(rewrite length_app, HLF; cbn [length]; lia)).
      rewrite app_nth1 by (rewrite HLF; lia).
      unfold seg_spec.zb, ZB0. rewrite (map_nth (Z_to_bv 8) (firstn (k + m) s) 0 (k + i)).
      rewrite nth_firstn. destruct (Nat.ltb_spec (k + i) (k + m)) as [_|Hc]; [|lia].
      rewrite w2_bv8 by (apply HR; lia). reflexivity.
    + assert (i = m) as -> by lia.
      rewrite app_nth2 by lia. rewrite Nat.sub_diag. cbn [nth].
      replace (p + Z.of_nat k + Z.of_nat m) with (p + Z.of_nat (k + m)) by lia.
      rewrite (HB (k + m)%nat ltac:(rewrite length_app, HLF; cbn [length]; lia)).
      rewrite app_nth2 by (rewrite HLF; lia). rewrite HLF, Nat.sub_diag. cbn [nth].
      reflexivity.
  - exact Hnf.
  - replace (p + Z.of_nat k + Z.of_nat m) with (p + Z.of_nat k + Z.of_nat (length (r_trim s))) by reflexivity.
    exact HT.
Qed.

(* one byte a run wrote into a one-byte written region, read back through the region's chunk
   (lib/A/Prog/pf_a2.v's pa2_cell_ok / pa2_cell_of_region, segment A2's proof, copied for an st_ok state) *)
Definition w2_cell_ok (cs : list YP09.chunk) (od v : Z) : bool :=
  existsb (fun c => match YP09.c_val c with
    | CVal w (SLit z) => (YP09.c_off c =? od) && (N.eqb w 1) && (bv_unsigned (byte_of_word (Z_to_bv 64 z) 0) =? v)
    | _ => false end) cs.

(** ** 3. The walk *)
(* the return points of the two calls (listing offsets) *)
Definition W2_RET_TRIM : Z := AF_reac_segconf_parse_file + 0x650.    (* 0x880c8 *)
Definition W2_RET_NCASE : Z := AF_reac_segconf_parse_file + 0x668.   (* 0x880e0 *)

(* the symbolic state of the first run: the one byte the store writes, on a0's own atom *)
Definition w2_regions1 : smem := [ YP09.mkRegion (Some 10%nat) 0 1 0 1 [] ].
Definition w2_facts1 : facts :=
  mkFacts [ (10%nat, mkAF 4096 (2 ^ 47 - 1) 0); (22%nat, mkAF SB SB 0) ] [] [].
Definition w2_ss1 : sstate := mkSS A7_CLOSE sr_atoms w2_regions1 None w2_facts1.
Definition w2_SH1 : list shent := [mkSHE 10 0 1].

Section d. Context {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

Lemma w2_cell_of_region : forall E H m n b lo hi wlo whi cs od v,
  region_ok SEGS E (mrestrict H m) (YP09.mkRegion (Some n) lo hi wlo whi cs) ->
  bv_unsigned (ew E n) = b -> w2_cell_ok cs od v = true -> aview SEGS H m (b + od) = Some v.
Proof.
intros E H m n b lo hi wlo whi cs od v HR Hb Hc.
apply existsb_exists in Hc as (c & Hin & Hc).
destruct c as [o [w e | | | ]]; cbn [YP09.c_val YP09.c_off] in Hc; try discriminate.
destruct e; try discriminate.
apply andb_prop in Hc as [Hc Hv]. apply andb_prop in Hc as [Ho Hw].
apply Z.eqb_eq in Ho. apply N.eqb_eq in Hw. apply Z.eqb_eq in Hv. subst o w.
unfold region_ok in HR. cbv zeta in HR. cbn [YP09.r_base YP09.r_chunks base_val] in HR.
destruct HR as (_ & _ & _ & Hcs).
pose proof (proj1 (Forall_forall _ _) Hcs _ Hin) as Hck.
destruct (Hck 0 ltac:(cbn; lia)) as (bb & Hb1 & Hb2). cbn [cbyte YP09.c_val YP09.c_off sv_denot] in Hb1, Hb2.
injection Hb1 as <-. rewrite Hb, Z.add_0_r in Hb2.
unfold aview. rewrite Hb2. cbn [option_map]. rewrite Hv. reflexivity.
Qed.

(* every byte of a C string read through a state's reader is a byte value *)
Lemma w2_bytes_rng : forall (W : world SEGS) mem q s, sa_str (rdW W mem) q s ->
  forall i, (i < length s)%nat -> 0 <= nth i s 0 < 256.
Proof.
intros W mem q s [[Hz _] _] i Hi.
assert (Hi' : (i < length (s ++ [0%Z]))%nat) by (rewrite length_app; cbn [length]; lia).
pose proof (Hz i Hi') as E. rewrite app_nth1 in E by lia.
exact (sa_aview_rng SEGS (w_H W) mem _ _ E).
Qed.

(* a C string whose bytes and NUL are kept, with its slack visible, is still a C string *)
Lemma w2_str_keep : forall (rd rd' : reader) q s, sa_str rd q s ->
  (forall x, q <= x <= q + Z.of_nat (length s) -> rd' x = rd x) ->
  sa_tail rd' (q + Z.of_nat (length s)) -> sa_str rd' q s.
Proof.
intros rd rd' q s [[Hz Hn] _] HK HT. split; [split; [|exact Hn] | exact HT].
intros i Hi. pose proof Hi as Hi'. rewrite length_app in Hi'. cbn [length] in Hi'.
rewrite HK by lia. exact (Hz i Hi).
Qed.

(* the interceptors' byte lists against SegModel's texts *)
Lemma w2_ZS_zb : forall (W : world SEGS) mem q l, sa_str (rdW W mem) q l ->
  map (fun b : byte => bv_unsigned b) (seg_spec.zb l) = l.
Proof.
intros W mem q l H. destruct (a7_astr_of_sa W mem q l H) as (_ & _ & _ & HZ & _). exact HZ.
Qed.

Lemma w2_ZS_seg : map (fun b : byte => bv_unsigned b) (seg_spec.zb S_segment) = S_segment.
Proof. vm_compute. reflexivity. Qed.

(* a register list carried to another register file that agrees on its registers *)
Lemma w2_rg_keep : forall (r1 r2 : bvmap 5 word) L,
  (forall rv, In rv L -> getr r2 (Z_to_bv 5 (fst rv)) = getr r1 (Z_to_bv 5 (fst rv))) ->
  pf_rg r1 L -> pf_rg r2 L.
Proof.
intros r1 r2 L HK H. unfold pf_rg in *. rewrite Forall_forall in *.
intros rv Hin. rewrite (HK rv Hin). exact (H rv Hin).
Qed.

Section e.
Variable B : asyms.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
(* the callee contracts of this piece, at image A's numbers, at every FP state *)
Hypothesis TRIM : forall fx0 : YK11.FPState,
  @trim_contract fx0 rc SK SEGS B (BASE + AF_trim) STK_trim RLO_A RHI_A.
Hypothesis ANCASE : forall fx0 : YK11.FPState,
  @RtSeg.astrncasecmp_realizes fx0 rc SEGS B (pa_sigma SS___interceptor_trampoline_strncasecmp).
(* the listing's facts over the walk's abstract instance *)
Hypothesis SIGP : seg_sig_prog (PI := PI).
Hypothesis OBJ : seg_val_objs (PI := PI).
Hypothesis TL : PALib B.

Section x. Context {fx : YK11.FPState}.
Let RUN := paj_run B LAWS.

(* the seed of the first run: a0 holds the ']' byte's address, s6 the shadow base *)
Lemma w2_seed1 : forall (W : world SEGS) (rX : bvmap 5 word) memc e,
  getr rX (Z_to_bv 5 10) = w64 e -> getr rX (Z_to_bv 5 22) = w64 SHADOW_OFF ->
  4096 <= e <= 2 ^ 47 - 1 -> apresent (w_H W) memc e ->
  st_ok_pi SEGS VAL (Eimg (Ereg rX [])) w2_ss1
    (restrict (w_H W) (mkst rX (Z_to_bv 64 (BASE + A7_CLOSE)) memc (seg_rom SEGS))).
Proof.
intros W rX memc e R10 R22 He Hpe.
set (E := Eimg (Ereg rX (@nil word))).
assert (E10 : ew E 10 = Z_to_bv 64 e)
  by (subst E; rewrite (ew_Eimg_Ereg_nat rX _ 10 (Z_to_bv 5 10) eq_refl); exact R10).
assert (E22 : ew E 22 = Z_to_bv 64 SHADOW_OFF)
  by (subst E; rewrite (ew_Eimg_Ereg_nat rX _ 22 (Z_to_bv 5 22) eq_refl); exact R22).
rewrite restrict_mkst_fx. unfold w2_ss1. apply pa_entry_st_ok_full.
- subst E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold w2_regions1. constructor; [|constructor].
  unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite E10, unsigned_lit_small by lia.
  split; [lia|]. split; [lia|]. split; [|constructor].
  intros o Ho. assert (o = 0) as -> by lia. rewrite Z.add_0_r.
  apply (apresent_writable SEGS). exact Hpe.
- exact (conj I I).
- split; [|split; exact I].
  cbn [w2_facts1 f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite E10, E22, !unsigned_lit_small by (unfold SHADOW_OFF, SB; lia).
  rewrite !Z.pow_0_r, !Z.mod_1_r. unfold SB, SHADOW_OFF. repeat split; lia.
Qed.

(* the state at 0x880c8, the return of trim: the body is the C string a7_body line ci at bp in buf *)
Definition w2_midA (n : nat) (v : pfv) (pos : Z) (lyc : alayout) (Sc : astate) (Wc : world SEGS)
  (rX : bvmap 5 word) (memc : word -> option byte) (mdc : Model) (cf : rconf) (nm : list Z)
  (o : nat) (ln : Z) (d : list (list Z)) (ci : nat) (bp : Z) : Prop :=
  pf_base B v pos lyc Sc Wc rX memc mdc PF_SC_LINE /\ pf_mid v o ln d n /\
  pf_st0 v pos (rdW Wc memc) cf nm (length (skipn o (p_s v))) /\
  (length (pf_line (p_s v) o) < 512)%nat /\
  strchr (pf_tline (p_s v) o) RBR = Some ci /\ nth (S ci) (pf_tline (p_s v) o) 0 = 0 /\
  sa_str (rdW Wc memc) bp (a7_body (pf_tline (p_s v) o) ci) /\
  pf_inb (pf_F v pos + PF_O_BUF) bp (a7_body (pf_tline (p_s v) o) ci) /\
  getr rX 10 = w64 bp /\
  pf_rg rX ([(18, 0x23); (24, p_c v); (27, pf_SH v pos); (20, 0x20); (25, 9)] ++ PF_RM v o ln).

(* CLOSE 0x880ac .. the return of trim 0x880c8 *)
Lemma w2_A : forall (n : nat) v pos lyc Sc Wc rX memc mdc cf cur nm o ln d lp ci
  (Q : world SEGS -> config -> Prop),
  INV_CLOSE B n v pos lyc Sc Wc rX memc mdc cf cur nm o ln d lp ci ->
  (forall S2 (W2 : world SEGS) regs2 mem2 md2 bp,
     w2_midA n v pos lyc S2 W2 regs2 mem2 md2 cf nm o ln d ci bp ->
     SRr SEGS W2 (mkCfg (mkst regs2 (w64 (BASE + W2_RET_TRIM)) mem2 (seg_rom SEGS)) md2) Q) ->
  SRr SEGS Wc (cfg_at SEGS (BASE + A7_CLOSE) rX memc mdc) Q.
Proof.
intros n v pos lyc Sc Wc rX memc mdc cf cur nm o ln d lp ci Q HI KC.
pose proof HI as (HB & HMID & HST & HSL & HLEN & HSTR & HINB & HHD & HCL & HNTH & HRG).
pose proof (a7_st_of_base B v pos lyc Sc Wc rX memc mdc HB) as HA7.
destruct (a5_geo B v pos lyc Sc Wc rX memc mdc PF_SC_LINE HB) as (HAR & Hly & Hfin & G & HFP & HSHP).
pose proof G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof alloc_ceiling_lt as Hac.
pose proof STK_values as (STT & _ & _ & SPF & _).
pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof HB as (HCX & HFI & HOBJ & HSLOT & HFSH).
pose proof HFI as (HJ & Hly' & HFS & HPERM & HSV & HFL & HFRM & HRGF).
pose proof HOBJ as (_ & _ & _ & _ & HCH0 & _).
destruct (w3_fi_get B v rX HRGF) as (R2 & R3 & R4 & R8).
destruct (a7_stk B v pos lyc Sc Wc memc mdc HA7) as (Hsp16 & Hceil & Hslo & Hs32 & Hs1b & Ho16).
destruct (a7_win B v pos lyc Sc Wc memc mdc STK_trim HA7 ltac:(rewrite STT; unfold ESTACK; lia))
  as (Wn1 & Wn2 & Wn3).
pose proof (a7_ci_pos (pf_tline (p_s v) o) ci HHD HCL) as Hci1.
pose proof HSTR as [[Hz0 Hn0] Htl0].
destruct (a7_close_last (pf_tline (p_s v) o) ci Hn0 HCL HNTH) as [Hcilt Hcilen].
pose proof HINB as [HI1 HI2].
destruct HST as (HRC & HCUR & HNM & HCNT).
assert (HST0 : pf_st0 v pos (rdW Wc memc) cf nm (length (skipn o (p_s v))))
  by (split; [exact HRC | split; [exact HNM | exact HCNT]]).
(* the string the store cuts out, and the body trim returns *)
set (sL := slice 1 ci (pf_tline (p_s v) o)) in *.
assert (HLS : length sL = (ci - 1)%nat)
  by (unfold sL, slice; rewrite length_firstn, length_skipn; lia).
assert (HnL : ~ In 0 sL)
  by (unfold sL, slice; apply nulfree_firstn; apply nulfree_skipn; exact Hn0).
destruct (L_trim_holds sL HnL) as (HTle & HTeq & HTnf).
set (e := lp + Z.of_nat ci) in *.
assert (Herng : 4096 <= e <= 2 ^ 47 - 1) by (unfold e, PF_O_BUF in *; lia).
assert (Hpe : apresent (w_H Wc) memc e) by (apply HFP; unfold e, PF_O_BUF in *; lia).
assert (HeB : a5_buf v pos <= e < a5_buf v pos + 512)
  by (unfold a5_buf, PF_O_BUF, e in *; lia).
assert (R10 : getr rX (Z_to_bv 5 10) = w64 e)
  by (eapply a5_rg_get; [exact HRG | cbn [In app PF_RL PF_RM]; tauto]).
assert (R22 : getr rX (Z_to_bv 5 22) = w64 SHADOW_OFF)
  by (eapply a5_rg_get; [exact HRGF | cbn [a5_FI In]; tauto]).
assert (R23 : getr rX (Z_to_bv 5 23) = w64 lp)
  by (eapply a5_rg_get; [exact HRG | cbn [In app PF_RL PF_RM]; tauto]).
pose proof (w2_seed1 Wc rX memc e R10 R22 Herng Hpe) as HS.
set (E := Eimg (Ereg rX (@nil word))) in HS.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (E10 : ew E 10 = Z_to_bv 64 e)
  by (subst E; rewrite (ew_Eimg_Ereg_nat rX _ 10 (Z_to_bv 5 10) eq_refl); exact R10).
assert (E22 : ew E 22 = Z_to_bv 64 SHADOW_OFF)
  by (subst E; rewrite (ew_Eimg_Ereg_nat rX _ 22 (Z_to_bv 5 22) eq_refl); exact R22).
assert (E23 : ew E 23 = Z_to_bv 64 lp)
  by (subst E; rewrite (ew_Eimg_Ereg_nat rX _ 23 (Z_to_bv 5 23) eq_refl); exact R23).
assert (U10 : U E (SOff 10 0) = e) by (apply U_atom; [exact E10 | lia]).
assert (U10' : bv_unsigned (ew E 10) = e) by (rewrite E10; apply unsigned_lit_small; lia).
assert (UB : U E a7_Bx = SHADOW_OFF)
  by (unfold a7_Bx; apply U_atom; [exact E22 | unfold SHADOW_OFF; lia]).
assert (HRA : range_addressable (rdW Wc memc) SHADOW_OFF e 1).
{ pose proof (a7_addr_buf B v pos lyc Sc Wc memc mdc e 1 HA7
    ltac:(unfold a7_buf, PF_O_BUF, e in *; lia) ltac:(lia)
    ltac:(unfold a7_buf, PF_O_BUF, e in *; lia)) as HA.
  exact (proj1 (proj2 (proj2 (proj2 HA)))). }
assert (SHOK : sh_ok SEGS a7_Bx w2_SH1 E (mrestrict (w_H Wc) memc)).
{ unfold sh_ok, w2_SH1. apply Forall_cons; [|apply Forall_nil].
  eapply (shent_ok_of_range SEGS (w_H Wc) memc E a7_Bx 10%nat e 1 e 0 1 HRA UB U10); [lia | lia |].
  intros x Hx. change (Z.min 0 1) with 0 in Hx. change (Z.max 0 1) with 1 in Hx.
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in G9.
  unfold SHADOW_OFF, PF_O_BUF, e in *. destruct G9 as [_ [G9 | G9]]; lia. }
change (cfg_at SEGS (BASE + A7_CLOSE) rX memc mdc)
  with (mkCfg (mkst rX (Z_to_bv 64 (BASE + A7_CLOSE)) memc (seg_rom SEGS)) mdc).
(* 0x880ac .. 0x880c4: check 13, the store of the NUL, a0 = line + 1, the call of trim *)
paj_run_tok RUN HS HJ SHOK Bspan.
{ lazymatch goal with |- awr_ok _ _ ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr0 ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok SEGS B Ex rs' stk spx fp b0 bc fr0 lyx own) end.
  eapply awr_ok_cons_gen with (n := 10%nat) (b := e); [reflexivity | exact U10' | | apply awr_ok_nil].
  intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. assert (a = e) as -> by lia.
  right; right; right; left. exists 5, pos. split; [left; reflexivity|]. left.
  unfold in_zr. cbn [fst snd]. rewrite Hly. change (frame_addr (p_ly v) 5 pos) with (pf_F v pos).
  change (fs_frame_bytes 5) with 2048. unfold e, PF_O_BUF in *. lia. }
(* what the run kept (everything but the ']' byte) and what it wrote (the NUL) *)
assert (KM : forall a, 0 <= a < 2 ^ 64 -> a <> e -> rdW Wc (ms_mem ms) a = rdW Wc memc a).
{ intros a Ha Hne.
  apply (kept_of_frame E (ss_mem w2_ss1) (w_H Wc) memc (ms_mem ms) (fun a' => a' = e) HFr);
    [|exact Ha | exact Hne].
  intros b wlo whi a' Hin Hrr. vm_compute in Hin.
  destruct Hin as [Hq | []]; injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite U10' in Hrr; lia. }
assert (HV1 : forall a, rdW Wc memc a <> None -> rdW Wc (ms_mem ms) a <> None)
  by (intros a Hv; exact (aview_keeps_vis SEGS (w_H Wc) memc (ms_mem ms) a HG Hv)).
assert (HW0 : rdW Wc (ms_mem ms) e = Some 0).
{ lazymatch type of HS with st_ok _ ?Ex ?ssx (restrict _ ?msx) =>
    let r0 := eval vm_compute in (nth 0 (ss_mem ssx) got_regionP) in
    pose proof (st_ok_region_nth Ex ssx (restrict (w_H Wc) msx) 0 r0 HS ltac:(vm_compute; reflexivity)) as HR0;
    assert (UX : bv_unsigned (ew Ex 10) = e) by (rewrite !ew_ewset_other by lia; exact U10') end.
  cbn [ms_mem restrict] in HR0.
  replace e with (e + 0) by lia.
  eapply (w2_cell_of_region _ (w_H Wc) (ms_mem ms) 10%nat e 0 1 0 1 _ 0 0 HR0 UX).
  vm_compute. reflexivity. }
lazymatch goal with |- SRr _ _ (mkCfg _ ?dM) _ => set (mdq := dM) in *; clearbody mdq end.
lazymatch type of HS with st_ok _ ?Ex _ _ =>
  assert (HAE : env_agree 32 (Ereg rX (@nil word)) Ex)
    by (split; [intros kk Hkk; rewrite !ew_ewset_other by lia; subst E; apply Eimg_low; unfold A_TEXT; lia
               | reflexivity]) end.
pose proof (aregs_preserved_of_st_ok SEGS _ _ _ _ rX (@nil word) HS HAE
  ltac:(vm_compute; reflexivity)) as HPR.
prreg HS (1%bv : bv 5) Q1. prreg HS (10%bv : bv 5) Q10.
assert (RA1 : getr (ms_regs ms) 1 = Z_to_bv 64 (BASE + W2_RET_TRIM))
  by (rewrite Q1; unfold W2_RET_TRIM, AF_reac_segconf_parse_file; reflexivity).
assert (RA10 : getr (ms_regs ms) 10 = w64 (lp + 1)).
{ rewrite Q10. rewrite ?ew_ewset_other by lia. rewrite E23.
  unfold w64. rewrite unsigned_lit_small by lia. reflexivity. }
assert (HRG1 : pf_rg (ms_regs ms) (a5_FI B v))
  by exact (a5_rg_pres rX (ms_regs ms) _ HPR (a5_FI_cs B v) HRGF).
destruct (w3_fi_get B v (ms_regs ms) HRG1) as (D2 & D3 & D4 & D8).
assert (HKW1 : forall sl shw a, 0 <= a < 2 ^ 64 -> ~ a5_Wrx v pos sl shw a ->
  rdW Wc (ms_mem ms) a = rdW Wc memc a).
{ intros sl shw. apply (w3_keepW v pos (pf_s1 v) e); [lia | exact HeB |].
  intros a Ha _ Hne. exact (KM a Ha Hne). }
assert (HSf0 : exists f, Sc = set_fs f Sc) by (exists (st_fs Sc); destruct Sc; reflexivity).
assert (HFSH1 : pf_fsh (rdW Wc (ms_mem ms)) (pf_SH v pos) PF_SC_LINE)
  by exact (a5_keep_fsh v pos _ _ true PF_SC_LINE G (HKW1 true false) HFSH).
pose proof (a5_move0 B v pos lyc Sc Wc rX memc mdc PF_SC_LINE Sc Wc (ms_regs ms) (ms_mem ms) mdq PF_SC_LINE
  HB HJ HSf0 (Permutation_refl _) (HKW1 true true) HV1 HRG1 HFSH1) as HB1.
pose proof (a7_st_of_base B v pos lyc Sc Wc (ms_regs ms) (ms_mem ms) mdq HB1) as HA7c.
(* the line in buf is now the C string slice 1 ci line *)
assert (HSTRc : sa_str (rdW Wc (ms_mem ms)) (lp + 1) sL).
{ apply (w2_cstr_close (rdW Wc memc) (rdW Wc (ms_mem ms)) lp (pf_tline (p_s v) o) ci HSTR Hci1 HCL HNTH).
  - intros x Hx. apply KM; [unfold PF_O_BUF in *; lia | unfold e; lia].
  - exact HW0.
  - exact (a7_tail_vis_buf B v pos lyc Sc Wc (ms_mem ms) mdq e HA7c
      ltac:(unfold a7_buf, PF_O_BUF, e in *; lia)). }
(* VERIFY rule 1j-bis at 0x880c4 (pf_a7_s.v) *)
destruct (a7_trim_site_880c4 B v pos lyc Sc Wc (ms_mem ms) mdq (ms_regs ms) o lp ci HA7c
  ltac:(unfold a7_buf; exact HINB) HHD RA10 HSTRc) as (HROD & _ & Hp64 & HTP & HEV).
destruct (a5_chain B v pos lyc Sc Wc (ms_regs ms) (ms_mem ms) mdq PF_SC_LINE HB1) as [ch1 HCH1].
set (e2 := trim_end_addr (lp + 1) sL) in *.
assert (He2 : lp + 1 <= e2 <= e) by (unfold e2, trim_end_addr, e; lia).
assert (HeB2 : a5_buf v pos <= e2 < a5_buf v pos + 512)
  by (unfold a5_buf, PF_O_BUF, e in *; lia).
assert (Hsp : spZ (ms_regs ms) = pf_sp0 v + (pf_s1 v - pf_sp0 v)).
{ unfold spZ. rewrite D2, a6_w64_u by lia. lia. }
pmkst HS. rewrite (SIGP SS_trim ltac:(unfold seg_prog_syms; cbn [In]; repeat (first [left; reflexivity | right]))).
replace (seg_af SS_trim) with AF_trim by (vm_compute; reflexivity).
eapply SRr_bind.
{ apply (cl_callS_wide B LAWS Wc (ms_regs ms) (ms_mem ms) (Z_to_bv 64 (BASE + AF_trim))
    STK_reac_segconf_parse_file (pf_sp0 v) (seg_spec.RC_PARSE_W (p_c v)) (p_ly v) (p_S v) (p_W v)
    (p_mem v) (p_md v) [(5, pos)] lyc Sc mdq 0 STK_trim [(e2, e2 + 1)] EV_trim
    (pf_s1 v - pf_sp0 v) (Z_to_bv 64 (BASE + W2_RET_TRIM)) ch1
    (fun ly2 S2 W2 regs2 mem2 md2 =>
       getr regs2 10 = w64 (lp + 1 + Z.of_nat (seg_spec.trim_lead sL)) /\
       sa_bytes (rdW W2 mem2) (lp + 1)
         (seg_spec.zb (firstn (seg_spec.trim_lead sL + length (r_trim sL)) sL) ++ [seg_spec.ZERO]) /\
       sa_kept SEGS Wc (ms_mem ms) W2 mem2 (ms_regs ms) STK_trim (fun a => a = e2) /\
       sa_noalloc B lyc Sc ly2 S2) HJ Hsp Ho16).
  - lia.
  - rewrite STT. lia.
  - exact Wn3.
  - exact D3.
  - exact D4.
  - exact RA1.
  - apply ret_ok_codeptr_v; [unfold W2_RET_TRIM, AF_reac_segconf_parse_file; lia | reflexivity].
  - rewrite unsigned_lit_small by (unfold W2_RET_TRIM, AF_reac_segconf_parse_file; lia).
    unfold W2_RET_TRIM, AF_reac_segconf_parse_file. lia.
  - replace (pf_sp0 v + (pf_s1 v - pf_sp0 v)) with (pf_s1 v) by lia.
    unfold s0Z.
    rewrite D8.
    rewrite a6_w64_u by lia. exact HCH1.
  - intros HPRE1. eapply SRr_mono.
    { exact (TRIM fx lyc Sc Wc (ms_regs ms) (ms_mem ms) mdq ch1 (lp + 1) sL HPRE1 HROD RA10 Hp64 HTP HEV). }
    cbv beta. intros W' c' _ (ly' & S' & regs' & mem' & md' & -> & HJ' & HP' & HQ').
    exists ly', S', regs', mem', md'. split; [rewrite RA1; reflexivity|].
    split; [exact HJ'|]. split; [exact HP' | exact HQ'].
  - intros a (r & Hr & Ha). destruct Hr as [<- | []]. cbn [fst snd] in Ha.
    right; right; right; left. exists 5, pos. split; [left; reflexivity|]. left.
    unfold in_zr. cbn [fst snd]. rewrite Hly. change (frame_addr (p_ly v) 5 pos) with (pf_F v pos).
    change (fs_frame_bytes 5) with 2048. unfold a5_buf, PF_O_BUF in HeB2. lia.
  - intros ly2 S2 W2 regs2 mem2 md2 _ a (r & Hr & Ha) Hw _. destruct Hr as [<- | []].
    cbn [fst snd] in Ha. exfalso. unfold a5_buf, PF_O_BUF in HeB2. rewrite SPF in G1, Hw. lia. }
(* back at 0x880c8 *)
cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJo & HJi & HP & (H10' & HBY & HKP & HNA)).
destruct HNA as (HPerm & -> & HSf).
change (0 + EV_trim) with 0 in HJo.
assert (HK0 : forall a, 0 <= a < 2 ^ 64 -> ~ (pf_s1 v - STK_trim <= a < pf_s1 v) -> ~ a = e2 ->
  rdW W2 mem2 a = rdW Wc (ms_mem ms) a).
{ intros a Ha Hw Hne. apply HKP; [exact Ha | | exact Hne]. rewrite Hsp. lia. }
assert (HKW2 : forall sl shw a, 0 <= a < 2 ^ 64 -> ~ a5_Wrx v pos sl shw a ->
  rdW W2 mem2 a = rdW Wc (ms_mem ms) a).
{ intros sl shw. apply (w3_keepW v pos (pf_s1 v - STK_trim) e2); [rewrite STT; lia | exact HeB2 | exact HK0]. }
assert (HKall : forall a, 0 <= a < 2 ^ 64 -> ~ a5_Wrx v pos true true a -> rdW W2 mem2 a = rdW Wc memc a).
{ intros a Ha Hw. rewrite (HKW2 true true a Ha Hw). exact (HKW1 true true a Ha Hw). }
assert (HV : forall a, rdW Wc (ms_mem ms) a <> None -> rdW W2 mem2 a <> None).
{ assert (HV0 : forall a, 0 <= a < 2 ^ 64 -> rdW Wc (ms_mem ms) a <> None -> rdW W2 mem2 a <> None).
  { intros a Ha Hs.
    destruct (Z_lt_le_dec a (pf_s1 v - STK_trim)) as [Hlo | Hlo];
      [|destruct (Z_lt_le_dec a (pf_s1 v)) as [Hhi | Hhi]].
    3: { destruct (Z.eq_dec a e2) as [-> | Hne];
         [unfold a5_buf, PF_O_BUF in HeB2; rewrite SPF in G1; lia|].
         rewrite (HK0 a Ha ltac:(lia) Hne). exact Hs. }
    1: { destruct (Z.eq_dec a e2) as [-> | Hne].
         - assert (Hix : (seg_spec.trim_lead sL + length (r_trim sL) <
               length (seg_spec.zb (firstn (seg_spec.trim_lead sL + length (r_trim sL)) sL)
                 ++ [seg_spec.ZERO]))%nat).
           { unfold seg_spec.zb. rewrite length_app, length_map, length_firstn. cbn [length]. lia. }
           pose proof (HBY _ Hix) as Ee. unfold e2, trim_end_addr. rewrite Ee. discriminate.
         - rewrite (HK0 a Ha ltac:(lia) Hne). exact Hs. }
    pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _).
    apply (aview_some_of_apresent SEGS). apply Hpres. lia. }
  intros a Hs. rewrite w3_view_wrap. rewrite w3_view_wrap in Hs.
  apply HV0; [apply Z.mod_pos_bound; lia | exact Hs]. }
assert (HPR2 : aregs_preserved rX regs2) by exact (aregs_preserved_trans _ _ _ HPR HP).
assert (HRG2 : pf_rg regs2 (a5_FI B v))
  by exact (a5_rg_pres rX regs2 _ HPR2 (a5_FI_cs B v) HRGF).
assert (HFSH2 : pf_fsh (rdW W2 mem2) (pf_SH v pos) PF_SC_LINE)
  by exact (a5_keep_fsh v pos _ _ true PF_SC_LINE G
       (fun a Ha Hw => eq_trans (HKW2 true false a Ha Hw) (HKW1 true false a Ha Hw)) HFSH).
pose proof (a5_move0 B v pos lyc Sc Wc rX memc mdc PF_SC_LINE S2 W2 regs2 mem2 md2 PF_SC_LINE
  HB HJo HSf HPerm HKall (fun a Ha => HV a (HV1 a Ha)) HRG2 HFSH2) as HB2.
pose proof (a7_st_of_base B v pos lyc S2 W2 regs2 mem2 md2 HB2) as HA7b.
(* the body: trim's kept prefix and its NUL *)
set (bp := lp + 1 + Z.of_nat (seg_spec.trim_lead sL)) in *.
assert (HBODY : sa_str (rdW W2 mem2) bp (r_trim sL)).
{ apply (w2_body_str (rdW W2 mem2) (lp + 1) sL HnL).
  - exact (w2_bytes_rng Wc (ms_mem ms) (lp + 1) sL HSTRc).
  - exact HBY.
  - replace (lp + 1 + Z.of_nat (seg_spec.trim_lead sL) + Z.of_nat (length (r_trim sL))) with e2
      by (unfold e2, trim_end_addr; lia).
    exact (a7_tail_vis_buf B v pos lyc S2 W2 mem2 md2 e2 HA7b
      ltac:(unfold a7_buf, PF_O_BUF; unfold a5_buf, PF_O_BUF in HeB2; lia)). }
apply (KC S2 W2 regs2 mem2 md2 bp).
split; [exact HB2|]. split; [exact HMID|].
split; [exact (w3_keep_st0 B v pos lyc Sc Wc memc mdc W2 mem2 cf nm _ G HAR Hfin Hly HKall HCH0 HST0)|].
split; [exact HLEN|]. split; [exact HCL|]. split; [exact HNTH|].
split; [exact HBODY|].
split.
{ change (a7_body (pf_tline (p_s v) o) ci) with (r_trim sL).
  unfold a5_buf in HeB2. unfold pf_inb. unfold PF_O_BUF in *.
  unfold bp, e2, trim_end_addr in *. split; lia. }
split; [exact H10'|].
apply (a5_rg_pres rX regs2 _ HPR2).
- unfold PF_RM. cbn [app]. repeat apply Forall_cons; try apply Forall_nil;
    cbn [fst]; unfold acallee_saved; lia.
- apply (a5_rg_incl rX (PF_RL v pos ++ PF_RM v o ln ++ [(20, 0x20); (25, 9); (23, lp); (10, e)])).
  + intros x Hx. cbn [app In PF_RL PF_RM] in Hx |- *. tauto.
  + exact HRG.
Qed.

(* the state at 0x880e0, the return of strncasecmp: a0 decides the keyword *)
Definition w2_midB (n : nat) (v : pfv) (pos : Z) (lyc : alayout) (Sc : astate) (Wc : world SEGS)
  (rX : bvmap 5 word) (memc : word -> option byte) (mdc : Model) (cf : rconf) (nm : list Z)
  (o : nat) (ln : Z) (d : list (list Z)) (ci : nat) (bp : Z) : Prop :=
  pf_base B v pos lyc Sc Wc rX memc mdc PF_SC_LINE /\ pf_mid v o ln d n /\
  pf_st0 v pos (rdW Wc memc) cf nm (length (skipn o (p_s v))) /\
  (length (pf_line (p_s v) o) < 512)%nat /\
  strchr (pf_tline (p_s v) o) RBR = Some ci /\ nth (S ci) (pf_tline (p_s v) o) 0 = 0 /\
  sa_str (rdW Wc memc) bp (a7_body (pf_tline (p_s v) o) ci) /\
  pf_inb (pf_F v pos + PF_O_BUF) bp (a7_body (pf_tline (p_s v) o) ci) /\
  (getr rX 10 = w64 0 <-> strncasecmp (a7_body (pf_tline (p_s v) o) ci) S_segment 7 = 0) /\
  pf_rg rX ([(19, bp)] ++ [(18, 0x23); (24, p_c v); (27, pf_SH v pos); (20, 0x20); (25, 9)]
            ++ PF_RM v o ln).

(* the literal a1 holds at 0x880dc: listing object 41 is .str.6, the keyword "segment" *)
Lemma w2_lit : forall E, img_env VAL A_LIM E -> ew E (A_OBJ 41) = w64 (seg_litA_rc S_segment).
Proof.
intros E HE. rewrite (img_env_atomP E (A_OBJ 41) HE) by (unfold A_OBJ, A_TEXT, A_LIM; lia).
rewrite (OBJ 41%nat ltac:(apply Nat.ltb_lt; vm_compute; reflexivity)).
unfold w64; f_equal; vm_compute; reflexivity.
Qed.

(* the run before a call of A7 writes nothing (pf_a7_u.v's a7u_awr) *)
Local Ltac w2_awr0 :=
  unfold a7_ss, a7_regions; cbn [ss_mem];
  repeat (apply awr_ok_cons_ro;
    [unfold a7_saved_r, a7_slot_r, a7_sh_r, a7_buf_r; cbn [YP09.r_wlo YP09.r_whi]; lia|]);
  apply awr_ok_nil.

(* 0x880c8 .. the return of strncasecmp 0x880e0 *)
Lemma w2_B : forall (n : nat) v pos lyc Sc Wc rX memc mdc cf nm o ln d ci bp
  (Q : world SEGS -> config -> Prop),
  w2_midA n v pos lyc Sc Wc rX memc mdc cf nm o ln d ci bp ->
  (forall regs2 mem2 md2,
     w2_midB n v pos lyc Sc Wc regs2 mem2 md2 cf nm o ln d ci bp ->
     SRr SEGS Wc (mkCfg (mkst regs2 (Z_to_bv 64 (BASE + W2_RET_NCASE)) mem2 (seg_rom SEGS)) md2) Q) ->
  SRr SEGS Wc (mkCfg (mkst rX (w64 (BASE + W2_RET_TRIM)) memc (seg_rom SEGS)) mdc) Q.
Proof.
intros n v pos lyc Sc Wc rX memc mdc cf nm o ln d ci bp Q HM KC.
pose proof HM as (HB & HMID & HST0 & HLEN & HCL & HNTH & HSTR & HINB & R10 & HRG).
pose proof (a7_st_of_base B v pos lyc Sc Wc rX memc mdc HB) as HA7.
destruct (a5_geo B v pos lyc Sc Wc rX memc mdc PF_SC_LINE HB) as (HAR & Hly & Hfin & G & HFP & HSHP).
pose proof G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof STK_values as (STT & _ & _ & SPF & _).
pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof (pal_env B TL) as ERRNO.
pose proof HB as (HCX & HFI & HOBJ & HSLOT & HFSH).
pose proof HFI as (HJ & Hly' & HFS & HPERM & HSV & HFL & HFRM & HRGF).
pose proof HOBJ as (_ & _ & _ & _ & HCH0 & _).
destruct (a7_stk B v pos lyc Sc Wc memc mdc HA7) as (Hsp16 & Hceil & Hslo & Hs32 & Hs1b & Ho16).
destruct (a7_win B v pos lyc Sc Wc memc mdc (2 * ESTACK) HA7 ltac:(unfold ESTACK; lia))
  as (Wn1 & Wn2 & Wn3).
(* the seed at 0x880c8: this run writes nothing *)
pose proof (a7_seed B v pos lyc Sc Wc rX memc mdc W2_RET_TRIM false HB) as HS.
assert (HEI : img_env VAL A_LIM (a7_E rX v pos)) by apply a7_E_img.
change (w64 (BASE + W2_RET_TRIM)) with (Z_to_bv 64 (BASE + W2_RET_TRIM)).
paj_run_shc (SRr_run_pi_AJ (fx := fx) B LAWS) (SRr_run_pi_AJ_call (fx := fx) B LAWS) HS HJ.
{ w2_awr0. }
assert (Hmem : ms_mem ms = memc).
{ apply functional_extensionality. intros x. unfold frame_of in HF. rewrite HF; [reflexivity|].
  intros (r & Hr & Ha). unfold a7_ss, a7_regions in Hr. cbn [ss_mem In] in Hr.
  destruct Hr as [<- | [<- | [<- | [<- | []]]]];
    unfold a7_saved_r, a7_slot_r, a7_sh_r, a7_buf_r in Ha;
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; lia. }
lazymatch goal with |- SRr _ _ (mkCfg _ ?dM) _ => set (mdq := dM) in *; clearbody mdq end.
pmkst HS. rewrite Hmem in HJ |- *.
clear HF HFr HG.
(* s3 is overwritten by the `mv s3, a0` at 0x880c8: the run keeps every OTHER register of the cut *)
assert (RK : forall k, In k [2; 3; 4; 8; 9; 22; 18; 20; 21; 24; 25; 26; 27] ->
  getr (ms_regs ms) (Z_to_bv 5 k) = getr rX (Z_to_bv 5 k)).
{ intros k Hk.
  exact (regs_kept_of_st_ok SEGS (a7_E rX v pos) _ _ rX (a7_extra v pos)
    (map (Z_to_bv 5) [2; 3; 4; 8; 9; 22; 18; 20; 21; 24; 25; 26; 27]) HS (a7_E_agree rX v pos)
    ltac:(vm_compute; reflexivity) (Z_to_bv 5 k) (in_map _ _ _ Hk)). }
assert (HRG1 : pf_rg (ms_regs ms) (a5_FI B v)).
{ apply (w2_rg_keep rX); [|exact HRGF].
  intros rv Hin. apply RK. unfold a5_FI in Hin. cbn [In] in Hin.
  destruct Hin as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]; cbn [fst In]; tauto. }
destruct (w3_fi_get B v (ms_regs ms) HRG1) as (D2 & D3 & D4 & D8).
assert (HSf1 : exists f, Sc = set_fs f Sc) by (exists (st_fs Sc); destruct Sc; reflexivity).
assert (HBc : pf_base B v pos lyc Sc Wc (ms_regs ms) memc mdq PF_SC_LINE)
  by exact (a5_move0 B v pos lyc Sc Wc rX memc mdc PF_SC_LINE Sc Wc (ms_regs ms) memc mdq
       PF_SC_LINE HB HJ HSf1 (Permutation_refl _) (fun a _ _ => eq_refl) (fun a H => H) HRG1 HFSH).
destruct (a5_geo B v pos lyc Sc Wc (ms_regs ms) memc mdq PF_SC_LINE HBc)
  as (HARc & _ & Hfinc & _ & _ & _).
assert (HA7c : a7_st B v pos lyc Sc Wc memc mdq)
  by exact (a7_st_of_base B v pos lyc Sc Wc (ms_regs ms) memc mdq HBc).
prreg HS (1%bv : bv 5) Q1. prreg HS (10%bv : bv 5) Q10.
prreg HS (11%bv : bv 5) Q11. prreg HS (12%bv : bv 5) Q12.
assert (RB1 : getr (ms_regs ms) 1 = Z_to_bv 64 (BASE + W2_RET_NCASE))
  by (rewrite Q1; unfold W2_RET_NCASE, AF_reac_segconf_parse_file; reflexivity).
assert (RB10 : getr (ms_regs ms) 10 = w64 bp)
  by (rewrite Q10, (a7_ew_reg rX v pos 10 10%bv eq_refl); exact R10).
assert (RB11 : getr (ms_regs ms) 11 = w64 (seg_litA_rc S_segment)).
{ rewrite Q11. change 282%nat with (A_OBJ 41). exact (w2_lit _ HEI). }
assert (RB12 : getr (ms_regs ms) 12 = w64 7) by (rewrite Q12; reflexivity).
prreg HS (19%bv : bv 5) Q19.
assert (RB19 : getr (ms_regs ms) 19 = w64 bp)
  by (rewrite Q19, (a7_ew_reg rX v pos 10 10%bv eq_refl); exact R10).
assert (HRGm : pf_rg (ms_regs ms)
  ([(19, bp)] ++ [(18, 0x23); (24, p_c v); (27, pf_SH v pos); (20, 0x20); (25, 9)] ++ PF_RM v o ln)).
{ unfold PF_RM. cbn [app]. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
  - exact RB19.
  - rewrite (RK 18 ltac:(cbn [In]; tauto)). eapply a5_rg_get; [exact HRG | cbn [app In PF_RM]; tauto].
  - rewrite (RK 24 ltac:(cbn [In]; tauto)). eapply a5_rg_get; [exact HRG | cbn [app In PF_RM]; tauto].
  - rewrite (RK 27 ltac:(cbn [In]; tauto)). eapply a5_rg_get; [exact HRG | cbn [app In PF_RM]; tauto].
  - rewrite (RK 20 ltac:(cbn [In]; tauto)). eapply a5_rg_get; [exact HRG | cbn [app In PF_RM]; tauto].
  - rewrite (RK 25 ltac:(cbn [In]; tauto)). eapply a5_rg_get; [exact HRG | cbn [app In PF_RM]; tauto].
  - rewrite (RK 21 ltac:(cbn [In]; tauto)). eapply a5_rg_get; [exact HRG | cbn [app In PF_RM]; tauto].
  - rewrite (RK 26 ltac:(cbn [In]; tauto)). eapply a5_rg_get; [exact HRG | cbn [app In PF_RM]; tauto]. }
assert (Hsp : spZ (ms_regs ms) = pf_sp0 v + (pf_s1 v - pf_sp0 v))
  by (unfold spZ; rewrite D2, a6_w64_u by lia; lia).
(* the interceptor's premises (pf_a7_r.v) *)
destruct (a7_ncase_pre_880dc B v pos lyc Sc Wc memc mdq (ms_regs ms) bp
  (a7_body (pf_tline (p_s v) o) ci) HA7c ltac:(rewrite Hsp; lia)
  ltac:(rewrite RB1; apply ret_ok_codeptr_v; [unfold W2_RET_NCASE, AF_reac_segconf_parse_file; lia | reflexivity])
  D3 D4 RB10 RB11 RB12 HSTR HINB)
  as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9 & N10 & N11 & N12 & N13 & N14 & N15 & N16).
(* 0x880dc: the interceptor, through PaArt.aj_art_at *)
eapply SRr_bind.
{ eapply (aj_art_at SEGS B LAWS pa_segs_low ERRNO (2 * ESTACK) (fun _ : Z => False)
    (pa_sigma SS___interceptor_trampoline_strncasecmp) Wc (ms_regs ms) memc
    STK_reac_segconf_parse_file (pf_sp0 v) (seg_spec.RC_PARSE_W (p_c v)) (p_ly v) (p_S v) (p_W v)
    (p_mem v) (p_md v) [(5, pos)] lyc Sc mdq 0 (pf_s1 v - pf_sp0 v)
    (Z_to_bv 64 (BASE + W2_RET_NCASE)) _ HJ Hsp Ho16).
  - lia.
  - unfold ESTACK; lia.
  - exact Wn3.
  - exact RB1.
  - intros a [].
  - exact (ANCASE fx lyc Sc Wc (ms_regs ms) memc mdq bp (seg_litA_rc S_segment) 7
      (seg_spec.zb (a7_body (pf_tline (p_s v) o) ci)) (seg_spec.zb S_segment)
      N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 N12 N13 N14 N15 N16). }
(* back at 0x880e0 *)
cbv beta. intros W' c' _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & A0 & HK).
rewrite (w2_ZS_zb Wc memc bp _ HSTR), w2_ZS_seg in A0.
change (Z.to_nat 7) with 7%nat in A0.
assert (HIFF : getr regs2 10 = w64 0 <->
  strncasecmp (a7_body (pf_tline (p_s v) o) ci) S_segment 7 = 0).
{ pose proof (w2_strncase_bridge (a7_body (pf_tline (p_s v) o) ci)
    (a7_body_nul (pf_tline (p_s v) o) ci)) as HBR.
  split; intros H; [apply HBR, A0, H | apply A0, HBR, H]. }
(* every byte off A5's write set is kept; the window is kept present by the journal *)
assert (HKB : forall sl shw a, 0 <= a < 2 ^ 64 -> ~ a5_Wrx v pos sl shw a ->
  rdW Wc mem2 a = rdW Wc memc a).
{ intros sl shw. apply (w3_keepW v pos (pf_s1 v - 2 * ESTACK) (a5_buf v pos));
    [rewrite SPF; unfold ESTACK; lia | lia |].
  intros a Ha Hwin _. apply HK; [exact Ha | | intros []].
  unfold ESTACK in *. lia. }
assert (HKbuf : forall x, pf_F v pos + PF_O_BUF <= x < pf_F v pos + PF_O_BUF + 512 ->
  rdW Wc mem2 x = rdW Wc memc x).
{ intros x Hx. apply HK; [unfold PF_O_BUF in *; lia | | intros []].
  unfold ESTACK, PF_O_BUF in *. rewrite SPF in G1. lia. }
assert (HVB : forall a, rdW Wc memc a <> None -> rdW Wc mem2 a <> None).
{ assert (HV0 : forall a, 0 <= a < 2 ^ 64 -> rdW Wc memc a <> None -> rdW Wc mem2 a <> None).
  { intros a Ha Hs.
    destruct (Z_lt_le_dec a (pf_s1 v - 2 * ESTACK)) as [Hlo | Hlo];
      [|destruct (Z_lt_le_dec a (pf_s1 v)) as [Hhi | Hhi]].
    - rewrite (HK a Ha ltac:(unfold ESTACK in *; lia) ltac:(intros [])). exact Hs.
    - pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _).
      apply (aview_some_of_apresent SEGS). apply Hpres. rewrite SPF. unfold ESTACK in Hlo. lia.
    - rewrite (HK a Ha ltac:(unfold ESTACK in *; lia) ltac:(intros [])). exact Hs. }
  intros a Hs. rewrite w3_view_wrap. rewrite w3_view_wrap in Hs.
  apply HV0; [apply Z.mod_pos_bound; lia | exact Hs]. }
assert (HSf0 : exists f, Sc = set_fs f Sc) by (exists (st_fs Sc); destruct Sc; reflexivity).
assert (HRG2 : pf_rg regs2 (a5_FI B v))
  by exact (a5_rg_pres (ms_regs ms) regs2 _ HP2 (a5_FI_cs B v) HRG1).
assert (HFSH2 : pf_fsh (rdW Wc mem2) (pf_SH v pos) PF_SC_LINE)
  by exact (a5_keep_fsh v pos _ _ true PF_SC_LINE G
       (HKB true false) HFSH).
pose proof (a5_move0 B v pos lyc Sc Wc (ms_regs ms) memc mdq PF_SC_LINE Sc Wc regs2 mem2 md2 PF_SC_LINE
  HBc HJ2 HSf0 (Permutation_refl _) (HKB true true) HVB HRG2 HFSH2) as HB2.
pose proof (a7_st_of_base B v pos lyc Sc Wc regs2 mem2 md2 HB2) as HA7b.
apply (KC regs2 mem2 md2).
split; [exact HB2|]. split; [exact HMID|].
split; [exact (w3_keep_st0 B v pos lyc Sc Wc memc mdq Wc mem2 cf nm _ G HARc Hfinc Hly
                 (HKB true true) HCH0 HST0)|].
split; [exact HLEN|]. split; [exact HCL|]. split; [exact HNTH|].
split.
{ apply (w2_str_keep (rdW Wc memc) (rdW Wc mem2) bp _ HSTR).
  - intros x Hx. apply HKbuf. destruct HINB as [HJ1 HJ2']. unfold PF_O_BUF in *. lia.
  - refine (a7_tail_vis_buf B v pos lyc Sc Wc mem2 md2 _ HA7b _).
    unfold a7_buf. destruct HINB as [HJ1 HJ2']. unfold PF_O_BUF in *. lia. }
split; [exact HINB|]. split; [exact HIFF|].
apply (a5_rg_pres (ms_regs ms) regs2 _ HP2).
- unfold PF_RM. cbn [app]. repeat apply Forall_cons; try apply Forall_nil;
    cbn [fst]; unfold acallee_saved; lia.
- exact HRGm.
Qed.

(* 0x880e0: the branch -> KWOK 0x882f0 or UNK 0x880e4 *)
Lemma w2_C : forall (n : nat) v pos lyc Sc Wc rX memc mdc cf nm o ln d (lp : Z) ci bp,
  HA_KWOK B n -> HA_UNK B n ->
  w2_midB n v pos lyc Sc Wc rX memc mdc cf nm o ln d ci bp ->
  SRr SEGS Wc (mkCfg (mkst rX (Z_to_bv 64 (BASE + W2_RET_NCASE)) memc (seg_rom SEGS)) mdc)
    (pf_postm B v (r_header cf nm (ln + 1) (pf_tline (p_s v) o)) o ln).
Proof.
intros n v pos lyc Sc Wc rX memc mdc cf nm o ln d lp ci bp HKW HUN HM.
pose proof HM as (HB & HMID & HST0 & HLEN & HCL & HNTH & HSTR & HINB & HIFF & HRG).
pose proof HB as (HCX & HFI & HOBJ & HSLOT & HFSH).
pose proof HFI as (HJ & Hly' & HFS & HPERM & HSV & HFL & HFRM & HRGF).
pose proof (a7_seed B v pos lyc Sc Wc rX memc mdc W2_RET_NCASE false HB) as HS.
assert (HEI : img_env VAL A_LIM (a7_E rX v pos)) by apply a7_E_img.
assert (U10 : U (a7_E rX v pos) (SOff 10 0) = bv_unsigned (getr rX 10)).
{ unfold U. cbn [sv_denot]. rewrite (a7_ew_reg rX v pos 10 10%bv eq_refl), Z.add_0_r.
  rewrite Z_to_bv_bv_unsigned. reflexivity. }
psrr_branch_pi (SRr_run_pi_AJ (fx := fx) B LAWS) (paj_branch (PI := PI)) HS.
- (* a0 = 0: the keyword matched, the walk jumps to KWOK *)
  rewrite branch_eq_U, U10, U_lit in Hc by lia.
  apply Z.eqb_eq in Hc.
  assert (HKWOK : strncasecmp (a7_body (pf_tline (p_s v) o) ci) S_segment 7 = 0)
    by (apply HIFF; apply bv_eq; rewrite a6_w64_u by lia; exact Hc).
  paj_run_to_sh (SRr_run_to_pi_AJ (fx := fx) B LAWS) HS HJ A7_KWOK.
  { w2_awr0. }
  assert (Hmem : ms_mem ms = memc).
  { apply functional_extensionality. intros x. unfold frame_of in HF. rewrite HF; [reflexivity|].
    intros (r & Hr & Ha). unfold a7_ss, a7_regions in Hr. cbn [ss_mem In] in Hr.
    destruct Hr as [<- | [<- | [<- | [<- | []]]]];
      unfold a7_saved_r, a7_slot_r, a7_sh_r, a7_buf_r in Ha;
      cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; lia. }
  lazymatch goal with |- SRr _ _ (mkCfg _ ?dM) _ => set (mdq := dM) in *; clearbody mdq end.
  pmkst HS. rewrite Hmem in HJ |- *.
  pose proof (aregs_preserved_of_st_ok SEGS _ _ _ _ rX (a7_extra v pos) HS (a7_E_agree rX v pos)
    ltac:(vm_compute; reflexivity)) as HPR.
  assert (HRG1 : pf_rg (ms_regs ms) (a5_FI B v))
    by exact (a5_rg_pres rX (ms_regs ms) _ HPR (a5_FI_cs B v) HRGF).
  change (cfg_at SEGS (BASE + A7_KWOK) (ms_regs ms) memc mdq)
    with (mkCfg (mkst (ms_regs ms) (Z_to_bv 64 (BASE + A7_KWOK)) memc (seg_rom SEGS)) mdq).
  apply (HKW fx v pos lyc Sc Wc (ms_regs ms) memc mdq cf nm o ln d lp ci bp).
  split; [exact (a5_move0 B v pos lyc Sc Wc rX memc mdc PF_SC_LINE Sc Wc (ms_regs ms) memc mdq
    PF_SC_LINE HB HJ ltac:(exists (st_fs Sc); destruct Sc; reflexivity) (Permutation_refl _)
    (fun a _ _ => eq_refl) (fun a H => H) HRG1 HFSH)|].
  split; [exact HMID|]. split; [exact HST0|]. split; [exact HLEN|].
  split; [exact HCL|]. split; [exact HNTH|]. split; [exact HKWOK|].
  split; [exact HSTR|]. split; [exact HINB|].
  apply (a5_rg_incl (ms_regs ms)
    ([(19, bp)] ++ [(18, 0x23); (24, p_c v); (27, pf_SH v pos); (20, 0x20); (25, 9)]
     ++ PF_RM v o ln));
    [intros x Hx; cbn [app In PF_RM] in Hx |- *; tauto |].
  apply (a5_rg_pres rX (ms_regs ms) _ HPR); [|exact HRG].
  unfold PF_RM. cbn [app]. repeat apply Forall_cons; try apply Forall_nil;
    cbn [fst]; unfold acallee_saved; lia.
- (* a0 <> 0: the keyword did not match, the walk falls into UNK *)
  rewrite branch_eq_U, U10, U_lit in Hc by lia.
  apply Z.eqb_neq in Hc.
  assert (HNE : strncasecmp (a7_body (pf_tline (p_s v) o) ci) S_segment 7 <> 0).
  { intros Heq. apply Hc. pose proof (proj2 HIFF Heq) as E.
    rewrite E, a6_w64_u by lia. reflexivity. }
  paj_run_to_sh (SRr_run_to_pi_AJ (fx := fx) B LAWS) HS HJ A7_UNK.
  { w2_awr0. }
  assert (Hmem : ms_mem ms = memc).
  { apply functional_extensionality. intros x. unfold frame_of in HF. rewrite HF; [reflexivity|].
    intros (r & Hr & Ha). unfold a7_ss, a7_regions in Hr. cbn [ss_mem In] in Hr.
    destruct Hr as [<- | [<- | [<- | [<- | []]]]];
      unfold a7_saved_r, a7_slot_r, a7_sh_r, a7_buf_r in Ha;
      cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; lia. }
  lazymatch goal with |- SRr _ _ (mkCfg _ ?dM) _ => set (mdq := dM) in *; clearbody mdq end.
  pmkst HS. rewrite Hmem in HJ |- *.
  pose proof (aregs_preserved_of_st_ok SEGS _ _ _ _ rX (a7_extra v pos) HS (a7_E_agree rX v pos)
    ltac:(vm_compute; reflexivity)) as HPR.
  assert (HRG1 : pf_rg (ms_regs ms) (a5_FI B v))
    by exact (a5_rg_pres rX (ms_regs ms) _ HPR (a5_FI_cs B v) HRGF).
  change (cfg_at SEGS (BASE + A7_UNK) (ms_regs ms) memc mdq)
    with (mkCfg (mkst (ms_regs ms) (Z_to_bv 64 (BASE + A7_UNK)) memc (seg_rom SEGS)) mdq).
  apply (HUN fx v pos lyc Sc Wc (ms_regs ms) memc mdq cf nm o ln d bp
    (a7_body (pf_tline (p_s v) o) ci)).
  split; [exact (a5_move0 B v pos lyc Sc Wc rX memc mdc PF_SC_LINE Sc Wc (ms_regs ms) memc mdq
    PF_SC_LINE HB HJ ltac:(exists (st_fs Sc); destruct Sc; reflexivity) (Permutation_refl _)
    (fun a _ _ => eq_refl) (fun a H => H) HRG1 HFSH)|].
  split; [exact HMID|]. split; [exact HST0|].
  split; [exact HSTR|]. split; [exact HINB|].
  split; [exact (a7_hdr_unknown cf nm (ln + 1) (pf_tline (p_s v) o) ci HCL HNTH (or_introl HNE))|].
  apply (a5_rg_incl (ms_regs ms)
    ([(19, bp)] ++ [(18, 0x23); (24, p_c v); (27, pf_SH v pos); (20, 0x20); (25, 9)]
     ++ PF_RM v o ln));
    [intros x Hx; cbn [app In PF_RM] in Hx |- *; tauto |].
  apply (a5_rg_pres rX (ms_regs ms) _ HPR); [|exact HRG].
  unfold PF_RM. cbn [app]. repeat apply Forall_cons; try apply Forall_nil;
    cbn [fst]; unfold acallee_saved; lia.
Qed.

(** ** The piece *)
Lemma w2_close : forall n, HA_KWOK B n -> HA_UNK B n -> H_CLOSE (fx := fx) B n.
Proof.
intros n HKW HUN. unfold H_CLOSE.
intros v pos lyc Sc Wc rX memc mdc cf cur nm o ln d lp ci HINV.
apply (w2_A n v pos lyc Sc Wc rX memc mdc cf cur nm o ln d lp ci _ HINV).
intros S2 W2 regs2 mem2 md2 bp HMA.
apply (w2_B n v pos lyc S2 W2 regs2 mem2 md2 cf nm o ln d ci bp _ HMA).
intros regs3 mem3 md3 HMB.
exact (w2_C n v pos lyc S2 W2 regs3 mem3 md3 cf nm o ln d lp ci bp HKW HUN HMB).
Qed.

End x.

(** ** The piece pf_a7.v's a7_assemble applies *)
Theorem a7_w2 : A7_S_CLOSE B.
Proof. intros f0 n HKW HUN. exact (w2_close (fx := f0) n HKW HUN). Qed.

End e.
End f.
End d.
