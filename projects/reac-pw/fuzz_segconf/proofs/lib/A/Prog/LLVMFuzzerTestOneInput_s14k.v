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
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/check_round_trip.v, with its module paths and module names changed; 4505 of its 4800 lines of code are new or changed and 4758 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/A/Prog/LLVMFuzzerTestOneInput_s15.v, with its module paths and module names changed; 356 of its 464 lines of code are new or changed and 4692 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, ASan image A (fuzz_segconf.asan, pin sha256 48c5355bdacb): the kit of segment S04 of the
   walk of the test harness's entry function LLVMFuzzerTestOneInput (0x85024 .. 0x850f4, _s14 of the harness walk):
   the turn's reads over the payload's bytes (pure list facts over seg_spec / SegModel). *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation String.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP00 YP0i YP0j YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0n YI0s YI16 YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05 YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaRun PaShadow PaJournal SegSyms SegList SegAddr SegPa.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPaLib PaLibG PaLibH PaSB PaDenot PaLibF PaCall PaCallRun PaArt.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegObj SegGlob SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Rt Require Import ConstsViewDef MemchrDef.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import LLVMFuzzerTestOneInput_c SegInstA
  LLVMFuzzerTestOneInput_inst LLVMFuzzerTestOneInput_defs LLVMFuzzerTestOneInput_s02 LLVMFuzzerTestOneInput_s10k.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require m_file_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A Require AF0m.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ===================================== the turn's reads (pure) ===================================== *)
Lemma s14_u8_snd : forall l, snd (SegModel.fuzz_u8 l) = skipn 1 l.
Proof. intros [|x l]; reflexivity. Qed.
Lemma s14_u8_fst : forall l, fst (SegModel.fuzz_u8 l) = nth 0 l 0.
Proof. intros [|x l]; reflexivity. Qed.
Lemma s14_u16_snd : forall l, snd (SegModel.fuzz_u16 l) = skipn 2 l.
Proof. intros [|x [|y l]]; reflexivity. Qed.
(* two bytes, low first: lo | hi << 8 is lo + 256 hi (checked over every pair) *)
Definition s14_or8_ok (x y : Z) : bool := Z.lor x (Z.shiftl y 8) =? x + 256 * y.
Lemma s14_or8_chk : forallb (fun x => forallb (fun y => s14_or8_ok (Z.of_nat x) (Z.of_nat y)) (seq 0 256)) (seq 0 256) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma s14_or8 : forall x y, 0 <= x < 256 -> 0 <= y < 256 -> Z.lor x (Z.shiftl y 8) = x + 256 * y.
Proof.
intros x y Hx Hy.
pose proof (proj1 (forallb_forall _ _) s14_or8_chk (Z.to_nat x) ltac:(apply in_seq; lia)) as H. cbv beta in H.
pose proof (proj1 (forallb_forall _ _) H (Z.to_nat y) ltac:(apply in_seq; lia)) as H2.
unfold s14_or8_ok in H2. rewrite !Z2Nat.id in H2 by lia. apply Z.eqb_eq in H2. exact H2.
Qed.
Lemma s14_u16_fst : forall l, (forall i, 0 <= nth i l 0 < 256) ->
  fst (SegModel.fuzz_u16 l) = nth 0 l 0 + 256 * nth 1 l 0.
Proof.
intros l Hb. pose proof (Hb 0%nat) as H0. pose proof (Hb 1%nat) as H1.
destruct l as [|x [|y l]]; cbn [SegModel.fuzz_u16 SegModel.fuzz_u8 fst nth] in *.
- reflexivity.
- rewrite (s14_or8 x 0) by lia. replace 65535 with (Z.ones 16) by reflexivity.
  rewrite Z.land_ones by lia. apply Z.mod_small. lia.
- rewrite (s14_or8 x y) by lia. replace 65535 with (Z.ones 16) by reflexivity.
  rewrite Z.land_ones by lia. apply Z.mod_small. lia.
Qed.

(* the cursor after k records is a suffix of the input *)
Lemma s14_skip_suffix : forall k l, exists j, seg_spec.seg_skip k l = skipn j l.
Proof.
induction k as [|k IH]; intros l; [exists 0%nat; reflexivity|].
cbn [seg_spec.seg_skip].
destruct (SegModel.fuzz_u8 l) as [lb i1] eqn:Eu1.
destruct (SegModel.fuzz_u16 i1) as [len i2] eqn:Eu2.
assert (E1 : i1 = skipn 1 l) by (rewrite <- (s14_u8_snd l), Eu1; reflexivity).
assert (E2 : i2 = skipn 2 i1) by (rewrite <- (s14_u16_snd i1), Eu2; reflexivity).
unfold SegModel.fuzz_take. cbv beta iota zeta.
destruct (IH (skipn (Nat.min (Z.to_nat len) (length i2)) i2)) as [j Hj]. rewrite Hj.
subst i2 i1. rewrite !skipn_skipn. eexists. reflexivity.
Qed.
Lemma s14_skipn_len : forall {A} j (l : list A), skipn j l = skipn (length l - length (skipn j l)) l.
Proof.
intros A j l. rewrite length_skipn. destruct (Nat.le_gt_cases j (length l)) as [H|H].
- replace (length l - (length l - j))%nat with j by lia. reflexivity.
- rewrite !skipn_all2 by lia. reflexivity.
Qed.
Lemma s14_hdr_skipn : forall pl, seg_spec.seg_hdr pl = skipn 3 (seg_spec.seg_in pl).
Proof. intros pl. unfold seg_spec.seg_hdr. rewrite !s14_u8_snd, !skipn_skipn. reflexivity. Qed.
Lemma s14_cur_eq : forall pl f,
  seg_spec.seg_cur pl f = skipn (length pl - length (seg_spec.seg_cur pl f)) (seg_spec.seg_in pl).
Proof.
intros pl f.
assert (Hs : exists j, seg_spec.seg_cur pl f = skipn j (seg_spec.seg_in pl)).
{ unfold seg_spec.seg_cur. rewrite s14_hdr_skipn.
  destruct (s14_skip_suffix f (skipn 3 (seg_spec.seg_in pl))) as [j Hj]. rewrite Hj, skipn_skipn.
  eexists; reflexivity. }
destruct Hs as [j Hj]. rewrite Hj.
replace (length pl) with (length (seg_spec.seg_in pl)) by (unfold seg_spec.seg_in, seg_spec.zs; apply length_map).
apply s14_skipn_len.
Qed.
(* byte i of the cursor is byte len - curn + i of the payload, and every byte is below 256 *)
Lemma s14_in_nth : forall pl j, nth j (seg_spec.seg_in pl) 0 =
  if (j <? length pl)%nat then bv_unsigned (nth j pl (Z_to_bv 8 0)) else 0.
Proof.
intros pl j. unfold seg_spec.seg_in, seg_spec.zs. destruct (Nat.ltb_spec j (length pl)) as [H|H].
- rewrite (nth_indep _ 0 (bv_unsigned (Z_to_bv 8 0))) by (rewrite length_map; exact H).
  exact (map_nth (fun b : byte => bv_unsigned b) pl (Z_to_bv 8 0) j).
- apply nth_overflow. rewrite length_map. exact H.
Qed.
Lemma s14_cur_nth : forall pl f i, (i < length (seg_spec.seg_cur pl f))%nat ->
  nth i (seg_spec.seg_cur pl f) 0 =
  bv_unsigned (nth (length pl - length (seg_spec.seg_cur pl f) + i) pl (Z_to_bv 8 0)).
Proof.
intros pl f i Hi. pose proof (s14_cur_eq pl f) as E.
assert (HL : (length (seg_spec.seg_cur pl f) <= length pl)%nat).
{ rewrite E at 1. rewrite length_skipn. unfold seg_spec.seg_in, seg_spec.zs. rewrite length_map. lia. }
rewrite E at 1. rewrite nth_skipn_add, s14_in_nth.
destruct (Nat.ltb_spec (length pl - length (seg_spec.seg_cur pl f) + i) (length pl)) as [H|H]; [reflexivity | lia].
Qed.
Lemma s14_cur_byte : forall pl f i, 0 <= nth i (seg_spec.seg_cur pl f) 0 < 256.
Proof.
intros pl f i. destruct (Nat.lt_ge_cases i (length (seg_spec.seg_cur pl f))) as [H|H].
- rewrite (s14_cur_nth pl f i H). pose proof (bv_unsigned_in_range 8 (nth (length pl - length (seg_spec.seg_cur pl f) + i) pl (Z_to_bv 8 0))) as R.
  change (bv_modulus 8) with 256 in R. exact R.
- rewrite nth_overflow by exact H. lia.
Qed.
Lemma s14_cur_len : forall pl f, (length (seg_spec.seg_cur pl f) <= length pl)%nat.
Proof.
intros pl f. rewrite s14_cur_eq at 1. rewrite length_skipn. unfold seg_spec.seg_in, seg_spec.zs. rewrite length_map. lia.
Qed.

(* the files decode builds: file f is read at the cursor after f records *)
Lemma s14_dec_nth : forall K l f, (f < K)%nat ->
  nth f (SegModel.dec_files K l) (SegModel.File 0 []) =
  SegModel.File (fst (SegModel.fuzz_u8 (seg_spec.seg_skip f l)))
    (SegModel.fuzz_str (fst (SegModel.fuzz_take (snd (SegModel.fuzz_u16 (snd (SegModel.fuzz_u8 (seg_spec.seg_skip f l)))))
      (fst (SegModel.fuzz_u16 (snd (SegModel.fuzz_u8 (seg_spec.seg_skip f l)))))))).
Proof.
induction K as [|K IH]; intros l f Hf; [lia|].
destruct f as [|f].
- cbn [SegModel.dec_files seg_spec.seg_skip].
  destruct (SegModel.fuzz_u8 l) as [lb i1]. cbn [fst snd].
  destruct (SegModel.fuzz_u16 i1) as [len i2]. cbn [fst snd].
  destruct (SegModel.fuzz_take i2 len) as [p i3]. reflexivity.
- cbn [SegModel.dec_files seg_spec.seg_skip].
  destruct (SegModel.fuzz_u8 l) as [lb i1]. destruct (SegModel.fuzz_u16 i1) as [len i2].
  destruct (SegModel.fuzz_take i2 len) as [p i3]. cbn [nth]. apply IH. lia.
Qed.
Lemma s14_files : forall pl,
  seg_spec.seg_files pl = SegModel.dec_files (length (seg_spec.seg_files pl)) (seg_spec.seg_hdr pl).
Proof.
intros pl. unfold seg_spec.seg_files, seg_spec.seg_pay, SegModel.decode, seg_spec.seg_hdr.
destruct (SegModel.fuzz_u8 (seg_spec.seg_in pl)) as [b0 i1]. cbn [snd].
destruct (SegModel.fuzz_u8 i1) as [fl i2]. cbn [snd].
destruct (SegModel.fuzz_u8 i2) as [b2 i3]. cbn [snd SegModel.p_files].
rewrite dec_files_length. reflexivity.
Qed.
Lemma s14_file : forall pl f, (f < length (seg_spec.seg_files pl))%nat ->
  seg_spec.seg_file pl f = SegModel.File (fst (SegModel.fuzz_u8 (seg_spec.seg_cur pl f)))
    (SegModel.fuzz_str (fst (SegModel.fuzz_take (seg_spec.seg_turn_tail pl f) (seg_spec.seg_turn_len pl f)))).
Proof.
intros pl f Hf. unfold seg_spec.seg_file. rewrite s14_files. rewrite s14_dec_nth by exact Hf. reflexivity.
Qed.

(* the turn's quantities in the cursor's terms *)
Lemma s14_tail : forall pl f, seg_spec.seg_turn_tail pl f = skipn 3 (seg_spec.seg_cur pl f).
Proof. intros pl f. unfold seg_spec.seg_turn_tail. rewrite s14_u16_snd, s14_u8_snd, skipn_skipn. reflexivity. Qed.
Lemma s14_len16 : forall pl f, seg_spec.seg_turn_len pl f =
  nth 1 (seg_spec.seg_cur pl f) 0 + 256 * nth 2 (seg_spec.seg_cur pl f) 0.
Proof.
intros pl f. unfold seg_spec.seg_turn_len. rewrite s14_u8_snd, s14_u16_fst.
- rewrite !nth_skipn_add. reflexivity.
- intros i. rewrite nth_skipn_add. apply s14_cur_byte.
Qed.
Lemma s14_np : forall pl f, seg_spec.seg_turn_np pl f =
  Z.min (seg_spec.seg_turn_len pl f) (Z.of_nat (length (seg_spec.seg_turn_tail pl f))).
Proof.
intros pl f. unfold seg_spec.seg_turn_np, SegModel.fuzz_take. cbn [fst].
rewrite length_firstn. rewrite s14_len16. pose proof (s14_cur_byte pl f 1). pose proof (s14_cur_byte pl f 2). lia.
Qed.
Lemma s14_lb : forall pl f, (f < length (seg_spec.seg_files pl))%nat ->
  seg_spec.seg_lb pl f = nth 0 (seg_spec.seg_cur pl f) 0.
Proof. intros pl f Hf. unfold seg_spec.seg_lb. rewrite s14_file by exact Hf. cbn [SegModel.f_lb]. apply s14_u8_fst. Qed.
Lemma s14_txt : forall pl f, (f < length (seg_spec.seg_files pl))%nat ->
  seg_spec.seg_txt pl f = SegModel.cut_nul (firstn (Z.to_nat (seg_spec.seg_turn_np pl f)) (seg_spec.seg_turn_tail pl f)).
Proof.
intros pl f Hf. unfold seg_spec.seg_txt. rewrite s14_file by exact Hf. cbn [SegModel.f_text].
unfold SegModel.fuzz_str, SegModel.fuzz_take. cbn [fst]. f_equal. f_equal.
rewrite s14_np. rewrite s14_len16. pose proof (s14_cur_byte pl f 1). pose proof (s14_cur_byte pl f 2). lia.
Qed.
(* the length of a text cut at its first NUL *)
Lemma s14_cut_len : forall l k, (k <= length l)%nat -> (forall i, (i < k)%nat -> nth i l 0 <> 0) ->
  ((k < length l)%nat -> nth k l 0 = 0) -> length (SegModel.cut_nul l) = k.
Proof.
induction l as [|x l IH]; intros k Hk Hnz Hz; cbn [length] in *.
- cbn [SegModel.cut_nul length]. lia.
- cbn [SegModel.cut_nul]. destruct (Z.eqb_spec x 0) as [E|E].
  + destruct k as [|k]; [reflexivity|]. exfalso. exact (Hnz 0%nat ltac:(lia) E).
  + destruct k as [|k]; [exfalso; exact (E (Hz ltac:(lia)))|].
    cbn [length]. f_equal. apply IH; [lia | intros i Hi; exact (Hnz (S i) ltac:(lia)) | intros Hl; exact (Hz ltac:(lia))].
Qed.

(* lo .. hi of the turn's text cut at its first NUL: every byte of the cut is from the text *)
Lemma s14_cut_le : forall l, (length (SegModel.cut_nul l) <= length l)%nat.
Proof.
induction l as [|x l IH]; cbn [SegModel.cut_nul length]; [lia|].
destruct (x =? 0); cbn [length]; lia.
Qed.
Lemma s14_txt_n_le : forall pl f, (f < length (seg_spec.seg_files pl))%nat ->
  0 <= seg_spec.seg_txt_n pl f <= seg_spec.seg_turn_np pl f /\ seg_spec.seg_turn_np pl f <= 65535 /\
  seg_spec.seg_turn_np pl f <= Z.of_nat (length (seg_spec.seg_turn_tail pl f)).
Proof.
intros pl f Hf. unfold seg_spec.seg_txt_n. rewrite s14_txt by exact Hf.
pose proof (s14_cut_le (firstn (Z.to_nat (seg_spec.seg_turn_np pl f)) (seg_spec.seg_turn_tail pl f))) as H.
rewrite length_firstn in H. rewrite s14_np in *. rewrite s14_len16 in *.
pose proof (s14_cur_byte pl f 1). pose proof (s14_cur_byte pl f 2). lia.
Qed.

(* ===================================== the symbolic state at K85024 ===================================== *)
(* every register its own atom (s4 = atom 20 for a turn with three header bytes, the literal curn otherwise);
   atom 32 the shadow base, atoms 33 .. 35 the turn's header bytes lb, len lo, len hi. Regions: the s1 slots
   [152, 184) (writable [152, 160) for `sd s4,152(s1)`, 176 = the shadow base the checks reload) and the h header
   bytes at the cursor s8 (atom 24), read-only; the shadow entry of those bytes makes checks 4-6 vanish. *)
Definition S14x : sv := SOff 32 0.
Definition S14span : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
Definition s14_chunks : list YP09.chunk :=
  [YP09.mkChunk 0 (CVal 1 (SOff 33 0)); YP09.mkChunk 1 (CVal 1 (SOff 34 0)); YP09.mkChunk 2 (CVal 1 (SOff 35 0))].
Definition s14_rslot : YP09.region := YP09.mkRegion (Some 9%nat) 152 184 152 160 [YP09.mkChunk 176 (CVal 8 (SOff 32 0))].
Definition s14_rpay (h : Z) : YP09.region := YP09.mkRegion (Some 24%nat) 0 h 0 0 (firstn (Z.to_nat h) s14_chunks).
Definition s14_regions (h : Z) : smem := if h =? 0 then [s14_rslot] else [s14_rslot; s14_rpay h].
Definition s14_facts (rlo rhi : Z) : facts :=
  mkFacts [ (9%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
    (24%nat, mkAF 0 0x7fffff800000 0); (20%nat, mkAF rlo rhi 0);
    (33%nat, mkAF 0 255 0); (34%nat, mkAF 0 255 0); (35%nat, mkAF 0 255 0) ] [] [].
Definition s14_SH (h : Z) : list shent := if h =? 0 then [] else [mkSHE 24 0 h].
Definition s14_sr (s4 : option Z) : list sv :=
  match s4 with None => sr_atoms | Some z => sr_set sr_atoms (20%bv : bv 5) (SLit z) end.
Definition ss_s14 (s4 : option Z) (h rlo rhi : Z) : sstate :=
  mkSS LO_K85024 (s14_sr s4) (s14_regions h) None (s14_facts rlo rhi).
Definition s14_extra (b0 b1 b2 : Z) : list word := map (Z_to_bv 64) [SHADOW_OFF; b0; b1; b2].
(* after memchr (0x850dc): every register its own atom, no region *)
Definition ss_s14b : sstate := mkSS 0x3a8 sr_atoms [] None (mkFacts [] [] []).
Definition S14_KEEP : list (bv 5) := [2; 3; 4; 8; 9; 18; 19; 21; 22; 25]%bv.
Definition S14_SAVED : list (bv 5) := [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.

(* ===================================== the memchr step ===================================== *)
(* copied from the m_file group's owner's lib/A/Prog/m_file_memchr.v (commit 0f5525e7ab4e, the m_file
   group's walk, memchr_rom_fact and aj_memchr_atM): the image fact of musl memchr's constant window (a walk
   hypothesis the close discharges), and the call of the memchr wrapper (interface row 20,
   MemchrDef.amemchr_realizesM at SegInstA.memchr_loA .. memchr_hiA) as a step of the journal *)
Definition s14_memchr_rom (segs : list Segment) (B : asyms) : Prop :=
forall a, memchr_loA <= a < memchr_hiA ->
in_rom segs a /\ ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section e.
Variable segs : list Segment.
Variable B : asyms.
Hypothesis LAWS : AR_laws segs B.
Hypothesis segs_low : forall a, in_img segs a -> 0 <= a < kLowMemEnd.
Lemma s14_aj_memchr : forall pc RLO RHI,
amemchr_realizesM segs B memchr_loA memchr_hiA pc -> s14_memchr_rom segs B ->
forall W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k x c n (o : Z) raw,
ajournal segs B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
getr regsT 10 = w64 x -> getr regsT 11 = w64 c -> getr regsT 12 = w64 n ->
0 <= c < 256 -> 0 <= n < 2 ^ 32 -> 0 < x -> x + n <= 2 ^ 63 ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ESTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = raw -> YK0s.ret_ok raw ->
src_ok segs W regsT memT x n -> amem_range x n ->
range_addressable (aview segs (w_H W) memT) SHADOW_OFF x n -> (0 < n -> shadow_hull_vis (aview segs (w_H W) memT) x n) ->
arodata_okP segs RLO RHI B (aview segs (w_H W) memT) ->
SRr segs W (mkCfg (mkst regsT (Z_to_bv 64 pc) memT (seg_rom segs)) mdc)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2 kk,
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
ajournal segs B STK sp0 FP ly S W0 mem md own lyc Sc W mem2 md2 k /\
aregs_preserved regsT regs2 /\
first_byte segs W memT x n c kk /\ getr regs2 10 = (if kk <? n then w64 (x + kk) else w64 0) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 + o - ESTACK <= a < sp0 + o) -> aview segs (w_H W) mem2 a = aview segs (w_H W) memT a) /\
(forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a)).
Proof.
intros pc RLO RHI AM MC W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k x c n o raw
HJ Ha0 Ha1 Ha2 Hc Hn Hx0 Hxn Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw Hsx Hmx Hrx Hhx HRO.
pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & _ & _ & _ & _ & _ & Hpres & Hstatic & F5 & HQT).
assert (HPRE : ecall_pre segs B lyc Sc W regsT memT mdc).
{ eapply (ecall_pre_at segs B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k regsT o); try eassumption.
  rewrite Hra. exact Hraw. }
assert (HCV : consts_view segs memchr_loA memchr_hiA W memT).
{ intros a Ha. destruct (MC a Ha) as (Hrom & Ho & He). apply HRO; [left; exact Hrom | exact Ho | exact He]. }
eapply SRr_mono.
{ exact (AM lyc Sc W regsT memT mdc x c n HPRE Ha0 Ha1 Ha2 Hc Hn Hx0 Hxn Hsx Hmx Hrx Hhx HCV). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HAR2 & HP & Hsame & (kk & Hfb & Hres) & Hfr & Hpres2).
rewrite Hsp' in Hfr.
split; [reflexivity|]. exists regs2, mem2, md2, kk.
split; [unfold cfg_at, raZ; rewrite Hra; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
split.
{ eapply (ajournal_after_write segs B LAWS segs_low STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k mem2 md2
    (fun a => sp0 + o - ESTACK <= a < sp0 + o) Sc own HJ).
  - intros a Ha Hna. apply (Hfr a Ha). exact Hna.
  - exact Hpres2.
  - exact Hsame.
  - intros a Ha; left; left; zlia.
  - exact HAR2.
  - reflexivity. - reflexivity. - zlia. - exact Hfrs. - exact HQT. }
split; [exact HP|]. split; [exact Hfb|]. split; [exact Hres|]. split; [exact Hfr | exact Hpres2].
Qed.
End e.
End c.

(* a list of entries no two of which overlap repeats none: x appended to l is not in l *)
Lemma s14_pw_snoc : forall (g : Z * Z -> Z * Z) l x, pairwise zdisjoint (map g (l ++ [x])) -> 0 < snd (g x) -> ~ In x l.
Proof.
intros g l. induction l as [|y l IH]; intros x Hpw Hx Hin; [destruct Hin|].
cbn [app map pairwise] in Hpw. destruct Hpw as [Hf Hpw]. destruct Hin as [<- | Hin].
- rewrite map_app in Hf. apply Forall_app in Hf as [_ Hf]. cbn [map] in Hf. inversion Hf as [|a b Hz _]; subst.
  unfold zdisjoint in Hz. lia.
- exact (IH x Hpw Hx Hin).
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation SIG s := (@pa_sigma _ seg_listing PI s).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
(* the walk's image facts lt_img needs at a later reader: _s10's bundle (LLVMFuzzerTestOneInput_s10k.v s10_img,
   which the close gives from SegRecBase.seg_img_facts) and the record's symbols (AR's stack-protector cells) *)
Hypothesis IMGS : s10_img.
Hypothesis BSYM : AF0m.SegBSyms B.

(* ---- where the entry's stack and frame lie ---- *)
Lemma s14_sp : forall cx, lt_base B MT cx ->
  x_sp0 cx mod 16 = 0 /\ alloc_ceiling + STK_LLVMFuzzerTestOneInput <= x_sp0 cx <= 2 ^ 47 /\
  x_sp0 cx - 352 < x_s1 cx <= x_sp0 cx - 320 /\ x_s1 cx mod 32 = 0 /\ (x_s1 cx - x_sp0 cx) mod 16 = 0.
Proof.
intros cx HB. pose proof HB as (HPRE & _). pose proof HPRE as (_ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal & _ & Hceil & Hslo & Hshi & H47 & _).
unfold x_s1, x_sp0, LT_FRAME, STK_LLVMFuzzerTestOneInput in *. set (sp := spZ (x_regs cx)) in *.
pose proof (Z.mod_pos_bound (sp - 320) 32 ltac:(lia)) as Hm.
pose proof (Z.div_mod (sp - 320) 32 ltac:(lia)) as Hd.
pose proof (Z.div_mod sp 16 ltac:(lia)) as Hd16.
split; [exact Hal|]. split; [lia|]. split; [lia|]. split.
- replace (sp - 320 - (sp - 320) mod 32) with (((sp - 320) / 32) * 32) by lia. apply Z_mod_mult.
- replace (sp - 320 - (sp - 320) mod 32 - sp) with ((2 * ((sp - 320) / 32) - sp / 16) * 16) by lia. apply Z_mod_mult.
Qed.
Lemma s14_frame : forall cx ly S (W : world SEGS) mem md own k, lt_base B MT cx ->
  ajournal SEGS B STK_LLVMFuzzerTestOneInput (x_sp0 cx) (ltoi_PG longlA) (x_ly cx) (x_S cx) (x_W cx) (x_mem cx)
    (x_md cx) own ly S W mem md k ->
  frames S = own /\ (forall cid pos, frame_addr ly cid pos = frame_addr (x_ly cx) cid pos).
Proof.
intros cx ly S W mem md own k HB HJ.
pose proof HB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hfr0 & _).
pose proof HJ as (_ & Hly & _ & _ & _ & Hfrs & _).
split; [rewrite Hfrs, Hfr0, app_nil_r; reflexivity|].
intros cid pos. unfold frame_addr. pose proof Hly as (_ & _ & _ & _ & _ & EF & _). rewrite EF. reflexivity.
Qed.
Lemma s14_fr_bounds : forall cx ly S (W : world SEGS) mem md k, lt_base B MT cx ->
  ajournal SEGS B STK_LLVMFuzzerTestOneInput (x_sp0 cx) (ltoi_PG longlA) (x_ly cx) (x_S cx) (x_W cx) (x_mem cx)
    (x_md cx) [(LT_FCLS, x_fpos cx)] ly S W mem md k ->
  In (LT_FCLS, x_fpos cx) (frames S) /\ frame_addr ly LT_FCLS (x_fpos cx) = x_fr cx /\
  4096 <= x_fr cx /\ x_fr cx + 512 <= alloc_ceiling /\ x_fr cx mod 32 = 0.
Proof.
intros cx ly S W mem md k HB HJ.
destruct (s14_frame cx ly S W mem md _ k HB HJ) as [Hfs Hfa].
assert (Hin : In (LT_FCLS, x_fpos cx) (frames S)) by (rewrite Hfs; left; reflexivity).
assert (Ea : frame_addr ly LT_FCLS (x_fpos cx) = x_fr cx) by (unfold x_fr; apply Hfa).
destruct (frames_bounds SEGS B LAWS ly S W mem md LT_FCLS (x_fpos cx) (proj1 HJ) Hin) as (H4 & Hc & _).
destruct (al_frames _ _ LAWS ly S W mem md LT_FCLS (x_fpos cx) (proj1 HJ) Hin) as (H32 & _).
rewrite Ea in H4, Hc, H32. change (fs_frame_bytes LT_FCLS) with 512 in Hc.
repeat split; assumption.
Qed.

(* ---- a live block, from the allocator state ---- *)
Lemma s14_hblk_of : forall ly S (W : world SEGS) mem md a n, AR SEGS B ly S W mem md -> In (a, n) (ablocks B ly S) ->
  0 < n -> lt_hblk B ly S (rdW W mem) a n.
Proof.
intros ly S W mem md a n HAR Hin Hn.
destruct (al_blocks _ _ LAWS ly S W mem md a n HAR Hin) as (H16 & H4096 & Hceil & _ & _ & _ & HM).
pose proof (req_size_pos n ltac:(lia)) as [_ Hreq]. pose proof asan_consts as (C1 & _).
split; [exact Hin|]. split; [exact H4096|]. split; [exact H16|].
split; [lia|]. split; [lia|].
split; [exact (amem_range_of_block SEGS B LAWS ly S W mem md a n a n HAR Hin ltac:(lia) ltac:(lia))|].
split; [exact (range_addressable_of_block SEGS B LAWS ly S W mem md a n a n HAR Hin ltac:(lia) ltac:(lia))|].
intros _. exact (shadow_hull_vis_of_block SEGS B LAWS ly S W mem md a n a n HAR Hin ltac:(lia) ltac:(lia) Hn).
Qed.


(* ---- the frame part carried to a state that keeps the entry's frame bytes ---- *)
Lemma s14_frame_kept : forall cx ly S (W : world SEGS) regs mem md k ly2 S2 (W2 : world SEGS) regs2 mem2 md2 k2,
  lt_base B MT cx -> lt_frame B cx ly S W regs mem md k LFO0 ->
  ajournal SEGS B STK_LLVMFuzzerTestOneInput (x_sp0 cx) (ltoi_PG longlA) (x_ly cx) (x_S cx) (x_W cx) (x_mem cx)
    (x_md cx) [(LT_FCLS, x_fpos cx)] ly2 S2 W2 mem2 md2 k2 ->
  (forall r, In r [2; 3; 4; 8; 9]%bv -> getr regs2 r = getr regs r) ->
  (forall a, ((x_s1 cx <= a < x_sp0 cx /\ ~ (x_s1 cx + 152 <= a < x_s1 cx + 160)) \/ x_fr cx <= a < x_fr cx + 512 \/
     x_sh cx <= a < x_sh cx + 36) -> rdW W2 mem2 a = rdW W mem a) ->
  lt_frame B cx ly2 S2 W2 regs2 mem2 md2 k2 LFO0.
Proof.
intros cx ly S W regs mem md k ly2 S2 W2 regs2 mem2 md2 k2 HB
  (HJ & R2 & R3 & R4 & R8 & R9 & HSV & HH0 & HH8 & HH16 & HFL & H176 & HZS) HJ2 HR HK.
pose proof (s14_sp cx HB) as (Hal0 & Hsp0 & Hs1 & _).
assert (HKw : forall a v, (x_s1 cx <= a /\ a + 8 <= x_sp0 cx /\ (a + 8 <= x_s1 cx + 152 \/ x_s1 cx + 160 <= a)) \/
  (x_fr cx <= a /\ a + 8 <= x_fr cx + 512) -> rdword (rdW W mem) a = Some v -> rdword (rdW W2 mem2) a = Some v).
{ intros a v Ha H. rewrite (rdword_ext (rdW W mem) (rdW W2 mem2) a); [exact H|]. intros kk Hkk. apply HK. lia. }
split; [exact HJ2|].
split; [rewrite (HR 2%bv) by (cbn; tauto); exact R2|]. split; [rewrite (HR 3%bv) by (cbn; tauto); exact R3|].
split; [rewrite (HR 4%bv) by (cbn; tauto); exact R4|]. split; [rewrite (HR 8%bv) by (cbn; tauto); exact R8|].
split; [rewrite (HR 9%bv) by (cbn; tauto); exact R9|].
split.
{ intros i r Hi. assert (Hi13 : (i < length LT_SAVED)%nat) by (apply nth_error_Some; congruence).
  change (length LT_SAVED) with 13%nat in Hi13. apply HKw; [|exact (HSV i r Hi)]. left. lia. }
split; [apply HKw; [right; lia | exact HH0]|].
split; [apply HKw; [right; lia | exact HH8]|].
split; [apply HKw; [right; lia | exact HH16]|].
split; [apply HKw; [right; unfold LT_FLAGW; lia | exact HFL]|].
split; [apply HKw; [left; lia | exact H176]|].
intros i Hi. rewrite lt_fsh_len in Hi. rewrite HK by lia. exact (HZS i ltac:(rewrite lt_fsh_len; exact Hi)).
Qed.
Lemma s14_slots_kept : forall cx (rd rd2 : reader) L, lt_slots cx rd L ->
  (forall o v, In (o, v) L -> forall j, 0 <= j < 8 -> rd2 (x_s1 cx + o + j) = rd (x_s1 cx + o + j)) -> lt_slots cx rd2 L.
Proof.
intros cx rd rd2 L H HK o v Hin. rewrite (rdword_ext rd rd2); [exact (H o v Hin)|]. intros j Hj. exact (HK o v Hin j Hj).
Qed.
Lemma s14_cm_kept : forall (rd rd2 : reader) c m st, lt_cm rd c m st ->
  (forall i, 0 <= i < seg_spec.SEG_C_SIZE -> rd2 (c + i) = rd (c + i)) ->
  (forall i, 0 <= i < seg_spec.SEG_M_SIZE -> rd2 (m + i) = rd (m + i)) -> lt_cm rd2 c m st.
Proof.
intros rd rd2 c m st ((bc & Hbc & Hec) & (bm & Hbm & Hem)) Hc Hm. split.
- exists bc. split; [|exact Hec]. pose proof (proj1 Hec) as Hl. intros i Hi. rewrite Hc by lia. exact (Hbc i Hi).
- exists bm. split; [|exact Hem]. pose proof (proj1 Hem) as Hl. intros i Hi. rewrite Hm by lia. exact (Hbm i Hi).
Qed.

(* ---- the facts of every point of the segment ---- *)
(* LT_K85024_stmt's premises but the turn's own registers (s4, s8, s10, s11, a0, ra); with sl the slot 152 the
   turn's `sd s4,152(s1)` (0x850c4) writes *)
Definition s14_pt (f : nat) (cx : lcx) ly S (W : world SEGS) (regs : bvmap 5 word) mem md (k acc c m : Z) (sl : bool)
  : Prop :=
  lt_base B MT cx /\ sa_frm0 /\ Z.of_nat f < x_nf cx /\
  lt_core B MT cx ly S W regs mem md k acc (6 + 2 * (x_nf cx - Z.of_nat f)) LFO0
    [(m, seg_spec.SEG_M_SIZE); (c, seg_spec.SEG_C_SIZE)] /\
  lt_hblk B ly S (rdW W mem) c seg_spec.SEG_C_SIZE /\ lt_hblk B ly S (rdW W mem) m seg_spec.SEG_M_SIZE /\
  getr regs 18 = w64 (Z.of_nat f) /\ getr regs 19 = w64 (-8) /\ getr regs 21 = w64 (x_sh cx) /\
  getr regs 22 = w64 (seg_spec.b2z (seg_spec.seg_ret (x_st cx f))) /\ getr regs 25 = w64 (x_nf cx) /\
  lt_slots cx (rdW W mem)
    (LT_L cx c m ++ (if sl then [(152, Z.of_nat (length (seg_spec.seg_turn_tail (x_pl cx) f)))] else [])) /\
  lt_cm (rdW W mem) c m (x_st cx f) /\
  lt_cnt f (seg_spec.seg_rc (x_st cx f)) (seg_spec.seg_mc (x_st cx f)).

(* the facts carried across a step that keeps the state's blocks and every byte but two windows of the stack: the
   wrappers' scratch below s1 and the slot 152 *)
Lemma s14_pt_keep : forall f cx ly S (W : world SEGS) regs mem md k acc c m sl regs2 mem2 md2 (sl2 : bool),
  s14_pt f cx ly S W regs mem md k acc c m sl ->
  ajournal SEGS B STK_LLVMFuzzerTestOneInput (x_sp0 cx) (ltoi_PG longlA) (x_ly cx) (x_S cx) (x_W cx) (x_mem cx)
    (x_md cx) [(LT_FCLS, x_fpos cx)] ly S W mem2 md2 k ->
  (forall r, In r S14_KEEP -> getr regs2 r = getr regs r) ->
  (forall a, 0 <= a < 2 ^ 64 -> (a < alloc_ceiling \/ x_s1 cx <= a < x_s1 cx + 152 \/ x_s1 cx + 160 <= a) ->
     rdW W mem2 a = rdW W mem a) ->
  (sl2 = true -> rdword (rdW W mem2) (x_s1 cx + 152) = Some (Z.of_nat (length (seg_spec.seg_turn_tail (x_pl cx) f)))) ->
  s14_pt f cx ly S W regs2 mem2 md2 k acc c m sl2.
Proof.
intros f cx ly S W regs mem md k acc c m sl regs2 mem2 md2 sl2 HP HJ2 HR HK H152.
destruct HP as (HB & Hfrm & Hf & (HFR & HIMG & HBL & HBUD) & HC & HM & R18 & R19 & R21 & R22 & R25 & HSL & HCM & HCNT).
pose proof (proj1 HJ2) as HAR2. pose proof (proj1 HFR) as HJ.
pose proof (s14_sp cx HB) as (Hal0 & Hsp0 & Hs1 & _).
pose proof (s14_fr_bounds cx ly S W mem md k HB HJ) as (_ & _ & HF4 & HFc & _).
pose proof asan_consts as (C1 & _).
assert (Hsh : 0x7fff8000 + 512 <= x_sh cx /\ x_sh cx + 64 <= alloc_ceiling).
{ unfold x_sh, shadow_addr, SHADOW_OFF. pose proof (Z.div_le_lower_bound (x_fr cx) 8 512 ltac:(lia) ltac:(lia)).
  pose proof (Z.div_le_upper_bound (x_fr cx) 8 (2 ^ 44) ltac:(lia) ltac:(lia)). lia. }
unfold STK_LLVMFuzzerTestOneInput in Hsp0.
assert (HKa : forall a, (a < alloc_ceiling \/ x_s1 cx <= a < x_s1 cx + 152 \/ x_s1 cx + 160 <= a < 2 ^ 64) -> 0 <= a ->
  rdW W mem2 a = rdW W mem a) by (intros a Ha Ha0; apply HK; lia).
split; [exact HB|]. split; [exact Hfrm|]. split; [exact Hf|].
split.
{ split; [|split; [|split; [exact HBL | exact HBUD]]].
  - apply (s14_frame_kept cx ly S W regs mem md k ly S W regs2 mem2 md2 k HB HFR HJ2).
    + intros r Hr. apply HR. cbn [S14_KEEP In] in *. tauto.
    + intros a Ha. apply HKa.
      * destruct Ha as [[[Ha1 Ha2] Ha3] | [Ha | Ha]].
        -- destruct (Z_lt_le_dec a (x_s1 cx + 152)) as [Hl|Hl]; [right; left; lia|].
           destruct (Z_lt_le_dec a (x_s1 cx + 160)) as [Hl2|Hl2]; [exfalso; apply Ha3; lia|].
           right; right. lia.
        -- left. lia.
        -- left. lia.
      * destruct Ha as [[[Ha1 Ha2] Ha3] | [Ha | Ha]]; lia.
  - apply (s10_lt_img_kept B IMGS BSYM cx W mem2 (rdW W mem) HAR2); [|exact HIMG]. intros a Ha _ _.
    pose proof (pa_img_range _ Ha). apply HKa; unfold kImgEnd in *; lia. }
split; [exact (s14_hblk_of ly S W mem2 md2 c _ HAR2 (proj1 HC) ltac:(unfold seg_spec.SEG_C_SIZE; lia))|].
split; [exact (s14_hblk_of ly S W mem2 md2 m _ HAR2 (proj1 HM) ltac:(unfold seg_spec.SEG_M_SIZE; lia))|].
split; [rewrite (HR 18%bv) by (cbn; tauto); exact R18|]. split; [rewrite (HR 19%bv) by (cbn; tauto); exact R19|].
split; [rewrite (HR 21%bv) by (cbn; tauto); exact R21|]. split; [rewrite (HR 22%bv) by (cbn; tauto); exact R22|].
split; [rewrite (HR 25%bv) by (cbn; tauto); exact R25|].
split.
{ intros o v Hin. apply in_app_or in Hin as [Hin | Hin].
  - rewrite (rdword_ext (rdW W mem) (rdW W mem2)); [exact (HSL o v (in_or_app _ _ _ (or_introl Hin)))|].
    intros j Hj. unfold LT_L in Hin. cbn [In] in Hin.
    repeat (destruct Hin as [Hq|Hin]; [injection Hq as <- _; apply HKa; lia|]). destruct Hin.
  - destruct sl2; [|destruct Hin]. destruct Hin as [Hq|[]]. injection Hq as <- <-. exact (H152 eq_refl). }
split.
{ pose proof (proj1 HC) as Hc. pose proof (proj1 HM) as Hm.
  destruct (al_blocks _ _ LAWS ly S W mem2 md2 _ _ HAR2 Hc) as (_ & Hc4 & Hcc & _).
  destruct (al_blocks _ _ LAWS ly S W mem2 md2 _ _ HAR2 Hm) as (_ & Hm4 & Hmc & _).
  pose proof (req_size_pos seg_spec.SEG_C_SIZE ltac:(unfold seg_spec.SEG_C_SIZE; lia)) as [_ Hrc].
  pose proof (req_size_pos seg_spec.SEG_M_SIZE ltac:(unfold seg_spec.SEG_M_SIZE; lia)) as [_ Hrm].
  apply (s14_cm_kept (rdW W mem) (rdW W mem2) c m _ HCM); intros i Hi; apply HKa; lia. }
exact HCNT.
Qed.

End e.
End f.
End d.
