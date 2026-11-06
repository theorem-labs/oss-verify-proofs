(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the program walk of rec_calls_equal on the ASan build of plugin-hostd/fuzz_command
   (0x89968, 135 instructions), in the shape of cgif_file_fuzzer's walks (lib/A/AChc.v, ACh1.v..ACh8.v): the
   symbolic executor over the position-abstract listing (CmdPaLib.v), the inline checks removed by the shadow tokens
   (PaShadow.v), and the strcmp wrapper's call stepped through by its contract (PaArt.v aj_art_at). The two loops
   are cut at their heads (0x899dc, 0x89a6c) and at the outer latch (0x89ab0); each piece is re-seeded from the
   concrete state there and the loops are proved by induction. Every call is strcmp, which writes only its stack
   window, so the memory below the frame stays the entry's (kept_out) and the read-only bytes strcmp reads
   (rt_rom_view) follow from the statement's arodata_okP. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/rec_calls_equal.v, with its module paths, module names and numbers changed; 532 of its 679 lines of code are new or changed and 1344 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/A/Prog/check_segments_s1.v, with its module paths and module names changed; 388 of its 515 lines of code are new or changed and 552 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, image A (fuzz_segconf.asan): the kit of segment A8a of reac_segconf_parse_file's walk
   (lib/A/Prog/pf_pieces.v S_A8a: SEG 0x887a4 -> NEW 0x8890c / FOUND 0x88964 / CLR 0x880fc, 49 instructions, the
   inlined seg_get search of reac_segconf.c:103-118). Segment A8a's proof, by the G3 walk owner, 2026-10-30.
   This file holds what the walk (lib/A/Prog/pf_a8a.v) reads off the cut predicates, with no instruction walked:
   1. the spine: r_find_go one entry at a time and seg_get's bound branch (the plain lane's pure lemmas
      p4_find_step / p4_find_end / p4_get_full / p4_rconf_ovf of the plain-build walk owner's lib/Prog/pfB_p4_spine.v
      at 16c6d72c0344, copied: that file is not in this tree), c->seg[i].name read through sa_rconf (the
      lemmas cs_bytes_app / cs_bytes_sub / cs_cstr / cs_rname / cs_le4_byte of the listing layer's owner's
      lib/A/Prog/check_segments_s1.v at commit 1119b387b532, copied);
   2. a8c, the facts every point of A8a has (INV_SEG's, less the registers the segment overwrites), and
      a8c_keep: they stay true when the memory changes only below the realigned sp (a callee's scratch window) or
      in the slot s1 + 0xb0 (the store at 0x887ac), and the registers they name are kept. Every object a8c names
      lies below alloc_ceiling (heap, image, shadow, the class-5 frame) or in the slots s1 + 0x20 .. s1 + 0xb8 and
      the save area sp0 - 0x68 .. sp0. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI04 YI09 YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI16 YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaRun PaShadow PaJournal SegSyms SegList SegPa SegPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaDenot PaSB PaLibG PaLibH PaLibF PaCallRun PaCall.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaArt PaFx.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pf_pieces_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require pfA_facts check_segments.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Mem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegAddr SegObj SegGlob.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPgBase SegABase refuse_c
  reac_segconf_parse_file_c SegInstA pf_pieces.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require reac_segconf_parse.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Module PCS := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog.check_segments.CsPure.
Module PMem := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib.Mem.
Module PFA := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog.pfA_facts.
Module RSP := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog.reac_segconf_parse.

(** ** 1. The spine *)
(* seg_get's bound branch (R:110): c->overflow + 1 *)
Definition a8_ovf (rc : rconf) : rconf :=
  RConf (rc_seg rc) (rc_refusal rc) (rc_refused rc) (rc_overflow rc + 1) (rc_reading rc) (rc_gen rc).
Lemma a8_step_full : forall cf nm ln name, r_find_go (rc_seg cf) name 0 = None -> (32 <= length (rc_seg cf))%nat ->
  pf_seg_step cf nm ln name = (refuse (a8_ovf cf) ln F_bound [AS name; AI 32], None, nm).
Proof. intros cf nm ln name H1 H2. unfold pf_seg_step, seg_get. rewrite H1. apply Nat.leb_le in H2. rewrite H2. reflexivity. Qed.
(* the search loop, one entry at a time (pfB_p4_spine.v p4_find_step / p4_find_end) *)
Lemma a8_find_step : forall segs name i k, (i < length segs)%nat ->
  r_find_go (skipn i segs) name k =
  if strcmp (rs_name (nth i segs rseg_d)) name =? 0 then Some k else r_find_go (skipn (S i) segs) name (S k).
Proof.
induction segs as [|g segs IH]; intros name i k H; cbn [length] in H; [lia|].
destruct i as [|i]; [reflexivity|].
cbn [skipn nth]. apply IH. lia.
Qed.
Lemma a8_find_end : forall segs name k, r_find_go (skipn (length segs) segs) name k = None.
Proof. intros segs name k. rewrite skipn_all. reflexivity. Qed.
(* c->overflow + 1 in the encoding (pfB_p4_spine.v p4_rconf_ovf and its helpers) *)
Lemma a8_nth_error_fld : forall (l : list byte) a n i,
  nth_error (seg_spec.fld a n l) i = if (i <? n)%nat then nth_error l (a + i) else None.
Proof.
intros l a n i. unfold seg_spec.fld. rewrite nth_error_firstn. destruct (i <? n)%nat; [|reflexivity].
rewrite nth_error_skipn. f_equal; lia.
Qed.
Lemma a8_upd_nth_error : forall (l ws : list byte) k i, (k + length ws <= length l)%nat ->
  nth_error (PMem.upd_bytes l k ws) i =
    if (k <=? i)%nat && (i <? k + length ws)%nat then nth_error ws (i - k) else nth_error l i.
Proof.
intros l ws k i H. destruct (Nat.lt_ge_cases i (length l)) as [Hi|Hi].
- apply PMem.upd_bytes_nth; assumption.
- rewrite (proj2 (nth_error_None (PMem.upd_bytes l k ws) i)) by (rewrite PMem.upd_bytes_length; lia).
  rewrite (proj2 (nth_error_None l i)) by lia.
  destruct (Nat.leb_spec0 k i), (Nat.ltb_spec0 i (k + length ws)); cbn [andb]; try reflexivity. lia.
Qed.
Lemma a8_fld_upd_out : forall (l ws : list byte) k a n, (k + length ws <= length l)%nat ->
  (a + n <= k \/ k + length ws <= a)%nat -> seg_spec.fld a n (PMem.upd_bytes l k ws) = seg_spec.fld a n l.
Proof.
intros l ws k a n H D. apply nth_error_ext. intros i. rewrite !a8_nth_error_fld.
destruct (Nat.ltb_spec0 i n); [|reflexivity]. rewrite a8_upd_nth_error by exact H.
destruct (Nat.leb_spec0 k (a + i)), (Nat.ltb_spec0 (a + i) (k + length ws)); cbn [andb]; try reflexivity. lia.
Qed.
Lemma a8_fld_upd_same : forall (l ws : list byte) k n, (k + length ws <= length l)%nat -> length ws = n ->
  seg_spec.fld k n (PMem.upd_bytes l k ws) = ws.
Proof.
intros l ws k n H <-. apply nth_error_ext. intros i. rewrite a8_nth_error_fld.
destruct (Nat.ltb_spec0 i (length ws)).
- rewrite a8_upd_nth_error by exact H.
  destruct (Nat.leb_spec0 k (k + i)), (Nat.ltb_spec0 (k + i) (k + length ws)); cbn [andb]; try lia.
  f_equal. lia.
- symmetry. apply nth_error_None. lia.
Qed.
Lemma a8_rconf_ovf : forall rc bs, seg_spec.rconf_enc rc bs -> rc_overflow rc + 1 < 2 ^ 32 ->
  seg_spec.rconf_enc (a8_ovf rc)
    (PMem.upd_bytes bs (Z.to_nat seg_spec.RC_OVERFLOW) (PMem.le4 (Z_to_bv 64 (rc_overflow rc + 1)))).
Proof.
intros rc bs (L & LS & SEGS & N & LR & REF & NR & RF & OV & RD & GEN) Hov.
unfold seg_spec.SEG_C_SIZE in L. unfold a8_ovf, seg_spec.rconf_enc.
cbn [rc_seg rc_refusal rc_refused rc_overflow rc_reading rc_gen].
unfold seg_spec.fldz, seg_spec.RC_N, seg_spec.RC_REFUSAL, seg_spec.RC_NREF, seg_spec.RC_REFUSED,
  seg_spec.RC_OVERFLOW, seg_spec.RC_READING, seg_spec.RC_GEN in *.
assert (Lw : length (PMem.le4 (Z_to_bv 64 (rc_overflow rc + 1))) = 4%nat) by apply PMem.length_le4.
pose proof OV as ((OV0 & _) & _).
assert (O : forall a n, (a + n <= Z.to_nat 13520 \/ Z.to_nat 13524 <= a)%nat ->
          seg_spec.fld a n (PMem.upd_bytes bs (Z.to_nat 13520) (PMem.le4 (Z_to_bv 64 (rc_overflow rc + 1)))) =
          seg_spec.fld a n bs).
{ intros a n D. apply a8_fld_upd_out; lia. }
split; [unfold seg_spec.SEG_C_SIZE; rewrite PMem.upd_bytes_length; lia|].
split; [exact LS|].
split; [intros j Hj; rewrite O by lia; apply SEGS; exact Hj|].
split; [rewrite O by lia; exact N|].
split; [exact LR|].
split; [intros j Hj; rewrite O by lia; apply REF; exact Hj|].
split; [rewrite O by lia; exact NR|].
split; [rewrite O by lia; exact RF|].
split; [rewrite a8_fld_upd_same by lia; split; [lia | reflexivity]|].
split; [rewrite O by lia; exact RD|].
rewrite O by lia; exact GEN.
Qed.

(** ** Bytes of the block through a reader (check_segments_s1.v cs_bytes_app .. cs_rname, cs_le4_byte) *)
Lemma a8_bytes_app : forall (rd : reader) a l1 l2, sa_bytes rd a (l1 ++ l2) ->
  sa_bytes rd a l1 /\ sa_bytes rd (a + Z.of_nat (length l1)) l2.
Proof.
intros rd a l1 l2 H. split.
- intros i Hi. rewrite (H i) by (rewrite length_app; lia). rewrite app_nth1 by exact Hi. reflexivity.
- intros i Hi. replace (a + Z.of_nat (length l1) + Z.of_nat i) with (a + Z.of_nat (length l1 + i)) by lia.
  rewrite (H (length l1 + i)%nat) by (rewrite length_app; lia). rewrite app_nth2 by lia.
  replace (length l1 + i - length l1)%nat with i by lia. reflexivity.
Qed.
Lemma a8_bytes_sub : forall (rd : reader) a bs k l, sa_bytes rd a bs -> (k + l <= length bs)%nat ->
  sa_bytes rd (a + Z.of_nat k) (firstn l (skipn k bs)).
Proof.
intros rd a bs k l H Hl.
rewrite <- (firstn_skipn k bs) in H. apply a8_bytes_app in H as [_ H].
rewrite length_firstn, Nat.min_l in H by lia.
rewrite <- (firstn_skipn l (skipn k bs)) in H. apply a8_bytes_app in H as [H _]. exact H.
Qed.
Lemma a8_cstr : forall (rd : reader) a f cap s, sa_bytes rd a f -> (cap <= length f)%nat ->
  seg_spec.cstr_enc cap s (firstn cap f) ->
  exists sx, sa_bytes rd a (sx ++ [seg_spec.ZERO]) /\ ~ In seg_spec.ZERO sx /\ seg_spec.zs sx = s /\ (length sx < cap)%nat.
Proof.
intros rd a f cap s H Hc (_ & Ls & N & E).
rewrite PCS.firstn_zs, firstn_firstn, Nat.min_l in E by lia.
remember (firstn (S (length s)) f) as g eqn:Hg.
assert (Lg : length g = S (length s)) by (subst g; rewrite length_firstn; lia).
destruct (skipn (length s) g) as [|b [|b' r]] eqn:Sk.
- apply (f_equal (@length byte)) in Sk. rewrite length_skipn in Sk. cbn in Sk. lia.
- assert (Eg : g = firstn (length s) g ++ [b]) by (rewrite <- Sk; symmetry; apply firstn_skipn).
  rewrite Eg in E. unfold seg_spec.zs in E. rewrite map_app in E. cbn [map] in E.
  apply app_inj_tail in E as [E1 E2].
  assert (Eb : b = seg_spec.ZERO) by (apply bv_eq; rewrite E2; reflexivity). subst b.
  exists (firstn (length s) g). split; [|split; [|split]].
  + rewrite <- Eg, Hg. rewrite <- (firstn_skipn (S (length s)) f) in H.
    apply a8_bytes_app in H as [H _]. exact H.
  + apply PCS.zs_nul. unfold seg_spec.zs. rewrite E1. exact N.
  + unfold seg_spec.zs. exact E1.
  + rewrite length_firstn. lia.
- apply (f_equal (@length byte)) in Sk. rewrite length_skipn in Sk. cbn in Sk. lia.
Qed.
Lemma a8_rname : forall (rd : reader) c rcs i, sa_rconf rd c rcs -> (i < length (rc_seg rcs))%nat ->
  exists sx, sa_bytes rd (c + 356 * Z.of_nat i) (sx ++ [seg_spec.ZERO]) /\ ~ In seg_spec.ZERO sx /\
             seg_spec.zs sx = rs_name (nth i (rc_seg rcs) rseg_d) /\ (length sx < 16)%nat.
Proof.
intros rd c rcs i (bs & H & L & L32 & HS & _) Hi.
destruct (HS i Hi) as (Lf & Hn & _).
unfold seg_spec.SEG_C_SIZE in L.
assert (B : sa_bytes rd (c + Z.of_nat (356 * i)) (seg_spec.fld (356 * i) 356 bs))
  by (unfold seg_spec.fld; apply a8_bytes_sub; [exact H | lia]).
replace (c + 356 * Z.of_nat i) with (c + Z.of_nat (356 * i)) by lia.
apply (a8_cstr rd _ _ 16 _ B); [lia | exact Hn].
Qed.
Lemma a8_le4_byte : forall v k, 0 <= v < 2 ^ 32 -> (k < 4)%nat ->
  bv_unsigned (nth k (PMem.le4 (Z_to_bv 64 v)) seg_spec.ZERO) = le_byte v 4 k.
Proof.
intros v k Hv Hk. unfold PMem.le4. rewrite unsigned_lit_small by lia.
unfold le_byte. change (8 * Z.of_nat 4) with 32. rewrite (Z.mod_small v (2 ^ 32)) by lia.
destruct k as [|[|[|[|k]]]]; [| | | | lia]; cbn [Z_to_le_bytes nth Z.of_nat];
rewrite Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 8) with 256;
rewrite ?Z.shiftr_shiftr by lia; rewrite ?Z.mul_0_r, ?Z.shiftr_0_r; try reflexivity; f_equal; f_equal; lia.
Qed.
(* the u32 field at k of a struct read through a reader *)
Lemma a8_u32_at : forall (rd : reader) a bs k v, sa_bytes rd a bs -> 0 <= k -> k + 4 <= Z.of_nat (length bs) ->
  seg_spec.u32_enc v (seg_spec.fldz k 4 bs) -> sa_val rd (a + k) 4 v.
Proof.
intros rd a bs k v H Hk Hl (Hv & E) j Hj.
replace (a + k + Z.of_nat j) with (a + Z.of_nat (Z.to_nat k + j)) by lia.
rewrite (H (Z.to_nat k + j)%nat) by lia. f_equal.
rewrite <- (a8_le4_byte v j Hv Hj). rewrite <- E. unfold seg_spec.fldz, seg_spec.fld.
change (Z.to_nat 4) with 4%nat. rewrite nth_firstn, nth_skipn.
replace (j <? 4)%nat with true by (symmetry; apply Nat.ltb_lt; exact Hj). reflexivity.
Qed.
(* listing offsets of the internal points (BASE + AF_reac_segconf_parse_file = 0x87a78) *)
Definition PF_A8L : Z := AF_reac_segconf_parse_file + 0xd58.    (* 0x887d0, the search loop's head *)
Definition PF_A8F : Z := AF_reac_segconf_parse_file + 0xd78.    (* 0x887f0, no name matched *)
Definition PF_A8RA : Z := AF_reac_segconf_parse_file + 0xd64.   (* 0x887dc, strcmp's return *)
Definition PF_A8RR : Z := AF_reac_segconf_parse_file + 0xdc0.   (* 0x88838, refuse's return *)
(* the shadow base is s6 (register 22, 0x87ae0); the frame's sp = s1 is 32-aligned in [2^46, 2^47] *)
Definition a8_Bx : sv := SOff 22 0.
Definition a8_spF : afact := mkAF (2 ^ 46) (2 ^ 47) 5.
(** ** Small facts of values and readers *)
Lemma a8_val_mem_of_sa : forall segs H mem a n v, sa_val (aview segs H mem) a n v -> val_mem segs (mrestrict H mem) a n v.
Proof.
intros segs H mem a n v Hv k Hk. specialize (Hv k Hk). unfold aview in Hv.
destruct (mbyte segs (mrestrict H mem) (a + Z.of_nat k)) as [b|] eqn:Eb; cbn in Hv; [|discriminate Hv].
injection Hv as Hb. rewrite <- (Z_to_bv_bv_unsigned 8 b). rewrite Hb. reflexivity.
Qed.
Lemma a8_sl_get : forall (rd : reader) b L off v, pf_sl rd b L -> In (off, v) L -> rdword rd (b + off) = Some v.
Proof. intros rd b L off v H Hin. unfold pf_sl in H. rewrite Forall_forall in H. exact (H _ Hin). Qed.
(* a reader's C string as the byte list the string wrappers take *)
Lemma a8_astr : forall segs (W : world segs) mem p s, sa_str (aview segs (w_H W) mem) p s ->
  astr_at segs W mem p (seg_spec.zb s) /\ seg_spec.zs (seg_spec.zb s) = s /\ ~ In (Z_to_bv 8 0) (seg_spec.zb s) /\
  length (seg_spec.zb s) = length s.
Proof.
intros segs W mem p s ((Hz & Hn) & _).
assert (Hb : Forall (fun x => 0 <= x < 256) s).
{ apply Forall_forall. intros x Hx. apply In_nth with (d := 0) in Hx as (i & Hi & <-).
  specialize (Hz i ltac:(rewrite length_app; cbn [length]; lia)). rewrite app_nth1 in Hz by exact Hi.
  destruct (aview_byte segs _ _ _ _ Hz) as (b & _ & -> & Hr). lia. }
assert (Hzs : seg_spec.zs (seg_spec.zb s) = s) by exact (sa_zs_zb s Hb).
assert (Hl : length (seg_spec.zb s) = length s) by (unfold seg_spec.zb; apply length_map).
assert (Hnz : ~ In (Z_to_bv 8 0) (seg_spec.zb s)).
{ intros Hin. apply Hn. rewrite <- Hzs. exact (in_map (@bv_unsigned 8) _ _ Hin). }
split; [|split; [exact Hzs | split; [exact Hnz | exact Hl]]].
split; [|exact Hnz].
intros i Hi. rewrite length_app, Hl in Hi. cbn [length] in Hi.
specialize (Hz i ltac:(rewrite length_app; cbn [length]; lia)). rewrite Hz. f_equal.
destruct (Nat.lt_ge_cases i (length s)) as [Hlt | Hge].
- rewrite !app_nth1 by lia. rewrite <- Hzs at 1. unfold seg_spec.zs.
  rewrite (nth_indep (map (@bv_unsigned 8) (seg_spec.zb s)) 0 (bv_unsigned (Z_to_bv 8 0)))
    by (rewrite length_map; lia).
  rewrite (map_nth (@bv_unsigned 8) (seg_spec.zb s) (Z_to_bv 8 0) i). reflexivity.
- rewrite !app_nth2 by lia. rewrite Hl. replace (i - length s)%nat with 0%nat by lia. reflexivity.
Qed.
Lemma a8_srl3 : forall E n z x, bv_unsigned (ew E n) + z = x -> 0 <= x < 2 ^ 64 ->
  sv_denot E (SAlu ALU_SRL (SOff n z) (SLit 3)) = Z_to_bv 64 (x / 8).
Proof.
intros E n z x Hx Hr. change (Z_to_bv 64 (x / 8)) with (sv_denot E (SLit (x / 8))). apply U_inj.
rewrite U_SAlu, U_SOff, !U_SLit, Hx. rewrite (zcanon_small x) by (unfold M64; lia).
change (zcanon 3) with 3. cbn [zalu_raw]. change (Z.land 3 63) with 3.
rewrite Z.shiftr_div_pow2 by lia. reflexivity.
Qed.
Lemma a8_soff : forall E n z x, bv_unsigned (ew E n) = x -> sv_denot E (SOff n z) = Z_to_bv 64 (x + z).
Proof. intros E n z x Hx. cbn [sv_denot]. rewrite Hx. reflexivity. Qed.
(* check_segments_s1.v cs_swrap_small / cs_bge0 *)
Lemma a8_swrap_small : forall z, 0 <= z < 2 ^ 63 -> bv_swrap 64 z = z.
Proof.
intros z Hz. unfold bv_swrap, bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64). change (2 ^ 64 / 2) with (2 ^ 63).
rewrite bv_wrap_small; [lia|]. change (bv_modulus 64) with (2 ^ 64). lia.
Qed.
Lemma a8_bge0 : forall E n v, ew E n = w64 v -> 0 <= v < 2 ^ 63 ->
  branch_taken BC_GE (sv_denot E (SLit 0)) (sv_denot E (SOff n 0)) = (v <=? 0).
Proof.
intros E n v Hn Hv. cbn [branch_taken sv_denot]. rewrite Hn, Z.add_0_r. unfold w64. rewrite unsigned_lit_small by lia.
unfold bv_lts. rewrite !signed_lit. rewrite !zcanon_small by lia. rewrite !a8_swrap_small by lia.
destruct (Z.ltb_spec 0 v); destruct (Z.leb_spec v 0); try reflexivity; lia.
Qed.
(* the value 0x887a8 adds: sh(&c->n) *)
Lemma a8_shaddr_den : forall E nc ns c, bv_unsigned (ew E nc) = c -> bv_unsigned (ew E ns) = SB ->
  0 <= c /\ c + seg_spec.RC_N < 2 ^ 47 ->
  sv_denot E (SAlu ALU_ADD (SAlu ALU_SRL (SOff nc 11392) (SLit 3)) (SOff ns 0)) =
  Z_to_bv 64 (shadow_addr (c + seg_spec.RC_N)).
Proof.
intros E nc ns c Hc Hs Hr. unfold seg_spec.RC_N in *.
change (Z_to_bv 64 (shadow_addr (c + 11392))) with (sv_denot E (SLit (shadow_addr (c + 11392)))). apply U_inj.
rewrite !U_SAlu, !U_SOff, !U_SLit, Hc, Hs. rewrite Z.add_0_r.
rewrite (zcanon_small (c + 11392)) by (unfold M64; lia). change (zcanon 3) with 3.
cbn [zalu_raw]. change (Z.land 3 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
assert (D : 0 <= (c + 11392) / 8 <= c + 11392)
  by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
rewrite (zcanon_small ((c + 11392) / 8)) by (unfold M64; lia).
rewrite (zcanon_small SB) by (unfold SB, M64; lia).
unfold shadow_addr, SHADOW_OFF, SB. f_equal. lia.
Qed.

(** ** 2. The facts every point of A8a has, and their keep *)
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
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
Lemma a8_u_reg : forall (rX : bvmap 5 word) extra n v, (n < 32)%nat -> getr rX (Z_to_bv 5 (Z.of_nat n)) = w64 v ->
  0 <= v < 2 ^ 64 -> bv_unsigned (ew (Eimg (Ereg rX extra)) n) = v.
Proof.
intros rX extra n v Hn Hr Hv. rewrite (ew_Eimg_Ereg_nat rX extra n (Z_to_bv 5 (Z.of_nat n))).
- rewrite Hr. unfold w64. apply unsigned_lit_small. lia.
- rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32. rewrite Z.mod_small; lia.
Qed.

(* INV_SEG less the registers A8a overwrites (s3, s4, s7, s8 and the argument registers): what NEW, FOUND and,
   through refuse, CLR share with SEG *)
Definition a8c (n : nat) (v : pfv) (pos : Z) (lyc : alayout) (Sc : astate) (Wc : world SEGS) (rX : bvmap 5 word)
  (memc : word -> option byte) (mdc : Model) (cf : rconf) (nm : list Z) (o : nat) (ln : Z) (d : list (list Z))
  (np : Z) (name : list Z) : Prop :=
  pf_base B v pos lyc Sc Wc rX memc mdc PF_SC_LINE /\ pf_mid v o ln d n /\
  pf_st0 v pos (rdW Wc memc) cf nm (length (skipn o (p_s v))) /\
  sa_str (rdW Wc memc) np name /\ pf_inb (pf_F v pos + PF_O_BUF) np name /\ (1 <= length name <= 15)%nat /\
  pf_rg rX ([(18, 0x23); (27, pf_SH v pos); (25, np)] ++ PF_RM v o ln).
(* the registers a8c and pf_fi name *)
Definition A8_REGS : list Z := [2; 3; 4; 8; 9; 22; 18; 27; 25; 21; 26].

Lemma a8_of_seg : forall n v pos lyc Sc Wc rX memc mdc cf nm o ln d np name,
  INV_SEG B n v pos lyc Sc Wc rX memc mdc cf nm o ln d np name ->
  a8c n v pos lyc Sc Wc rX memc mdc cf nm o ln d np name.
Proof.
intros n v pos lyc Sc Wc rX memc mdc cf nm o ln d np name (HB & HM & HST & HS & HI & HL & HR).
split; [exact HB|]. split; [exact HM|]. split; [exact HST|]. split; [exact HS|]. split; [exact HI|].
split; [exact HL|].
unfold PF_RL, PF_RM in HR. unfold PF_RM. cbn [app] in HR |- *. unfold pf_rg in HR |- *.
repeat match goal with H : Forall _ (_ :: _) |- _ => apply Forall_cons_iff in H as [? ?] end.
repeat constructor; assumption.
Qed.

(* the stack: sp0 the entry sp, s1 the realigned locals base *)
Lemma a8_sp : forall v, pf_cx B v ->
  pf_sp0 v mod 16 = 0 /\ alloc_ceiling + 12800 <= pf_sp0 v /\ pf_sp0 v <= 2 ^ 47 /\
  pf_s1 v mod 32 = 0 /\ pf_sp0 v - 0x150 <= pf_s1 v <= pf_sp0 v - 0x140.
Proof.
intros v (HPRE & _).
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof STK_values as (_ & _ & _ & SPF & _).
rewrite SPF in Hslo. fold (pf_sp0 v) in *. unfold pf_s1.
pose proof (Z.mod_pos_bound (pf_sp0 v - 0x140) 32 ltac:(lia)) as M.
assert (M2 : (pf_sp0 v - 0x140) mod 32 = 0 \/ (pf_sp0 v - 0x140) mod 32 = 16).
{ pose proof (Z.div_mod (pf_sp0 v) 16 ltac:(lia)) as D. rewrite Hal16, Z.add_0_r in D.
  rewrite D. replace (16 * (pf_sp0 v / 16) - 0x140) with (16 * (pf_sp0 v / 16 - 20)) by lia.
  destruct (Z.even (pf_sp0 v / 16 - 20)) eqn:E.
  - apply Z.even_spec in E as (k & Ek). rewrite Ek. left.
    replace (16 * (2 * k)) with (k * 32) by lia. apply Z_mod_mult.
  - assert (Eo : Z.odd (pf_sp0 v / 16 - 20) = true) by (rewrite <- Z.negb_even, E; reflexivity).
    apply Z.odd_spec in Eo as (k & Ek). rewrite Ek. right.
    replace (16 * (2 * k + 1)) with (16 + k * 32) by lia. rewrite Z_mod_plus_full. reflexivity. }
split; [exact Hal16|]. split; [lia|]. split; [lia|].
split; [|lia]. rewrite Zminus_mod, Z.mod_mod, Z.sub_diag by lia. reflexivity.
Qed.

(* the class-5 frame: 32-aligned, in the application band, below alloc_ceiling, apart from every live block *)
Lemma a8_frame : forall v pos lyc Sc (Wc : world SEGS) memc mdc,
  AR SEGS B lyc Sc Wc memc mdc -> In (5, pos) (frames Sc) -> lyc = p_ly v ->
  pf_F v pos mod 32 = 0 /\ 4096 <= pf_F v pos /\ pf_F v pos + 2048 <= alloc_ceiling /\ in_app (pf_F v pos) 2048 /\
  (forall b m, In (b, m) (ablocks B lyc Sc) -> pf_F v pos + 2048 <= b \/ b + req_size m <= pf_F v pos).
Proof.
intros v pos lyc Sc Wc memc mdc HAR Hin Hly. unfold pf_F. rewrite <- Hly.
destruct (al_frames _ _ LAWS lyc Sc Wc memc mdc 5 pos HAR Hin) as (H32 & Happ & _).
destruct (al_sep _ _ LAWS lyc Sc Wc memc mdc HAR) as [Hdisj Hf].
pose proof (proj1 (Forall_forall _ _) Hf (5, pos) Hin) as [H1 H2]. cbn [fst snd] in H1, H2.
change (fs_frame_bytes 5) with 2048 in *.
split; [exact H32|]. split; [exact H1|]. split; [exact H2|]. split; [exact Happ|].
intros b m Hb.
assert (Ib : In (b, req_size m) (map (fun b0 => (fst b0, req_size (snd b0))) (ablocks B lyc Sc)))
  by (apply in_map_iff; exists (b, m); auto).
assert (If : In (frame_addr lyc 5 pos, 2048)
  (map (fun f => (frame_addr lyc (fst f) (snd f), fs_frame_bytes (fst f))) (frames Sc)))
  by (apply in_map_iff; exists (5, pos); auto).
pose proof (YG0s.pairwise_In zdisjoint _ _ _ _ _ eq_refl Hdisj Ib If) as Hz.
unfold zdisjoint in Hz. cbn [fst snd] in Hz. lia.
Qed.

(* a live heap range: below alloc_ceiling, inside one live block *)
Lemma a8_heap : forall lyc Sc (Wc : world SEGS) memc mdc q n,
  AR SEGS B lyc Sc Wc memc mdc -> sa_heap B lyc Sc q n -> 0 < n ->
  4096 <= q /\ q + n <= alloc_ceiling /\
  exists b m, In (b, m) (ablocks B lyc Sc) /\ b <= q /\ q + n <= b + req_size m /\ b + req_size m <= alloc_ceiling.
Proof.
intros lyc Sc Wc memc mdc q n HAR (b & m & Hin & Hb & Hm) Hn.
destruct (al_blocks _ _ LAWS lyc Sc Wc memc mdc b m HAR Hin) as (Hp16 & Hp4096 & Hpceil & Hpapp & Hppres & _ & Hkr).
pose proof (req_size_pos m ltac:(lia)) as [_ Hreq].
split; [lia|]. split; [lia|]. exists b, m. split; [exact Hin|]. lia.
Qed.

(* ---- reader facts carried to a reader that agrees below alloc_ceiling ---- *)
Lemma a8_low_of_kept : forall (rd rd' : reader) lo hi, kept_out rd rd' lo hi -> alloc_ceiling <= lo ->
  forall a, 0 <= a < alloc_ceiling -> rd' a = rd a.
Proof. intros rd rd' lo hi K Hlo a Ha. pose proof asan_consts as (C1 & _). apply K; lia. Qed.
Lemma a8_sa_addr_low : forall (rd rd' : reader) q n, sa_addr rd q n -> q + n <= 2 ^ 47 ->
  (forall a, 0 <= a < alloc_ceiling -> rd' a = rd a) -> sa_addr rd' q n.
Proof.
intros rd rd' q n (H0 & H1 & H2 & H3 & H4) Hq K. pose proof asan_consts as (C1 & C2 & _).
assert (K' : forall s, 0 <= s < 2 ^ 64 -> ~ (alloc_ceiling <= s < 2 ^ 64) -> rd' s = rd s) by (intros s Hs Hn; apply K; lia).
split; [exact H0|]. split; [exact H1|]. split; [exact H2|].
split; [exact (range_addressable_kept_win rd rd' alloc_ceiling (2 ^ 64) q n K' ltac:(lia) H0 Hq H3)|].
intros Hn. exact (shadow_hull_vis_kept_win rd rd' alloc_ceiling (2 ^ 64) q n K' ltac:(lia) H0 Hq Hn (H4 Hn)).
Qed.
Lemma a8_bytes_low : forall (rd rd' : reader) a bs, sa_bytes rd a bs -> 0 <= a ->
  a + Z.of_nat (length bs) <= alloc_ceiling -> (forall x, 0 <= x < alloc_ceiling -> rd' x = rd x) -> sa_bytes rd' a bs.
Proof. intros rd rd' a bs H Ha Hl K i Hi. rewrite K by lia. exact (H i Hi). Qed.
Lemma a8_fsh_low : forall (rd rd' : reader) sh sc, pf_fsh rd sh sc -> 0 <= sh -> sh + 144 <= alloc_ceiling ->
  (forall x, 0 <= x < alloc_ceiling -> rd' x = rd x) -> pf_fsh rd' sh sc.
Proof. intros rd rd' sh sc H H0 H1 K i Hi. rewrite K by lia. exact (H i Hi). Qed.
Lemma a8_sl_kept : forall (rd rd' : reader) lo hi b L, pf_sl rd b L -> kept_out rd rd' lo hi ->
  (forall ov, In ov L -> 0 <= b + fst ov /\ b + fst ov + 8 < 2 ^ 64 /\ (b + fst ov + 8 <= lo \/ hi <= b + fst ov)) ->
  pf_sl rd' b L.
Proof.
intros rd rd' lo hi b L H K HL. unfold pf_sl in *. rewrite Forall_forall in H |- *. intros ov Hov.
destruct (HL ov Hov) as (H0 & H1 & H2). rewrite (rdword_ext rd rd'); [exact (H ov Hov)|].
intros k Hk. apply K; lia.
Qed.
Lemma a8_rg_keep : forall (rX rX' : bvmap 5 word) L, pf_rg rX L ->
  (forall rv, In rv L -> getr rX' (Z_to_bv 5 (fst rv)) = getr rX (Z_to_bv 5 (fst rv))) -> pf_rg rX' L.
Proof.
intros rX rX' L H HE. unfold pf_rg in *. rewrite Forall_forall in H |- *. intros rv Hrv.
rewrite (HE rv Hrv). exact (H rv Hrv).
Qed.
Lemma a8_sl_offs : forall v pos ov, In ov (PF_SL v pos) -> 0x20 <= fst ov <= 0xb8 /\ fst ov <> 0xb0 /\ fst ov mod 8 = 0.
Proof.
intros v pos ov H. unfold PF_SL in H. cbn [In] in H.
repeat (destruct H as [<- | H]; [cbn [fst]; split; [lia | split; [lia | reflexivity]]|]). destruct H.
Qed.
Lemma a8_saved_off : forall j r, nth_error PF_SAVED j = Some r -> (j < 13)%nat.
Proof. intros j r H. change 13%nat with (length PF_SAVED). apply nth_error_Some. rewrite H. discriminate. Qed.
(* every read-only byte lies in the image's low band: a segment byte (pa_img_range) or the RELRO window
   RLO_A .. RHI_A (0xa14a0 .. 0xa3748) itself *)
Lemma a8_roP_low : forall a, in_roP SEGS RLO_A RHI_A a -> 0 <= a < kImgEnd.
Proof.
intros a [(sg & Hsg & _ & Hr) | Hr].
- pose proof (pa_img_range a ltac:(exists sg; split; [exact Hsg | exact Hr])). lia.
- unfold RLO_A, RHI_A, SEG_RLO, SEG_RHI, kImgEnd in *. lia.
Qed.
Lemma a8_rod_low : forall (rd rd' : reader), arodata_okP SEGS RLO_A RHI_A B rd ->
  (forall x, 0 <= x < alloc_ceiling -> rd' x = rd x) -> arodata_okP SEGS RLO_A RHI_A B rd'.
Proof.
intros rd rd' H K a Hro Ho He. pose proof (a8_roP_low a Hro) as Hrg. unfold kImgEnd in Hrg.
pose proof asan_consts as (C1 & _). rewrite K by lia. exact (H a Hro Ho He).
Qed.

(* a8c is kept when the memory changes only in a window [lo, hi) at or above alloc_ceiling that misses the slots
   s1 + 0x20 .. s1 + 0xb8 but s1 + 0xb0 (a callee's scratch window below s1, or the store at 0x887ac), the
   journal goes on with the same layout and state, and the registers a8c names are kept *)
Lemma a8c_keep : forall n v pos lyc Sc Wc rX memc mdc cf nm o ln d np name rX' memc' mdc' lo hi,
  a8c n v pos lyc Sc Wc rX memc mdc cf nm o ln d np name ->
  ajournal SEGS B STK_reac_segconf_parse_file (pf_sp0 v) (seg_spec.RC_PARSE_W (p_c v)) (p_ly v) (p_S v) (p_W v)
    (p_mem v) (p_md v) [(5, pos)] lyc Sc Wc memc' mdc' 0 ->
  kept_out (rdW Wc memc) (rdW Wc memc') lo hi -> alloc_ceiling <= lo ->
  (hi <= pf_s1 v + 0x20 \/ (pf_s1 v + 0xb0 <= lo /\ hi <= pf_s1 v + 0xb8)) ->
  (forall r, In r A8_REGS -> getr rX' (Z_to_bv 5 r) = getr rX (Z_to_bv 5 r)) ->
  a8c n v pos lyc Sc Wc rX' memc' mdc' cf nm o ln d np name.
Proof.
intros n v pos lyc Sc Wc rX memc mdc cf nm o ln d np name rX' memc' mdc' lo hi
  (HB & HM & HST & HS & HI & HL & HR) HJ' HK Hlo Hwin HRG.
destruct HB as (HCX & HFI & HOB & HSL & HFSH).
destruct HFI as (HJ & Hly & HSc & HPm & HSV & HFL & HFRM & HRF).
destruct HOB as (OT & OTA & OTH & OCA & OCH & OCAT & OLIT & OROD & OSSP).
destruct HST as (SRC & SNM & SCNT).
pose proof (proj1 HJ') as HAR'.
pose proof HJ' as (_ & _ & _ & _ & _ & Hfr & _).
assert (Hin5 : In (5, pos) (frames Sc)) by (rewrite Hfr; left; reflexivity).
pose proof (a8_sp v HCX) as (S1 & S2 & S3 & S4 & S5).
destruct (a8_frame v pos lyc Sc Wc memc' mdc' HAR' Hin5 Hly) as (F1 & F2 & F3 & F4 & F5).
destruct (a8_heap lyc Sc Wc memc' mdc' _ _ HAR' OTH ltac:(unfold pf_len; lia)) as (T1 & T2 & _).
destruct (a8_heap lyc Sc Wc memc' mdc' _ _ HAR' OCH ltac:(unfold seg_spec.SEG_C_SIZE; lia)) as (C1 & C2 & _).
pose proof asan_consts as (A1 & A2 & A3 & A4 & A5).
pose proof (a8_low_of_kept _ _ lo hi HK Hlo) as K.
unfold pf_len, seg_spec.SEG_C_SIZE in *.
assert (Hfl : forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> rdW Wc memc' a = rdW Wc memc a) by exact HK.
destruct HI as [HI1 HI2]. unfold PF_O_BUF in HI1, HI2.
split.
{ split; [exact HCX|]. split.
  { split; [exact HJ'|]. split; [exact Hly|]. split; [exact HSc|]. split; [exact HPm|].
    split.
    { intros j r Hj. pose proof (a8_saved_off j r Hj) as Hj13.
      rewrite (rdword_ext (rdW Wc memc) (rdW Wc memc')); [exact (HSV j r Hj)|].
      intros k Hk. apply HK; lia. }
    split.
    { change (fs_frame_bytes 5) with 2048 in *.
      rewrite (RSP.rdword_low (rdW Wc memc) (rdW Wc memc')); [exact HFL | lia | lia | exact K]. }
    split; [exact HFRM|].
    apply (a8_rg_keep rX); [exact HRF|]. intros rv Hrv. apply HRG.
    cbn [In] in Hrv. unfold A8_REGS. repeat (destruct Hrv as [<- | Hrv]; [cbn; tauto|]). destruct Hrv. }
  split.
  { split; [apply (RSP.sa_str_low (rdW Wc memc)); [exact OT | lia | lia | exact K]|].
    split; [apply (a8_sa_addr_low (rdW Wc memc)); [exact OTA | unfold pf_len; lia | exact K]|].
    split; [exact OTH|].
    split; [apply (a8_sa_addr_low (rdW Wc memc)); [exact OCA | unfold seg_spec.SEG_C_SIZE; lia | exact K]|].
    split; [exact OCH|].
    split; [apply (RSP.sa_cat_low B (rdW Wc memc)); [exact OCAT | exact K]|].
    split; [intros x Hx; apply (RSP.sa_lit_low B (rdW Wc memc)); [exact (OLIT x Hx) | exact K]|].
    split; [exact (a8_rod_low (rdW Wc memc) _ OROD K)|].
    exact (RSP.sa_ssp_low (rdW Wc memc) _ OSSP K). }
  split.
  { apply (a8_sl_kept (rdW Wc memc) _ lo hi _ _ HSL HK). intros ov Hov.
    pose proof (a8_sl_offs v pos ov Hov). lia. }
  apply (a8_fsh_low (rdW Wc memc)); [exact HFSH | | | exact K]; unfold pf_SH, shadow_addr, SHADOW_OFF;
    pose proof (Z.div_le_mono (pf_F v pos + 2048) alloc_ceiling 8 ltac:(lia) F3); lia. }
split; [exact HM|].
split.
{ split; [apply (RSP.sa_rconf_low (rdW Wc memc)); [exact SRC | lia | unfold seg_spec.SEG_C_SIZE; lia | exact K]|].
  split; [|exact SCNT].
  destruct SNM as (f & Hf & Hfe). exists f. split; [|exact Hfe].
  destruct Hfe as (Lf & _). unfold PF_O_CN.
  apply (a8_bytes_low (rdW Wc memc)); [exact Hf | lia | rewrite Lf; lia | exact K]. }
split; [apply (RSP.sa_str_low (rdW Wc memc)); [exact HS | lia | lia | exact K]|].
split; [unfold pf_inb, PF_O_BUF; split; lia|].
split; [exact HL|].
apply (a8_rg_keep rX); [exact HR|]. intros rv Hrv. apply HRG.
unfold PF_RM in Hrv. cbn [In app] in Hrv. unfold A8_REGS. repeat (destruct Hrv as [<- | Hrv]; [cbn; tauto|]). destruct Hrv.
Qed.

(** ** The internal cut points and the exits *)
(* the loop head 0x887d0 after j entries (pf_p4.v w_loop): s4 = &seg[j], s7 = &seg[j].seen_gen, s8 = n - j entries
   left, s3 = n; the names before j differ from name; slot 0xb0 holds sh(&c->n) (0x887ac, read by NEW) *)
Definition a8L (n : nat) (v : pfv) (pos : Z) (lyc : alayout) (Sc : astate) (Wc : world SEGS) (rX : bvmap 5 word)
  (memc : word -> option byte) (mdc : Model) (cf : rconf) (nm : list Z) (o : nat) (ln : Z) (d : list (list Z))
  (np : Z) (name : list Z) (j : nat) : Prop :=
  a8c n v pos lyc Sc Wc rX memc mdc cf nm o ln d np name /\
  pf_sl (rdW Wc memc) (pf_s1 v) [(0xb0, shadow_addr (p_c v + seg_spec.RC_N))] /\
  (j < length (rc_seg cf))%nat /\
  r_find_go (rc_seg cf) name 0 = r_find_go (skipn j (rc_seg cf)) name j /\
  pf_rg rX [(19, Z.of_nat (length (rc_seg cf))); (20, seg_spec.rseg_addr (p_c v) j);
            (23, seg_spec.rseg_addr (p_c v) j + seg_spec.RS_SEEN_GEN); (24, Z.of_nat (length (rc_seg cf) - j))].
(* 0x887f0: no entry has the name, s3 = n >= 1 *)
Definition a8F (n : nat) (v : pfv) (pos : Z) (lyc : alayout) (Sc : astate) (Wc : world SEGS) (rX : bvmap 5 word)
  (memc : word -> option byte) (mdc : Model) (cf : rconf) (nm : list Z) (o : nat) (ln : Z) (d : list (list Z))
  (np : Z) (name : list Z) : Prop :=
  a8c n v pos lyc Sc Wc rX memc mdc cf nm o ln d np name /\
  pf_sl (rdW Wc memc) (pf_s1 v) [(0xb0, shadow_addr (p_c v + seg_spec.RC_N))] /\
  r_find_go (rc_seg cf) name 0 = None /\ (1 <= length (rc_seg cf))%nat /\
  pf_rg rX [(19, Z.of_nat (length (rc_seg cf)))].
(* the post of every point of A8a: the header step from seg_get on *)
Definition a8Q (v : pfv) (cf : rconf) (nm : list Z) (o : nat) (ln : Z) (name : list Z) : world SEGS -> config -> Prop :=
  pf_postm B v (pf_seg_step cf nm (ln + 1) name) o ln.

Lemma a8_new_ok : forall n v pos lyc Sc Wc rX memc mdc cf nm o ln d np name,
  a8c n v pos lyc Sc Wc rX memc mdc cf nm o ln d np name ->
  pf_sl (rdW Wc memc) (pf_s1 v) [(0xb0, shadow_addr (p_c v + seg_spec.RC_N))] ->
  r_find_go (rc_seg cf) name 0 = None -> (length (rc_seg cf) < 32)%nat ->
  getr rX (Z_to_bv 5 19) = w64 (Z.of_nat (length (rc_seg cf))) ->
  INV_NEW B n v pos lyc Sc Wc rX memc mdc cf nm o ln d np name.
Proof.
intros n v pos lyc Sc Wc rX memc mdc cf nm o ln d np name (HB & HM & HST & HS & HI & HL & HR) HSL HF HN R19.
split; [exact HB|]. split; [exact HM|]. split; [exact HST|]. split; [exact HS|]. split; [exact HI|].
split; [exact HL|]. split; [exact HF|]. split; [exact HN|]. split; [exact HSL|].
unfold PF_RM in HR |- *. cbn [app] in HR |- *. unfold pf_rg in HR |- *.
repeat match goal with H : Forall _ (_ :: _) |- _ => apply Forall_cons_iff in H as [? ?] end.
repeat constructor; assumption.
Qed.
Lemma a8_found_ok : forall n v pos lyc Sc Wc rX memc mdc cf nm o ln d np name i,
  a8c n v pos lyc Sc Wc rX memc mdc cf nm o ln d np name ->
  r_find_go (rc_seg cf) name 0 = Some i ->
  getr rX (Z_to_bv 5 20) = w64 (seg_spec.rseg_addr (p_c v) i) ->
  getr rX (Z_to_bv 5 23) = w64 (seg_spec.rseg_addr (p_c v) i + seg_spec.RS_SEEN_GEN) ->
  INV_FOUND B n v pos lyc Sc Wc rX memc mdc cf nm o ln d np name i.
Proof.
intros n v pos lyc Sc Wc rX memc mdc cf nm o ln d np name i (HB & HM & HST & HS & HI & HL & HR) HF R20 R23.
split; [exact HB|]. split; [exact HM|]. split; [exact HST|]. split; [exact HS|]. split; [exact HI|].
split; [exact HL|]. split; [exact HF|].
unfold PF_RM in HR |- *. cbn [app] in HR |- *. unfold pf_rg in HR |- *.
repeat match goal with H : Forall _ (_ :: _) |- _ => apply Forall_cons_iff in H as [? ?] end.
repeat constructor; assumption.
Qed.
End e.
End f.
End d.
