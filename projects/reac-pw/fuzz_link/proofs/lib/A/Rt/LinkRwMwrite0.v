(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/libreac/fuzz_grant/lib/A/Rt/StrcmpLoop.v (commit 97c611eec86, file sha256 df262e182c54; donor not released), with its module paths changed, GrantSyms renamed PcapSyms and its addresses moved to libreac/fuzz_pcap's v1.9.0 ASan build. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/A/Rt/StrcmpLoop.v, with its module paths and module names changed; 1747 of its 1785 lines of code are new or changed and 189 lines of the source are left out. *)
(* reac-pw/fuzz_link, image A (the asan build, pin 059dae63e07c): the walk of musl mwrite 0x96cc0 at k = 0
   pending bytes, i.e. LinkRwDefs.v's amwrite_mf_k0_realizes = amwrite_mf_at (48 + ESTACK) 0 LA_MWRITE.

   The body, from the neutral listing (internal path)
   (internal record, sha256 0f1962ed05d4) (69 instructions, frame 48). With k = 0 the write window is empty
   (wpos = wbase, whichever of amf_win's two shapes holds), so the self-call at +0x4c is not reached:
     +0x00..+0x18  push 48, save ra / s0 / s1 / s2 / s3 / s4; s0 = n, s2 = f, s1 = x
     +0x24 / +0x28 a0 = f->wpos, a2 = f->wbase; +0x2c s4 = f->cookie (= f + 232)
     +0x34 beq a0, a2    TAKEN (k = 0, so the two words hold the same value)   -> +0x5c
     +0x5c / +0x64 lw c->mode; bne 'a'   TAKEN (link's mode is 'w' = 119)      -> +0x74
     +0x74..+0x80 s3 = c->size - c->pos; bgeu s3, n: the one open branch of the entry phase
       TAKEN  (n <= size - pos): the fitting arm, n2 = n
       NOT    (n > size - pos):  +0x84 jal ___errno_location 0x90a7c (mv a0,tp; addi a0,a0,-0xa4; ret, so
              a0 = as_tp B - 164 = as_errno B by PcapSyms), errno = ENOSPC (28), flags |= F_ERR,
              wend = wpos = wbase = 0, n2 = size - pos
     +0xb0..+0xc0 jal 0x52d74 = pc_wrap_memcpy (as_code B): the memory-checking runtime's memcpy interceptor,
              whose behaviour is the hypothesis AMEMCPY (the AsanAPI field aa_memcpy_icpt)
     +0xc4..+0xd0 c->pos += n2; +0xd4..+0xdc c->len = max c->len c->pos; +0xe0..+0xec a NUL at
              c->buf + c->pos when c->pos < c->size; +0xf0..+0x110 a0 = n2, restore, ret.
   Five leaves: the fitting arm splits on len >= pos + n2 and then on pos + n2 >= size (only the last one
   stores the NUL, through a fresh atom 56 for its address c->buf + pos + n and a one-byte region); the
   ENOSPC arm has pos + n2 = size, which the engine computes, so its second branch is decided and only
   len >= size stays open.

   The kept-bytes clause comes from the engine's frame_of: every store of the run resolves into one of the
   state's windows (the 48-byte frame, the FILE's first 248 bytes, errno, and in the NUL leaf the NUL's one
   byte), and the interceptor's own clause covers the copy's destination. Those windows are inside the
   contract's excepted ranges (the walk's window, the FILE's first 272 bytes, g_said and errno). This agrees
   with AMemFileT06.v link_amwrite_stores / link_amwrite_closure_ok, which the proof does not need.

   PcapSyms B is needed because the contract is true only at link's image and FILE: as_code B = Tfib_code
   makes 0x52d74 the interceptor's entry, as_errno B = as_tp B - 164 makes the ENOSPC store land in the
   excepted errno range, and as_owned_static B = Tfib_owned_static shows that errno is not runtime-owned.

   The step pattern (entry state by entry_st_ok_full, one phase by SRr_run_gen, the call by aintrin_realizes
   spliced with st_ok_after_call, the return by SRr_ret_at) is the frame's, lib/A/AE36.v and lib/A/AE3h.v.
   mw_phase adds one clause to the frame's phase lemma: the raw memory of a phase only grows on the visible
   bytes, which is what the contract's unconditional presence clause needs.
   The determinism lemmas mw_le_bytes_mod / mw_val_det are COPIED (and generalised from 8 bytes to n) from
   pcap's released A walk of mseek, relocated by a Theorem Labs lane:
   (internal path) (internal record, sha256 5332f18fa29b) (wms_le_bytes_mod,
   wms_val_mem8_det). Every address and instruction count below is read from link's own binary. *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0k YK0s YK0n YP0n YK1d.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP04 YP0g YP01.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YN3v YI04 YI08 YI0n YI16 YFen.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v YO0f.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AB1v AE34 AF0l AF0m AF0x AE20 AE23 AE2y AMemFile.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Rt Require Import LinkMfDefs LinkRwDefs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* ==========================================================================
   1. The code table: mwrite (0x96cc0, 276 B = 69 instructions) and
      ___errno_location (0x90a7c, 12 B = 3 instructions). Both sizes are read from link's own unstripped
      twin (.symtab, link-a/facts/syms.tsv (internal record, sha256 4def0c9bfebf)). The interceptor's entry
      0x52d74 is not in the table, so the run stops there and AMEMCPY takes over.
   ========================================================================== *)
Definition mw_ranges : list (Z * nat) := [(0x96cc0, 69%nat); (0x90a7c, 3%nat)].
Definition tbl_mw : ctable := Eval vm_compute in build_ranges mw_ranges TEmpty.
Lemma tbl_mw_eq : tbl_mw = build_ranges mw_ranges TEmpty.
Proof. vm_cast_no_check (eq_refl tbl_mw). Qed.
Lemma tbl_mw_ok : table_ok tfibsegs tbl_mw.
Proof.
  rewrite tbl_mw_eq. apply build_ranges_ok; [| apply table_ok_empty].
  unfold mw_ranges. repeat constructor; cbn; discriminate.
Qed.

(* ==========================================================================
   2. Byte-level and image helpers
   ========================================================================== *)
Lemma mw_le_bytes_mod : forall (w : nat) x y,
  (forall k, (k < w)%nat -> YO0f.le_byte x w k = YO0f.le_byte y w k) ->
  x mod 2 ^ (8 * Z.of_nat w) = y mod 2 ^ (8 * Z.of_nat w).
Proof.
  intros w x y H. unfold YO0f.le_byte in H.
  assert (Hp : 0 < 2 ^ (8 * Z.of_nat w)) by (apply Z.pow_pos_nonneg; lia).
  apply Z.bits_inj'. intros i Hi.
  destruct (Z_lt_le_dec i (8 * Z.of_nat w)) as [Hlt|Hge].
  - pose proof (Z.div_mod i 8 ltac:(lia)) as Hd. pose proof (Z.mod_pos_bound i 8 ltac:(lia)) as Hm.
    assert (Hq : 0 <= i / 8 < Z.of_nat w) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
    set (k := Z.to_nat (i / 8)).
    assert (Hk : (k < w)%nat) by (subst k; lia).
    assert (Ek : Z.of_nat k = i / 8) by (subst k; rewrite Z2Nat.id; lia).
    specialize (H k Hk). change 256 with (2 ^ 8) in H.
    assert (Hb : forall z, Z.testbit (Z.shiftr (z mod 2 ^ (8 * Z.of_nat w)) (8 * Z.of_nat k) mod 2 ^ 8) (i mod 8) =
                           Z.testbit (z mod 2 ^ (8 * Z.of_nat w)) i).
    { intros z. rewrite Z.mod_pow2_bits_low by lia. rewrite Z.shiftr_spec by lia. f_equal. lia. }
    rewrite <- (Hb x), <- (Hb y), H. reflexivity.
  - rewrite !Z.mod_pow2_bits_high by lia. reflexivity.
Qed.

Lemma mw_val_det : forall segs (m : word -> option byte) a (w : nat) x y,
  val_mem segs m a w x -> val_mem segs m a w y -> 0 <= y < 2 ^ (8 * Z.of_nat w) ->
  x mod 2 ^ (8 * Z.of_nat w) = y.
Proof.
  intros segs m a w x y Hx Hy Hr. rewrite <- (Z.mod_small y (2 ^ (8 * Z.of_nat w))) by lia.
  apply mw_le_bytes_mod.
  intros k Hk. specialize (Hx k Hk). specialize (Hy k Hk). rewrite Hx in Hy.
  assert (Hb : Z_to_bv 8 (YO0f.le_byte x w k) = Z_to_bv 8 (YO0f.le_byte y w k)) by congruence. clear Hy.
  apply (f_equal bv_unsigned) in Hb. rewrite !Z_to_bv_unsigned in Hb. unfold bv_wrap in Hb. rename Hb into Hy.
  change (bv_modulus 8) with 256 in Hy. unfold YO0f.le_byte in *. rewrite !Z.mod_mod in Hy by lia. exact Hy.
Qed.

Lemma mw_val8_det : forall segs (m : word -> option byte) a x y,
  val_mem segs m a 8 x -> val_mem segs m a 8 y -> 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 -> x = y.
Proof.
  intros segs m a x y Hx Hy Rx Ry.
  pose proof (mw_val_det segs m a 8%nat x y Hx Hy ltac:(cbn; lia)) as H. cbn in H.
  rewrite Z.mod_small in H by (cbn; lia). exact H.
Qed.

Lemma mw_val4_det : forall segs (m : word -> option byte) a x y,
  val_mem segs m a 4 x -> val_mem segs m a 4 y -> 0 <= x < 2 ^ 32 -> 0 <= y < 2 ^ 32 -> x = y.
Proof.
  intros segs m a x y Hx Hy Rx Ry.
  pose proof (mw_val_det segs m a 4%nat x y Hx Hy ltac:(cbn; lia)) as H. cbn in H.
  rewrite Z.mod_small in H by (cbn; lia). exact H.
Qed.

Lemma mw_nth_firstn : forall (A : Type) (d : A) k (l : list A) i,
  (i < k)%nat -> nth i (firstn k l) d = nth i l d.
Proof.
  intros A d k. induction k as [|k IH]; intros l i Hi; [lia|].
  destruct l as [|a l]; cbn; [destruct i; reflexivity|].
  destruct i as [|i]; [reflexivity | cbn; apply IH; lia].
Qed.

(* every byte of g_said and of errno is writable in ANY memory: both lie in the image's last (rw) segment *)
Lemma mw_wz_said : wseg_ok tfibsegs (Z_to_bv 64 0x62fee0) (Z.to_nat 4096) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma mw_wz_errno : wseg_ok tfibsegs (Z_to_bv 64 0x631b6c) (Z.to_nat 4) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma mw_said_writable : forall (m : word -> option byte) a, 0x62fee0 <= a < 0x62fee0 + 4096 ->
  writable_at tfibsegs m a.
Proof. intros m a Ha. apply (wseg_writable m 0x62fee0 4096 a mw_wz_said); lia. Qed.
Lemma mw_errno_writable : forall (m : word -> option byte) a, 0x631b6c <= a < 0x631b6c + 4 ->
  writable_at tfibsegs m a.
Proof. intros m a Ha. apply (wseg_writable m 0x631b6c 4 a mw_wz_errno); lia. Qed.

(* the image's four loaded segments, by evaluation of link's own segment list *)
Lemma mw_seg_table :
  map (fun s => (Z.of_N (seg_base s), Z.of_N (seg_size s))) tfibsegs =
  [(65536, 135168); (200704, 458752); (659456, 8192); (667648, 5967872)].
Proof. vm_compute. reflexivity. Qed.
Lemma mw_img_full : forall x, 0x10000 <= x < 0x654000 -> in_img tfibsegs x.
Proof.
  intros x Hx. pose proof mw_seg_table as Hm. unfold in_img.
  destruct tfibsegs as [|s0 [|s1 [|s2 [|s3 [|s4 l]]]]]; cbn [map] in Hm; try discriminate Hm.
  injection Hm as E0 F0 E1 F1 E2 F2 E3 F3.
  destruct (Z_lt_le_dec x 200704). { exists s0. split; [left; reflexivity | lia]. }
  destruct (Z_lt_le_dec x 659456). { exists s1. split; [right; left; reflexivity | lia]. }
  destruct (Z_lt_le_dec x 667648). { exists s2. split; [right; right; left; reflexivity | lia]. }
  exists s3. split; [right; right; right; left; reflexivity | lia].
Qed.
Lemma mw_blk_off_img : forall p n, 0 < n -> (forall a, p <= a < p + n -> ~ in_img tfibsegs a) ->
  p + n <= 0x10000 \/ 0x654000 <= p.
Proof.
  intros p n Hn H. destruct (Z_le_gt_dec (p + n) 0x10000) as [L|L]; [left; exact L|].
  destruct (Z_le_gt_dec 0x654000 p) as [L2|L2]; [right; exact L2|]. exfalso.
  apply (H (Z.max p 0x10000)); [lia|]. apply mw_img_full. lia.
Qed.

(* errno is not runtime-owned: no extent of the runtime's static-ownership list covers its four bytes *)
Definition zr_free (l : list (Z * Z)) (lo hi : Z) : bool :=
  forallb (fun r => (hi <=? fst r) || (fst r + snd r <=? lo)) l.
Lemma zr_free_sound : forall l lo hi a, zr_free l lo hi = true -> lo <= a < hi -> ~ Exists (in_zr a) l.
Proof.
  intros l lo hi a H Ha HE. rewrite Exists_exists in HE. destruct HE as (r & Hin & Hr).
  unfold zr_free in H. rewrite forallb_forall in H. specialize (H r Hin).
  apply orb_prop in H as [H|H]; apply Z.leb_le in H; unfold in_zr in Hr; lia.
Qed.
Lemma mw_errno_free : zr_free Tfib_owned_static 0x631b6c 0x631b70 = true.
Proof. vm_compute. reflexivity. Qed.

(* the bytes this walk may change, and the FILE cells it may change *)
Definition mw_set (sp0 f a : Z) : Prop :=
  (sp0 - 4144 <= a < sp0) \/ (f <= a < f + 272) \/ (0x62fee0 <= a < 0x62fee0 + 4096) \/
  (0x631b6c <= a < 0x631b6c + 4).

(* ==========================================================================
   3. The symbolic entry state. Atoms 0..31 are the registers; 32 = f->wpos = f->wbase, 33 = f->flags,
      34 = c->pos, 35 = c->len, 36 = f->wend, 37 = f->orientation. The FILE region carries a chunk for
      every cell amemfile_at names, so the walk reads the whole predicate back out of the final state.
   ========================================================================== *)
Definition R_mstk : YP09.region := YP09.mkRegion (Some 2%nat) (-48) 0 (-48) 0 [].
Definition mw_static_chunks : list YP09.chunk :=
  [ YP09.mkChunk 8 (CVal 8 (SLit 0));
    YP09.mkChunk 16 (CVal 8 (SLit 0));
    YP09.mkChunk 24 (CVal 8 (SLit 0x96e70));
    YP09.mkChunk 48 (CVal 8 (SLit 0));
    YP09.mkChunk 64 (CVal 8 (SLit 0x96bec));
    YP09.mkChunk 72 (CVal 8 (SLit 0x96cc0));
    YP09.mkChunk 80 (CVal 8 (SLit 0x96dd4));
    YP09.mkChunk 88 (CVal 8 (SOff 10 280));
    YP09.mkChunk 96 (CVal 8 (SLit 1024));
    YP09.mkChunk 104 (CVal 8 (SLit 0));
    YP09.mkChunk 112 (CVal 8 (SLit 0));
    YP09.mkChunk 120 (CVal 4 (SLit 4294967295));
    YP09.mkChunk 124 (CVal 4 (SLit 0));
    YP09.mkChunk 128 (CVal 8 (SLit 0));
    YP09.mkChunk 136 (CVal 4 (SOff 37 0));
    YP09.mkChunk 140 (CVal 4 (SLit 4294967295));
    YP09.mkChunk 144 (CVal 4 (SLit 4294967295));
    YP09.mkChunk 152 (CVal 8 (SOff 10 232));
    YP09.mkChunk 160 (CVal 8 (SLit 0));
    YP09.mkChunk 168 (CVal 8 (SLit 0));
    YP09.mkChunk 176 (CVal 8 (SLit 0));
    YP09.mkChunk 184 (CVal 8 (SLit 0));
    YP09.mkChunk 192 (CVal 8 (SLit 0));
    YP09.mkChunk 200 (CVal 8 (SLit 0));
    YP09.mkChunk 208 (CVal 8 (SLit 0));
    YP09.mkChunk 216 (CVal 8 (SLit 0));
    YP09.mkChunk 224 (CVal 8 (SLit 0));
    YP09.mkChunk 248 (CVal 8 (SLit 4096));
    YP09.mkChunk 256 (CVal 8 (SLit 6487776));
    YP09.mkChunk 264 (CVal 4 (SLit 119)) ].
Definition R_mfile : YP09.region :=
  YP09.mkRegion (Some 10%nat) 0 272 0 248
    ([ YP09.mkChunk 0 (CVal 4 (SOff 33 0));
       YP09.mkChunk 32 (CVal 8 (SOff 36 0));
       YP09.mkChunk 40 (CVal 8 (SOff 32 0));
       YP09.mkChunk 56 (CVal 8 (SOff 32 0));
       YP09.mkChunk 232 (CVal 8 (SOff 34 0));
       YP09.mkChunk 240 (CVal 8 (SOff 35 0)) ] ++ mw_static_chunks).
Definition R_merrno : YP09.region := YP09.mkRegion (Some 4%nat) (-164) (-160) (-164) (-160) [].
Definition mw_facts : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 44) (2 ^ 47) 4); (10%nat, mkAF 4096 (2 ^ 47) 4)] [] [].
Definition ss_mw : sstate := mkSS 0x96cc0 sr_atoms [R_mstk; R_mfile; R_merrno] None mw_facts.

Ltac inlist := cbn [In app]; repeat (first [ left; reflexivity | right ]).

Section W. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Hypothesis TB : PcapSyms B.
Hypothesis AMEMCPY : aintrin_realizes tfibsegs B OCpy (pc_wrap_memcpy (as_code B)).

(* One phase of the symbolic run, lifted to SRr. This is the frame's icpt_phase (lib/A/AE2y.v) with one
   extra conclusion: on the visible bytes the raw memory only grows, which the contract's presence clause
   needs for the bytes of the image (errno) that a symbolic window covers. *)
Lemma mw_phase : forall (W : world tfibsegs) E ss ss' st ms md,
  st_ok tfibsegs E ss (restrict (w_H W) ms) ->
  sym_runN tfibsegs tbl_mw FUEL ss = (ss', st) ->
  SRr tfibsegs W (mkCfg ms md)
    (fun W' c' => W' = W /\ exists ms1 mat1, c' = mkCfg ms1 (with_vm_backing (m_vm_lazy md) mat1 md) /\
       match st with RS_ecall => st_ok_ecall tfibsegs E ss' (restrict (w_H W) ms1)
       | _ => st_ok tfibsegs E ss' (restrict (w_H W) ms1) end /\
       frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms1) /\
       frame_of E (ss_mem ss) (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms1)) /\
       (forall xw : word, w_H W xw = false -> ms_mem ms xw <> None -> ms_mem ms1 xw <> None)).
Proof.
  intros W E ss ss' st ms md HS Hrun.
  pose proof AF0x.Hwx_tfa as Hwx.
  destruct (msteps_run_gen tfibsegs tbl_mw tbl_mw_ok FUEL E ss ss' st _ HS Hrun) as (msr' & Hms & HS' & Hfr).
  pose proof (msteps_mem_grows tfibsegs _ _ Hms) as Hgrow.
  apply (SRr_msteps tfibsegs Hwx W ms msr' md _ Hms).
  intros model' Hsame Hcl.
  rewrite (same_but_materialized_wvb md model' Hsame).
  pose proof (restrict_unrestrict_clean (w_H W) (ms_mem ms) msr' Hcl) as Hrr.
  apply SRr_ret. split; [reflexivity|].
  exists (unrestrict (w_H W) (ms_mem ms) msr'), (m_vm_materialized model').
  split; [reflexivity|].
  split. { rewrite Hrr. exact HS'. }
  split. { cbn [unrestrict ms_mem]. apply frame_of_unrestrict. exact Hfr. }
  split.
  { change (mrestrict (w_H W) (ms_mem (unrestrict (w_H W) (ms_mem ms) msr')))
      with (ms_mem (restrict (w_H W) (unrestrict (w_H W) (ms_mem ms) msr'))).
    rewrite Hrr. exact Hfr. }
  intros xw Hh Hne. cbn [unrestrict ms_mem]. unfold munrestrict. rewrite Hh.
  apply Hgrow. cbn [restrict ms_mem]. unfold mrestrict. rewrite Hh. exact Hne.
Qed.

(* one phase of the run, as srr_run_with does it but through mw_phase, with the names given *)
Tactic Notation "mwrun" ident(HS) ident(msn) ident(matn) ident(HFn) ident(HFrn) ident(HGn) :=
  lazymatch type of HS with
  | st_ok ?segs ?E ?ss (restrict (w_H ?W) ?ms) =>
      let r := eval vm_compute in (sym_runN segs tbl_mw FUEL ss) in
      lazymatch r with
      | (?ss', ?st) =>
        let Hrun := fresh "Hrun" in
        assert (Hrun : sym_runN segs tbl_mw FUEL ss = (ss', st)) by (vm_compute; reflexivity);
        eapply SRr_bind; [ apply (mw_phase W E ss ss' st ms _ HS Hrun) |];
        clear Hrun HS;
        cbv beta;
        intros ? ? ? (-> & msn & matn & -> & HS & HFn & HFrn & HGn)
      end
  end.

Theorem link_amwrite_k0 : amwrite_mf_k0_realizes tfibsegs B link_amf LA_MWRITE.
Proof.
  unfold amwrite_mf_k0_realizes, amwrite_mf_at.
  intros ly S W regs mem md f k fl om wend wpos wbase pos len x pb ds.
  intros HPRE HSTK HPRES H10 H11 H12 HBLK HK HKMAX HDYN HPEND HPBLEN HBUF HZB HX0 HXHI HAM HRA HHULL HSEP.
  pose proof (YG0q.AR_laws_ok tfibsegs B) as LAWS.
  pose proof HPRE as (HAR & Hra & Hal16 & Hslo & Htop & HpresE & Hgp & Htp).
  pose proof AF0x.Hwx_tfa as Hwx.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof (am_layout B ly S _ (proj1 HAR)) as HLY.
  pose proof (lo_top ly HLY) as (Lbot & Ltop & _ & Lhi & _ & _ & Lbeg).
  pose proof (lo_stk_ceil ly HLY) as Lceil.
  unfold ASAN_CEIL in Lceil.
  set (sp0 := spZ regs) in *.
  set (n := Z.of_nat (length ds)) in *.
  assert (Hsp44 : 2 ^ 44 <= sp0 <= 2 ^ 47) by (unfold AMW0_STK, ESTACK in HSTK; lia).
  (* the FILE words *)
  destruct HK as (HMF & HWIN).
  pose proof HMF as (Hf0 & Hfhi & Hf16 & HST & HFL & HOM & HWD & HCK).
  destruct HDYN as (Dfl & Dom & Dwend & Dwpos & Dwbase & Dpos & Dlen & Vfl & Vom & Vwend & Vwpos & Vwbase & Vpos & Vlen).
  (* k = 0 and pb = [] *)
  assert (Hk0 : k = 0).
  { destruct HWIN as [(Hk & _) | (Hk & _)]; lia. }
  assert (Hpb : pb = []).
  { rewrite Hk0 in HPBLEN. destruct pb; [reflexivity | cbn in HPBLEN; lia]. }
  subst pb. clear HPBLEN HPEND. subst k.
  (* with an empty window wpos = wbase *)
  assert (Hwpb : wpos = wbase).
  { destruct HWIN as [(_ & _ & Hp & Hb) | (Hkr & _ & Hp & Hb)].
    - assert (A1 : wpos = 0) by (apply (mw_val8_det tfibsegs _ _ _ _ Vwpos Hp); lia).
      assert (A2 : wbase = 0) by (apply (mw_val8_det tfibsegs _ _ _ _ Vwbase Hb); lia).
      lia.
    - assert (A1 : wpos = f + AMF_BUF + 0)
        by (apply (mw_val8_det tfibsegs _ _ _ _ Vwpos Hp); unfold AMF_BUF, AMF_BLOCK in *; lia).
      assert (A2 : wbase = f + AMF_BUF)
        by (apply (mw_val8_det tfibsegs _ _ _ _ Vwbase Hb); unfold AMF_BUF, AMF_BLOCK in *; lia).
      lia. }
  (* the window of the final state is one of amf_win's two shapes *)
  assert (HWSHAPE : (wend = 0 /\ wpos = 0) \/
                    (wend = f + AMF_BUF + AMF_BUFSIZ /\ wpos = f + AMF_BUF)).
  { destruct HWIN as [(_ & He & Hp & _) | (Hkr & He & Hp & _)].
    - left. split.
      + apply (mw_val8_det tfibsegs _ _ _ _ Vwend He); lia.
      + apply (mw_val8_det tfibsegs _ _ _ _ Vwpos Hp); lia.
    - right. split.
      + apply (mw_val8_det tfibsegs _ _ _ _ Vwend He); unfold AMF_BUF, AMF_BUFSIZ, AMF_BLOCK in *; lia.
      + assert (A1 : wpos = f + AMF_BUF + 0)
          by (apply (mw_val8_det tfibsegs _ _ _ _ Vwpos Hp); unfold AMF_BUF, AMF_BLOCK in *; lia).
        lia. }
  (* the orientation and the flags take one of two values *)
  assert (Hom2 : om = 0 \/ om = AU32M1).
  { destruct HOM as [Ho | Ho].
    - left. apply (mw_val4_det tfibsegs _ _ _ _ Vom Ho); unfold AU32M1; lia.
    - right. apply (mw_val4_det tfibsegs _ _ _ _ Vom Ho); unfold AU32M1; lia. }
  assert (Hfl2 : fl = AF_NORD \/ fl = AF_NORD + AF_ERR).
  { destruct HFL as [Ho | Ho].
    - left. apply (mw_val4_det tfibsegs _ _ _ _ Vfl Ho); unfold AF_NORD, AF_ERR; lia.
    - right. apply (mw_val4_det tfibsegs _ _ _ _ Vfl Ho); unfold AF_NORD, AF_ERR; lia. }
  (* the FILE's static cells *)
  destruct HST as (S24 & S48 & S64 & S72 & S80 & S88 & S96 & S104 & S112 & S120 & S124 & S128 & S140 & S144
    & S152 & S160 & S168 & S176 & S184 & S192 & S200 & S208 & S216 & S224 & Ssz & Sbuf & Smode).
  destruct HWD as (Srp & Sre & _).
  (* the block *)
  destruct (al_blocks _ _ LAWS ly S W mem md f AMF_BLOCK HAR HBLK) as (Hb16 & Hf4096 & Hfceil & Hfapp & Hfpres & _ & _).
  assert (RQ : req_size AMF_BLOCK = AMF_BLOCK) by reflexivity.
  rewrite RQ in Hfceil, Hfpres.
  assert (Hfimg : f + AMF_BLOCK <= 0x10000 \/ 0x654000 <= f).
  { apply (mw_blk_off_img f AMF_BLOCK); [unfold AMF_BLOCK; lia|]. intros a Ha.
    apply (al_client_img _ _ LAWS ly S W mem md a HAR). left. exists f, AMF_BLOCK.
    split; [exact HBLK | rewrite RQ; lia]. }
  assert (Hfstk : f + AMF_BLOCK <= sp0 - AMW0_STK).
  { unfold AMF_BLOCK in Hfceil. unfold AMW0_STK, ESTACK in HSTK. unfold AMF_BLOCK, AMW0_STK, ESTACK. lia. }
  (* the buffer *)
  pose proof HBUF as (Hbuf0 & Hbufhi & Hsize & Hbufw & Hbufam & Hbufra & Hbufhull).
  assert (HB : amf_buf link_amf = 0x62fee0) by reflexivity.
  assert (HSZ : amf_size link_amf = 4096) by reflexivity.
  assert (Hterr : as_tp B = 0x631c10) by (rewrite (ts_tp B TB); reflexivity).
  assert (Herr : as_errno B = 0x631b6c) by (rewrite (ts_errno B TB); reflexivity).
  (* ownership of every byte this walk may change *)
  assert (NOERR : forall a, 0x631b6c <= a < 0x631b6c + 4 -> ~ aowned B ly S a).
  { intros a Ha Hown.
    rewrite (al_owned_image _ _ LAWS ly S W mem md a HAR (mw_img_full a ltac:(lia))) in Hown.
    rewrite (ts_owned B TB) in Hown.
    exact (zr_free_sound _ _ _ a mw_errno_free ltac:(lia) Hown). }
  assert (NOWN : forall a, mw_set sp0 f a -> ~ aowned B ly S a).
  { intros a [Hs | [Hff | [Hg | He]]].
    - apply (al_stack _ _ LAWS ly S W mem md a HAR). unfold AMW0_STK, ESTACK in HSTK. lia.
    - apply (proj2 (Hfpres a ltac:(unfold AMF_BLOCK; lia))).
    - apply (proj1 (proj2 (Hbufw a ltac:(rewrite HB, HSZ; lia)))).
    - apply NOERR. lia. }
  assert (NOBAND : forall a, mw_set sp0 f a -> ~ in_band_rw a).
  { intros a Hm Hb.
    unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in Hb.
    unfold in_app, kLowShadowBeg, kHighMemBeg in Hfapp.
    unfold kHighMemBeg in Lbeg. unfold AMW0_STK, ESTACK in HSTK.
    destruct Hm as [Hs | [Hff | [Hg | He]]]; unfold AMF_BLOCK in *; lia. }
  (* the environment *)
  set (extra := [Z_to_bv 64 wpos; Z_to_bv 64 fl; Z_to_bv 64 pos; Z_to_bv 64 len;
                 Z_to_bv 64 wend; Z_to_bv 64 om]).
  set (E := Ereg regs extra).
  assert (EE : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew E i = getr regs r)
    by (intros i r Hi; subst E; exact (ew_Ereg_nat regs extra i r Hi)).
  assert (E1 : ew E 1 = getr regs 1) by (apply EE; reflexivity).
  assert (E2 : ew E 2 = getr regs 2) by (apply EE; reflexivity).
  assert (E3 : ew E 3 = getr regs 3) by (apply EE; reflexivity).
  assert (E4 : ew E 4 = getr regs 4) by (apply EE; reflexivity).
  assert (E10 : ew E 10 = Z_to_bv 64 f) by (rewrite (EE 10%nat 10%bv eq_refl); exact H10).
  assert (E11 : ew E 11 = Z_to_bv 64 x) by (rewrite (EE 11%nat 11%bv eq_refl); exact H11).
  assert (E12 : ew E 12 = Z_to_bv 64 n) by (rewrite (EE 12%nat 12%bv eq_refl); exact H12).
  assert (E32 : ew E 32 = Z_to_bv 64 wpos) by exact (ew_Ereg_extra regs extra 0).
  assert (E33 : ew E 33 = Z_to_bv 64 fl) by exact (ew_Ereg_extra regs extra 1).
  assert (E34 : ew E 34 = Z_to_bv 64 pos) by exact (ew_Ereg_extra regs extra 2).
  assert (E35 : ew E 35 = Z_to_bv 64 len) by exact (ew_Ereg_extra regs extra 3).
  assert (E36 : ew E 36 = Z_to_bv 64 wend) by exact (ew_Ereg_extra regs extra 4).
  assert (E37 : ew E 37 = Z_to_bv 64 om) by exact (ew_Ereg_extra regs extra 5).
  assert (Usp : bv_unsigned (ew E 2) = sp0) by (rewrite E2; reflexivity).
  assert (Uf : bv_unsigned (ew E 10) = f) by (rewrite E10; apply unsigned_lit_small; unfold AMF_BLOCK in *; lia).
  assert (Utp : bv_unsigned (ew E 4) = as_tp B) by (rewrite E4, Htp; apply unsigned_lit_small; lia).
  (* the entry state *)
  assert (HS0 : st_ok tfibsegs E ss_mw (restrict (w_H W) (mkst regs (Z_to_bv 64 0x96cc0) mem (seg_rom tfibsegs)))).
  { rewrite restrict_mkst_fx. unfold ss_mw. apply (entry_st_ok_full tfibsegs); fold E.
    - apply regs_ok_Ereg.
    - vm_compute. reflexivity.
    - unfold R_mstk, R_mfile, R_merrno, mw_static_chunks. repeat apply Forall_cons; try apply Forall_nil.
      + apply (region_ok_stack tfibsegs E _ 2 sp0 (-48) Usp); [lia | lia |].
        intros a Ha. apply apresent_writable. apply HPRES. unfold AMW0_STK, ESTACK. lia.
      + unfold region_ok.
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val app].
        rewrite Uf. split; [unfold AMF_BLOCK in *; lia|]. split; [unfold AMF_BLOCK in *; lia|]. split.
        { intros o Ho. apply apresent_writable. apply (proj1 (Hfpres (f + o) ltac:(unfold AMF_BLOCK; lia))). }
        repeat apply Forall_cons; try apply Forall_nil.
        * apply (chunk_ok_val tfibsegs E _ f 0 4 (SOff 33 0) fl);
            [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact Vfl].
        * apply (chunk_ok_val tfibsegs E _ f 32 8 (SOff 36 0) wend);
            [cbn [sv_denot]; rewrite E36, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact Vwend].
        * apply (chunk_ok_val tfibsegs E _ f 40 8 (SOff 32 0) wpos);
            [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact Vwpos].
        * apply (chunk_ok_val tfibsegs E _ f 56 8 (SOff 32 0) wpos);
            [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |
             rewrite Hwpb; exact Vwbase].
        * apply (chunk_ok_val tfibsegs E _ f 232 8 (SOff 34 0) pos);
            [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact Vpos].
        * apply (chunk_ok_val tfibsegs E _ f 240 8 (SOff 35 0) len);
            [cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact Vlen].
        * apply (chunk_ok_val tfibsegs E _ f 8 8 (SLit 0) 0); [reflexivity | zside | zside | exact Srp].
        * apply (chunk_ok_val tfibsegs E _ f 16 8 (SLit 0) 0); [reflexivity | zside | zside | exact Sre].
        * apply (chunk_ok_val tfibsegs E _ f 24 8 (SLit 0x96e70) 0x96e70);
            [reflexivity | zside | zside | exact S24].
        * apply (chunk_ok_val tfibsegs E _ f 48 8 (SLit 0) 0); [reflexivity | zside | zside | exact S48].
        * apply (chunk_ok_val tfibsegs E _ f 64 8 (SLit 0x96bec) 0x96bec);
            [reflexivity | zside | zside | exact S64].
        * apply (chunk_ok_val tfibsegs E _ f 72 8 (SLit 0x96cc0) 0x96cc0);
            [reflexivity | zside | zside | exact S72].
        * apply (chunk_ok_val tfibsegs E _ f 80 8 (SLit 0x96dd4) 0x96dd4);
            [reflexivity | zside | zside | exact S80].
        * apply (chunk_ok_val tfibsegs E _ f 88 8 (SOff 10 280) (f + AMF_BUF));
            [cbn [sv_denot]; rewrite E10, unsigned_lit_small by (unfold AMF_BLOCK in *; lia);
             unfold AMF_BUF; reflexivity
            | unfold AMF_BUF, AMF_BLOCK in *; cbn; lia | cbn; lia | exact S88].
        * apply (chunk_ok_val tfibsegs E _ f 96 8 (SLit 1024) AMF_BUFSIZ);
            [reflexivity | unfold AMF_BUFSIZ; zside | zside | exact S96].
        * apply (chunk_ok_val tfibsegs E _ f 104 8 (SLit 0) 0); [reflexivity | zside | zside | exact S104].
        * apply (chunk_ok_val tfibsegs E _ f 112 8 (SLit 0) 0); [reflexivity | zside | zside | exact S112].
        * apply (chunk_ok_val tfibsegs E _ f 120 4 (SLit 4294967295) AU32M1);
            [reflexivity | unfold AU32M1; zside | zside | exact S120].
        * apply (chunk_ok_val tfibsegs E _ f 124 4 (SLit 0) 0); [reflexivity | zside | zside | exact S124].
        * apply (chunk_ok_val tfibsegs E _ f 128 8 (SLit 0) 0); [reflexivity | zside | zside | exact S128].
        * apply (chunk_ok_val tfibsegs E _ f 136 4 (SOff 37 0) om);
            [cbn [sv_denot]; rewrite E37, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact Vom].
        * apply (chunk_ok_val tfibsegs E _ f 140 4 (SLit 4294967295) AU32M1);
            [reflexivity | unfold AU32M1; zside | zside | exact S140].
        * apply (chunk_ok_val tfibsegs E _ f 144 4 (SLit 4294967295) AU32M1);
            [reflexivity | unfold AU32M1; zside | zside | exact S144].
        * apply (chunk_ok_val tfibsegs E _ f 152 8 (SOff 10 232) (f + AMF_COOKIE));
            [cbn [sv_denot]; rewrite E10, unsigned_lit_small by (unfold AMF_BLOCK in *; lia);
             unfold AMF_COOKIE; reflexivity
            | unfold AMF_COOKIE, AMF_BLOCK in *; cbn; lia | cbn; lia | exact S152].
        * apply (chunk_ok_val tfibsegs E _ f 160 8 (SLit 0) 0); [reflexivity | zside | zside | exact S160].
        * apply (chunk_ok_val tfibsegs E _ f 168 8 (SLit 0) 0); [reflexivity | zside | zside | exact S168].
        * apply (chunk_ok_val tfibsegs E _ f 176 8 (SLit 0) 0); [reflexivity | zside | zside | exact S176].
        * apply (chunk_ok_val tfibsegs E _ f 184 8 (SLit 0) 0); [reflexivity | zside | zside | exact S184].
        * apply (chunk_ok_val tfibsegs E _ f 192 8 (SLit 0) 0); [reflexivity | zside | zside | exact S192].
        * apply (chunk_ok_val tfibsegs E _ f 200 8 (SLit 0) 0); [reflexivity | zside | zside | exact S200].
        * apply (chunk_ok_val tfibsegs E _ f 208 8 (SLit 0) 0); [reflexivity | zside | zside | exact S208].
        * apply (chunk_ok_val tfibsegs E _ f 216 8 (SLit 0) 0); [reflexivity | zside | zside | exact S216].
        * apply (chunk_ok_val tfibsegs E _ f 224 8 (SLit 0) 0); [reflexivity | zside | zside | exact S224].
        * apply (chunk_ok_val tfibsegs E _ f 248 8 (SLit 4096) (amf_size link_amf));
            [rewrite HSZ; reflexivity | rewrite HSZ; zside | zside | exact Ssz].
        * apply (chunk_ok_val tfibsegs E _ f 256 8 (SLit 6487776) (amf_buf link_amf));
            [rewrite HB; reflexivity | rewrite HB; zside | zside | exact Sbuf].
        * apply (chunk_ok_val tfibsegs E _ f 264 4 (SLit 119) (amf_mode link_amf));
            [reflexivity | cbn; lia | zside | exact Smode].
      + unfold region_ok.
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
        rewrite Utp, Hterr. split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
        intros o Ho. apply mw_errno_writable. lia.
    - apply pairwise_disjoint_of_extents. unfold R_mstk, R_mfile, R_merrno, extent_of_region.
      cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite Usp, Uf, Utp, Hterr.
      cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
      unfold AMF_BLOCK, AMW0_STK, ESTACK in *. repeat split; lia.
    - split; [|split; exact I]. cbn [mw_facts f_atoms atoms_ok]. unfold afact_ok.
      cbn [af_lo af_hi af_al2]. rewrite Usp, Uf. change (2 ^ 4) with 16.
      unfold AMF_BLOCK in *. repeat split; lia. }
  (* ---------------------------------------------------------------------- *)
  (* generic steps: AR across a memory change, and the FILE predicate from the chunks of a final state  *)
  (* ---------------------------------------------------------------------- *)
  assert (AVNN : forall (m m' : word -> option byte),
     (forall xw : word, w_H W xw = false -> m xw <> None -> m' xw <> None) ->
     forall a, aview tfibsegs (w_H W) m a <> None -> aview tfibsegs (w_H W) m' a <> None).
  { intros m m' Hgr a Hv. unfold aview, mbyte, mrestrict in Hv |- *.
    destruct (w_H W (Z_to_bv 64 a)) eqn:Eh; [exact Hv|].
    destruct (m (Z_to_bv 64 a)) as [b|] eqn:Em.
    - destruct (m' (Z_to_bv 64 a)) as [b'|] eqn:Em'; cbn; [discriminate|].
      exfalso. apply (Hgr (Z_to_bv 64 a) Eh); [rewrite Em; discriminate | exact Em'].
    - destruct (m' (Z_to_bv 64 a)) as [b'|] eqn:Em'; cbn; [discriminate | exact Hv]. }
  assert (ARSTEP : forall (m m' : word -> option byte) (d d' : Model),
    AR tfibsegs B ly S W m d -> same_but_materialized d d' ->
    (forall xw : word, ~ mw_set sp0 f (bv_unsigned xw) -> m' xw = m xw) ->
    (forall xw : word, w_H W xw = false -> m xw <> None -> m' xw <> None) ->
    AR tfibsegs B ly S W m' d').
  { intros m m' d d' HARm Hsbm Heq Hgr.
    pose proof (same_but_materialized_frame d d' Hsbm) as MF.
    assert (MRE : forall xw : word, ~ mw_set sp0 f (bv_unsigned xw) ->
              mrestrict (w_H W) m' xw = mrestrict (w_H W) m xw).
    { intros xw Hx. unfold mrestrict. rewrite (Heq xw Hx). reflexivity. }
    apply (al_frame _ _ LAWS ly S W m d m' d' HARm).
    - intros a Hr Hown. apply aview_eq_of. apply MRE.
      rewrite unsigned_lit_small by lia. intros Hm. exact (NOWN a Hm Hown).
    - exact (AVNN m m' Hgr).
    - apply MF. - apply MF. - apply MF.
    - intros a Hband Hh. apply Heq.
      rewrite unsigned_lit_small by (apply in_band_rw_u64; exact Hband).
      intros Hm. exact (NOBAND a Hm Hband). }
  (* the FILE predicate of a final state, from the chunks that every leaf keeps *)
  assert (MKAT : forall (Ef : env) (m3 : word -> option byte) nfl nwend nwpos nwbase npos nlen,
    bv_unsigned (ew Ef 10) = f -> ew Ef 37 = Z_to_bv 64 om ->
    Forall (YP09.chunk_ok tfibsegs Ef m3 f) mw_static_chunks ->
    val_mem tfibsegs m3 (f + 0) 4 nfl ->
    val_mem tfibsegs m3 (f + 32) 8 nwend ->
    val_mem tfibsegs m3 (f + 40) 8 nwpos ->
    val_mem tfibsegs m3 (f + 56) 8 nwbase ->
    val_mem tfibsegs m3 (f + 232) 8 npos ->
    val_mem tfibsegs m3 (f + 240) 8 nlen ->
    (nfl = AF_NORD \/ nfl = AF_NORD + AF_ERR) ->
    ((nwend = 0 /\ nwpos = 0 /\ nwbase = 0) \/
     (nwend = f + AMF_BUF + AMF_BUFSIZ /\ nwpos = f + AMF_BUF /\ nwbase = f + AMF_BUF)) ->
    0 <= npos <= nlen -> nlen <= amf_size link_amf ->
    amf_k tfibsegs link_amf m3 f 0).
  { intros Ef m3 nfl nwend nwpos nwbase npos nlen Uf' Eom' HSC V0 V32 V40 V56 V232 V240 Hnfl Hnw Hnp Hnl.
    assert (KF : forall off (w : N) e v, In (YP09.mkChunk off (CVal w e)) mw_static_chunks ->
       sv_denot Ef e = Z_to_bv 64 v -> 0 <= v < 2 ^ (8 * Z.of_N w) -> Z.of_N w <= 8 ->
       val_mem tfibsegs m3 (f + off) (N.to_nat w) v).
    { intros off w e v Hin Hd Hv Hw.
      exact (val_of_chunk_ok tfibsegs Ef m3 f off w e v
               (proj1 (Forall_forall _ _) HSC _ Hin) Hd Hv Hw). }
    assert (L0 : forall z, sv_denot Ef (SLit z) = Z_to_bv 64 z) by (intros z; reflexivity).
    split; [|].
    - split; [exact Hf0|]. split; [exact Hfhi|]. split; [exact Hf16|].
      split.
      { unfold amemfile_static.
        split. { apply (KF 24 8%N (SLit 0x96e70) 0x96e70); [inlist | reflexivity | zside | zside]. }
        split. { apply (KF 48 8%N (SLit 0) 0); [inlist | reflexivity | zside | zside]. }
        split. { apply (KF 64 8%N (SLit 0x96bec) 0x96bec); [inlist | reflexivity | zside | zside]. }
        split. { apply (KF 72 8%N (SLit 0x96cc0) 0x96cc0); [inlist | reflexivity | zside | zside]. }
        split. { apply (KF 80 8%N (SLit 0x96dd4) 0x96dd4); [inlist | reflexivity | zside | zside]. }
        split. { apply (KF 88 8%N (SOff 10 280) (f + AMF_BUF));
                 [inlist
                 | cbn [sv_denot]; rewrite Uf'; unfold AMF_BUF; reflexivity
                 | unfold AMF_BUF, AMF_BLOCK in *; cbn; lia | cbn; lia]. }
        split. { apply (KF 96 8%N (SLit 1024) AMF_BUFSIZ);
                 [inlist | reflexivity | unfold AMF_BUFSIZ; zside | zside]. }
        split. { apply (KF 104 8%N (SLit 0) 0); [inlist | reflexivity | zside | zside]. }
        split. { apply (KF 112 8%N (SLit 0) 0); [inlist | reflexivity | zside | zside]. }
        split. { apply (KF 120 4%N (SLit 4294967295) AU32M1);
                 [inlist | reflexivity | unfold AU32M1; zside | zside]. }
        split. { apply (KF 124 4%N (SLit 0) 0); [inlist | reflexivity | zside | zside]. }
        split. { apply (KF 128 8%N (SLit 0) 0); [inlist | reflexivity | zside | zside]. }
        split. { apply (KF 140 4%N (SLit 4294967295) AU32M1);
                 [inlist | reflexivity | unfold AU32M1; zside | zside]. }
        split. { apply (KF 144 4%N (SLit 4294967295) AU32M1);
                 [inlist | reflexivity | unfold AU32M1; zside | zside]. }
        split. { apply (KF 152 8%N (SOff 10 232) (f + AMF_COOKIE));
                 [inlist
                 | cbn [sv_denot]; rewrite Uf'; unfold AMF_COOKIE; reflexivity
                 | unfold AMF_COOKIE, AMF_BLOCK in *; cbn; lia | cbn; lia]. }
        split. { apply (KF 160 8%N (SLit 0) 0); [inlist | reflexivity | zside | zside]. }
        split. { apply (KF 168 8%N (SLit 0) 0); [inlist | reflexivity | zside | zside]. }
        split. { apply (KF 176 8%N (SLit 0) 0); [inlist | reflexivity | zside | zside]. }
        split. { apply (KF 184 8%N (SLit 0) 0); [inlist | reflexivity | zside | zside]. }
        split. { apply (KF 192 8%N (SLit 0) 0); [inlist | reflexivity | zside | zside]. }
        split. { apply (KF 200 8%N (SLit 0) 0); [inlist | reflexivity | zside | zside]. }
        split. { apply (KF 208 8%N (SLit 0) 0); [inlist | reflexivity | zside | zside]. }
        split. { apply (KF 216 8%N (SLit 0) 0); [inlist | reflexivity | zside | zside]. }
        split. { apply (KF 224 8%N (SLit 0) 0); [inlist | reflexivity | zside | zside]. }
        split. { apply (KF 248 8%N (SLit 4096) (amf_size link_amf));
                 [inlist | rewrite HSZ; reflexivity | rewrite HSZ; zside | zside]. }
        split. { apply (KF 256 8%N (SLit 6487776) (amf_buf link_amf));
                 [inlist | rewrite HB; reflexivity | rewrite HB; zside | zside]. }
        { apply (KF 264 4%N (SLit 119) (amf_mode link_amf));
          [inlist | reflexivity | cbn; lia | zside]. } }
      split. { unfold amemfile_flags. destruct Hnfl as [-> | ->]; [left | right]; exact V0. }
      assert (V136 : val_mem tfibsegs m3 (f + 136) 4 om).
      { apply (KF 136 4%N (SOff 37 0) om);
        [inlist | cbn [sv_denot]; rewrite Eom', Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
        | zside | zside]. }
      split. { unfold amemfile_omode. destruct Hom2 as [Ho | Ho]; [left | right];
               rewrite <- Ho; exact V136. }
      split.
      { unfold amemfile_window.
        split. { apply (KF 8 8%N (SLit 0) 0); [inlist | reflexivity | zside | zside]. }
        split. { apply (KF 16 8%N (SLit 0) 0); [inlist | reflexivity | zside | zside]. }
        destruct Hnw as [(-> & -> & ->) | (-> & -> & ->)].
        - left. split; [exact V32 | split; [exact V40 | exact V56]].
        - right. exists 0. split; [unfold AMF_BUFSIZ; lia|].
          split; [exact V32|]. split; [rewrite Z.add_0_r; exact V40 | exact V56]. }
      { unfold amemfile_cookie. exists npos, nlen. split; [exact Hnp|]. split; [exact Hnl|].
        split; [exact V232 | exact V240]. }
    - unfold amf_win. destruct Hnw as [(-> & -> & ->) | (-> & -> & ->)].
      + left. split; [reflexivity|]. split; [exact V32 | split; [exact V40 | exact V56]].
      + right. split; [unfold AMF_BUFSIZ; lia|].
        split; [exact V32|]. split; [rewrite Z.add_0_r; exact V40 | exact V56]. }
  (* every symbolic window of this walk lies in the set of bytes the contract lets it change *)
  assert (WINX : forall (Ex : env) (ssx : sstate) a,
      bv_unsigned (ew Ex 2) = sp0 -> bv_unsigned (ew Ex 10) = f -> bv_unsigned (ew Ex 4) = as_tp B ->
      windows (ss_mem ssx) = windows (ss_mem ss_mw) ->
      in_wrange Ex (ss_mem ssx) a ->
      (sp0 - 48 <= a < sp0) \/ (f <= a < f + 248) \/ (as_tp B - 164 <= a < as_tp B - 160)).
  { intros Ex ssx a U2 U10 U4 Hw Ha.
    destruct (in_wrange_windows Ex _ a Ha) as (b & lo & hi & Ht & Hr). rewrite Hw in Ht.
    unfold ss_mw, R_mstk, R_mfile, R_merrno in Ht.
    cbn [windows ss_mem map YP09.r_base YP09.r_wlo YP09.r_whi] in Ht.
    destruct Ht as [Hq|[Hq|[Hq|[]]]]; injection Hq as <- <- <-; cbn [base_val] in Hr;
      rewrite ?U2, ?U10, ?U4 in Hr; [left | right; left | right; right]; lia. }
  assert (WIN : forall (Ex : env) (ssx : sstate) a,
      bv_unsigned (ew Ex 2) = sp0 -> bv_unsigned (ew Ex 10) = f -> bv_unsigned (ew Ex 4) = as_tp B ->
      windows (ss_mem ssx) = windows (ss_mem ss_mw) ->
      in_wrange Ex (ss_mem ssx) a -> mw_set sp0 f a).
  { intros Ex ssx a U2 U10 U4 Hw Ha.
    destruct (WINX Ex ssx a U2 U10 U4 Hw Ha) as [Hx|[Hx|Hx]]; unfold mw_set;
      [left | right; left | right; right; right];
      rewrite ?Hterr in Hx; unfold AMW0_STK, ESTACK; lia. }
  assert (KEEPV : forall (ma mb : word -> option byte),
      (forall xw : word, ~ mw_set sp0 f (bv_unsigned xw) -> mb xw = ma xw) ->
      forall a, 0 <= a < 2 ^ 64 -> ~ mw_set sp0 f a ->
      aview tfibsegs (w_H W) mb a = aview tfibsegs (w_H W) ma a).
  { intros ma mb Heq a Hr Ha. apply aview_eq_of. unfold mrestrict.
    rewrite (Heq (Z_to_bv 64 a)); [reflexivity|]. rewrite unsigned_lit_small by lia. exact Ha. }
  assert (PRESTEP : forall (ma mb : word -> option byte),
      (forall xw : word, w_H W xw = false -> ma xw <> None -> mb xw <> None) ->
      forall a, apresent (w_H W) ma a -> apresent (w_H W) mb a).
  { intros ma mb Hgr a [Hh [b Hb]]. split; [exact Hh|].
    destruct (mb (Z_to_bv 64 a)) as [b'|] eqn:Em; [exists b'; reflexivity|].
    exfalso. apply (Hgr (Z_to_bv 64 a) Hh); [rewrite Hb; discriminate | exact Em]. }
  (* no shadow byte of the application range is one of the bytes this walk changes *)
  assert (NOSH : forall s, kLowMemEnd <= s < kHighShadowEnd -> ~ mw_set sp0 f s).
  { intros s Hs [Hst | [Hff | [Hg | He]]];
    unfold in_app, kLowShadowBeg, kHighMemBeg in Hfapp;
    unfold kLowMemEnd, kHighShadowEnd in Hs; unfold kHighMemBeg in Lbeg;
    unfold AMW0_STK, ESTACK in HSTK; unfold AMF_BLOCK in *; lia. }
  assert (Hn64 : 0 <= n < 2 ^ 64) by (unfold n in *; lia).
  assert (Ubnd : U E (SAlu ALU_SUB (SLit 0) (SOff 34 (-4096))) = 4096 - pos).
  { rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit, U_SOff, E34.
    rewrite unsigned_lit_small by lia. unfold zcanon, M64.
    rewrite (Z.mod_small 0 (2 ^ 64)) by lia.
    rewrite Zminus_mod_idemp_r. rewrite Z.mod_small by (rewrite HSZ in Dlen; lia). lia. }
  assert (Un : U E (SOff 12 0) = n) by (apply (U_atom E 12 n E12); lia).
  unfold cfg_at. change (w64 LA_MWRITE) with (Z_to_bv 64 0x96cc0).
  mwrun HS0 msA matA HFA HFrA HGA.
  srr_branch_with tbl_mw_ok HS0.
  - (* the fitting arm: n <= size - pos, so the whole of ds is copied *)
    rewrite branch_geu_U, Ubnd, Un in Hc. apply negb_true_iff, Z.ltb_ge in Hc.
    rename Hc into Hfit.
    mwrun HS0 msB matB HFB HFrB HGB.
    (* the state at the interceptor's entry 0x52d74 *)
    assert (KB : forall xw : word, ~ mw_set sp0 f (bv_unsigned xw) -> ms_mem msB xw = mem xw).
    { intros xw Hx.
      assert (Hb : ms_mem msB xw = ms_mem msA xw).
      { apply HFB. intros Hin. refine (Hx (WIN E _ _ Usp Uf Utp _ Hin)). vm_compute; reflexivity. }
      assert (Ha : ms_mem msA xw = mem xw).
      { apply HFA. intros Hin. refine (Hx (WIN E _ _ Usp Uf Utp _ Hin)). reflexivity. }
      rewrite Hb, Ha. reflexivity. }
    assert (GB : forall xw : word, w_H W xw = false -> mem xw <> None -> ms_mem msB xw <> None).
    { intros xw Hh Hne. apply (HGB xw Hh). apply (HGA xw Hh). exact Hne. }
    assert (ARB : AR tfibsegs B ly S W (ms_mem msB) (with_vm_backing (m_vm_lazy md) matB md))
      by (apply (ARSTEP mem (ms_mem msB) md _ HAR (with_vm_backing_same md matB) KB GB)).
    assert (PRB : forall a, apresent (w_H W) mem a -> apresent (w_H W) (ms_mem msB) a)
      by (exact (PRESTEP mem (ms_mem msB) GB)).
    rreg HS0 (1%bv : bv 5) RA1. rreg HS0 (2%bv : bv 5) RA2. rreg HS0 (3%bv : bv 5) RA3.
    rreg HS0 (4%bv : bv 5) RA4. rreg HS0 (10%bv : bv 5) RA10. rreg HS0 (11%bv : bv 5) RA11.
    rreg HS0 (12%bv : bv 5) RA12.
    assert (HspB : spZ (ms_regs msB) = sp0 - 48).
    { unfold spZ. rewrite RA2, Usp. rewrite unsigned_lit_small by lia. lia. }
    assert (RA10' : getr (ms_regs msB) 10 = w64 (0x62fee0 + pos)).
    { rewrite RA10, E34. rewrite unsigned_lit_small by lia. unfold w64. f_equal. lia. }
    assert (RA11' : getr (ms_regs msB) 11 = w64 x) by (rewrite RA11, E11; reflexivity).
    assert (RA12' : getr (ms_regs msB) 12 = w64 n) by (rewrite RA12, E12; reflexivity).
    (* the shadow and the bytes of the copy, at the state of the call *)
    assert (SHV : forall s, kLowMemEnd <= s < kHighShadowEnd ->
              aview tfibsegs (w_H W) (ms_mem msB) s = aview tfibsegs (w_H W) mem s).
    { intros s Hs. apply (KEEPV mem (ms_mem msB) KB); [unfold kLowMemEnd, kHighShadowEnd in Hs; lia|].
      exact (NOSH s Hs). }
    assert (HSEPM : forall a, x <= a < x + n -> ~ mw_set sp0 f a).
    { intros a Ha Hm. destruct (HSEP a Ha) as (N1 & N2 & N3 & N4).
      rewrite HB, HSZ in N1. rewrite Herr in N3. unfold AMF_ZEROED in N2.
      destruct Hm as [Hs | [Hff | [Hg | He]]]; unfold AMW0_STK, ESTACK in *; lia. }
    pose proof AMEMCPY as AM. unfold aintrin_realizes, cfg_at in AM.
    rewrite (ts_code B TB) in AM. cbn [pc_wrap_memcpy Tfib_code] in AM.
    pose proof (st_ok_restrict_mkst tfibsegs (w_H W) E _ _ HS0 eq_refl) as HshB. cbn [ss_pc] in HshB.
    rewrite HshB.
    eapply SRr_bind.
    { apply (AM ly S W (ms_regs msB) (ms_mem msB) (with_vm_backing (m_vm_lazy md) matB md)
                (0x62fee0 + pos) x n).
      - split; [exact ARB|].
        split; [rewrite RA1; apply YK0s.ret_ok_even;
                rewrite unsigned_lit_small by lia; lia|].
        rewrite HspB.
        split; [replace (sp0 - 48) with (sp0 + (-3) * 16) by lia; rewrite Z_mod_plus_full; exact Hal16|].
        split; [unfold AMW0_STK, ESTACK in HSTK; unfold ESTACK; lia|].
        split; [lia|].
        split; [intros a Ha; apply PRB; apply HPRES; unfold ESTACK in Ha;
                unfold AMW0_STK, ESTACK; lia|].
        split.
        + rewrite RA3, E3. exact Hgp.
        + rewrite RA4, E4. exact Htp.
      - exact RA10'.
      - exact RA11'.
      - exact RA12'.
      - rewrite HSZ in Dlen. lia.
      - lia.
      - rewrite HSZ in Dlen. lia.
      - intros a Ha. split; [apply mw_said_writable; rewrite HSZ in Dlen; lia|].
        split; [apply (proj1 (proj2 (Hbufw a ltac:(rewrite HB, HSZ; rewrite HSZ in Dlen; lia))))|].
        rewrite HspB. unfold ESTACK. lia.
      - unfold amem_range, kLowMemEnd. rewrite HSZ in Dlen. lia.
      - intros y Hy. rewrite SHV.
        + apply Hbufra. rewrite HB, HSZ. rewrite HSZ in Dlen. lia.
        + change (shadow_of_addr SHADOW_OFF y) with (shadow_addr y).
          apply shadow_addr_bounds. unfold kHighMemEnd. rewrite HSZ in Dlen. lia.
      - intros Hn0 s Hs. rewrite SHV.
        + apply Hbufhull. rewrite HB, HSZ.
          pose proof (shadow_addr_bounds (0x62fee0 + pos) ltac:(unfold kHighMemEnd; lia)) as Q1.
          pose proof (shadow_addr_bounds (0x62fee0 + pos + n - 1) ltac:(unfold kHighMemEnd;
            rewrite HSZ in Dlen; lia)) as Q2.
          pose proof (shadow_addr_bounds 0x62fee0 ltac:(unfold kHighMemEnd; lia)) as Q3.
          pose proof (shadow_addr_bounds (0x62fee0 + 4096 - 1) ltac:(unfold kHighMemEnd; lia)) as Q4.
          unfold shadow_addr, SHADOW_OFF in *. rewrite HSZ in Dlen. lia.
        + pose proof (shadow_addr_bounds (0x62fee0 + pos) ltac:(unfold kHighMemEnd; lia)) as Q1.
          pose proof (shadow_addr_bounds (0x62fee0 + pos + n - 1) ltac:(unfold kHighMemEnd;
            rewrite HSZ in Dlen; lia)) as Q2.
          unfold shadow_addr, SHADOW_OFF in *. lia.
      - split; [lia|]. split; [lia|]. split.
        + intros a Ha. split.
          * rewrite (KEEPV mem (ms_mem msB) KB a ltac:(lia) (HSEPM a Ha)).
            pose proof (HZB (Z.to_nat (a - x)) ltac:(unfold n in *; lia)) as HB1.
            rewrite Z2Nat.id in HB1 by lia.
            replace (x + (a - x)) with a in HB1 by lia.
            change (amf_rd tfibsegs (mrestrict (w_H W) mem) a)
              with (aview tfibsegs (w_H W) mem a) in HB1.
            rewrite HB1. discriminate.
          * rewrite HspB. unfold ESTACK.
            destruct (HSEP a Ha) as (_ & _ & _ & N4). unfold AMW0_STK, ESTACK in N4. lia.
        + split.
          * (* the source does not meet the destination, which lies in g_said *)
            destruct (Z_le_gt_dec (0x62fee0 + pos + n) x) as [Hd1|Hd1]; [left; lia|].
            destruct (Z_le_gt_dec (x + n) (0x62fee0 + pos)) as [Hd2|Hd2]; [right; lia|].
            exfalso. assert (Hz : 0 < n) by lia.
            destruct (HSEP (Z.max x (0x62fee0 + pos)) ltac:(lia)) as (N1 & _ & _ & _).
            apply N1. rewrite HB, HSZ. rewrite HSZ in Dlen. lia.
          * split; [exact HAM|].
            split.
            -- intros y Hy. rewrite SHV.
               ++ apply HRA. exact Hy.
               ++ change (shadow_of_addr SHADOW_OFF y) with (shadow_addr y).
                  apply shadow_addr_bounds. unfold kHighMemEnd. unfold amem_range, kLowMemEnd,
                  kHighMemBeg, kHighMemEnd in HAM. lia.
            -- intros Hn0 s Hs. rewrite SHV.
               ++ apply HHULL; [exact Hn0 | exact Hs].
               ++ pose proof (shadow_addr_bounds x ltac:(unfold amem_range, kLowMemEnd, kHighMemBeg,
                    kHighMemEnd in HAM; unfold kHighMemEnd; lia)) as Q1.
                  pose proof (shadow_addr_bounds (x + n - 1) ltac:(unfold amem_range, kLowMemEnd,
                    kHighMemBeg, kHighMemEnd in HAM; unfold kHighMemEnd; lia)) as Q2.
                  unfold shadow_addr, SHADOW_OFF in *. lia. }
    cbv beta.
    intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HAR2 & HP2 & Hsbm2 & Ha0 & Hcpy & Hfr2 & Hpres2).
    assert (AV2 : forall a, 0 <= a < 2 ^ 64 -> ~ mw_set sp0 f a ->
                  aview tfibsegs (w_H W) mem2 a = aview tfibsegs (w_H W) mem a).
    { intros a Hr Ha.
      rewrite (Hfr2 a Hr
        ltac:(intros Hd; apply Ha; unfold mw_set; right; right; left; rewrite HSZ in Dlen; lia)
        ltac:(rewrite HspB; unfold ESTACK; intros Hw; apply Ha; unfold mw_set; left; lia)).
      exact (KEEPV mem (ms_mem msB) KB a Hr Ha). }
    assert (PR2 : forall a, apresent (w_H W) mem a -> apresent (w_H W) mem2 a)
      by (intros a Hp; apply Hpres2; exact (PRB a Hp)).
    assert (HraB : raZ (ms_regs msB) = 0x96d84).
    { unfold raZ. rewrite RA1. apply unsigned_lit_small. lia. }
    jafter_call HS0 40%nat regs2 (mrestrict (w_H W) mem2) HP2 HS2.
    match type of HS2 with ?t -> _ => assert (HRK : t); [|specialize (HS2 HRK); clear HRK] end.
    { cbn [ms_mem restrict].
      repeat apply Forall_cons; try apply Forall_nil; split;
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val];
        rewrite ?Usp, ?Uf, ?Utp.
      - intros a Ha. apply mbyte_of_aview.
        apply (Hfr2 a ltac:(lia) ltac:(rewrite HSZ in Dlen; lia) ltac:(rewrite HspB; lia)).
      - intros a Ha _. apply apresent_writable. apply Hpres2. apply PRB. apply HPRES.
        unfold AMW0_STK, ESTACK. lia.
      - intros a Ha. apply mbyte_of_aview.
        apply (Hfr2 a ltac:(unfold AMF_BLOCK in *; lia)
                 ltac:(rewrite HSZ in Dlen; unfold AMF_BLOCK in *; lia)
                 ltac:(rewrite HspB; unfold AMF_BLOCK in *; lia)).
      - intros a Ha _. apply apresent_writable. apply Hpres2. apply PRB.
        apply (proj1 (Hfpres a ltac:(unfold AMF_BLOCK in *; lia))).
      - intros a Ha. rewrite Hterr in Ha. apply mbyte_of_aview.
        apply (Hfr2 a ltac:(lia) ltac:(rewrite HSZ in Dlen; lia) ltac:(rewrite HspB; lia)).
      - intros a Ha _. rewrite Hterr in Ha. apply mw_errno_writable. lia. }
    clear HS0. rewrite <- restrict_mkst_fx in HS2.
    set (Ev := havoc E 40 (map (getr regs2) CLOB)) in *.
    assert (OLD3 : forall i, (i < 40)%nat -> ew Ev i = ew E i)
      by (intros i Hi; unfold Ev; apply ew_havoc_old; exact Hi).
    assert (Usp3 : bv_unsigned (ew Ev 2) = sp0) by (rewrite (OLD3 2%nat ltac:(lia)); exact Usp).
    assert (Uf3 : bv_unsigned (ew Ev 10) = f) by (rewrite (OLD3 10%nat ltac:(lia)); exact Uf).
    assert (Utp3 : bv_unsigned (ew Ev 4) = as_tp B) by (rewrite (OLD3 4%nat ltac:(lia)); exact Utp).
    assert (E1v : ew Ev 1 = getr regs 1) by (rewrite (OLD3 1%nat ltac:(lia)); exact E1).
    assert (E12v : ew Ev 12 = Z_to_bv 64 n) by (rewrite (OLD3 12%nat ltac:(lia)); exact E12).
    assert (E32v : ew Ev 32 = Z_to_bv 64 wpos) by (rewrite (OLD3 32%nat ltac:(lia)); exact E32).
    assert (E33v : ew Ev 33 = Z_to_bv 64 fl) by (rewrite (OLD3 33%nat ltac:(lia)); exact E33).
    assert (E34v : ew Ev 34 = Z_to_bv 64 pos) by (rewrite (OLD3 34%nat ltac:(lia)); exact E34).
    assert (E35v : ew Ev 35 = Z_to_bv 64 len) by (rewrite (OLD3 35%nat ltac:(lia)); exact E35).
    assert (E36v : ew Ev 36 = Z_to_bv 64 wend) by (rewrite (OLD3 36%nat ltac:(lia)); exact E36).
    assert (E37v : ew Ev 37 = Z_to_bv 64 om) by (rewrite (OLD3 37%nat ltac:(lia)); exact E37).
    assert (HAEv : YP06.env_agree 32 (Ereg regs extra) Ev)
      by (unfold Ev; apply env_agree_havoc_ge; [cbv; lia | apply YP06.env_agree_refl]).
    assert (UADD : U Ev (SAlu ALU_ADD (SOff 12 0) (SOff 34 0)) = n + pos).
    { rewrite U_SAlu. cbn [zalu_raw].
      rewrite (U_atom Ev 12 n E12v ltac:(lia)), (U_atom Ev 34 pos E34v ltac:(lia)).
      apply zcanon_id. unfold M64. rewrite HSZ in Dlen. lia. }
    assert (Ulen3 : U Ev (SOff 35 0) = len) by (apply (U_atom Ev 35 len E35v); rewrite HSZ in Dlen; lia).
    unfold cfg_at. rewrite HraB.
    mwrun HS2 msC matC HFC HFrC HGC.
    srr_branch_with tbl_mw_ok HS2.
    + (* len >= pos + n: the cookie's len does not move *)
      rewrite branch_geu_U, Ulen3, UADD in Hc. apply negb_true_iff, Z.ltb_ge in Hc.
      mwrun HS2 msF matF HFF HFrF HGF.
      assert (AVF : forall a, 0 <= a < 2 ^ 64 ->
                 ~ (sp0 - 48 <= a < sp0) -> ~ (f <= a < f + 248) ->
                 ~ (as_tp B - 164 <= a < as_tp B - 160) ->
                 aview tfibsegs (w_H W) (ms_mem msF) a = aview tfibsegs (w_H W) mem2 a).
      { intros a Hr G1 G2 G3.
        assert (Q1 : mrestrict (w_H W) (ms_mem msF) (Z_to_bv 64 a)
                     = mrestrict (w_H W) (ms_mem msC) (Z_to_bv 64 a)).
        { apply HFrF. rewrite unsigned_lit_small by lia. intros Hin.
          assert (HWX : (sp0 - 48 <= a < sp0) \/ (f <= a < f + 248) \/
                        (as_tp B - 164 <= a < as_tp B - 160))
            by (refine (WINX Ev _ _ Usp3 Uf3 Utp3 _ Hin); vm_compute; reflexivity).
          destruct HWX as [Z1|[Z2|Z3]]; [exact (G1 Z1) | exact (G2 Z2) | exact (G3 Z3)]. }
        assert (Q2 : mrestrict (w_H W) (ms_mem msC) (Z_to_bv 64 a)
                     = mrestrict (w_H W) mem2 (Z_to_bv 64 a)).
        { apply HFrC. rewrite unsigned_lit_small by lia. intros Hin.
          assert (HWX : (sp0 - 48 <= a < sp0) \/ (f <= a < f + 248) \/
                        (as_tp B - 164 <= a < as_tp B - 160))
            by (refine (WINX Ev _ _ Usp3 Uf3 Utp3 _ Hin); vm_compute; reflexivity).
          destruct HWX as [Z1|[Z2|Z3]]; [exact (G1 Z1) | exact (G2 Z2) | exact (G3 Z3)]. }
        apply aview_eq_of. rewrite Q1, Q2. reflexivity. }
      assert (KF3 : forall xw : word, ~ mw_set sp0 f (bv_unsigned xw) -> ms_mem msF xw = mem2 xw).
      { intros xw Hx.
        assert (Q1 : ms_mem msF xw = ms_mem msC xw).
        { apply HFF. intros Hin. refine (Hx (WIN Ev _ _ Usp3 Uf3 Utp3 _ Hin)). vm_compute; reflexivity. }
        assert (Q2 : ms_mem msC xw = mem2 xw).
        { apply HFC. intros Hin. refine (Hx (WIN Ev _ _ Usp3 Uf3 Utp3 _ Hin)). vm_compute; reflexivity. }
        rewrite Q1, Q2. reflexivity. }
      assert (GF3 : forall xw : word, w_H W xw = false -> mem2 xw <> None -> ms_mem msF xw <> None)
        by (intros xw Hh Hne; apply (HGF xw Hh); apply (HGC xw Hh); exact Hne).
      assert (ARF : forall mt, AR tfibsegs B ly S W (ms_mem msF) (with_vm_backing (m_vm_lazy md2) mt md2))
        by (intros mt;
            apply (ARSTEP mem2 (ms_mem msF) md2 _ HAR2 (with_vm_backing_same md2 mt) KF3 GF3)).
      assert (SBMF : forall mt, same_but_materialized md (with_vm_backing (m_vm_lazy md2) mt md2)).
      { intros mt. eapply same_but_materialized_trans; [apply with_vm_backing_same|].
        eapply same_but_materialized_trans; [exact Hsbm2 | apply with_vm_backing_same]. }
      assert (Hlen4 : len <= 4096) by (rewrite HSZ in Dlen; exact Dlen).
      assert (AREGSF : aregs_preserved regs (ms_regs msF))
        by (exact (aregs_preserved_of_st_ok _ Ev _ _ regs extra HS2 HAEv
                     ltac:(vm_compute; reflexivity))).
      rreg HS2 (1%bv : bv 5) RF1. rreg HS2 (10%bv : bv 5) RF10.
      assert (RET10 : getr (ms_regs msF) 10 = w64 n) by (rewrite RF10, E12v; reflexivity).
      (* the FILE cells of the final state, from its chunks *)
      pose proof (st_ok_mem_ok tfibsegs Ev _ _ HS2) as HMO. destruct HMO as (_ & Hrs & _).
      cbn [ms_mem restrict] in Hrs.
      lazymatch type of Hrs with Forall _ (ss_mem ?s) =>
        let l := eval vm_compute in (ss_mem s) in change (ss_mem s) with l in Hrs end.
      pose proof (Forall_inv (Forall_inv_tail Hrs)) as HRF.
      unfold region_ok in HRF. cbn [YP09.r_base YP09.r_chunks base_val] in HRF.
      destruct HRF as (_ & _ & _ & Hcs). rewrite Uf3 in Hcs.
      assert (HSC : Forall (YP09.chunk_ok tfibsegs Ev (mrestrict (w_H W) (ms_mem msF)) f)
                      mw_static_chunks).
      { apply Forall_forall. intros cc Hcc. apply (proj1 (Forall_forall _ _) Hcs cc).
        unfold mw_static_chunks in Hcc. cbn [In] in Hcc.
        repeat (destruct Hcc as [Hcc|Hcc]; [subst cc; inlist|]). destruct Hcc. }
      assert (V0 : val_mem tfibsegs (mrestrict (w_H W) (ms_mem msF)) (f + 0) 4 fl).
      { apply (val_of_chunk_ok tfibsegs Ev _ f 0 4%N (SOff 33 0) fl);
        [apply (proj1 (Forall_forall _ _) Hcs); inlist
        | rewrite denot_lit_U, (U_atom Ev 33 fl E33v ltac:(lia)); reflexivity | zside | zside]. }
      assert (V32 : val_mem tfibsegs (mrestrict (w_H W) (ms_mem msF)) (f + 32) 8 wend).
      { apply (val_of_chunk_ok tfibsegs Ev _ f 32 8%N (SOff 36 0) wend);
        [apply (proj1 (Forall_forall _ _) Hcs); inlist
        | rewrite denot_lit_U, (U_atom Ev 36 wend E36v ltac:(lia)); reflexivity | zside | zside]. }
      assert (V40 : val_mem tfibsegs (mrestrict (w_H W) (ms_mem msF)) (f + 40) 8 wpos).
      { apply (val_of_chunk_ok tfibsegs Ev _ f 40 8%N (SOff 32 0) wpos);
        [apply (proj1 (Forall_forall _ _) Hcs); inlist
        | rewrite denot_lit_U, (U_atom Ev 32 wpos E32v ltac:(lia)); reflexivity | zside | zside]. }
      assert (V56 : val_mem tfibsegs (mrestrict (w_H W) (ms_mem msF)) (f + 56) 8 wpos).
      { apply (val_of_chunk_ok tfibsegs Ev _ f 56 8%N (SOff 32 0) wpos);
        [apply (proj1 (Forall_forall _ _) Hcs); inlist
        | rewrite denot_lit_U, (U_atom Ev 32 wpos E32v ltac:(lia)); reflexivity | zside | zside]. }
      assert (V136 : val_mem tfibsegs (mrestrict (w_H W) (ms_mem msF)) (f + 136) 4 om).
      { apply (val_of_chunk_ok tfibsegs Ev _ f 136 4%N (SOff 37 0) om);
        [apply (proj1 (Forall_forall _ _) Hcs); inlist
        | rewrite denot_lit_U, (U_atom Ev 37 om E37v ltac:(lia)); reflexivity | zside | zside]. }
      assert (V232 : val_mem tfibsegs (mrestrict (w_H W) (ms_mem msF)) (f + 232) 8 (n + pos)).
      { apply (val_of_chunk_ok tfibsegs Ev _ f 232 8%N
                 (SAlu ALU_ADD (SOff 12 0) (SOff 34 0)) (n + pos));
        [apply (proj1 (Forall_forall _ _) Hcs); inlist
        | rewrite denot_lit_U, UADD; reflexivity | rewrite HSZ in Dlen; zside | zside]. }
      assert (V240 : val_mem tfibsegs (mrestrict (w_H W) (ms_mem msF)) (f + 240) 8 len).
      { apply (val_of_chunk_ok tfibsegs Ev _ f 240 8%N (SOff 35 0) len);
        [apply (proj1 (Forall_forall _ _) Hcs); inlist
        | rewrite denot_lit_U, (U_atom Ev 35 len E35v ltac:(rewrite HSZ in Dlen; lia)); reflexivity
        | rewrite HSZ in Dlen; zside | zside]. }
      assert (MFK : amf_k tfibsegs link_amf (mrestrict (w_H W) (ms_mem msF)) f 0).
      { apply (MKAT Ev _ fl wend wpos wpos (n + pos) len Uf3 E37v HSC V0 V32 V40 V56 V232 V240 Hfl2);
        [ destruct HWSHAPE as [(Q1 & Q2)|(Q1 & Q2)]; [left | right]; repeat split; lia
        | rewrite HSZ in Dlen; lia | lia ]. }
      assert (HMX : Z.max len (pos + n) = len) by lia.
      assert (DYNF : amf_dyn tfibsegs link_amf (mrestrict (w_H W) (ms_mem msF)) f fl om wend wpos wpos
                       (pos + n) (Z.max len (pos + n))).
      { rewrite HMX. unfold amf_dyn.
        split; [exact Dfl|]. split; [exact Dom|]. split; [exact Dwend|]. split; [exact Dwpos|].
        split; [exact Dwpos|].
        split; [lia|]. split; [exact Dlen|].
        split; [exact V0|]. split; [exact V136|]. split; [exact V32|]. split; [exact V40|].
        split; [exact V56|].
        split; [replace (pos + n) with (n + pos) by lia; exact V232 | exact V240]. }
      assert (AZF : azbytes tfibsegs (mrestrict (w_H W) (ms_mem msF)) (amf_buf link_amf + pos)
                      (firstn (Z.to_nat n) ds)).
      { intros i Hi.
        assert (Hil : (i < Z.to_nat n)%nat)
          by (rewrite firstn_length_le in Hi by (unfold n in *; lia); exact Hi).
        rewrite (mw_nth_firstn Z 0 (Z.to_nat n) ds i Hil).
        change (amf_rd tfibsegs (mrestrict (w_H W) (ms_mem msF)) (amf_buf link_amf + pos + Z.of_nat i))
          with (aview tfibsegs (w_H W) (ms_mem msF) (amf_buf link_amf + pos + Z.of_nat i)).
        rewrite HB.
        rewrite (AVF (0x62fee0 + pos + Z.of_nat i) ltac:(rewrite HSZ in Dlen; lia)
                   ltac:(lia) ltac:(unfold AMF_BLOCK in *; lia) ltac:(rewrite Hterr; lia)).
        rewrite (Hcpy (Z.of_nat i) ltac:(lia)).
        rewrite (KEEPV mem (ms_mem msB) KB (x + Z.of_nat i) ltac:(lia)
                   (HSEPM (x + Z.of_nat i) ltac:(lia))).
        pose proof (HZB i ltac:(unfold n in *; lia)) as HB2.
        change (amf_rd tfibsegs (mrestrict (w_H W) mem) (x + Z.of_nat i))
          with (aview tfibsegs (w_H W) mem (x + Z.of_nat i)) in HB2.
        exact HB2. }
      (* the return *)
      eapply (SRr_ret_at tfibsegs tbl_mw tbl_mw_ok Hwx W Ev);
        [exact HS2 | reflexivity | vm_compute; reflexivity |].
      intros matG. rewrite wvb_collapse.
      replace (v_jalr (getr (ms_regs msF) 1) 0) with (w64 (raZ regs))
        by (rewrite RF1, E1v; unfold raZ, w64; rewrite Z_to_bv_bv_unsigned; symmetry; exact Hra).
      split; [reflexivity|].
      exists (ms_regs msF), (ms_mem msF), (with_vm_backing (m_vm_lazy md2) matG md2).
      cbv zeta.
      split; [reflexivity|].
      split; [exact (ARF matG)|].
      split; [exact AREGSF|].
      split; [exact (SBMF matG)|].
      split; [exact MFK|].
      split; [intros i Hi; cbn in Hi; lia|].
      split; [intros Hlt; exfalso; unfold amf_n1 in Hlt; rewrite HSZ in Hlt; lia|].
      split.
      { intros _.
        assert (HN2 : amw_n2 link_amf 0 pos n = n).
        { unfold amw_n2, amw_pos1, amf_n1. rewrite HSZ.
          replace (Z.min 0 (4096 - pos)) with 0 by lia.
          replace (pos + 0) with pos by lia. lia. }
        assert (HP1 : amw_pos1 link_amf 0 pos = pos).
        { unfold amw_pos1, amf_n1. rewrite HSZ. lia. }
        rewrite HN2, HP1. split; [exact RET10|]. split.
        - exists fl, wend, wpos, wpos. split; [exact DYNF|].
          split; [intros Hlt; exfalso; lia|].
          intros _. split; [reflexivity|]. split; [reflexivity|].
          split; [exact Hwpb | exact Hwpb].
        - rewrite app_nil_l. exact AZF. }
      split.
      { intros a Hr G1 G2 G3 G4.
        rewrite (AVF a Hr ltac:(unfold AMW0_STK, ESTACK in G1; lia)
                   ltac:(unfold AMF_ZEROED in G2; lia)
                   ltac:(rewrite Hterr; rewrite Herr in G4; lia)).
        apply AV2; [exact Hr|]. intros [Z1|[Z2|[Z3|Z4]]];
          [ apply G1; unfold AMW0_STK, ESTACK; lia
          | apply G2; unfold AMF_ZEROED; lia
          | apply G3; rewrite HB, HSZ; lia
          | apply G4; rewrite Herr; lia]. }
      split.
      { intros a Hp. apply (PRESTEP mem2 (ms_mem msF) GF3). apply PR2. exact Hp. }
      { intros a Ha. apply (PRESTEP mem2 (ms_mem msF) GF3). apply PR2. apply HPRES. exact Ha. }
    + (* len < pos + n: the cookie's len moves to pos + n *)
      rewrite branch_geu_U, Ulen3, UADD in Hc. apply negb_false_iff, Z.ltb_lt in Hc.
      rename Hc into Hlen.
      mwrun HS2 msD matD HFD HFrD HGD.
      srr_branch_with tbl_mw_ok HS2.
      * (* pos + n >= size: the NUL is not written *)
        rewrite branch_geu_U, UADD, (U_lit Ev 4096 ltac:(lia)) in Hc.
        apply negb_true_iff, Z.ltb_ge in Hc.
        mwrun HS2 msF matF HFF HFrF HGF.
        assert (AVF : forall a, 0 <= a < 2 ^ 64 ->
                   ~ (sp0 - 48 <= a < sp0) -> ~ (f <= a < f + 248) ->
                   ~ (as_tp B - 164 <= a < as_tp B - 160) ->
                   aview tfibsegs (w_H W) (ms_mem msF) a = aview tfibsegs (w_H W) mem2 a).
        { intros a Hr G1 G2 G3.
          assert (HOUT : forall (ma mb : word -> option byte) ssx,
                    frame_of Ev (ss_mem ssx) ma mb ->
                    windows (ss_mem ssx) = windows (ss_mem ss_mw) ->
                    mb (Z_to_bv 64 a) = ma (Z_to_bv 64 a)).
          { intros ma mb ssx Hfr Hw. apply Hfr. rewrite unsigned_lit_small by lia. intros Hin.
            destruct (WINX Ev ssx a Usp3 Uf3 Utp3 Hw Hin) as [Z1|[Z2|Z3]];
              [exact (G1 Z1) | exact (G2 Z2) | exact (G3 Z3)]. }
          apply aview_eq_of.
          rewrite (HOUT _ _ _ HFrF ltac:(vm_compute; reflexivity)).
          rewrite (HOUT _ _ _ HFrD ltac:(vm_compute; reflexivity)).
          rewrite (HOUT _ _ _ HFrC ltac:(vm_compute; reflexivity)). reflexivity. }
        assert (KF3 : forall xw : word, ~ mw_set sp0 f (bv_unsigned xw) -> ms_mem msF xw = mem2 xw).
        { intros xw Hx.
          assert (Q1 : ms_mem msF xw = ms_mem msD xw).
          { apply HFF. intros Hin. refine (Hx (WIN Ev _ _ Usp3 Uf3 Utp3 _ Hin)). vm_compute; reflexivity. }
          assert (Q2 : ms_mem msD xw = ms_mem msC xw).
          { apply HFD. intros Hin. refine (Hx (WIN Ev _ _ Usp3 Uf3 Utp3 _ Hin)). vm_compute; reflexivity. }
          assert (Q3 : ms_mem msC xw = mem2 xw).
          { apply HFC. intros Hin. refine (Hx (WIN Ev _ _ Usp3 Uf3 Utp3 _ Hin)). vm_compute; reflexivity. }
          rewrite Q1, Q2, Q3. reflexivity. }
        assert (GF3 : forall xw : word, w_H W xw = false -> mem2 xw <> None -> ms_mem msF xw <> None)
          by (intros xw Hh Hne; apply (HGF xw Hh); apply (HGD xw Hh); apply (HGC xw Hh); exact Hne).
        assert (ARF : forall mt, AR tfibsegs B ly S W (ms_mem msF)
                                   (with_vm_backing (m_vm_lazy md2) mt md2))
          by (intros mt;
              apply (ARSTEP mem2 (ms_mem msF) md2 _ HAR2 (with_vm_backing_same md2 mt) KF3 GF3)).
        assert (SBMF : forall mt, same_but_materialized md (with_vm_backing (m_vm_lazy md2) mt md2)).
        { intros mt. eapply same_but_materialized_trans; [apply with_vm_backing_same|].
          eapply same_but_materialized_trans; [exact Hsbm2 | apply with_vm_backing_same]. }
        assert (Hlen4 : len <= 4096) by (rewrite HSZ in Dlen; exact Dlen).
        assert (AREGSF : aregs_preserved regs (ms_regs msF))
          by (exact (aregs_preserved_of_st_ok _ Ev _ _ regs extra HS2 HAEv
                       ltac:(vm_compute; reflexivity))).
        rreg HS2 (1%bv : bv 5) RF1. rreg HS2 (10%bv : bv 5) RF10.
        assert (RET10 : getr (ms_regs msF) 10 = w64 n) by (rewrite RF10, E12v; reflexivity).
        pose proof (st_ok_mem_ok tfibsegs Ev _ _ HS2) as HMO. destruct HMO as (_ & Hrs & _).
        cbn [ms_mem restrict] in Hrs.
        lazymatch type of Hrs with Forall _ (ss_mem ?s) =>
          let l := eval vm_compute in (ss_mem s) in change (ss_mem s) with l in Hrs end.
        pose proof (Forall_inv (Forall_inv_tail Hrs)) as HRF.
        unfold region_ok in HRF. cbn [YP09.r_base YP09.r_chunks base_val] in HRF.
        destruct HRF as (_ & _ & _ & Hcs). rewrite Uf3 in Hcs.
        assert (HSC : Forall (YP09.chunk_ok tfibsegs Ev (mrestrict (w_H W) (ms_mem msF)) f)
                        mw_static_chunks).
        { apply Forall_forall. intros cc Hcc. apply (proj1 (Forall_forall _ _) Hcs cc).
          unfold mw_static_chunks in Hcc. cbn [In] in Hcc.
          repeat (destruct Hcc as [Hcc|Hcc]; [subst cc; inlist|]). destruct Hcc. }
        assert (V0 : val_mem tfibsegs (mrestrict (w_H W) (ms_mem msF)) (f + 0) 4 fl).
        { apply (val_of_chunk_ok tfibsegs Ev _ f 0 4%N (SOff 33 0) fl);
          [apply (proj1 (Forall_forall _ _) Hcs); inlist
          | rewrite denot_lit_U, (U_atom Ev 33 fl E33v ltac:(lia)); reflexivity | zside | zside]. }
        assert (V32 : val_mem tfibsegs (mrestrict (w_H W) (ms_mem msF)) (f + 32) 8 wend).
        { apply (val_of_chunk_ok tfibsegs Ev _ f 32 8%N (SOff 36 0) wend);
          [apply (proj1 (Forall_forall _ _) Hcs); inlist
          | rewrite denot_lit_U, (U_atom Ev 36 wend E36v ltac:(lia)); reflexivity | zside | zside]. }
        assert (V40 : val_mem tfibsegs (mrestrict (w_H W) (ms_mem msF)) (f + 40) 8 wpos).
        { apply (val_of_chunk_ok tfibsegs Ev _ f 40 8%N (SOff 32 0) wpos);
          [apply (proj1 (Forall_forall _ _) Hcs); inlist
          | rewrite denot_lit_U, (U_atom Ev 32 wpos E32v ltac:(lia)); reflexivity | zside | zside]. }
        assert (V56 : val_mem tfibsegs (mrestrict (w_H W) (ms_mem msF)) (f + 56) 8 wpos).
        { apply (val_of_chunk_ok tfibsegs Ev _ f 56 8%N (SOff 32 0) wpos);
          [apply (proj1 (Forall_forall _ _) Hcs); inlist
          | rewrite denot_lit_U, (U_atom Ev 32 wpos E32v ltac:(lia)); reflexivity | zside | zside]. }
        assert (V136 : val_mem tfibsegs (mrestrict (w_H W) (ms_mem msF)) (f + 136) 4 om).
        { apply (val_of_chunk_ok tfibsegs Ev _ f 136 4%N (SOff 37 0) om);
          [apply (proj1 (Forall_forall _ _) Hcs); inlist
          | rewrite denot_lit_U, (U_atom Ev 37 om E37v ltac:(lia)); reflexivity | zside | zside]. }
        assert (V232 : val_mem tfibsegs (mrestrict (w_H W) (ms_mem msF)) (f + 232) 8 (n + pos)).
        { apply (val_of_chunk_ok tfibsegs Ev _ f 232 8%N
                   (SAlu ALU_ADD (SOff 12 0) (SOff 34 0)) (n + pos));
          [apply (proj1 (Forall_forall _ _) Hcs); inlist
          | rewrite denot_lit_U, UADD; reflexivity | zside | zside]. }
        assert (V240 : val_mem tfibsegs (mrestrict (w_H W) (ms_mem msF)) (f + 240) 8 (n + pos)).
        { apply (val_of_chunk_ok tfibsegs Ev _ f 240 8%N
                   (SAlu ALU_ADD (SOff 12 0) (SOff 34 0)) (n + pos));
          [apply (proj1 (Forall_forall _ _) Hcs); inlist
          | rewrite denot_lit_U, UADD; reflexivity | zside | zside]. }
        assert (MFK : amf_k tfibsegs link_amf (mrestrict (w_H W) (ms_mem msF)) f 0).
        { apply (MKAT Ev _ fl wend wpos wpos (n + pos) (n + pos) Uf3 E37v HSC V0 V32 V40 V56 V232 V240
                   Hfl2);
          [ destruct HWSHAPE as [(Q1 & Q2)|(Q1 & Q2)]; [left | right]; repeat split; lia
          | lia | rewrite HSZ; lia ]. }
        assert (HMX : Z.max len (pos + n) = pos + n) by lia.
        assert (DYNF : amf_dyn tfibsegs link_amf (mrestrict (w_H W) (ms_mem msF)) f fl om wend wpos wpos
                         (pos + n) (Z.max len (pos + n))).
        { rewrite HMX. unfold amf_dyn.
          split; [exact Dfl|]. split; [exact Dom|]. split; [exact Dwend|]. split; [exact Dwpos|].
          split; [exact Dwpos|].
          split; [lia|]. split; [rewrite HSZ; lia|].
          split; [exact V0|]. split; [exact V136|]. split; [exact V32|]. split; [exact V40|].
          split; [exact V56|].
          split; replace (pos + n) with (n + pos) by lia; [exact V232 | exact V240]. }
        assert (AZF : azbytes tfibsegs (mrestrict (w_H W) (ms_mem msF)) (amf_buf link_amf + pos)
                        (firstn (Z.to_nat n) ds)).
        { intros i Hi.
          assert (Hil : (i < Z.to_nat n)%nat)
            by (rewrite firstn_length_le in Hi by (unfold n in *; lia); exact Hi).
          rewrite (mw_nth_firstn Z 0 (Z.to_nat n) ds i Hil).
          change (amf_rd tfibsegs (mrestrict (w_H W) (ms_mem msF))
                    (amf_buf link_amf + pos + Z.of_nat i))
            with (aview tfibsegs (w_H W) (ms_mem msF) (amf_buf link_amf + pos + Z.of_nat i)).
          rewrite HB.
          rewrite (AVF (0x62fee0 + pos + Z.of_nat i) ltac:(lia)
                     ltac:(lia) ltac:(unfold AMF_BLOCK in *; lia) ltac:(rewrite Hterr; lia)).
          rewrite (Hcpy (Z.of_nat i) ltac:(lia)).
          rewrite (KEEPV mem (ms_mem msB) KB (x + Z.of_nat i) ltac:(lia)
                     (HSEPM (x + Z.of_nat i) ltac:(lia))).
          pose proof (HZB i ltac:(unfold n in *; lia)) as HB2.
          change (amf_rd tfibsegs (mrestrict (w_H W) mem) (x + Z.of_nat i))
            with (aview tfibsegs (w_H W) mem (x + Z.of_nat i)) in HB2.
          exact HB2. }
        eapply (SRr_ret_at tfibsegs tbl_mw tbl_mw_ok Hwx W Ev);
          [exact HS2 | reflexivity | vm_compute; reflexivity |].
        intros matG. rewrite wvb_collapse.
        replace (v_jalr (getr (ms_regs msF) 1) 0) with (w64 (raZ regs))
          by (rewrite RF1, E1v; unfold raZ, w64; rewrite Z_to_bv_bv_unsigned; symmetry; exact Hra).
        split; [reflexivity|].
        exists (ms_regs msF), (ms_mem msF), (with_vm_backing (m_vm_lazy md2) matG md2).
        cbv zeta.
        split; [reflexivity|].
        split; [exact (ARF matG)|].
        split; [exact AREGSF|].
        split; [exact (SBMF matG)|].
        split; [exact MFK|].
        split; [intros i Hi; cbn in Hi; lia|].
        split; [intros Hlt; exfalso; unfold amf_n1 in Hlt; rewrite HSZ in Hlt; lia|].
        split.
        { intros _.
          assert (HN2 : amw_n2 link_amf 0 pos n = n).
          { unfold amw_n2, amw_pos1, amf_n1. rewrite HSZ.
            replace (Z.min 0 (4096 - pos)) with 0 by lia.
            replace (pos + 0) with pos by lia. lia. }
          assert (HP1 : amw_pos1 link_amf 0 pos = pos).
          { unfold amw_pos1, amf_n1. rewrite HSZ. lia. }
          rewrite HN2, HP1. split; [exact RET10|]. split.
          - exists fl, wend, wpos, wpos. split; [exact DYNF|].
            split; [intros Hlt; exfalso; lia|].
            intros _. split; [reflexivity|]. split; [reflexivity|].
            split; [exact Hwpb | exact Hwpb].
          - rewrite app_nil_l. exact AZF. }
        split.
        { intros a Hr G1 G2 G3 G4.
          rewrite (AVF a Hr ltac:(unfold AMW0_STK, ESTACK in G1; lia)
                     ltac:(unfold AMF_ZEROED in G2; lia)
                     ltac:(rewrite Hterr; rewrite Herr in G4; lia)).
          apply AV2; [exact Hr|]. intros [Z1|[Z2|[Z3|Z4]]];
            [ apply G1; unfold AMW0_STK, ESTACK; lia
            | apply G2; unfold AMF_ZEROED; lia
            | apply G3; rewrite HB, HSZ; lia
            | apply G4; rewrite Herr; lia]. }
        split.
        { intros a Hp. apply (PRESTEP mem2 (ms_mem msF) GF3). apply PR2. exact Hp. }
        { intros a Ha. apply (PRESTEP mem2 (ms_mem msF) GF3). apply PR2. apply HPRES. exact Ha. }
      * (* pos + n < size: the NUL goes to c->buf + c->pos, inside g_said *)
        rewrite branch_geu_U, UADD, (U_lit Ev 4096 ltac:(lia)) in Hc.
        apply negb_false_iff, Z.ltb_lt in Hc.
        mwrun HS2 msN matN HFN HFrN HGN.
        pose proof (st_ok_restrict_reg tfibsegs (w_H W) Ev _ _ (10%bv : bv 5) HS2) as RG10.
        lazymatch type of RG10 with _ = sv_denot _ ?t =>
          let e := eval vm_compute in t in change t with e in RG10 end.
        rewrite denot_lit_U in RG10.
        assert (UNUL : U Ev (SAlu ALU_ADD (SOff 12 6487776) (SOff 34 0)) = 0x62fee0 + n + pos).
        { rewrite U_SAlu. cbn [zalu_raw].
          rewrite (U_atom_off Ev 12 n 6487776 E12v ltac:(lia) ltac:(lia)),
                  (U_atom Ev 34 pos E34v ltac:(lia)).
          rewrite zcanon_id by (unfold M64; lia). lia. }
        rewrite UNUL in RG10.
        set (Ew := havoc Ev 56 [Z_to_bv 64 (0x62fee0 + n + pos)]).
        assert (OLDW : forall i, (i < 56)%nat -> ew Ew i = ew Ev i)
          by (intros i Hi; unfold Ew; apply ew_havoc_old; exact Hi).
        assert (E56 : ew Ew 56 = Z_to_bv 64 (0x62fee0 + n + pos)).
        { change (ew Ew 56) with (ew Ew (56 + 0)%nat). unfold Ew.
          rewrite (ew_havoc_new Ev 56 _ 0 (Z_to_bv 64 0)) by (cbn; lia). reflexivity. }
        pose proof (st_ok_agree_on tfibsegs (fun i => (i <? 56)%nat) Ev Ew _ _ HS2
                      ltac:(intros i Hi; apply OLDW; apply Nat.ltb_lt; exact Hi)
                      ltac:(vm_compute; reflexivity)) as HSw.
        pose proof (st_ok_set_reg tfibsegs Ew _ _ (10%bv : bv 5) (SOff 56 0) HSw
                      ltac:(intros Hq; discriminate Hq)
                      ltac:(cbn [ms_regs restrict]; rewrite RG10; cbn [sv_denot]; rewrite E56;
                            rewrite unsigned_lit_small by lia; rewrite Z.add_0_r; reflexivity)) as HSp.
        pose proof (st_ok_add_region' tfibsegs Ew _ _ (YP09.mkRegion (Some 56%nat) 0 1 0 1 []) HSp
                      ltac:(vm_compute; reflexivity)
                      ltac:(unfold region_ok;
                            cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi
                                 YP09.r_chunks base_val];
                            rewrite E56; rewrite unsigned_lit_small by lia;
                            split; [lia|]; split; [lia|]; split; [|apply Forall_nil];
                            intros o Ho; apply mw_said_writable; lia)
                      ltac:(lazymatch goal with |- all_disjoint _ _ ?rs =>
                              let l := eval vm_compute in rs in change rs with l end;
                            cbn [all_disjoint]; repeat split;
                            unfold extent_disjoint;
                            cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
                            rewrite E56; rewrite unsigned_lit_small by lia;
                            rewrite ?(OLDW 2%nat ltac:(lia)), ?(OLDW 10%nat ltac:(lia)),
                                    ?(OLDW 4%nat ltac:(lia));
                            rewrite ?Usp3, ?Uf3, ?Utp3, ?Hterr;
                            [ left; lia
                            | destruct Hfimg as [Hq|Hq]; [right | left];
                              unfold AMF_BLOCK in Hq; lia
                            | left; lia ])) as HSr.
        clear HS2 HSw HSp.
        mwrun HSr msF matF HFF HFrF HGF.
        assert (Uspw : bv_unsigned (ew Ew 2) = sp0) by (rewrite (OLDW 2%nat ltac:(lia)); exact Usp3).
        assert (Ufw : bv_unsigned (ew Ew 10) = f) by (rewrite (OLDW 10%nat ltac:(lia)); exact Uf3).
        assert (Utpw : bv_unsigned (ew Ew 4) = as_tp B)
          by (rewrite (OLDW 4%nat ltac:(lia)); exact Utp3).
        assert (E1w : ew Ew 1 = getr regs 1) by (rewrite (OLDW 1%nat ltac:(lia)); exact E1v).
        assert (E12w : ew Ew 12 = Z_to_bv 64 n) by (rewrite (OLDW 12%nat ltac:(lia)); exact E12v).
        assert (E32w : ew Ew 32 = Z_to_bv 64 wpos) by (rewrite (OLDW 32%nat ltac:(lia)); exact E32v).
        assert (E33w : ew Ew 33 = Z_to_bv 64 fl) by (rewrite (OLDW 33%nat ltac:(lia)); exact E33v).
        assert (E34w : ew Ew 34 = Z_to_bv 64 pos) by (rewrite (OLDW 34%nat ltac:(lia)); exact E34v).
        assert (E35w : ew Ew 35 = Z_to_bv 64 len) by (rewrite (OLDW 35%nat ltac:(lia)); exact E35v).
        assert (E36w : ew Ew 36 = Z_to_bv 64 wend) by (rewrite (OLDW 36%nat ltac:(lia)); exact E36v).
        assert (E37w : ew Ew 37 = Z_to_bv 64 om) by (rewrite (OLDW 37%nat ltac:(lia)); exact E37v).
        assert (Unulw : bv_unsigned (ew Ew 56) = 0x62fee0 + n + pos)
          by (rewrite E56; apply unsigned_lit_small; lia).
        assert (HAEw : YP06.env_agree 32 (Ereg regs extra) Ew)
          by (unfold Ew; apply env_agree_havoc_ge; [cbv; lia | exact HAEv]).
        assert (UADDw : U Ew (SAlu ALU_ADD (SOff 12 0) (SOff 34 0)) = n + pos).
        { rewrite U_SAlu. cbn [zalu_raw].
          rewrite (U_atom Ew 12 n E12w ltac:(lia)), (U_atom Ew 34 pos E34w ltac:(lia)).
          apply zcanon_id. unfold M64. lia. }
        assert (WINX4 : forall (ssx : sstate) a,
            windows (ss_mem ssx) = (Some 56%nat, 0, 1) :: windows (ss_mem ss_mw) ->
            in_wrange Ew (ss_mem ssx) a ->
            (sp0 - 48 <= a < sp0) \/ (f <= a < f + 248) \/
            (as_tp B - 164 <= a < as_tp B - 160) \/ a = 0x62fee0 + n + pos).
        { intros ssx a Hw Ha.
          destruct (in_wrange_windows Ew _ a Ha) as (b & lo & hi & Ht & Hr). rewrite Hw in Ht.
          unfold ss_mw, R_mstk, R_mfile, R_merrno in Ht.
          cbn [windows ss_mem map YP09.r_base YP09.r_wlo YP09.r_whi] in Ht.
          destruct Ht as [Hq|[Hq|[Hq|[Hq|[]]]]]; injection Hq as <- <- <-; cbn [base_val] in Hr;
            rewrite ?Uspw, ?Ufw, ?Utpw, ?Unulw in Hr;
            [right; right; right | left | right; left | right; right; left]; lia. }
        assert (AVF : forall a, 0 <= a < 2 ^ 64 ->
                   ~ (sp0 - 48 <= a < sp0) -> ~ (f <= a < f + 248) ->
                   ~ (as_tp B - 164 <= a < as_tp B - 160) -> a <> 0x62fee0 + n + pos ->
                   aview tfibsegs (w_H W) (ms_mem msF) a = aview tfibsegs (w_H W) mem2 a).
        { intros a Hr G1 G2 G3 G5.
          assert (HOUTv : forall (ma mb : word -> option byte) ssx,
                    frame_of Ev (ss_mem ssx) ma mb ->
                    windows (ss_mem ssx) = windows (ss_mem ss_mw) ->
                    mb (Z_to_bv 64 a) = ma (Z_to_bv 64 a)).
          { intros ma mb ssx Hfr Hw. apply Hfr. rewrite unsigned_lit_small by lia. intros Hin.
            destruct (WINX Ev ssx a Usp3 Uf3 Utp3 Hw Hin) as [Z1|[Z2|Z3]];
              [exact (G1 Z1) | exact (G2 Z2) | exact (G3 Z3)]. }
          assert (HOUTw : forall (ma mb : word -> option byte) ssx,
                    frame_of Ew (ss_mem ssx) ma mb ->
                    windows (ss_mem ssx) = (Some 56%nat, 0, 1) :: windows (ss_mem ss_mw) ->
                    mb (Z_to_bv 64 a) = ma (Z_to_bv 64 a)).
          { intros ma mb ssx Hfr Hw. apply Hfr. rewrite unsigned_lit_small by lia. intros Hin.
            destruct (WINX4 ssx a Hw Hin) as [Z1|[Z2|[Z3|Z4]]];
              [exact (G1 Z1) | exact (G2 Z2) | exact (G3 Z3) | exact (G5 Z4)]. }
          apply aview_eq_of.
          rewrite (HOUTw _ _ _ HFrF ltac:(vm_compute; reflexivity)).
          rewrite (HOUTv _ _ _ HFrN ltac:(vm_compute; reflexivity)).
          rewrite (HOUTv _ _ _ HFrD ltac:(vm_compute; reflexivity)).
          rewrite (HOUTv _ _ _ HFrC ltac:(vm_compute; reflexivity)). reflexivity. }
        assert (KF3 : forall xw : word, ~ mw_set sp0 f (bv_unsigned xw) -> ms_mem msF xw = mem2 xw).
        { intros xw Hx.
          assert (Q1 : ms_mem msF xw = ms_mem msN xw).
          { apply HFF. intros Hin.
            assert (HW4 : (sp0 - 48 <= bv_unsigned xw < sp0) \/ (f <= bv_unsigned xw < f + 248) \/
                          (as_tp B - 164 <= bv_unsigned xw < as_tp B - 160) \/
                          bv_unsigned xw = 0x62fee0 + n + pos)
              by (refine (WINX4 _ _ _ Hin); vm_compute; reflexivity).
            apply Hx. unfold mw_set.
            destruct HW4 as [Z1|[Z2|[Z3|Z4]]];
              [left | right; left | right; right; right | right; right; left];
              rewrite ?Hterr in *; unfold AMW0_STK, ESTACK; lia. }
          assert (Q2 : ms_mem msN xw = ms_mem msD xw).
          { apply HFN. intros Hin. refine (Hx (WIN Ev _ _ Usp3 Uf3 Utp3 _ Hin)). vm_compute; reflexivity. }
          assert (Q3 : ms_mem msD xw = ms_mem msC xw).
          { apply HFD. intros Hin. refine (Hx (WIN Ev _ _ Usp3 Uf3 Utp3 _ Hin)). vm_compute; reflexivity. }
          assert (Q4 : ms_mem msC xw = mem2 xw).
          { apply HFC. intros Hin. refine (Hx (WIN Ev _ _ Usp3 Uf3 Utp3 _ Hin)). vm_compute; reflexivity. }
          rewrite Q1, Q2, Q3, Q4. reflexivity. }
        assert (GF3 : forall xw : word, w_H W xw = false -> mem2 xw <> None -> ms_mem msF xw <> None)
          by (intros xw Hh Hne; apply (HGF xw Hh); apply (HGN xw Hh); apply (HGD xw Hh);
              apply (HGC xw Hh); exact Hne).
        assert (ARF : forall mt, AR tfibsegs B ly S W (ms_mem msF)
                                   (with_vm_backing (m_vm_lazy md2) mt md2))
          by (intros mt;
              apply (ARSTEP mem2 (ms_mem msF) md2 _ HAR2 (with_vm_backing_same md2 mt) KF3 GF3)).
        assert (SBMF : forall mt, same_but_materialized md (with_vm_backing (m_vm_lazy md2) mt md2)).
        { intros mt. eapply same_but_materialized_trans; [apply with_vm_backing_same|].
          eapply same_but_materialized_trans; [exact Hsbm2 | apply with_vm_backing_same]. }
        assert (Hlen4 : len <= 4096) by (rewrite HSZ in Dlen; exact Dlen).
        assert (AREGSF : aregs_preserved regs (ms_regs msF))
          by (exact (aregs_preserved_of_st_ok _ Ew _ _ regs extra HSr HAEw
                       ltac:(vm_compute; reflexivity))).
        rreg HSr (1%bv : bv 5) RF1. rreg HSr (10%bv : bv 5) RF10.
        assert (RET10 : getr (ms_regs msF) 10 = w64 n) by (rewrite RF10, E12w; reflexivity).
        pose proof (st_ok_mem_ok tfibsegs Ew _ _ HSr) as HMO. destruct HMO as (_ & Hrs & _).
        cbn [ms_mem restrict] in Hrs.
        lazymatch type of Hrs with Forall _ ?rs =>
          let l := eval vm_compute in rs in change rs with l in Hrs end.
        pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail Hrs))) as HRF.
        unfold region_ok in HRF. cbn [YP09.r_base YP09.r_chunks base_val] in HRF.
        destruct HRF as (_ & _ & _ & Hcs). rewrite Ufw in Hcs.
        assert (HSC : Forall (YP09.chunk_ok tfibsegs Ew (mrestrict (w_H W) (ms_mem msF)) f)
                        mw_static_chunks).
        { apply Forall_forall. intros cc Hcc. apply (proj1 (Forall_forall _ _) Hcs cc).
          unfold mw_static_chunks in Hcc. cbn [In] in Hcc.
          repeat (destruct Hcc as [Hcc|Hcc]; [subst cc; inlist|]). destruct Hcc. }
        assert (V0 : val_mem tfibsegs (mrestrict (w_H W) (ms_mem msF)) (f + 0) 4 fl).
        { apply (val_of_chunk_ok tfibsegs Ew _ f 0 4%N (SOff 33 0) fl);
          [apply (proj1 (Forall_forall _ _) Hcs); inlist
          | rewrite denot_lit_U, (U_atom Ew 33 fl E33w ltac:(lia)); reflexivity | zside | zside]. }
        assert (V32 : val_mem tfibsegs (mrestrict (w_H W) (ms_mem msF)) (f + 32) 8 wend).
        { apply (val_of_chunk_ok tfibsegs Ew _ f 32 8%N (SOff 36 0) wend);
          [apply (proj1 (Forall_forall _ _) Hcs); inlist
          | rewrite denot_lit_U, (U_atom Ew 36 wend E36w ltac:(lia)); reflexivity | zside | zside]. }
        assert (V40 : val_mem tfibsegs (mrestrict (w_H W) (ms_mem msF)) (f + 40) 8 wpos).
        { apply (val_of_chunk_ok tfibsegs Ew _ f 40 8%N (SOff 32 0) wpos);
          [apply (proj1 (Forall_forall _ _) Hcs); inlist
          | rewrite denot_lit_U, (U_atom Ew 32 wpos E32w ltac:(lia)); reflexivity | zside | zside]. }
        assert (V56 : val_mem tfibsegs (mrestrict (w_H W) (ms_mem msF)) (f + 56) 8 wpos).
        { apply (val_of_chunk_ok tfibsegs Ew _ f 56 8%N (SOff 32 0) wpos);
          [apply (proj1 (Forall_forall _ _) Hcs); inlist
          | rewrite denot_lit_U, (U_atom Ew 32 wpos E32w ltac:(lia)); reflexivity | zside | zside]. }
        assert (V136 : val_mem tfibsegs (mrestrict (w_H W) (ms_mem msF)) (f + 136) 4 om).
        { apply (val_of_chunk_ok tfibsegs Ew _ f 136 4%N (SOff 37 0) om);
          [apply (proj1 (Forall_forall _ _) Hcs); inlist
          | rewrite denot_lit_U, (U_atom Ew 37 om E37w ltac:(lia)); reflexivity | zside | zside]. }
        assert (V232 : val_mem tfibsegs (mrestrict (w_H W) (ms_mem msF)) (f + 232) 8 (n + pos)).
        { apply (val_of_chunk_ok tfibsegs Ew _ f 232 8%N
                   (SAlu ALU_ADD (SOff 12 0) (SOff 34 0)) (n + pos));
          [apply (proj1 (Forall_forall _ _) Hcs); inlist
          | rewrite denot_lit_U, UADDw; reflexivity | zside | zside]. }
        assert (V240 : val_mem tfibsegs (mrestrict (w_H W) (ms_mem msF)) (f + 240) 8 (n + pos)).
        { apply (val_of_chunk_ok tfibsegs Ew _ f 240 8%N
                   (SAlu ALU_ADD (SOff 12 0) (SOff 34 0)) (n + pos));
          [apply (proj1 (Forall_forall _ _) Hcs); inlist
          | rewrite denot_lit_U, UADDw; reflexivity | zside | zside]. }
        assert (MFK : amf_k tfibsegs link_amf (mrestrict (w_H W) (ms_mem msF)) f 0).
        { apply (MKAT Ew _ fl wend wpos wpos (n + pos) (n + pos) Ufw E37w HSC V0 V32 V40 V56 V232 V240
                   Hfl2);
          [ destruct HWSHAPE as [(Q1 & Q2)|(Q1 & Q2)]; [left | right]; repeat split; lia
          | lia | rewrite HSZ; lia ]. }
        assert (HMX : Z.max len (pos + n) = pos + n) by lia.
        assert (DYNF : amf_dyn tfibsegs link_amf (mrestrict (w_H W) (ms_mem msF)) f fl om wend wpos wpos
                         (pos + n) (Z.max len (pos + n))).
        { rewrite HMX. unfold amf_dyn.
          split; [exact Dfl|]. split; [exact Dom|]. split; [exact Dwend|]. split; [exact Dwpos|].
          split; [exact Dwpos|].
          split; [lia|]. split; [rewrite HSZ; lia|].
          split; [exact V0|]. split; [exact V136|]. split; [exact V32|]. split; [exact V40|].
          split; [exact V56|].
          split; replace (pos + n) with (n + pos) by lia; [exact V232 | exact V240]. }
        assert (AZF : azbytes tfibsegs (mrestrict (w_H W) (ms_mem msF)) (amf_buf link_amf + pos)
                        (firstn (Z.to_nat n) ds)).
        { intros i Hi.
          assert (Hil : (i < Z.to_nat n)%nat)
            by (rewrite firstn_length_le in Hi by (unfold n in *; lia); exact Hi).
          rewrite (mw_nth_firstn Z 0 (Z.to_nat n) ds i Hil).
          change (amf_rd tfibsegs (mrestrict (w_H W) (ms_mem msF))
                    (amf_buf link_amf + pos + Z.of_nat i))
            with (aview tfibsegs (w_H W) (ms_mem msF) (amf_buf link_amf + pos + Z.of_nat i)).
          rewrite HB.
          rewrite (AVF (0x62fee0 + pos + Z.of_nat i) ltac:(lia)
                     ltac:(lia) ltac:(unfold AMF_BLOCK in *; lia) ltac:(rewrite Hterr; lia)
                     ltac:(lia)).
          rewrite (Hcpy (Z.of_nat i) ltac:(lia)).
          rewrite (KEEPV mem (ms_mem msB) KB (x + Z.of_nat i) ltac:(lia)
                     (HSEPM (x + Z.of_nat i) ltac:(lia))).
          pose proof (HZB i ltac:(unfold n in *; lia)) as HB2.
          change (amf_rd tfibsegs (mrestrict (w_H W) mem) (x + Z.of_nat i))
            with (aview tfibsegs (w_H W) mem (x + Z.of_nat i)) in HB2.
          exact HB2. }
        eapply (SRr_ret_at tfibsegs tbl_mw tbl_mw_ok Hwx W Ew);
          [exact HSr | reflexivity | vm_compute; reflexivity |].
        intros matG. rewrite wvb_collapse.
        replace (v_jalr (getr (ms_regs msF) 1) 0) with (w64 (raZ regs))
          by (rewrite RF1, E1w; unfold raZ, w64; rewrite Z_to_bv_bv_unsigned; symmetry; exact Hra).
        split; [reflexivity|].
        exists (ms_regs msF), (ms_mem msF), (with_vm_backing (m_vm_lazy md2) matG md2).
        cbv zeta.
        split; [reflexivity|].
        split; [exact (ARF matG)|].
        split; [exact AREGSF|].
        split; [exact (SBMF matG)|].
        split; [exact MFK|].
        split; [intros i Hi; cbn in Hi; lia|].
        split; [intros Hlt; exfalso; unfold amf_n1 in Hlt; rewrite HSZ in Hlt; lia|].
        split.
        { intros _.
          assert (HN2 : amw_n2 link_amf 0 pos n = n).
          { unfold amw_n2, amw_pos1, amf_n1. rewrite HSZ.
            replace (Z.min 0 (4096 - pos)) with 0 by lia.
            replace (pos + 0) with pos by lia. lia. }
          assert (HP1 : amw_pos1 link_amf 0 pos = pos).
          { unfold amw_pos1, amf_n1. rewrite HSZ. lia. }
          rewrite HN2, HP1. split; [exact RET10|]. split.
          - exists fl, wend, wpos, wpos. split; [exact DYNF|].
            split; [intros Hlt; exfalso; lia|].
            intros _. split; [reflexivity|]. split; [reflexivity|].
            split; [exact Hwpb | exact Hwpb].
          - rewrite app_nil_l. exact AZF. }
        split.
        { intros a Hr G1 G2 G3 G4.
          rewrite (AVF a Hr ltac:(unfold AMW0_STK, ESTACK in G1; lia)
                     ltac:(unfold AMF_ZEROED in G2; lia)
                     ltac:(rewrite Hterr; rewrite Herr in G4; lia)
                     ltac:(rewrite HB, HSZ in G3; lia)).
          apply AV2; [exact Hr|]. intros [Z1|[Z2|[Z3|Z4]]];
            [ apply G1; unfold AMW0_STK, ESTACK; lia
            | apply G2; unfold AMF_ZEROED; lia
            | apply G3; rewrite HB, HSZ; lia
            | apply G4; rewrite Herr; lia]. }
        split.
        { intros a Hp. apply (PRESTEP mem2 (ms_mem msF) GF3). apply PR2. exact Hp. }
        { intros a Ha. apply (PRESTEP mem2 (ms_mem msF) GF3). apply PR2. apply HPRES. exact Ha. }
  - (* the ENOSPC arm: n > size - pos, so n2 = size - pos bytes are copied. This is the ONLY part of the
       walk that steps into ___errno_location 0x90a7c (3 instructions, in the code table: mv a0,tp;
       addi a0,a0,-0xa4; ret), so the ENOSPC store +0x8c lands at as_tp B - 164 = as_errno B. *)
    rewrite branch_geu_U, Ubnd, Un in Hc. apply negb_false_iff, Z.ltb_lt in Hc.
    rename Hc into Hnofit.
    assert (Hpos4 : 0 <= pos <= 4096) by (rewrite HSZ in Dlen; lia).
    assert (Hlen4 : len <= 4096) by (rewrite HSZ in Dlen; exact Dlen).
    assert (LORV : Z.lor fl AF_ERR = 36) by (destruct Hfl2 as [Hq|Hq]; rewrite Hq; reflexivity).
    mwrun HS0 msB matB HFB HFrB HGB.
    (* the state at the interceptor's entry 0x52d74, after ___errno_location and the ENOSPC stores *)
    assert (KB : forall xw : word, ~ mw_set sp0 f (bv_unsigned xw) -> ms_mem msB xw = mem xw).
    { intros xw Hx.
      assert (Hb : ms_mem msB xw = ms_mem msA xw).
      { apply HFB. intros Hin. refine (Hx (WIN E _ _ Usp Uf Utp _ Hin)). vm_compute; reflexivity. }
      assert (Ha : ms_mem msA xw = mem xw).
      { apply HFA. intros Hin. refine (Hx (WIN E _ _ Usp Uf Utp _ Hin)). reflexivity. }
      rewrite Hb, Ha. reflexivity. }
    assert (GB : forall xw : word, w_H W xw = false -> mem xw <> None -> ms_mem msB xw <> None).
    { intros xw Hh Hne. apply (HGB xw Hh). apply (HGA xw Hh). exact Hne. }
    assert (ARB : AR tfibsegs B ly S W (ms_mem msB) (with_vm_backing (m_vm_lazy md) matB md))
      by (apply (ARSTEP mem (ms_mem msB) md _ HAR (with_vm_backing_same md matB) KB GB)).
    assert (PRB : forall a, apresent (w_H W) mem a -> apresent (w_H W) (ms_mem msB) a)
      by (exact (PRESTEP mem (ms_mem msB) GB)).
    rreg HS0 (1%bv : bv 5) RA1. rreg HS0 (2%bv : bv 5) RA2. rreg HS0 (3%bv : bv 5) RA3.
    rreg HS0 (4%bv : bv 5) RA4. rreg HS0 (10%bv : bv 5) RA10. rreg HS0 (11%bv : bv 5) RA11.
    assert (HspB : spZ (ms_regs msB) = sp0 - 48).
    { unfold spZ. rewrite RA2, Usp. rewrite unsigned_lit_small by lia. lia. }
    assert (RA10' : getr (ms_regs msB) 10 = w64 (0x62fee0 + pos)).
    { rewrite RA10, E34. rewrite unsigned_lit_small by lia. unfold w64. f_equal. lia. }
    assert (RA11' : getr (ms_regs msB) 11 = w64 x) by (rewrite RA11, E11; reflexivity).
    assert (RA12' : getr (ms_regs msB) 12 = w64 (4096 - pos)).
    { refine (eq_trans (st_ok_restrict_reg tfibsegs (w_H W) E _ _ (12%bv : bv 5) HS0) _).
      lazymatch goal with |- sv_denot _ ?t = _ => let e := eval vm_compute in t in change t with e end.
      rewrite denot_lit_U, Ubnd. reflexivity. }
    assert (SHV : forall s, kLowMemEnd <= s < kHighShadowEnd ->
              aview tfibsegs (w_H W) (ms_mem msB) s = aview tfibsegs (w_H W) mem s).
    { intros s Hs. apply (KEEPV mem (ms_mem msB) KB); [unfold kLowMemEnd, kHighShadowEnd in Hs; lia|].
      exact (NOSH s Hs). }
    assert (HSEPM : forall a, x <= a < x + n -> ~ mw_set sp0 f a).
    { intros a Ha Hm. destruct (HSEP a Ha) as (N1 & N2 & N3 & N4).
      rewrite HB, HSZ in N1. rewrite Herr in N3. unfold AMF_ZEROED in N2.
      destruct Hm as [Hs | [Hff | [Hg | He]]]; unfold AMW0_STK, ESTACK in *; lia. }
    pose proof AMEMCPY as AM. unfold aintrin_realizes, cfg_at in AM.
    rewrite (ts_code B TB) in AM. cbn [pc_wrap_memcpy Tfib_code] in AM.
    pose proof (st_ok_restrict_mkst tfibsegs (w_H W) E _ _ HS0 eq_refl) as HshB. cbn [ss_pc] in HshB.
    rewrite HshB.
    eapply SRr_bind.
    { apply (AM ly S W (ms_regs msB) (ms_mem msB) (with_vm_backing (m_vm_lazy md) matB md)
                (0x62fee0 + pos) x (4096 - pos)).
      - split; [exact ARB|].
        split; [rewrite RA1; apply YK0s.ret_ok_even;
                rewrite unsigned_lit_small by lia; lia|].
        rewrite HspB.
        split; [replace (sp0 - 48) with (sp0 + (-3) * 16) by lia; rewrite Z_mod_plus_full; exact Hal16|].
        split; [unfold AMW0_STK, ESTACK in HSTK; unfold ESTACK; lia|].
        split; [lia|].
        split; [intros a Ha; apply PRB; apply HPRES; unfold ESTACK in Ha;
                unfold AMW0_STK, ESTACK; lia|].
        split.
        + rewrite RA3, E3. exact Hgp.
        + rewrite RA4, E4. exact Htp.
      - exact RA10'.
      - exact RA11'.
      - exact RA12'.
      - lia.
      - lia.
      - lia.
      - intros a Ha. split; [apply mw_said_writable; lia|].
        split; [apply (proj1 (proj2 (Hbufw a ltac:(rewrite HB, HSZ; lia))))|].
        rewrite HspB. unfold ESTACK. lia.
      - unfold amem_range, kLowMemEnd. lia.
      - intros y Hy. rewrite SHV.
        + apply Hbufra. rewrite HB, HSZ. lia.
        + change (shadow_of_addr SHADOW_OFF y) with (shadow_addr y).
          apply shadow_addr_bounds. unfold kHighMemEnd. lia.
      - intros Hn0 s Hs.
        pose proof (shadow_addr_bounds (0x62fee0 + pos) ltac:(unfold kHighMemEnd; lia)) as Q1.
        pose proof (shadow_addr_bounds (0x62fee0 + pos + (4096 - pos) - 1)
                      ltac:(unfold kHighMemEnd; lia)) as Q2.
        pose proof (shadow_addr_bounds 0x62fee0 ltac:(unfold kHighMemEnd; lia)) as Q3.
        pose proof (shadow_addr_bounds (0x62fee0 + 4096 - 1) ltac:(unfold kHighMemEnd; lia)) as Q4.
        rewrite SHV.
        + apply Hbufhull. rewrite HB, HSZ. unfold shadow_addr, SHADOW_OFF in *. lia.
        + unfold shadow_addr, SHADOW_OFF in *. lia.
      - split; [lia|]. split; [lia|]. split.
        + intros a Ha. split.
          * rewrite (KEEPV mem (ms_mem msB) KB a ltac:(lia) (HSEPM a ltac:(lia))).
            pose proof (HZB (Z.to_nat (a - x)) ltac:(unfold n in *; lia)) as HB1.
            rewrite Z2Nat.id in HB1 by lia.
            replace (x + (a - x)) with a in HB1 by lia.
            change (amf_rd tfibsegs (mrestrict (w_H W) mem) a)
              with (aview tfibsegs (w_H W) mem a) in HB1.
            rewrite HB1. discriminate.
          * rewrite HspB. unfold ESTACK.
            destruct (HSEP a ltac:(lia)) as (_ & _ & _ & N4). unfold AMW0_STK, ESTACK in N4. lia.
        + split.
          * (* the source does not meet the destination, which lies in g_said *)
            destruct (Z_le_gt_dec (0x62fee0 + pos + (4096 - pos)) x) as [Hd1|Hd1]; [left; lia|].
            destruct (Z_le_gt_dec (x + (4096 - pos)) (0x62fee0 + pos)) as [Hd2|Hd2]; [right; lia|].
            exfalso.
            destruct (HSEP (Z.max x (0x62fee0 + pos)) ltac:(lia)) as (N1 & _ & _ & _).
            apply N1. rewrite HB, HSZ. lia.
          * split; [unfold amem_range in *; lia|].
            assert (HXR : x < kHighMemEnd /\ 0 <= x)
              by (unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in HAM;
                  unfold kHighMemEnd; lia).
            split.
            -- intros y Hy. rewrite SHV.
               ++ apply HRA. lia.
               ++ change (shadow_of_addr SHADOW_OFF y) with (shadow_addr y).
                  apply shadow_addr_bounds. unfold amem_range, kLowMemEnd,
                  kHighMemBeg, kHighMemEnd in HAM. unfold kHighMemEnd. lia.
            -- intros Hn0 s Hs.
               pose proof (shadow_addr_bounds x ltac:(unfold amem_range, kLowMemEnd, kHighMemBeg,
                 kHighMemEnd in HAM; unfold kHighMemEnd; lia)) as Q1.
               pose proof (shadow_addr_bounds (x + (4096 - pos) - 1) ltac:(unfold amem_range,
                 kLowMemEnd, kHighMemBeg, kHighMemEnd in HAM; unfold kHighMemEnd; lia)) as Q2.
               pose proof (shadow_addr_bounds (x + n - 1) ltac:(unfold amem_range, kLowMemEnd,
                 kHighMemBeg, kHighMemEnd in HAM; unfold kHighMemEnd; lia)) as Q3.
               rewrite SHV.
               ++ apply (HHULL ltac:(lia) s). unfold shadow_addr, SHADOW_OFF in *. lia.
               ++ unfold shadow_addr, SHADOW_OFF in *. lia. }
    cbv beta.
    intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HAR2 & HP2 & Hsbm2 & Ha0 & Hcpy & Hfr2 & Hpres2).
    assert (AV2 : forall a, 0 <= a < 2 ^ 64 -> ~ mw_set sp0 f a ->
                  aview tfibsegs (w_H W) mem2 a = aview tfibsegs (w_H W) mem a).
    { intros a Hr Ha.
      rewrite (Hfr2 a Hr
        ltac:(intros Hd; apply Ha; unfold mw_set; right; right; left; lia)
        ltac:(rewrite HspB; unfold ESTACK; intros Hw; apply Ha; unfold mw_set; left; lia)).
      exact (KEEPV mem (ms_mem msB) KB a Hr Ha). }
    assert (PR2 : forall a, apresent (w_H W) mem a -> apresent (w_H W) mem2 a)
      by (intros a Hp; apply Hpres2; exact (PRB a Hp)).
    assert (HraB : raZ (ms_regs msB) = 0x96d84).
    { unfold raZ. rewrite RA1. apply unsigned_lit_small. lia. }
    jafter_call HS0 40%nat regs2 (mrestrict (w_H W) mem2) HP2 HS2.
    match type of HS2 with ?t -> _ => assert (HRK : t); [|specialize (HS2 HRK); clear HRK] end.
    { cbn [ms_mem restrict].
      repeat apply Forall_cons; try apply Forall_nil; split;
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val];
        rewrite ?Usp, ?Uf, ?Utp.
      - intros a Ha. apply mbyte_of_aview.
        apply (Hfr2 a ltac:(lia) ltac:(lia) ltac:(rewrite HspB; lia)).
      - intros a Ha _. apply apresent_writable. apply Hpres2. apply PRB. apply HPRES.
        unfold AMW0_STK, ESTACK. lia.
      - intros a Ha. apply mbyte_of_aview.
        apply (Hfr2 a ltac:(unfold AMF_BLOCK in *; lia)
                 ltac:(unfold AMF_BLOCK in *; lia)
                 ltac:(rewrite HspB; unfold AMF_BLOCK in *; lia)).
      - intros a Ha _. apply apresent_writable. apply Hpres2. apply PRB.
        apply (proj1 (Hfpres a ltac:(unfold AMF_BLOCK in *; lia))).
      - intros a Ha. rewrite Hterr in Ha. apply mbyte_of_aview.
        apply (Hfr2 a ltac:(lia) ltac:(lia) ltac:(rewrite HspB; lia)).
      - intros a Ha _. rewrite Hterr in Ha. apply mw_errno_writable. lia. }
    clear HS0. rewrite <- restrict_mkst_fx in HS2.
    set (Ev := havoc E 40 (map (getr regs2) CLOB)) in *.
    assert (OLD3 : forall i, (i < 40)%nat -> ew Ev i = ew E i)
      by (intros i Hi; unfold Ev; apply ew_havoc_old; exact Hi).
    assert (Usp3 : bv_unsigned (ew Ev 2) = sp0) by (rewrite (OLD3 2%nat ltac:(lia)); exact Usp).
    assert (Uf3 : bv_unsigned (ew Ev 10) = f) by (rewrite (OLD3 10%nat ltac:(lia)); exact Uf).
    assert (Utp3 : bv_unsigned (ew Ev 4) = as_tp B) by (rewrite (OLD3 4%nat ltac:(lia)); exact Utp).
    assert (E1v : ew Ev 1 = getr regs 1) by (rewrite (OLD3 1%nat ltac:(lia)); exact E1).
    assert (E33v : ew Ev 33 = Z_to_bv 64 fl) by (rewrite (OLD3 33%nat ltac:(lia)); exact E33).
    assert (E34v : ew Ev 34 = Z_to_bv 64 pos) by (rewrite (OLD3 34%nat ltac:(lia)); exact E34).
    assert (E35v : ew Ev 35 = Z_to_bv 64 len) by (rewrite (OLD3 35%nat ltac:(lia)); exact E35).
    assert (E37v : ew Ev 37 = Z_to_bv 64 om) by (rewrite (OLD3 37%nat ltac:(lia)); exact E37).
    assert (HAEv : YP06.env_agree 32 (Ereg regs extra) Ev)
      by (unfold Ev; apply env_agree_havoc_ge; [cbv; lia | apply YP06.env_agree_refl]).
    assert (UbndV : U Ev (SAlu ALU_SUB (SLit 0) (SOff 34 (-4096))) = 4096 - pos).
    { rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit, U_SOff, E34v.
      rewrite unsigned_lit_small by lia. unfold zcanon, M64.
      rewrite (Z.mod_small 0 (2 ^ 64)) by lia.
      rewrite Zminus_mod_idemp_r. rewrite Z.mod_small by lia. lia. }
    assert (FLV : U Ev (SAlu ALU_OR (SExt true 32 (SOff 33 0)) (SLit 32)) = 36).
    { rewrite U_SAlu, U_SExt, U_SLit, (U_atom Ev 33 fl E33v ltac:(lia)).
      destruct Hfl2 as [Hq|Hq]; rewrite Hq; vm_compute; reflexivity. }
    assert (Ulen3 : U Ev (SOff 35 0) = len) by (apply (U_atom Ev 35 len E35v); lia).
    assert (U4096 : U Ev (SLit 4096) = 4096) by (apply U_lit; lia).
    (* the facts every ENOSPC leaf shares, at a final state msZ reached from mem2 inside the walk's windows *)
    assert (ELEAF : forall (msZ : machine_state) mdZ,
      (forall a, 0 <= a < 2 ^ 64 ->
         ~ (sp0 - 48 <= a < sp0) -> ~ (f <= a < f + 248) -> ~ (as_tp B - 164 <= a < as_tp B - 160) ->
         aview tfibsegs (w_H W) (ms_mem msZ) a = aview tfibsegs (w_H W) mem2 a) ->
      (forall xw : word, ~ mw_set sp0 f (bv_unsigned xw) -> ms_mem msZ xw = mem2 xw) ->
      (forall xw : word, w_H W xw = false -> mem2 xw <> None -> ms_mem msZ xw <> None) ->
      same_but_materialized md2 mdZ ->
      aregs_preserved regs (ms_regs msZ) ->
      getr (ms_regs msZ) 10 = w64 (4096 - pos) ->
      Forall (YP09.chunk_ok tfibsegs Ev (mrestrict (w_H W) (ms_mem msZ)) f) mw_static_chunks ->
      val_mem tfibsegs (mrestrict (w_H W) (ms_mem msZ)) (f + 0) 4 36 ->
      val_mem tfibsegs (mrestrict (w_H W) (ms_mem msZ)) (f + 32) 8 0 ->
      val_mem tfibsegs (mrestrict (w_H W) (ms_mem msZ)) (f + 40) 8 0 ->
      val_mem tfibsegs (mrestrict (w_H W) (ms_mem msZ)) (f + 56) 8 0 ->
      val_mem tfibsegs (mrestrict (w_H W) (ms_mem msZ)) (f + 136) 4 om ->
      val_mem tfibsegs (mrestrict (w_H W) (ms_mem msZ)) (f + 232) 8 4096 ->
      val_mem tfibsegs (mrestrict (w_H W) (ms_mem msZ)) (f + 240) 8 4096 ->
      let n1 := amf_n1 link_amf 0 pos in
      let pos1 := amw_pos1 link_amf 0 pos in
      let n2 := amw_n2 link_amf 0 pos n in
      AR tfibsegs B ly S W (ms_mem msZ) mdZ /\ aregs_preserved regs (ms_regs msZ) /\
      same_but_materialized md mdZ /\
      amf_k tfibsegs link_amf (mrestrict (w_H W) (ms_mem msZ)) f 0 /\
      amf_pend tfibsegs (mrestrict (w_H W) (ms_mem msZ)) f [] /\
      (n1 < 0 ->
         getr (ms_regs msZ) 10 = w64 0 /\
         amf_dyn tfibsegs link_amf (mrestrict (w_H W) (ms_mem msZ)) f (Z.lor fl AF_ERR) om 0 0 0 pos1
           (Z.max len pos1) /\
         azbytes tfibsegs (mrestrict (w_H W) (ms_mem msZ)) (amf_buf link_amf + pos) (firstn (Z.to_nat n1) [])) /\
      (n1 = 0 ->
         getr (ms_regs msZ) 10 = w64 n2 /\
         (exists fl' wend' wpos' wbase',
            amf_dyn tfibsegs link_amf (mrestrict (w_H W) (ms_mem msZ)) f fl' om wend' wpos' wbase'
              (pos1 + n2) (Z.max len (pos1 + n2)) /\
            (n2 < n -> fl' = Z.lor fl AF_ERR /\ wend' = 0 /\ wpos' = 0 /\ wbase' = 0) /\
            (n2 = n -> fl' = fl /\ wend' = wend /\ wpos' = wbase /\ wbase' = wbase)) /\
         azbytes tfibsegs (mrestrict (w_H W) (ms_mem msZ)) (amf_buf link_amf + pos) ([] ++ firstn (Z.to_nat n2) ds)) /\
      (forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - AMW0_STK <= a < sp0) -> ~ (f <= a < f + AMF_ZEROED) ->
         ~ (amf_buf link_amf <= a < amf_buf link_amf + amf_size link_amf) ->
         ~ (as_errno B <= a < as_errno B + 4) ->
         aview tfibsegs (w_H W) (ms_mem msZ) a = aview tfibsegs (w_H W) mem a) /\
      (forall a, apresent (w_H W) mem a -> apresent (w_H W) (ms_mem msZ) a) /\
      (forall a, sp0 - AMW0_STK <= a < sp0 -> apresent (w_H W) (ms_mem msZ) a)).
    { intros msZ mdZ AVZ KZ GZ SBZ AREGZ RETZ HSC V0 V32 V40 V56 V136 V232 V240.
      cbv zeta.
      assert (MFK : amf_k tfibsegs link_amf (mrestrict (w_H W) (ms_mem msZ)) f 0).
      { apply (MKAT Ev _ 36 0 0 0 4096 4096 Uf3 E37v HSC V0 V32 V40 V56 V232 V240);
        [ right; reflexivity | left; repeat split | lia | rewrite HSZ; lia ]. }
      assert (DYNF : amf_dyn tfibsegs link_amf (mrestrict (w_H W) (ms_mem msZ)) f 36 om 0 0 0 4096 4096).
      { unfold amf_dyn.
        split; [lia|]. split; [exact Dom|]. split; [lia|]. split; [lia|]. split; [lia|].
        split; [lia|]. split; [rewrite HSZ; lia|].
        split; [exact V0|]. split; [exact V136|]. split; [exact V32|]. split; [exact V40|].
        split; [exact V56|]. split; [exact V232 | exact V240]. }
      assert (AZF : azbytes tfibsegs (mrestrict (w_H W) (ms_mem msZ)) (amf_buf link_amf + pos)
                      (firstn (Z.to_nat (4096 - pos)) ds)).
      { intros i Hi.
        assert (Hil : (i < Z.to_nat (4096 - pos))%nat)
          by (rewrite firstn_length_le in Hi by (unfold n in *; lia); exact Hi).
        rewrite (mw_nth_firstn Z 0 (Z.to_nat (4096 - pos)) ds i Hil).
        change (amf_rd tfibsegs (mrestrict (w_H W) (ms_mem msZ)) (amf_buf link_amf + pos + Z.of_nat i))
          with (aview tfibsegs (w_H W) (ms_mem msZ) (amf_buf link_amf + pos + Z.of_nat i)).
        rewrite HB.
        rewrite (AVZ (0x62fee0 + pos + Z.of_nat i) ltac:(lia)
                   ltac:(lia) ltac:(unfold AMF_BLOCK in *; lia) ltac:(rewrite Hterr; lia)).
        rewrite (Hcpy (Z.of_nat i) ltac:(lia)).
        rewrite (KEEPV mem (ms_mem msB) KB (x + Z.of_nat i) ltac:(lia)
                   (HSEPM (x + Z.of_nat i) ltac:(unfold n in *; lia))).
        pose proof (HZB i ltac:(unfold n in *; lia)) as HB2.
        change (amf_rd tfibsegs (mrestrict (w_H W) mem) (x + Z.of_nat i))
          with (aview tfibsegs (w_H W) mem (x + Z.of_nat i)) in HB2.
        exact HB2. }
      split; [apply (ARSTEP mem2 (ms_mem msZ) md2 mdZ HAR2 SBZ KZ GZ)|].
      split; [exact AREGZ|].
      split; [eapply same_but_materialized_trans;
              [apply with_vm_backing_same | eapply same_but_materialized_trans; [exact Hsbm2 | exact SBZ]]|].
      split; [exact MFK|].
      split; [intros i Hi; cbn in Hi; lia|].
      split; [intros Hlt; exfalso; unfold amf_n1 in Hlt; rewrite HSZ in Hlt; lia|].
      split.
      { intros _.
        assert (HN2 : amw_n2 link_amf 0 pos n = 4096 - pos).
        { unfold amw_n2, amw_pos1, amf_n1. rewrite HSZ.
          replace (Z.min 0 (4096 - pos)) with 0 by lia.
          replace (pos + 0) with pos by lia. lia. }
        assert (HP1 : amw_pos1 link_amf 0 pos = pos).
        { unfold amw_pos1, amf_n1. rewrite HSZ. lia. }
        rewrite HN2, HP1. replace (pos + (4096 - pos)) with 4096 by lia.
        replace (Z.max len 4096) with 4096 by lia.
        split; [exact RETZ|]. split.
        - exists 36, 0, 0, 0. split; [exact DYNF|].
          split.
          + intros _. split; [symmetry; exact LORV|]. repeat split.
          + intros Heq. exfalso. unfold n in *. lia.
        - rewrite app_nil_l. exact AZF. }
      split.
      { intros a Hr G1 G2 G3 G4.
        rewrite (AVZ a Hr ltac:(unfold AMW0_STK, ESTACK in G1; lia)
                   ltac:(unfold AMF_ZEROED in G2; lia)
                   ltac:(rewrite Hterr; rewrite Herr in G4; lia)).
        apply AV2; [exact Hr|]. intros [Z1|[Z2|[Z3|Z4]]];
          [ apply G1; unfold AMW0_STK, ESTACK; lia
          | apply G2; unfold AMF_ZEROED; lia
          | apply G3; rewrite HB, HSZ; lia
          | apply G4; rewrite Herr; lia]. }
      split.
      { intros a Hp. apply (PRESTEP mem2 (ms_mem msZ) GZ). apply PR2. exact Hp. }
      { intros a Ha. apply (PRESTEP mem2 (ms_mem msZ) GZ). apply PR2. apply HPRES. exact Ha. } }
    unfold cfg_at. rewrite HraB.
    mwrun HS2 msC matC HFC HFrC HGC.
    srr_branch_with tbl_mw_ok HS2.
    + (* len >= size: len = size and nothing more is stored *)
      rewrite branch_geu_U, Ulen3, U4096 in Hc. apply negb_true_iff, Z.ltb_ge in Hc.
      assert (Hl4 : len = 4096) by lia.
      mwrun HS2 msF matF HFF HFrF HGF.
      assert (AVF : forall a, 0 <= a < 2 ^ 64 ->
                 ~ (sp0 - 48 <= a < sp0) -> ~ (f <= a < f + 248) ->
                 ~ (as_tp B - 164 <= a < as_tp B - 160) ->
                 aview tfibsegs (w_H W) (ms_mem msF) a = aview tfibsegs (w_H W) mem2 a).
      { intros a Hr G1 G2 G3.
        assert (HOUT : forall (ma mb : word -> option byte) ssx,
                  frame_of Ev (ss_mem ssx) ma mb ->
                  windows (ss_mem ssx) = windows (ss_mem ss_mw) ->
                  mb (Z_to_bv 64 a) = ma (Z_to_bv 64 a)).
        { intros ma mb ssx Hfr Hw. apply Hfr. rewrite unsigned_lit_small by lia. intros Hin.
          destruct (WINX Ev ssx a Usp3 Uf3 Utp3 Hw Hin) as [Z1|[Z2|Z3]];
            [exact (G1 Z1) | exact (G2 Z2) | exact (G3 Z3)]. }
        apply aview_eq_of.
        rewrite (HOUT _ _ _ HFrF ltac:(vm_compute; reflexivity)).
        rewrite (HOUT _ _ _ HFrC ltac:(vm_compute; reflexivity)). reflexivity. }
      assert (KF3 : forall xw : word, ~ mw_set sp0 f (bv_unsigned xw) -> ms_mem msF xw = mem2 xw).
      { intros xw Hx.
        assert (Q1 : ms_mem msF xw = ms_mem msC xw).
        { apply HFF. intros Hin. refine (Hx (WIN Ev _ _ Usp3 Uf3 Utp3 _ Hin)). vm_compute; reflexivity. }
        assert (Q2 : ms_mem msC xw = mem2 xw).
        { apply HFC. intros Hin. refine (Hx (WIN Ev _ _ Usp3 Uf3 Utp3 _ Hin)). vm_compute; reflexivity. }
        rewrite Q1, Q2. reflexivity. }
      assert (GF3 : forall xw : word, w_H W xw = false -> mem2 xw <> None -> ms_mem msF xw <> None)
        by (intros xw Hh Hne; apply (HGF xw Hh); apply (HGC xw Hh); exact Hne).
      assert (AREGSF : aregs_preserved regs (ms_regs msF))
        by (exact (aregs_preserved_of_st_ok _ Ev _ _ regs extra HS2 HAEv
                     ltac:(vm_compute; reflexivity))).
      assert (RET10 : getr (ms_regs msF) 10 = w64 (4096 - pos)).
      { refine (eq_trans (st_ok_restrict_reg tfibsegs (w_H W) Ev _ _ (10%bv : bv 5) HS2) _).
        lazymatch goal with |- sv_denot _ ?t = _ => let e := eval vm_compute in t in change t with e end.
        rewrite denot_lit_U, UbndV. reflexivity. }
      rreg HS2 (1%bv : bv 5) RF1.
      pose proof (st_ok_mem_ok tfibsegs Ev _ _ HS2) as HMO. destruct HMO as (_ & Hrs & _).
      cbn [ms_mem restrict] in Hrs.
      lazymatch type of Hrs with Forall _ (ss_mem ?s) =>
        let l := eval vm_compute in (ss_mem s) in change (ss_mem s) with l in Hrs end.
      pose proof (Forall_inv (Forall_inv_tail Hrs)) as HRF.
      unfold region_ok in HRF. cbn [YP09.r_base YP09.r_chunks base_val] in HRF.
      destruct HRF as (_ & _ & _ & Hcs). rewrite Uf3 in Hcs.
      assert (HSC : Forall (YP09.chunk_ok tfibsegs Ev (mrestrict (w_H W) (ms_mem msF)) f)
                      mw_static_chunks).
      { apply Forall_forall. intros cc Hcc. apply (proj1 (Forall_forall _ _) Hcs cc).
        unfold mw_static_chunks in Hcc. cbn [In] in Hcc.
        repeat (destruct Hcc as [Hcc|Hcc]; [subst cc; inlist|]). destruct Hcc. }
      assert (V0 : val_mem tfibsegs (mrestrict (w_H W) (ms_mem msF)) (f + 0) 4 36).
      { apply (val_of_chunk_ok tfibsegs Ev _ f 0 4%N
                 (SAlu ALU_OR (SExt true 32 (SOff 33 0)) (SLit 32)) 36);
        [apply (proj1 (Forall_forall _ _) Hcs); inlist
        | rewrite denot_lit_U, FLV; reflexivity | zside | zside]. }
      assert (V32 : val_mem tfibsegs (mrestrict (w_H W) (ms_mem msF)) (f + 32) 8 0).
      { apply (val_of_chunk_ok tfibsegs Ev _ f 32 8%N (SLit 0) 0);
        [apply (proj1 (Forall_forall _ _) Hcs); inlist | reflexivity | zside | zside]. }
      assert (V40 : val_mem tfibsegs (mrestrict (w_H W) (ms_mem msF)) (f + 40) 8 0).
      { apply (val_of_chunk_ok tfibsegs Ev _ f 40 8%N (SLit 0) 0);
        [apply (proj1 (Forall_forall _ _) Hcs); inlist | reflexivity | zside | zside]. }
      assert (V56 : val_mem tfibsegs (mrestrict (w_H W) (ms_mem msF)) (f + 56) 8 0).
      { apply (val_of_chunk_ok tfibsegs Ev _ f 56 8%N (SLit 0) 0);
        [apply (proj1 (Forall_forall _ _) Hcs); inlist | reflexivity | zside | zside]. }
      assert (V136 : val_mem tfibsegs (mrestrict (w_H W) (ms_mem msF)) (f + 136) 4 om).
      { apply (val_of_chunk_ok tfibsegs Ev _ f 136 4%N (SOff 37 0) om);
        [apply (proj1 (Forall_forall _ _) Hcs); inlist
        | rewrite denot_lit_U, (U_atom Ev 37 om E37v ltac:(lia)); reflexivity | zside | zside]. }
      assert (V232 : val_mem tfibsegs (mrestrict (w_H W) (ms_mem msF)) (f + 232) 8 4096).
      { apply (val_of_chunk_ok tfibsegs Ev _ f 232 8%N (SLit 4096) 4096);
        [apply (proj1 (Forall_forall _ _) Hcs); inlist | reflexivity | zside | zside]. }
      assert (V240 : val_mem tfibsegs (mrestrict (w_H W) (ms_mem msF)) (f + 240) 8 4096).
      { apply (val_of_chunk_ok tfibsegs Ev _ f 240 8%N (SOff 35 0) 4096);
        [apply (proj1 (Forall_forall _ _) Hcs); inlist
        | rewrite denot_lit_U, Ulen3, Hl4; reflexivity | zside | zside]. }
      eapply (SRr_ret_at tfibsegs tbl_mw tbl_mw_ok Hwx W Ev);
        [exact HS2 | reflexivity | vm_compute; reflexivity |].
      intros matG. rewrite wvb_collapse.
      replace (v_jalr (getr (ms_regs msF) 1) 0) with (w64 (raZ regs))
        by (rewrite RF1, E1v; unfold raZ, w64; rewrite Z_to_bv_bv_unsigned; symmetry; exact Hra).
      split; [reflexivity|].
      exists (ms_regs msF), (ms_mem msF), (with_vm_backing (m_vm_lazy md2) matG md2).
      cbv zeta.
      split; [reflexivity|].
      exact (ELEAF msF _ AVF KF3 GF3 (with_vm_backing_same md2 matG) AREGSF RET10 HSC
               V0 V32 V40 V56 V136 V232 V240).
    + (* len < size: c->len := size; pos + n2 = size, so the NUL branch +0xe0 is decided (no NUL) *)
      rewrite branch_geu_U, Ulen3, U4096 in Hc. apply negb_false_iff, Z.ltb_lt in Hc.
      mwrun HS2 msF matF HFF HFrF HGF.
      assert (AVF : forall a, 0 <= a < 2 ^ 64 ->
                 ~ (sp0 - 48 <= a < sp0) -> ~ (f <= a < f + 248) ->
                 ~ (as_tp B - 164 <= a < as_tp B - 160) ->
                 aview tfibsegs (w_H W) (ms_mem msF) a = aview tfibsegs (w_H W) mem2 a).
      { intros a Hr G1 G2 G3.
        assert (HOUT : forall (ma mb : word -> option byte) ssx,
                  frame_of Ev (ss_mem ssx) ma mb ->
                  windows (ss_mem ssx) = windows (ss_mem ss_mw) ->
                  mb (Z_to_bv 64 a) = ma (Z_to_bv 64 a)).
        { intros ma mb ssx Hfr Hw. apply Hfr. rewrite unsigned_lit_small by lia. intros Hin.
          destruct (WINX Ev ssx a Usp3 Uf3 Utp3 Hw Hin) as [Z1|[Z2|Z3]];
            [exact (G1 Z1) | exact (G2 Z2) | exact (G3 Z3)]. }
        apply aview_eq_of.
        rewrite (HOUT _ _ _ HFrF ltac:(vm_compute; reflexivity)).
        rewrite (HOUT _ _ _ HFrC ltac:(vm_compute; reflexivity)). reflexivity. }
      assert (KF3 : forall xw : word, ~ mw_set sp0 f (bv_unsigned xw) -> ms_mem msF xw = mem2 xw).
      { intros xw Hx.
        assert (Q1 : ms_mem msF xw = ms_mem msC xw).
        { apply HFF. intros Hin. refine (Hx (WIN Ev _ _ Usp3 Uf3 Utp3 _ Hin)). vm_compute; reflexivity. }
        assert (Q2 : ms_mem msC xw = mem2 xw).
        { apply HFC. intros Hin. refine (Hx (WIN Ev _ _ Usp3 Uf3 Utp3 _ Hin)). vm_compute; reflexivity. }
        rewrite Q1, Q2. reflexivity. }
      assert (GF3 : forall xw : word, w_H W xw = false -> mem2 xw <> None -> ms_mem msF xw <> None)
        by (intros xw Hh Hne; apply (HGF xw Hh); apply (HGC xw Hh); exact Hne).
      assert (AREGSF : aregs_preserved regs (ms_regs msF))
        by (exact (aregs_preserved_of_st_ok _ Ev _ _ regs extra HS2 HAEv
                     ltac:(vm_compute; reflexivity))).
      assert (RET10 : getr (ms_regs msF) 10 = w64 (4096 - pos)).
      { refine (eq_trans (st_ok_restrict_reg tfibsegs (w_H W) Ev _ _ (10%bv : bv 5) HS2) _).
        lazymatch goal with |- sv_denot _ ?t = _ => let e := eval vm_compute in t in change t with e end.
        rewrite denot_lit_U, UbndV. reflexivity. }
      rreg HS2 (1%bv : bv 5) RF1.
      pose proof (st_ok_mem_ok tfibsegs Ev _ _ HS2) as HMO. destruct HMO as (_ & Hrs & _).
      cbn [ms_mem restrict] in Hrs.
      lazymatch type of Hrs with Forall _ (ss_mem ?s) =>
        let l := eval vm_compute in (ss_mem s) in change (ss_mem s) with l in Hrs end.
      pose proof (Forall_inv (Forall_inv_tail Hrs)) as HRF.
      unfold region_ok in HRF. cbn [YP09.r_base YP09.r_chunks base_val] in HRF.
      destruct HRF as (_ & _ & _ & Hcs). rewrite Uf3 in Hcs.
      assert (HSC : Forall (YP09.chunk_ok tfibsegs Ev (mrestrict (w_H W) (ms_mem msF)) f)
                      mw_static_chunks).
      { apply Forall_forall. intros cc Hcc. apply (proj1 (Forall_forall _ _) Hcs cc).
        unfold mw_static_chunks in Hcc. cbn [In] in Hcc.
        repeat (destruct Hcc as [Hcc|Hcc]; [subst cc; inlist|]). destruct Hcc. }
      assert (V0 : val_mem tfibsegs (mrestrict (w_H W) (ms_mem msF)) (f + 0) 4 36).
      { apply (val_of_chunk_ok tfibsegs Ev _ f 0 4%N
                 (SAlu ALU_OR (SExt true 32 (SOff 33 0)) (SLit 32)) 36);
        [apply (proj1 (Forall_forall _ _) Hcs); inlist
        | rewrite denot_lit_U, FLV; reflexivity | zside | zside]. }
      assert (V32 : val_mem tfibsegs (mrestrict (w_H W) (ms_mem msF)) (f + 32) 8 0).
      { apply (val_of_chunk_ok tfibsegs Ev _ f 32 8%N (SLit 0) 0);
        [apply (proj1 (Forall_forall _ _) Hcs); inlist | reflexivity | zside | zside]. }
      assert (V40 : val_mem tfibsegs (mrestrict (w_H W) (ms_mem msF)) (f + 40) 8 0).
      { apply (val_of_chunk_ok tfibsegs Ev _ f 40 8%N (SLit 0) 0);
        [apply (proj1 (Forall_forall _ _) Hcs); inlist | reflexivity | zside | zside]. }
      assert (V56 : val_mem tfibsegs (mrestrict (w_H W) (ms_mem msF)) (f + 56) 8 0).
      { apply (val_of_chunk_ok tfibsegs Ev _ f 56 8%N (SLit 0) 0);
        [apply (proj1 (Forall_forall _ _) Hcs); inlist | reflexivity | zside | zside]. }
      assert (V136 : val_mem tfibsegs (mrestrict (w_H W) (ms_mem msF)) (f + 136) 4 om).
      { apply (val_of_chunk_ok tfibsegs Ev _ f 136 4%N (SOff 37 0) om);
        [apply (proj1 (Forall_forall _ _) Hcs); inlist
        | rewrite denot_lit_U, (U_atom Ev 37 om E37v ltac:(lia)); reflexivity | zside | zside]. }
      assert (V232 : val_mem tfibsegs (mrestrict (w_H W) (ms_mem msF)) (f + 232) 8 4096).
      { apply (val_of_chunk_ok tfibsegs Ev _ f 232 8%N (SLit 4096) 4096);
        [apply (proj1 (Forall_forall _ _) Hcs); inlist | reflexivity | zside | zside]. }
      assert (V240 : val_mem tfibsegs (mrestrict (w_H W) (ms_mem msF)) (f + 240) 8 4096).
      { apply (val_of_chunk_ok tfibsegs Ev _ f 240 8%N (SLit 4096) 4096);
        [apply (proj1 (Forall_forall _ _) Hcs); inlist | reflexivity | zside | zside]. }
      eapply (SRr_ret_at tfibsegs tbl_mw tbl_mw_ok Hwx W Ev);
        [exact HS2 | reflexivity | vm_compute; reflexivity |].
      intros matG. rewrite wvb_collapse.
      replace (v_jalr (getr (ms_regs msF) 1) 0) with (w64 (raZ regs))
        by (rewrite RF1, E1v; unfold raZ, w64; rewrite Z_to_bv_bv_unsigned; symmetry; exact Hra).
      split; [reflexivity|].
      exists (ms_regs msF), (ms_mem msF), (with_vm_backing (m_vm_lazy md2) matG md2).
      cbv zeta.
      split; [reflexivity|].
      exact (ELEAF msF _ AVF KF3 GF3 (with_vm_backing_same md2 matG) AREGSF RET10 HSC
               V0 V32 V40 V56 V136 V232 V240).
Qed.

End W.

About link_amwrite_k0.
Print Assumptions link_amwrite_k0.
