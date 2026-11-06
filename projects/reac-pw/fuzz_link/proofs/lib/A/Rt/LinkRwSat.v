(* reac-pw/fuzz_link, image A (pin 059dae63e07c): a satisfiability witness for the premises of
   arewind_mf_realizes (LinkMfDefs.v section 3) and of amwrite_mf_flush_realizes (LinkRwDefs.v), at one concrete
   memory of link's own run.

   The run: LLVMFuzzerTestOneInput marks twice. The FIRST mark runs mark_quietly 0x883d4, which opens
   g_sink = fmemopen(g_said, 4096, "w"), sets g_say and tail-jumps to reac_served_mark; its fprintf / vfprintf
   calls leave 60 bytes in the FILE's 1024-byte buffer (under the buffer size, so nothing reached g_said yet) and
   __towrite has set the orientation to -1. The SECOND mark reaches 0x88424 (`jal 0x430d4`, a0 = g_sink), the
   rewind this contract covers. So at that call:
   - the FILE block is a 1304-byte block of the A allocator; the witness places it at f = 0x10000000, an address
     the ledger can hold (AMemFileT06.v link_amf_block_exists uses the same one: 16-aligned, above 4096, below the
     ceiling, no byte of it in the image, since every image byte is below 0x700000);
   - its words are what fmemopen and the first mark left: flags F_NORD (no error), orientation -1 (AU32M1), the
     write window active with k = 60 pending bytes (wbase = f + 280, wpos = f + 280 + 60, wend = f + 280 + 1024),
     the cookie's pos = 0 and len = 0 (nothing written to g_said yet);
   - the 60 pending bytes are the first 60 bytes a mark writes ("reac-pw: E_NOT_MARKED [nl0] could not read the
     interface ali": reac_code_emit's fprintf text .str.10 / .str.2 / .str.33 followed by its vfprintf text
     .str.3 with the name "nl0"; link-a/libc/printf.md (internal record, sha256 7bbba2c3aa7f) section 1);
   - g_said (0x62fee0, the cookie's buf, 4096 bytes) is readable and writable, its shadow bytes are 0;
   - the two guard words (the .got cell 0xa2658 holds 0x651c50; 0x651c50 holds the canary) are readable (the
     cell REAL(rewind) 0xa37d8 is no premise: AR's const law fixes it, lib/A/AF0m.v row z8 (ANum 0xa37d8) 0x97210);
   - sp is a real-stack address (0x7ffffffde000), so the window [sp - K, sp) is clear of g_said.

   What this file proves (closed, for every segment list, because the witness memory holds every byte read, so no
   ROM byte is read): every premise of arewind_mf_realizes and of amwrite_mf_flush_realizes that speaks of the
   memory, the registers' values or arithmetic. The premises that speak of the A state are NOT closed here, as in
   link-a/form/WITNESS.md (internal record, sha256 b8aaf8151f7f): `ecall_pre` (AR of a state of the run),
   `In (f, AMF_BLOCK) (ablocks B ly S)` (the ledger holds the FILE's block from the first mark) and the
   `~ aowned B ly S a` conjunct of amf_buf_ok. For that last one the file proves the closed half that the caller needs:
   no range of the frame's owned-static list (lib/A/AF0m.v Tfib_owned_static, which is `as_owned_static PcapB`) meets
   g_said, so AR's owned-image law gives `~ aowned B ly S a` for every byte of g_said. (The owned-static list's ranges
   stop exactly at g_said's two ends: (0x62fec8, 0x18) ends at 0x62fee0 and (0x630ee0, 0x400) starts at g_said's end.)
   Proves no function (kind: statement text and witness). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK11 YK0s YK0i YK15 YK0j YK18 YP09.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YI04 YI16.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YO0f.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AB1v AF0l AF0m AMemFile AMemFileT06.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Rt Require Import LinkMfDefs LinkRwDefs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

(* ==========================================================================
   1. The run's values
   ========================================================================== *)

Definition RW_F : Z := 0x10000000.          (* the FILE block (AMemFileT06.v link_amf_block_exists) *)
Definition RW_SP : Z := 0x7ffffffde000.     (* the real-stack sp at the call *)
Definition RW_K : Z := 60.                  (* the pending bytes the first mark left *)
Definition RW_CANARY : Z := 0x1122334455667788.
Definition RW_SAID : Z := 0x62fee0.         (* amf_buf link_amf *)
Definition RW_SINK : Z := 0x62fec0.         (* amf_sink_addr link_amf *)
Definition RW_SAY : Z := 0x6312e0.          (* amf_say_addr link_amf *)
Definition RW_OFL : Z := 0x652308.          (* amf_ofl_head link_amf *)
(* the shadow bytes of g_said, with room for the hull rounding of shadow_hull_vis *)
Definition RW_SH_LO : Z := 2148261788.      (* 0x7fff8000 + 0x62fee0 / 8 - 64 *)
Definition RW_SH_HI : Z := 2148262427.      (* 0x7fff8000 + 0x630edf / 8 + 64 *)

(* "reac-pw: E_NOT_MARKED [nl0] could not read the interface ali" *)
Definition rw_pb : list Z :=
  [114; 101; 97; 99; 45; 112; 119; 58; 32; 69; 95; 78; 79; 84; 95; 77; 65; 82; 75; 69; 68; 32;
   91; 110; 108; 48; 93; 32; 99; 111; 117; 108; 100; 32; 110; 111; 116; 32; 114; 101; 97; 100; 32;
   116; 104; 101; 32; 105; 110; 116; 101; 114; 102; 97; 99; 101; 32; 97; 108; 105].

Lemma rw_pb_len : Z.of_nat (length rw_pb) = RW_K.
Proof. vm_compute. reflexivity. Qed.

Lemma rw_pb_range : forall i, (i < length rw_pb)%nat -> 0 <= nth i rw_pb 0 < 256.
Proof.
  intros i Hi. change (length rw_pb) with 60%nat in Hi.
  do 60 (destruct i as [|i]; [cbv [nth rw_pb]; lia|]). lia.
Qed.

(* ==========================================================================
   2. The witness memory
   ========================================================================== *)

Definition rwin (a lo n : Z) : bool := (lo <=? a) && (a <? lo + n).

Lemma rwin_true : forall a lo n, lo <= a < lo + n -> rwin a lo n = true.
Proof. intros a lo n H. unfold rwin. apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia. Qed.

Lemma rwin_false : forall a lo n, a < lo \/ lo + n <= a -> rwin a lo n = false.
Proof.
  intros a lo n [H|H]; unfold rwin.
  - replace (lo <=? a) with false by (symmetry; apply Z.leb_gt; lia). reflexivity.
  - replace (a <? lo + n) with false by (symmetry; apply Z.ltb_ge; lia). apply andb_false_r.
Qed.

(* the bytes the run holds outside the FILE's first 272 words: the pending bytes, g_said and its shadow, and the
   two guard words *)
Definition rw_base : word -> option byte := fun w =>
  let a := bv_unsigned w in
  if rwin a (RW_F + AMF_BUF) RW_K
  then Some (Z_to_bv 8 (nth (Z.to_nat (a - (RW_F + AMF_BUF))) rw_pb 0))
  else if rwin a RW_SAID 4096 then Some (Z_to_bv 8 0)
  else if rwin a RW_SH_LO (RW_SH_HI - RW_SH_LO) then Some (Z_to_bv 8 0)
  else if rwin a LA_GOT_GUARD 8 then Some (Z_to_bv 8 (YO0f.le_byte LA_GUARD 8 (Z.to_nat (a - LA_GOT_GUARD))))
  else if rwin a LA_GUARD 8 then Some (Z_to_bv 8 (YO0f.le_byte RW_CANARY 8 (Z.to_nat (a - LA_GUARD))))
  else None.

(* the FILE's words on top of it (AMemFile.v amf_state: fmemopen's stores, then the seven changing words and the
   three heads) *)
Definition rw_mem : word -> option byte :=
  amf_state link_amf rw_base RW_F AF_NORD AU32M1
    (RW_F + AMF_BUF + AMF_BUFSIZ) (RW_F + AMF_BUF + RW_K) (RW_F + AMF_BUF) 0 0.

(* a byte the FILE's stores do not touch *)
Definition rw_out (a : Z) : Prop :=
  0 <= a < 2 ^ 64 /\ ~ (RW_F <= a < RW_F + AMF_ZEROED) /\
  ~ (RW_SINK <= a < RW_SINK + 8) /\ ~ (RW_SAY <= a < RW_SAY + 8) /\ ~ (RW_OFL <= a < RW_OFL + 8).

Lemma rw_mem_out : forall segs a, rw_out a -> mbyte segs rw_mem a = mbyte segs rw_base a.
Proof.
  intros segs a (Ha & H1 & H2 & H3 & H4).
  unfold rw_mem, amf_state, amf_heads_set.
  repeat (rewrite amf_upd_out;
    [| exact Ha
     | cbv [link_amf amf_sink_addr amf_say_addr amf_ofl_head amf_ofl_lock] in *;
       unfold RW_SINK, RW_SAY, RW_OFL in *; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia]).
  rewrite amf_dynw_out by (exact Ha || (unfold AMF_ZEROED in *; lia)).
  rewrite amf_fm_out by (exact Ha || (unfold AMF_ZEROED in *; lia)).
  reflexivity.
Qed.

Lemma rw_rd_out : forall segs a, rw_out a -> amf_rd segs rw_mem a = amf_rd segs rw_base a.
Proof. intros segs a H. unfold amf_rd. rewrite (rw_mem_out segs a H). reflexivity. Qed.

Ltac rw_outside :=
  unfold rw_out, RW_F, RW_SINK, RW_SAY, RW_OFL, RW_SAID, RW_SH_LO, RW_SH_HI, AMF_ZEROED, AMF_BUF, RW_K,
    LA_GOT_GUARD, LA_GUARD in *;
  repeat split; lia.

(* the field tactic of AMemFile.v (its Ltac is local to its section), over the exported update lemmas *)
Ltac rw_ar := cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; unfold AMF_COOKIE, AMF_BUF, AMF_BUFSIZ, AMF_BLOCK in *; lia.
Ltac rw_fld :=
  repeat first
    [ apply amf_val_mem_upd_same; rw_ar
    | apply amf_val_mem_upd_zero; rw_ar
    | apply amf_val_mem_upd_other; [rw_ar | rw_ar | rw_ar | ] ].

(* ==========================================================================
   3. The FILE at f
   ========================================================================== *)

Lemma rw_block_off_img : forall i, 0 <= i < AMF_BLOCK -> ~ in_img tfibsegs (RW_F + i).
Proof.
  intros i Hi Hin. apply link_ain_img_range in Hin. unfold AMF_BLOCK, RW_F in *. lia.
Qed.

Lemma rw_place : amf_place link_amf RW_F.
Proof.
  apply link_amf_place; [unfold RW_F; lia | unfold RW_F, AMF_BLOCK; lia | reflexivity | exact rw_block_off_img].
Qed.

Lemma rw_amemfile : forall segs, amemfile_at segs link_amf rw_mem RW_F.
Proof.
  intros segs. unfold rw_mem.
  apply (amf_state_at segs link_amf); [exact rw_place | cbn; lia | left; reflexivity | right; reflexivity | | lia |].
  - right. exists RW_K. split; [unfold RW_K, AMF_BUFSIZ; lia|]. split; [reflexivity|]. split; reflexivity.
  - cbn. lia.
Qed.

Lemma rw_win : forall segs, amf_win segs rw_mem RW_F RW_K.
Proof.
  intros segs. right.
  unfold rw_mem, amf_state, amf_heads_set, amf_dynw, amf_fm.
  split; [unfold RW_K, AMF_BUFSIZ; lia|].
  pose proof rw_place as HP. unfold amf_place, amf_apart in HP.
  cbv [link_amf amf_sink_addr amf_say_addr amf_ofl_head amf_ofl_lock amf_close amf_read amf_write amf_seek
       amf_size amf_buf amf_mode amf_threaded amf_need_locks] in HP |- *.
  unfold RW_F, RW_K in *.
  split; [rw_fld | split; rw_fld].
Qed.

Lemma rw_k_ok : forall segs, amf_k segs link_amf rw_mem RW_F RW_K.
Proof. intros segs. split; [exact (rw_amemfile segs) | exact (rw_win segs)]. Qed.

Lemma rw_dyn : forall segs,
  amf_dyn segs link_amf rw_mem RW_F AF_NORD AU32M1
    (RW_F + AMF_BUF + AMF_BUFSIZ) (RW_F + AMF_BUF + RW_K) (RW_F + AMF_BUF) 0 0.
Proof.
  intros segs. unfold amf_dyn.
  split; [unfold AF_NORD; lia|]. split; [unfold AU32M1; lia|].
  split; [unfold RW_F, AMF_BUF, AMF_BUFSIZ; lia|]. split; [unfold RW_F, AMF_BUF, RW_K; lia|].
  split; [unfold RW_F, AMF_BUF; lia|]. split; [lia|]. split; [cbn; lia|].
  unfold rw_mem, amf_state, amf_heads_set, amf_dynw, amf_fm.
  cbv [link_amf amf_sink_addr amf_say_addr amf_ofl_head amf_ofl_lock amf_close amf_read amf_write amf_seek
       amf_size amf_buf amf_mode amf_threaded amf_need_locks].
  unfold RW_F, RW_K.
  repeat (split; [rw_fld|]). rw_fld.
Qed.

Lemma rw_pend : forall segs, amf_pend segs rw_mem RW_F rw_pb.
Proof.
  intros segs i Hi. change (length rw_pb) with 60%nat in Hi.
  rewrite rw_rd_out by rw_outside.
  unfold amf_rd, mbyte, rw_base.
  rewrite amf_unsigned64 by (unfold RW_F, AMF_BUF; lia).
  rewrite rwin_true by (unfold RW_F, AMF_BUF, RW_K; lia).
  cbv beta iota zeta.
  replace (Z.to_nat (RW_F + AMF_BUF + Z.of_nat i - (RW_F + AMF_BUF))) with i by lia.
  cbn [option_map]. f_equal.
  pose proof (rw_pb_range i ltac:(change (length rw_pb) with 60%nat; lia)) as Hr.
  rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. apply Z.mod_small. exact Hr.
Qed.

(* ==========================================================================
   4. g_said: its bytes, its shadow, and that it is not the runtime's
   ========================================================================== *)

Lemma rw_said_byte : forall a, RW_SAID <= a < RW_SAID + 4096 -> rw_mem (Z_to_bv 64 a) = Some (Z_to_bv 8 0).
Proof.
  intros a Ha.
  assert (Hm : forall segs, mbyte segs rw_mem a = mbyte segs rw_base a) by (intros segs; apply rw_mem_out; rw_outside).
  assert (Hb : rw_base (Z_to_bv 64 a) = Some (Z_to_bv 8 0)).
  { unfold rw_base. rewrite amf_unsigned64 by (unfold RW_SAID in *; lia).
    rewrite rwin_false by (unfold RW_F, AMF_BUF, RW_K, RW_SAID in *; lia).
    rewrite rwin_true by (unfold RW_SAID in *; lia). reflexivity. }
  specialize (Hm []). unfold mbyte in Hm. rewrite Hb in Hm.
  destruct (rw_mem (Z_to_bv 64 a)) as [b|]; [injection Hm as <-; reflexivity|].
  cbn in Hm. destruct (seg_rom [] (Z_to_bv 64 a)); discriminate.
Qed.

Lemma rw_said_writable : forall segs a, RW_SAID <= a < RW_SAID + 4096 -> writable_at segs rw_mem a.
Proof.
  intros segs a Ha. unfold writable_at, wview. rewrite (rw_said_byte a Ha). discriminate.
Qed.

Lemma rw_shadow_zero : forall segs s, RW_SH_LO <= s < RW_SH_HI -> amf_rd segs rw_mem s = Some 0.
Proof.
  intros segs s Hs. rewrite rw_rd_out by rw_outside.
  unfold amf_rd, mbyte, rw_base. rewrite amf_unsigned64 by (unfold RW_SH_LO, RW_SH_HI in *; lia).
  rewrite rwin_false by (unfold RW_F, AMF_BUF, RW_K, RW_SH_LO, RW_SH_HI in *; lia).
  rewrite rwin_false by (unfold RW_SAID, RW_SH_LO, RW_SH_HI in *; lia).
  rewrite rwin_true by lia. reflexivity.
Qed.

Lemma rw_said_ra : forall segs,
  range_addressable (amf_rd segs rw_mem) SHADOW_OFF (amf_buf link_amf) (amf_size link_amf).
Proof.
  intros segs x Hx. cbv [amf_buf amf_size link_amf] in Hx.
  exists 0. split; [|left; reflexivity].
  apply rw_shadow_zero.
  assert (H1 : 0x62fee0 / 8 <= x / 8) by (apply Z.div_le_mono; lia).
  assert (H2 : x / 8 <= 0x630edf / 8) by (apply Z.div_le_mono; lia).
  assert (E1 : 0x62fee0 / 8 = 810972) by reflexivity.
  assert (E2 : 0x630edf / 8 = 811483) by reflexivity.
  rewrite E1 in H1. rewrite E2 in H2. clear E1 E2 Hx.
  unfold shadow_of_addr, SHADOW_OFF, RW_SH_LO, RW_SH_HI.
  set (q := x / 8) in *. clearbody q. lia.
Qed.

Lemma rw_said_hull : forall segs,
  shadow_hull_vis (amf_rd segs rw_mem) (amf_buf link_amf) (amf_size link_amf).
Proof.
  intros segs s Hs. cbv [amf_buf amf_size link_amf] in Hs.
  rewrite rw_shadow_zero; [discriminate|].
  unfold shadow_addr, SHADOW_OFF in Hs.
  assert (E1 : (2147450880 + 0x62fee0 / 8) / 8 * 8 = 2148261848) by reflexivity.
  assert (E2 : (2147450880 + (0x62fee0 + 4096 - 1) / 8) / 8 * 8 + 8 = 2148262368) by reflexivity.
  rewrite E1, E2 in Hs. unfold RW_SH_LO, RW_SH_HI. lia.
Qed.

(* No range of the frame's owned-static list meets g_said, so AR's owned-image law gives ~ aowned for every byte
   of it (the walk's step; Tfib_owned_static is as_owned_static PcapB). *)
Definition rw_disj_said (r : Z * Z) : bool := (fst r + snd r <=? RW_SAID) || (RW_SAID + 4096 <=? fst r).

Lemma rw_owned_disj : forallb rw_disj_said Tfib_owned_static = true.
Proof. vm_compute. reflexivity. Qed.

Lemma rw_said_not_owned_static : forall a, RW_SAID <= a < RW_SAID + 4096 ->
  ~ Exists (in_zr a) Tfib_owned_static.
Proof.
  intros a Ha Hex. rewrite Exists_exists in Hex. destruct Hex as (r & Hin & Hr).
  pose proof (proj1 (forallb_forall _ _) rw_owned_disj r Hin) as Hd.
  unfold rw_disj_said in Hd. unfold in_zr in Hr.
  apply orb_prop in Hd as [Hd|Hd]; apply Z.leb_le in Hd; lia.
Qed.

(* ==========================================================================
   5. The three cells, and the stack window
   ========================================================================== *)

(* The two guard words, byte by byte. The reads go through amf_unsigned64, never through a computation on a
   bit-vector term: evaluating Z_to_bv under vm_compute normalises its well-formedness proof as well. *)
Lemma rw_base_cell : forall a lo v, 0 <= a < 2 ^ 64 -> lo <= a < lo + 8 ->
  (lo = LA_GOT_GUARD /\ v = LA_GUARD) \/ (lo = LA_GUARD /\ v = RW_CANARY) ->
  rw_base (Z_to_bv 64 a) = Some (Z_to_bv 8 (YO0f.le_byte v 8 (Z.to_nat (a - lo)))).
Proof.
  intros a lo v Ha Hr Hc. unfold rw_base. rewrite amf_unsigned64 by exact Ha.
  unfold LA_GOT_GUARD, LA_GUARD, RW_F, AMF_BUF, RW_K, RW_SAID, RW_SH_LO, RW_SH_HI in *.
  destruct Hc as [(-> & ->) | (-> & ->)].
  - rewrite rwin_false by lia. rewrite rwin_false by lia. rewrite rwin_false by lia.
    rewrite rwin_true by lia. reflexivity.
  - rewrite rwin_false by lia. rewrite rwin_false by lia. rewrite rwin_false by lia.
    rewrite rwin_false by lia. rewrite rwin_true by lia. reflexivity.
Qed.

Lemma rw_rd_cell : forall segs a lo v, lo <= a < lo + 8 ->
  (lo = LA_GOT_GUARD /\ v = LA_GUARD) \/ (lo = LA_GUARD /\ v = RW_CANARY) ->
  amf_rd segs rw_mem a = Some (YO0f.le_byte v 8 (Z.to_nat (a - lo))).
Proof.
  intros segs a lo v Hr Hc.
  assert (Ha : 0 <= a < 2 ^ 64)
    by (destruct Hc as [(-> & _) | (-> & _)]; unfold LA_GOT_GUARD, LA_GUARD in *; lia).
  rewrite rw_rd_out by (destruct Hc as [(-> & _) | (-> & _)]; rw_outside).
  unfold amf_rd, mbyte. rewrite (rw_base_cell a lo v Ha Hr Hc). cbn [option_map]. f_equal.
  rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
  apply Z.mod_small. unfold YO0f.le_byte. apply Z.mod_pos_bound. lia.
Qed.

Ltac rw_cell lo v :=
  rewrite (rw_rd_cell _ lo lo v) by (unfold LA_GOT_GUARD, LA_GUARD; (lia || tauto));
  repeat (rewrite (rw_rd_cell _ _ lo v) by (unfold LA_GOT_GUARD, LA_GUARD; (lia || tauto))).

Lemma rw_got_guard : forall segs, rdword (amf_rd segs rw_mem) LA_GOT_GUARD = Some LA_GUARD.
Proof.
  intros segs. unfold rdword.
  repeat (rewrite (rw_rd_cell segs _ LA_GOT_GUARD LA_GUARD)
            by (first [unfold LA_GOT_GUARD; lia | left; split; reflexivity])).
  unfold LA_GOT_GUARD, LA_GUARD, YO0f.le_byte. reflexivity.
Qed.

Lemma rw_guard_word : forall segs, rdword (amf_rd segs rw_mem) LA_GUARD = Some RW_CANARY.
Proof.
  intros segs. unfold rdword.
  repeat (rewrite (rw_rd_cell segs _ LA_GUARD RW_CANARY)
            by (first [unfold LA_GUARD; lia | right; split; reflexivity])).
  unfold LA_GUARD, RW_CANARY, YO0f.le_byte. reflexivity.
Qed.

Lemma rw_said_off_window : forall K a, 0 <= K <= ARW_STK -> RW_SAID <= a < RW_SAID + 4096 ->
  ~ (RW_SP - K <= a < RW_SP).
Proof.
  intros K a HK Ha. unfold ARW_STK, ESTACK in HK. unfold RW_SAID, RW_SP in *. lia.
Qed.

(* ==========================================================================
   6. The witness
   ========================================================================== *)

(* Every premise of arewind_mf_realizes (and of amwrite_mf_flush_realizes, at K = AMW_STK) that speaks of the
   memory or of arithmetic, at the state of the second mark. *)
Definition rw_sat (segs : list Segment) (K : Z) : Prop :=
  amf_k segs link_amf rw_mem RW_F RW_K /\
  amf_dyn segs link_amf rw_mem RW_F AF_NORD AU32M1
    (RW_F + AMF_BUF + AMF_BUFSIZ) (RW_F + AMF_BUF + RW_K) (RW_F + AMF_BUF) 0 0 /\
  amf_pend segs rw_mem RW_F rw_pb /\ Z.of_nat (length rw_pb) = RW_K /\
  0 <= amf_buf link_amf /\ amf_buf link_amf + amf_size link_amf <= 2 ^ 63 /\
  0 < amf_size link_amf < 2 ^ 32 /\
  (forall a, amf_buf link_amf <= a < amf_buf link_amf + amf_size link_amf ->
     writable_at segs rw_mem a /\ ~ Exists (in_zr a) Tfib_owned_static /\ ~ (RW_SP - K <= a < RW_SP)) /\
  amem_range (amf_buf link_amf) (amf_size link_amf) /\
  range_addressable (amf_rd segs rw_mem) SHADOW_OFF (amf_buf link_amf) (amf_size link_amf) /\
  shadow_hull_vis (amf_rd segs rw_mem) (amf_buf link_amf) (amf_size link_amf) /\
  rdword (amf_rd segs rw_mem) LA_GOT_GUARD = Some LA_GUARD /\
  (exists g, rdword (amf_rd segs rw_mem) LA_GUARD = Some g).

Theorem rw_sat_ok : forall segs K, 0 <= K <= ARW_STK -> rw_sat segs K.
Proof.
  intros segs K HK. unfold rw_sat.
  split; [exact (rw_k_ok segs)|]. split; [exact (rw_dyn segs)|].
  split; [exact (rw_pend segs)|]. split; [exact rw_pb_len|].
  split; [cbv [amf_buf link_amf]; lia|].
  split; [cbv [amf_buf amf_size link_amf]; lia|].
  split; [cbv [amf_size link_amf]; lia|].
  split.
  { intros a Ha. cbv [amf_buf amf_size link_amf] in Ha.
    split; [apply rw_said_writable; unfold RW_SAID; lia|].
    split; [apply rw_said_not_owned_static; unfold RW_SAID; lia|].
    apply (rw_said_off_window K); [exact HK | unfold RW_SAID; lia]. }
  split; [cbv [amf_buf amf_size link_amf]; unfold amem_range, kLowMemEnd; left; lia|].
  split; [exact (rw_said_ra segs)|]. split; [exact (rw_said_hull segs)|].
  split; [exact (rw_got_guard segs)|].
  exists RW_CANARY. exact (rw_guard_word segs).
Qed.

(* the witness of the two contracts' windows *)
Corollary rw_sat_rewind : forall segs, rw_sat segs ARW_STK.
Proof. intros segs. apply rw_sat_ok. unfold ARW_STK, ESTACK. lia. Qed.

Corollary rw_sat_flush : forall segs, rw_sat segs AMW_STK.
Proof. intros segs. apply rw_sat_ok. unfold AMW_STK, ARW_STK, ESTACK. lia. Qed.

(* The reader the contracts use IS this memory's: a run whose hidden set leaves these bytes present has
   `mrestrict (w_H W) mem = rw_mem`, and then `aview segs (w_H W) mem = amf_rd segs rw_mem`. *)
Lemma rw_aview_rd : forall segs (H : word -> bool) (mem : word -> option byte),
  aview segs H mem = amf_rd segs (mrestrict H mem).
Proof. intros segs H mem. reflexivity. Qed.
