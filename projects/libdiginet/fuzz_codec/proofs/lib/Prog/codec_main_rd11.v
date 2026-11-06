(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c. *)
(* Modified by Theorem Labs: for reac-repacer/fuzz_uci. Sections G / G2 are
   libreac/fuzz_decode's released lib/Prog/crt_glue.v with its module paths changed and its one decode-specific
   import (check_braid_c, for braid_map) dropped. Section Body is the invariant layer of that release's
   lib/Prog/check_round_trip.v `Section Body` (cr_inv, cr_pre, cr_inv_call, cr_inv_A, cr_inv_kept, cr_heap_E,
   cr_free_keep, cr_old_in, cr_frame_call), with the one change that the function's own stack size is the section
   variable K instead of decode's CRT_STACK, and with cr_frame_call generalised from decode's fixed frame cell list
   to any (base, cells): so fuzz_uci's check_no_overread and check_value, whose frames differ, share one copy. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_uci/lib/Prog/CheckGlue.v, with its module paths changed; 187 of its 423 lines of code are new or changed and 255 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_wire/lib/Prog/cc_glue.v, with its module paths changed; 503 of its 621 lines of code are new or changed and 305 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_codec/lib/KindBGlue.v, with its module names changed; 185 of its 205 lines of code are new or changed and 601 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_codec/lib/Prog/codec_main_rd14.v, with its module names, addresses and numbers changed; 204 of its 263 lines of code are new or changed and 146 lines of the source are left out. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_owe codec_cells codec_img codec_main_inv
  codec_main_rdb_lib memcpy_c diginet_sysex_encode_c LLVMFuzzerTestOneInput_c.
Import ListNotations.
Open Scope Z_scope.

Ltac addr_eq_tac ::= first [ apply wa_of_var; lia
                           | symmetry; first [ apply wa_of_Z_to_bv; lia | apply wa_of_var; lia | unfold wa; f_equal; lia ] ].

(** Segment RD11 of the walk of LLVMFuzzerTestOneInput in the plain image: the SYSEX reader (u8 a and b, the
    length byte % 25, memcpy of the payload, diginet_sysex_encode), to JOIN. *)

(** ---- bytes and cells ---- *)

Lemma bytes_at_subZ : forall m a bs (k : Z) n, bytes_at rsegs m a bs -> 0 <= k -> (Z.to_nat k + n <= length bs)%nat ->
  bytes_at rsegs m (a + k) (firstn n (skipn (Z.to_nat k) bs)).
Proof.
  intros m a bs k n H Hk Hkn.
  rewrite <- (firstn_skipn (Z.to_nat k) bs) in H. apply bytes_at_app in H. destruct H as [_ H].
  rewrite length_firstn in H. replace (Nat.min (Z.to_nat k) (length bs)) with (Z.to_nat k) in H by lia.
  rewrite Z2Nat.id in H by lia.
  rewrite <- (firstn_skipn n (skipn (Z.to_nat k) bs)) in H. apply bytes_at_app in H. destruct H as [H _]. exact H.
Qed.

Lemma Forall_zb : forall l, Forall (fun x => 0 <= x < 256) (zb l).
Proof.
  intros l. unfold zb. apply Forall_forall. intros x Hx. apply in_map_iff in Hx. destruct Hx as (b & <- & _).
  pose proof (bv_unsigned_in_range 8 b) as H. unfold bv_modulus in H. change (2 ^ Z.of_N 8) with 256 in H. lia.
Qed.

(** The length byte % 25 as 0x1345c-0x13474 compute it (x * 0x29 >> 10 is x / 25, subw, andi 0xff). *)
Lemma sx_mod25 : forall x, 0 <= x < 256 ->
  Z.land (bv_swrap 32 (x - (Z.shiftr (x * 41) 10 * 25) mod 18446744073709551616) mod 18446744073709551616) 255
  = x mod 25.
Proof.
  intros x H. apply Z.eqb_eq.
  refine (zall_range (fun y => Z.land (bv_swrap 32 (y - (Z.shiftr (y * 41) 10 * 25) mod 18446744073709551616)
                                 mod 18446744073709551616) 255 =? y mod 25) 0 256 _ x H).
  vm_compute. reflexivity.
Qed.

(** A run of j cells from cell i replaced by cells with the same bytes. *)
Lemma rw_cells_splice : forall m A cs i j mid',
  rw_cells rsegs m A cs ->
  cells_bytes mid' = cells_bytes (firstn j (skipn i cs)) -> cells_size mid' = cells_size (firstn j (skipn i cs)) ->
  cells_wf mid' ->
  rw_cells rsegs m A (firstn i cs ++ mid' ++ skipn (i + j) cs).
Proof.
  intros m A cs i j mid' [[Hwf Hb] Hw] Hby Hsz Hmw.
  assert (E : cs = firstn i cs ++ firstn j (skipn i cs) ++ skipn (i + j) cs).
  { rewrite <- (firstn_skipn i cs) at 1. f_equal. rewrite <- (firstn_skipn j (skipn i cs)) at 1. f_equal.
    rewrite skipn_skipn. f_equal. lia. }
  rewrite E in Hwf, Hb, Hw.
  apply cells_wf_app in Hwf. destruct Hwf as [W1 W23]. apply cells_wf_app in W23. destruct W23 as [W2 W3].
  split; [split|].
  - apply cells_wf_app. split; [exact W1|]. apply cells_wf_app. split; assumption.
  - rewrite !cells_bytes_app in *. rewrite Hby. exact Hb.
  - rewrite !cells_size_app in *. rewrite Hsz. exact Hw.
Qed.

Lemma rw_cells_merge_CB2 : forall m A n1 b1 n2 b2,
  rw_cells rsegs m A [CB n1 b1; CB n2 b2] -> rw_cells rsegs m A [CB (n1 + n2) (b1 ++ b2)].
Proof.
  intros m A n1 b1 n2 b2 H.
  pose proof (rw_cells_merge rsegs m A [] [CB n1 b1; CB n2 b2] []) as M. cbn [app] in M. specialize (M H).
  cbn [cells_size csize cells_bytes cbytes] in M. rewrite Nat.add_0_r, app_nil_r in M. exact M.
Qed.

Lemma rw_cells_join2 : forall m A B cs1 cs2,
  rw_cells rsegs m A cs1 -> rw_cells rsegs m B cs2 -> B = A + Z.of_nat (cells_size cs1) ->
  rw_cells rsegs m A (cs1 ++ cs2).
Proof. intros m A B cs1 cs2 H1 H2 ->. apply rw_cells_app_join; assumption. Qed.

(** The frame at 0x13a38 (a and b stored as words, k.bytes and k.n as HEAD left them). *)
Definition rd11_cells (pv dv : Z) (wA wB inp inn : word) (tl : list byte) : list cell :=
  [C8 (Z_to_bv 64 0x5cb0); C8 (Z_to_bv 64 0x13f0); C4 (Z_to_bv 64 11); CB 4 (fz0 4); C8 (Z_to_bv 64 pv);
   C8 (Z_to_bv 64 dv); C4 wA; C4 wB; C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); CB 24 (fz0 24);
   C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); CB 32 (fa5 32); CB 32 (fa5 32); C4 (Z_to_bv 64 0); CB 24 (fz0 24);
   C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 inp; C8 inn; CB 80 tl].

(** 0x13a38-0x13a6c: in.p += take, in.n -= take, k.n = take, memcpy(&k.bytes, cur, take),
    diginet_sysex_encode((u8) a, (u8) b, &k.bytes, k.n, &k.out), j JOIN. a0 = in.n, a1 = the cursor, a2 = take. *)
Lemma rd11_tail : memcpy_contract -> diginet_sysex_encode_contract -> forall e fuel, env_ok e -> join_ok e fuel ->
  forall (ra' t0' t1' t2' a0w a1w a2w a3' a4' a5' a6' a7' s8' s10' t3' t4' t5' t6' ops wA wB inp inn : word)
         (pv dv : Z) (od : option desk) (c rem t : Z) (tl : list byte) (m1 : word -> option byte),
    rw_cells rsegs m1 (bv_unsigned (e_sp e) + -400) (rd11_cells pv dv wA wB inp inn tl) ->
    fr_ok e m1 ->
    fuel_ok ops (S fuel) -> pd_ok pv dv od -> cur_ok e c rem ->
    inp = Z_to_bv 64 (bv_unsigned (e_p e) + c) -> inn = Z_to_bv 64 rem -> a0w = Z_to_bv 64 rem ->
    bv_unsigned a1w = bv_unsigned (e_p e) + c -> bv_unsigned a2w = t -> 0 <= t <= rem -> t <= 24 ->
    bv_unsigned wA < 256 -> bv_unsigned wB < 256 ->
    evt rsegs (Qk e)
      (st e (body_regs e ra' t0' t1' t2' a0w a1w a2w a3' a4' a5' a6' a7' (Z_to_bv 64 pv) ops s8' s10' t3' t4' t5' t6')
          0x13a38 m1).
Proof.
  intros MC CS e fuel HE JN ra' t0' t1' t2' a0w a1w a2w a3' a4' a5' a6' a7' s8' s10' t3' t4' t5' t6' ops wA wB inp inn
         pv dv od c rem t tl m1 FR HFR HF HPD HC -> -> -> Ha1 Ha2 Ht Ht24 HwA HwB.
  unfold st, body_regs.
  pose proof (bv_unsigned_in_range 64 (e_sp e)) as Rsp. unfold bv_modulus in Rsp.
  pose proof (bv_unsigned_in_range 64 (e_p e)) as Rp. unfold bv_modulus in Rp.
  pose proof HE as (_ & _ & _ & HLO & _ & DJ & HPB & _).
  pose proof (data_of_fr e m1 HE HFR) as HD.
  destruct HFR as (SV & ST & MU & WM & HMI).
  unfold LLVM_CODEC_STACK in *.
  pose proof ST as [Hlo0 _].
  pose proof HC as (Hc0 & Hr0 & Hcr).
  assert (USP : bv_unsigned (Z_to_bv 64 (bv_unsigned (e_sp e) + -400)) = bv_unsigned (e_sp e) + -400)
    by (apply unsigned_lit; lia).
  assert (U344 : bv_unsigned (Z_to_bv 64 (bv_unsigned (e_sp e) + -344)) = bv_unsigned (e_sp e) + -344)
    by (apply unsigned_lit; lia).
  assert (Htn : Z.of_nat (Z.to_nat t) = t) by lia.
  set (src := firstn (Z.to_nat t) (skipn (Z.to_nat c) (e_data e))).
  assert (Hlen : length src = Z.to_nat t) by (unfold src; rewrite length_firstn, length_skipn; lia).
  unfold rd11_cells in FR.
  do 7 zstep.
  (* k.bytes cut at take for memcpy *)
  destruct (rw_cells_cut3 _ _ _ 10%nat (CB 24 (fz0 24)) FR eq_refl) as (PRE & MID & POST). clear FR.
  norm_piece PRE. norm_piece MID. norm_piece POST.
  replace (bv_unsigned (e_sp e) + -400 + 56) with (bv_unsigned (e_sp e) + -344) in MID, POST by lia.
  apply (rw_cells_split_CB rsegs _ _ [] 24 (fz0 24) [] [Z.to_nat t; (24 - Z.to_nat t)%nat]) in MID;
    [ | cbn [sum_nat]; lia ].
  cbn [app mk_CB_cells] in MID.
  destruct (rw_cells_cut3 _ _ _ 0%nat _ MID eq_refl) as (_ & MIDa & MIDb). clear MID.
  norm_piece MIDa. norm_piece MIDb.
  replace (bv_unsigned (e_sp e) + -344 + 0) with (bv_unsigned (e_sp e) + -344) in MIDa, MIDb by lia.
  unfold memcpy_contract in MC.
  call (MC _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ src (firstn (Z.to_nat t) (fz0 24))).
  - rewrite Ha1. apply bytes_at_subZ; [exact HD | lia | lia].
  - rewrite Ha2. exact Hlen.
  - rewrite U344, Ha2. exact MIDa.
  - rewrite U344, Ha1, Ha2. lia.
  - exact HMI.
  - rewrite ?USP, ?U344, ?Ha2 in *.
    match goal with H : rw_cells rsegs _ (bv_unsigned (e_sp e) + -344) [CB _ src] |- _ => rename H into MIDc end.
    pose proof MIDc as [[_ HSRC] _]. cbn [cells_bytes cbytes] in HSRC. rewrite app_nil_r in HSRC.
    pose proof (rw_cells_join2 _ _ _ _ _ MIDc MIDb ltac:(cbn [cells_size csize]; lia)) as J.
    apply rw_cells_merge_CB2 in J.
    replace (Z.to_nat t + (24 - Z.to_nat t))%nat with 24%nat in J by lia.
    pose proof (rw_cells_join3 _ _ _ _ _ _ _ PRE J POST ltac:(norm_sizes; lia) ltac:(norm_sizes; lia)) as FULL.
    clear PRE J POST MIDc MIDb.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (HRa : ov_read_bytes rsegs mm (wa (bv_unsigned (e_sp e) + -400 + 40)) 1 = Some [Z_to_bv 8 (bv_unsigned wA)]);
      [ pose proof FULL as [[Hwf HBY] _];
        rewrite (bytes_at_read rsegs _ _ _ 40 1 HBY) by (try lia; rewrite cells_bytes_length by exact Hwf; cbn; lia);
        reflexivity | ];
      assert (HRb : ov_read_bytes rsegs mm (wa (bv_unsigned (e_sp e) + -400 + 44)) 1 = Some [Z_to_bv 8 (bv_unsigned wB)]);
      [ pose proof FULL as [[Hwf HBY] _];
        rewrite (bytes_at_read rsegs _ _ _ 44 1 HBY) by (try lia; rewrite cells_bytes_length by exact Hwf; cbn; lia);
        reflexivity | ]
    end.
    zstep. zstep. clear HRa HRb.
    do 4 zstep.
    cbn [app] in FULL.
    destruct (rw_cells_cut3 _ _ _ 14%nat (CB 32 (fa5 32)) FULL eq_refl) as (PRE & OUT & POST). clear FULL.
    norm_piece PRE. norm_piece OUT. norm_piece POST.
    replace (bv_unsigned (e_sp e) + -400 + 124) with (bv_unsigned (e_sp e) + -276) in OUT, POST by lia.
    assert (U276 : bv_unsigned (Z_to_bv 64 (bv_unsigned (e_sp e) + -276)) = bv_unsigned (e_sp e) + -276)
      by (apply unsigned_lit; lia).
    set (dev := bv_unsigned wA mod 256). set (fn := bv_unsigned wB mod 256).
    unfold diginet_sysex_encode_contract, DIGINET_SYSEX_ENCODE, DIGINET_SYSEX_ENCODE_DEPTH in CS.
    call (CS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (e_lo e) dev fn src (fa5 32)).
    { unfold diginet_sysex_encode_pre, DIGINET_SYSEX_ENCODE_DEPTH. rewrite U344, U276, USP.
      split; [ split; [ unfold dev; apply Z.mod_pos_bound; lia | f_equal; rewrite Z_to_bv_unsigned; reflexivity ] | ].
      split; [ split; [ unfold fn; apply Z.mod_pos_bound; lia | f_equal; rewrite Z_to_bv_unsigned; reflexivity ] | ].
      split; [lia|]. split; [exact HSRC|]. split; [rewrite Ha2, Hlen; lia|].
      split; [lia|]. split; [exact OUT|]. split; [unfold disj; rewrite Hlen; lia|].
      split; [lia|]. split; [lia|]. split; [exact MI|]. split; [eassumption | lia]. }
    rewrite ?USP, ?U276, ?U344 in *.
    match goal with H : context [sysex_spec dev fn (zb src)] |- _ =>
      rewrite (surjective_pairing (sysex_spec dev fn (zb src))) in H; cbv beta iota in H; destruct H as [Ea0 OUT2] end.
    rewrite Ea0.
    zstep.
    rewrite <- (Z_to_bv_bv_unsigned wA), <- (Z_to_bv_bv_unsigned wB), <- (Z_to_bv_bv_unsigned a2w), Ha2 in PRE.
    rewrite Ha1 in POST.
    replace (bv_unsigned (e_p e) + c + t) with (bv_unsigned (e_p e) + (c + t)) in POST by lia.
    pose proof (rw_cells_join3 _ _ _ _ _ _ _ PRE OUT2 POST ltac:(norm_sizes; lia) ltac:(norm_sizes; lia)) as FJ.
    set (R := firstn (24 - Z.to_nat t) (skipn (Z.to_nat t) (fz0 24))) in FJ.
    assert (HR : length R = (24 - Z.to_nat t)%nat)
      by (unfold R, fz0; rewrite length_firstn, length_skipn, repeat_length; lia).
    set (k := mkKcall 11 (fz0 4) pv dv (bv_unsigned wA) (bv_unsigned wB) 0 0 (src ++ R) t 0 (fa5 32)
                      (cmd_out (fa5 32) (snd (sysex_spec dev fn (zb src)))) 0 (fz0 24) 0 0 0).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (FB : rw_cells rsegs mm (bv_unsigned (e_sp e) + -400) (body_cells e k (c + t) (rem - t) tl))
        by exact FJ end.
    clear FJ PRE OUT2 POST.
    assert (EB : firstn (Z.to_nat t) (zb (src ++ R)) = zb src).
    { unfold zb. rewrite map_app, firstn_app, length_map, Hlen, Nat.sub_diag. cbn [firstn]. rewrite app_nil_r.
      apply firstn_all2. rewrite length_map, Hlen. lia. }
    assert (EK : sysex_spec dev fn (zb src) = enc_k k od).
    { unfold enc_k, k. cbn [k_kind k_a k_b k_c k_delta k_bytes k_n]. unfold enc_of_call. rewrite EB. reflexivity. }
    rewrite EK.
    unfold join_ok, st, body_regs in JN.
    eapply JN with (c := c + t) (rem := rem - t) (tl := tl);
      [ exact HF | | unfold cur_ok; lia | exact FB | unfold fr_ok; repeat (split; [eassumption|]); eassumption ].
    unfold rec_ok. split; [unfold k; cbn; lia|]. split; [exact HPD|]. split.
    { unfold rdr_k, reader_ok, k. cbn [k_kind k_a k_b k_c k_delta k_bytes k_n].
      pose proof (bv_unsigned_in_range 64 wA) as RwA. pose proof (bv_unsigned_in_range 64 wB) as RwB.
      unfold bv_modulus in RwA, RwB.
      split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
      split; [unfold zb; rewrite length_map, length_app, Hlen, HR; lia|].
      split; [apply Forall_zb|]. split; [lia|].
      split; [intros; discriminate|]. split; [intros; discriminate|]. intros _; lia. }
    split; [reflexivity|]. rewrite <- EK. reflexivity.
Qed.

Ltac rd_close Hcur :=
  first [ reflexivity | (unfold cur_ok; lia) | (rewrite Hcur; f_equal; lia) | (f_equal; lia)
        | (rewrite <- Hcur; symmetry; apply Z_to_bv_bv_unsigned) | (rewrite unsigned_lit by lia; lia) | lia ].

(** A branch whose condition is false on literals (the taken goal is closed). *)
Ltac never_taken H := first [ if_cases H; [ exfalso; zify_cond H; lia | try zify_cond H ] | idtac ].
(** A branch whose condition is true on literals. *)
Ltac always_taken H := first [ if_cases H; [ try zify_cond H | exfalso; zify_cond H; lia ] | idtac ].

(** 0x13400-0x1347c, 0x13a24-0x13a34, 0x13b90-0x13ba0, 0x14934-0x14940: a = fuzz_u8 and b = fuzz_u8 (an
    empty input stores 0 into both with one 8-byte store), len = fuzz_u8 % 25, take = min(len, in.n); then
    the tail at 0x13a38. *)
Lemma codec_main_rd11 : S_rd11.
Proof.
  unfold S_rd11. intros MC CS e fuel HE JN.
  pose proof (rd11_tail MC CS e fuel HE JN) as TL. unfold st, body_regs in TL.
  unfold rd_ok, st, body_regs.
  intros ra' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s8' s10' t3' t4' t5' t6' ops pv dv od c rem tl m1
         HF HPD HC FR HFR.
  replace (rd_pc 11) with 0x13400 by (vm_compute; reflexivity).
  pose proof (bv_unsigned_in_range 64 (e_sp e)) as Rsp. unfold bv_modulus in Rsp.
  pose proof (bv_unsigned_in_range 64 (e_p e)) as Rp. unfold bv_modulus in Rp.
  pose proof HE as (_ & _ & _ & HLO & _ & DJ & HPB & _).
  pose proof (data_of_fr e m1 HE HFR) as HD.
  destruct HFR as (SV & ST & MU & WM & HMI).
  unfold LLVM_CODEC_STACK in *.
  pose proof ST as [Hlo0 _].
  pose proof HC as (Hc0 & Hr0 & Hcr).
  unfold body_cells in FR. cbn [kcall_cells k_rd k_kind k_pad k_p k_desk k_a k_b k_c k_delta k_bytes k_n k_rc
    k_before k_out k_want_rc k_want k_want_len k_want_key k_want_display app] in FR.
  set (cur := Z_to_bv 64 (bv_unsigned (e_p e) + c)) in FR.
  assert (Hcur : bv_unsigned cur = bv_unsigned (e_p e) + c) by (unfold cur; apply unsigned_lit; lia).
  clearbody cur.
  zstep. zstep.
  if_cases E0.
  { zify_cond E0. zstep. zstep.
    apply (rw_cells_splice _ _ _ 6 2 [C8 (Z_to_bv 64 0)]) in FR; [ | reflexivity | reflexivity | split; exact I ].
    cbn [firstn skipn app Nat.add] in FR.
    zstep.
    apply (rw_cells_splice _ _ _ 6 1 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)]) in FR;
      [ | reflexivity | reflexivity | repeat split ].
    cbn [firstn skipn app Nat.add] in FR.
    zstep. never_taken EB. zstep.
    eapply TL with (od := od) (c := c) (rem := rem) (t := 0);
      [ exact FR | exact (conj SV (conj ST (conj MU (conj WM HMI)))) | exact HF | exact HPD | .. ];
      rd_close Hcur. }
  zify_cond E0.
  do 5 zstep. in_byte0 cur c. zstep. zstep. zstep.
  if_cases E1.
  { zify_cond E1. do 3 zstep. zstep. never_taken EB. zstep. zstep.
    eapply TL with (od := od) (c := c + 1) (rem := rem - 1) (t := 0);
      [ exact FR | exact (conj SV (conj ST (conj MU (conj WM HMI)))) | exact HF | exact HPD | .. ];
      rd_close Hcur. }
  zify_cond E1.
  do 4 zstep. in_byte cur c 1. zstep. zstep. zstep.
  if_cases E2.
  2: { zify_cond E2. zstep. zstep. zstep. zstep. always_taken EB. zstep.
       eapply TL with (od := od) (c := c + 2) (rem := rem - 2) (t := 0);
         [ exact FR | exact (conj SV (conj ST (conj MU (conj WM HMI)))) | exact HF | exact HPD | .. ];
         rd_close Hcur. }
  zify_cond E2.
  do 4 zstep. in_byte cur c 2. zstep.
  do 7 zstep.
  set (x := bv_unsigned (nth (Z.to_nat (c + 2)) (e_data e) (Z_to_bv 8 0))) in *.
  assert (Rx : 0 <= x < 256) by (unfold x; change 256 with (2 ^ Z.of_N 8); exact Rb1).
  lazymatch goal with |- context [Z_to_bv 64 (Z.land ?X 255)] =>
    remember (Z_to_bv 64 (Z.land X 255)) as L eqn:EL end.
  assert (HL : bv_unsigned L = x mod 25).
  { rewrite EL, sx_mod25 by exact Rx. apply unsigned_lit. pose proof (Z.mod_pos_bound x 25 ltac:(lia)). lia. }
  clear EL. clearbody x.
  pose proof (Z.mod_pos_bound x 25 ltac:(lia)) as Rm.
  zstep.
  if_cases E3.
  { zify_cond E3. zstep.
    eapply TL with (od := od) (c := c + 3) (rem := rem - 3) (t := rem - 3);
      [ exact FR | exact (conj SV (conj ST (conj MU (conj WM HMI)))) | exact HF | exact HPD | .. ];
      rd_close Hcur. }
  zify_cond E3. zstep.
  eapply TL with (od := od) (c := c + 3) (rem := rem - 3) (t := x mod 25);
    [ exact FR | exact (conj SV (conj ST (conj MU (conj WM HMI)))) | exact HF | exact HPD | .. ];
    rd_close Hcur.
Qed.
