(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/varnish/esi_parse_fuzzer/lib/Lib/Step.v, with its module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/Lib/Step.v; 229 of its 247 lines of code are new or changed and 675 lines of the source are left out. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_owe codec_cells memcpy_c
  diginet_sysex_encode_c diginet_scribble_encode_c diginet_scribble_encode_lib.
Import ListNotations.
Open Scope Z_scope.

(** diginet_scribble_encode (diginet_codec.c:287-303; 164 bytes at 0x15a50, frame 0x40). The frame holds
    the saved ra, s0..s3 at sp-40..sp-1 and pl[10] at sp-50..sp-41; memcpy copies the scribble_chars
    characters to sp-48, and diginet_sysex_encode reads pl from sp-50 and writes out. *)

Local Ltac addr_eq_tac ::= first [ apply wa_of_var; lia
                           | symmetry; first [ apply wa_of_Z_to_bv; lia | apply wa_of_var; lia | unfold wa; f_equal; lia ] ].

Local Ltac cell_of_bytes bs ::=
  lazymatch bs with
  | le8 ?v => constr:(C8 v)
  | le4 ?v => constr:(C4 v)
  | le2 ?v => constr:(C2 v)
  | [?b] => constr:(C1 b)
  | le1 (zxb ?b) => constr:(C1 b)
  | le1 ?v => constr:(C1 (Z_to_bv 8 (bv_unsigned v)))
  end.

Local Ltac sc_splits := repeat match goal with |- _ /\ _ => split end.

(** Join the three frame pieces at S-64 (pl[0..1] and below), S-48 (the copied characters) and
    S-48+D (the rest of pl) into one piece at S-64, as the epilogue lemma takes it. *)
Local Ltac sc_join :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch goal with
    | H1 : rw_cells rsegs mm (?S + -64) ?c1,
      H2 : rw_cells rsegs mm (?S + -48) ?c2,
      H3 : rw_cells rsegs mm (?S + -48 + ?D) ?c3 |- _ =>
      let FLj := fresh "FLj" in
      assert (FLj : rw_cells rsegs mm (S + -64) (c1 ++ c2 ++ c3));
      [ apply sc_rw_join; [exact H1|];
        replace (S + -64 + Z.of_nat (cells_size c1)) with (S + -48) by (cbn [cells_size csize Nat.add]; lia);
        apply sc_rw_join; [exact H2|];
        replace (S + -48 + Z.of_nat (cells_size c2)) with (S + -48 + D) by (cbn [cells_size csize Nat.add]; lia);
        exact H3
      | clear H1 H2 H3; cbn [app] in FLj ]
    end
  end.

(** The contract's postcondition. *)
Definition sc_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (lo : Z) (a3 : word) (pd : option desk) (addr : Z) (cs before : list byte)
    : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F (ret_pc ra) fc None m' (seg_rom rsegs) /\
    munch [(bv_unsigned sp - DIGINET_SCRIBBLE_ENCODE_DEPTH, bv_unsigned sp); (bv_unsigned a3, bv_unsigned a3 + 32)] m m' /\
    wmono rsegs m m' /\
    mem_inv rsegs m' /\
    stk rsegs m' lo (bv_unsigned sp) /\
    let '(rc, o) := scribble_spec pd addr (zb cs) in
    a0' = Z_to_bv 64 rc /\ rw_cells rsegs m' (bv_unsigned a3) [CB 32 (cmd_out before o)].

(** The epilogue at 0x15ad8: reload ra, s0..s3, free the frame, return. *)
Lemma sc_exit : forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (lo : Z) (a3 : word) (pd : option desk) (addr : Z) (cs before : list byte)
    (ra' t0' t1' t2' x8 x9 a0' a1' a2' a3' a4' a5' a6' a7' x18 x19 t3' t4' t5' t6' : word)
    (m1 : word -> option byte) (cs1 : list cell) (rc : Z) (o : option cmd),
  rw_cells rsegs m1 (bv_unsigned sp + -64) cs1 ->
  cells_size cs1 = 24%nat ->
  rw_cells rsegs m1 (bv_unsigned sp + -40) [C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  stk rsegs m1 lo (bv_unsigned sp + -64) ->
  lo + 112 <= bv_unsigned sp ->
  munch [(bv_unsigned sp - 112, bv_unsigned sp); (bv_unsigned a3, bv_unsigned a3 + 32)] m m1 ->
  wmono rsegs m m1 ->
  mem_inv rsegs m1 ->
  rw_cells rsegs m1 (bv_unsigned a3) [CB 32 (cmd_out before o)] ->
  scribble_spec pd addr (zb cs) = (rc, o) ->
  a0' = Z_to_bv 64 rc ->
  evt rsegs (sc_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo a3 pd addr cs before)
    (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0' t1' t2' x8 x9 a0' a1' a2' a3' a4' a5' a6' a7'
             x18 x19 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
        F (Z_to_bv 64 0x15ad8) fc None m1 (seg_rom rsegs)).
Proof.
  intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo a3 pd addr cs before
         ra' t0' t1' t2' x8 x9 a0' a1' a2' a3' a4' a5' a6' a7' x18 x19 t3' t4' t5' t6' m1 cs1 rc o
         FL HS FS ST HLO MU WM HMI OUT HSPEC HA0.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  pose proof ST as [Hlo _].
  do 6 zstep.
  assert (FR : rw_cells rsegs m1 (bv_unsigned sp + -64) (cs1 ++ [C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])).
  { apply sc_rw_join; [exact FL|]. rewrite HS.
    replace (bv_unsigned sp + -64 + Z.of_nat 24) with (bv_unsigned sp + -40) by lia. exact FS. }
  clear FL FS.
  eapply stk_release in FR; [ | exact ST | lia ].
  rewrite cells_size_app, HS in FR. cbn [cells_size csize Nat.add] in FR.
  replace (bv_unsigned sp + -64 + Z.of_nat 64) with (bv_unsigned sp) in FR by lia.
  clear ST.
  zstep.
  unfold sc_post, DIGINET_SCRIBBLE_ENCODE_DEPTH.
  rewrite HSPEC.
  finish.
  all: split; assumption.
Qed.

Theorem diginet_scribble_encode_holds : memcpy_contract -> diginet_sysex_encode_contract -> diginet_scribble_encode_contract.
Proof.
  intros MEMCPY SYSEX.
  unfold memcpy_contract in MEMCPY.
  unfold diginet_sysex_encode_contract, diginet_sysex_encode_pre, DIGINET_SYSEX_ENCODE_DEPTH,
         DIGINET_SYSEX_ENCODE in SYSEX.
  unfold diginet_scribble_encode_contract.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
         F fc m lo pd addr cs before PRE.
  change (evt rsegs (sc_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo a3 pd addr cs before)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x15a50) fc None m (seg_rom rsegs))).
  unfold diginet_scribble_encode_pre, DIGINET_SCRIBBLE_ENCODE_DEPTH in PRE.
  destruct PRE as (HP & HD1 & HCH & HA1 & HA2 & HCS & HA3 & OUT & SPA2 & SPA3 & HMI & ST & LO).
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. pose proof (bv_unsigned_in_range 64 a0) as Ra0.
  pose proof (bv_unsigned_in_range 64 a2) as Ra2. pose proof (bv_unsigned_in_range 64 a3) as Ra3.
  unfold bv_modulus in Rsp, Ra0, Ra2, Ra3.
  pose proof ST as [Hlo _].
  pose proof (bytes_at_bound rsegs m _ _ HCS) as Bcs.
  pose proof (rw_cells_bound rsegs m _ _ OUT) as Bout. cbn [cells_size csize Nat.add] in Bout.
  assert (Lbf : length before = 32%nat) by (destruct OUT as [[[Lb _] _] _]; exact Lb).
  assert (MU : munch [(bv_unsigned sp - 112, bv_unsigned sp); (bv_unsigned a3, bv_unsigned a3 + 32)] m m)
    by apply munch_refl.
  assert (WM : wmono rsegs m m) by apply wmono_refl.
  carve_frame 64%nat ST.
  destruct (sc_CB_cut m _ 64 24 junk ltac:(lia) FR) as [FL FS]. clear FR.
  change (64 - 24)%nat with 40%nat in FS.
  replace (bv_unsigned sp + -64 + Z.of_nat 24) with (bv_unsigned sp + -40) in FS by lia.
  destruct pd as [d|].
  2: {
    (* p == NULL: E_ARG before any store to out *)
    cbn [pers_arg] in HP. subst a0.
    do 8 zstep.
    zstep. if_cases K1; [ exfalso; zify_cond K1; lia | ].
    zstep. try if_true.
    eapply (sc_exit ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo a3 None addr cs before)
      with (rc := -1) (o := None).
    all: first [ eassumption | reflexivity | lia | (apply bv_eq; vm_compute; reflexivity) ].
  }
  destruct HP as [Hp0 [Hdk HPB]].
  unfold desk_ok in Hdk. destruct Hdk as (Hdv & Hst & Hdc & Hct).
  cbn [bz map] in HPB.
  specialize (HD1 d eq_refl). unfold disj in HD1.
  specialize (HCH d eq_refl). destruct HCH as [Hc8 Hcl].
  do 8 zstep.
  zstep. if_cases K1; [ exfalso; zify_cond K1; lia | ].
  zstep. if_cases K2; [ exfalso; zify_cond K2; lia | ].
  zstep.
  zstep. if_cases K3; [ exfalso; zify_cond K3; lia | ].
  do 2 zstep.
  zstep. if_cases K4.
  2: {
    (* addr > 0x7f: E_RANGE before any store to out *)
    zify_cond K4.
    assert (Haddr : 127 < addr).
    { destruct (Z_lt_le_dec addr (2 ^ 31)) as [Hl | Hl];
        [ pose proof (sc_u32_small _ _ HA1 Hl) | pose proof (sc_u32_big _ _ HA1 Hl) ]; lia. }
    do 2 zstep.
    eapply (sc_exit ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo a3 (Some d) addr cs before)
      with (rc := -11) (o := None).
    all: first [ eassumption | reflexivity | lia | (apply bv_eq; vm_compute; reflexivity)
               | (rewrite sc_scribble_big by lia; reflexivity) ].
  }
  zify_cond K4.
  assert (Hadr : addr <= 127 /\ bv_unsigned a1 = addr).
  { destruct (Z_lt_le_dec addr (2 ^ 31)) as [Hl | Hl];
      [ pose proof (sc_u32_small _ _ HA1 Hl) | pose proof (sc_u32_big _ _ HA1 Hl) ]; lia. }
  destruct Hadr as [Hadr Ha1].
  destruct HA1 as [Ba _].
  (* 0x15a94 lbu s3, 0x12(s2): scribble_chars *)
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch goal with H : bytes_at rsegs mm (bv_unsigned a0 + 16) _ |- _ =>
      pose proof (bytes_at_ov_read rsegs mm _ _ 2 1 H ltac:(cbn; lia)) as HRc end end.
  cbn [firstn skipn] in HRc.
  zstep.
  cbv beta. rewrite (sc_b8_unsigned (d_chars d)) by lia.
  zstep. zstep.
  do 4 zstep.
  (* the frame bytes below the saved registers: pl[0..1] at sp-50, the memcpy target at sp-48 *)
  lazymatch goal with H : rw_cells rsegs ?mm (bv_unsigned sp + -64) [?c1; ?c2; ?c3; ?c4] |- _ =>
    destruct (sc_rw_split mm _ [c1; c2; c3] [c4] H) as [F16 F8]; clear H end.
  cbn [cells_size csize Nat.add] in F8.
  replace (bv_unsigned sp + -64 + Z.of_nat 16) with (bv_unsigned sp + -48) in F8 by lia.
  lazymatch type of F8 with rw_cells rsegs ?mm _ [CB 8 ?y] =>
    destruct (sc_CB_cut mm _ 8 (Z.to_nat (d_chars d)) y ltac:(lia) F8) as [Fm Fr]; clear F8 end.
  rewrite Z2Nat.id in Fr by lia.
  (* 0x15aac memcpy(sp-48, chars, scribble_chars) *)
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
  lazymatch type of Fm with rw_cells _ _ _ [CB _ ?jk] =>
  eapply evt_cut;
  [ eapply MEMCPY with (src := firstn (Z.to_nat (d_chars d)) cs) (junk := jk)
  | intros ms' PO; unfold memcpy_post in PO;
    rewrite (unsigned_lit (bv_unsigned sp + -48)), (unsigned_lit (d_chars d)) in PO by lia;
    revert ms' PO; post_call rsegs mm ]
  end end.
  1: (apply sc_bytes_firstn; eassumption).
  1: (rewrite unsigned_lit by lia; rewrite length_firstn; lia).
  1: (rewrite !unsigned_lit by lia; exact Fm).
  1: (rewrite !unsigned_lit by lia; lia).
  1: eassumption.
  (* 0x15ab0 lbu a0, 0x10(s2): device *)
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch goal with H : bytes_at rsegs mm (bv_unsigned a0 + 16) _ |- _ =>
      pose proof (bytes_at_ov_read rsegs mm _ _ 0 1 H ltac:(cbn; lia)) as HRd end end.
  cbn [firstn skipn] in HRd.
  zstep.
  cbv beta. rewrite (sc_b8_unsigned (d_dev d)) by lia.
  do 5 zstep.
  (* pl = [addr; 0] ++ chars[0..scribble_chars) at sp-50 *)
  lazymatch goal with
  | H16 : rw_cells rsegs ?mm (bv_unsigned sp + -64) [CB 14 ?x; C1 ?b1; C1 ?b2],
    Hm : rw_cells rsegs ?mm (bv_unsigned sp + -48) [CB _ ?src] |- _ =>
    assert (HPL : bytes_at rsegs mm (bv_unsigned sp + -50) ([b1; b2] ++ src));
    [ apply bytes_at_app; split;
      [ pose proof (sc_rw_split mm _ [CB 14 x] [C1 b1; C1 b2] H16) as [_ H2];
        apply sc_bytes_of_rw in H2; cbn [cells_size csize Nat.add cells_bytes cbytes app] in H2;
        replace (bv_unsigned sp + -64 + Z.of_nat 14) with (bv_unsigned sp + -50) in H2 by lia; exact H2
      | apply sc_bytes_of_rw in Hm; cbn [cells_bytes cbytes] in Hm; rewrite app_nil_r in Hm;
        cbn [length]; replace (bv_unsigned sp + -50 + Z.of_nat 2) with (bv_unsigned sp + -48) by lia; exact Hm ]
    | ]
  end.
  lazymatch type of HPL with bytes_at _ _ _ ([?b1; ?b2] ++ _) =>
    assert (ZPL : zb ([b1; b2] ++ firstn (Z.to_nat (d_chars d)) cs)
                  = [u8 addr; 0] ++ firstn (Z.to_nat (d_chars d)) (zb cs))
      by (apply sc_zb_pl; [ rewrite sc_z8, Ha1; reflexivity | vm_compute; reflexivity ])
  end.
  (* 0x15ac4 diginet_sysex_encode(device, 0x40, sp-50, 2 + scribble_chars, out) *)
  lazymatch type of HPL with bytes_at _ ?mm _ ?PL =>
    assert (LPL : Z.of_nat (length PL) = d_chars d + 2)
      by (rewrite length_app, length_firstn; cbn [length]; lia);
    eapply evt_cut;
    [ eapply SYSEX with (lo := lo) (dev := d_dev d) (fn := 64) (pl := PL) (before := before)
    | intros ms' PO; rewrite (unsigned_lit (bv_unsigned sp + -64)) in PO by lia; rewrite ZPL in PO;
      destruct (sc_sysex_shape (d_dev d) 64 ([u8 addr; 0] ++ firstn (Z.to_nat (d_chars d)) (zb cs)))
        as [[rc [SX Hrc]] | [bs [dp [SX Hbs]]]];
      rewrite SX in PO; cbv beta iota in PO; revert ms' PO; post_call rsegs mm ]
  end.
  1: { rewrite (unsigned_lit (bv_unsigned sp + -50)), (unsigned_lit (d_chars d + 2)),
               (unsigned_lit (bv_unsigned sp + -64)) by lia.
       unfold arg_zx, disj. sc_splits; first [ reflexivity | lia | eassumption ]. }
  (* the 24 frame bytes below the saved registers as one piece *)
  all: sc_join.
  all: match goal with H : ?x = Z_to_bv 64 _ |- _ => is_var x; subst x end.
  - (* sysex failed: its rc, out unchanged *)
    zstep. if_cases K5.
    + eapply (sc_exit ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo a3 (Some d) addr cs before)
        with (rc := rc) (o := None).
      all: first [ exact FLj | eassumption | reflexivity | lia
                 | (cbn [cells_size csize Nat.add]; lia)
                 | (rewrite sc_scribble_some by lia; rewrite SX; apply sc_with_key_none) ].
    + exfalso. zify_cond K5. Z.div_mod_to_equations. lia.
  - (* sysex succeeded: 0x15ad4 out->key = DIGINET_KEY(7, addr) *)
    zstep. try if_false.
    do 3 zstep.
    lazymatch goal with H : rw_cells rsegs ?mm (bv_unsigned a3) [CB 28 ?X; C4 ?v] |- _ =>
      assert (OUTF : rw_cells rsegs mm (bv_unsigned a3) [CB 32 (cmd_out before (Some (bs, KEY 7 addr, dp)))]);
      [ eapply sc_out_fin; [ exact H | apply sc_cmd_out_key; [ exact Lbf | exact Hbs | apply sc_key7; [ lia | exact Ha1 ] ] ]
      | clear H ]
    end.
    eapply (sc_exit ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo a3 (Some d) addr cs before)
      with (rc := 0) (o := Some (bs, KEY 7 addr, dp)).
    all: first [ exact FLj | exact OUTF | eassumption | reflexivity | lia
               | (cbn [cells_size csize Nat.add]; lia)
               | (rewrite sc_scribble_some by lia; rewrite SX; reflexivity) ].
Qed.
