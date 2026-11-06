(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

(* [comment removed for export] *)
From Stdlib Require ZArith.
From Stdlib Require NArith.
From Stdlib Require List.
From Stdlib Require Lia.
From Stdlib Require Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase.
From LinuxProcessSemantics.LinuxProcessSem Require RiscvSemantics.
From LinuxProcessSemantics.LinuxProcessSem Require MemImageType.
From LinuxProcessSemantics.LinuxProcessSem Require State.
From LinuxProcessSemantics.LinuxProcessSem Require Run.
From LinuxProcessSemantics.Riscv Require Prelude.
From LinuxProcessSemantics.Riscv Require Instr.
From LinuxProcessSemantics.Riscv Require Decode.
From LinuxProcessSemantics.Riscv Require DecodeC.
From LinuxProcessSemantics.Riscv Require Sem.
From LinuxProcessSemantics.Riscv Require Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require ShapeAlg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Tac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Bytes.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require ZBridge.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require BImg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_defs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require CJ_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require AShadow.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require CJ_tree.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require CJ_phex4.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require CJ_conv.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require NElim.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require CJ_pstrA.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require StoreCache.
Module CJ_pstring_A.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ZBridge.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.BImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.AShadow OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_tree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_phex4.CJ_pbuf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_conv OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_phex4.CJ_parse_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_phex4.CJ_parse_lemmas.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_pstrA.CJ_shfast.
Local Ltac sh_resolve_if ::= sh_resolve_if_fast.
Local Ltac sh_join v Cv rdk ::= sh_join_fast v Cv rdk.
(* [comment removed for export] *)
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.StoreFast.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.
Local Ltac mem_after_store ::= mem_after_store_cached.
Local Ltac addr_eq_tac ::= addr_eq_tac_cached.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_cached segs m m' MU WM.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Ltac guard1 := let G := fresh "G" in zstep; if_cases G; zify_cond G; [exfalso; lia|].
Ltac guard2 := let G := fresh "G" in zstep; if_cases G; zify_cond G; [| exfalso; lia].

(* [comment removed for export] *)
Definition ps_frame (j0 : list byte) (U P : Z) (s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra : word) : list cell :=
  [CB 8 j0; C8 (Z_to_bv 64 0xdc00); C8 (Z_to_bv 64 0xd800); C8 (Z_to_bv 64 U); C8 (Z_to_bv 64 P);
   C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Section PS.
  Variables (sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 rav t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (m2 : word -> option byte) (CA blen off e sk S P U lo : Z) (bs j0 : list byte).

  Definition F0 : nat := Z.to_nat blen.
  Definition nalloc : Z := e - off - sk + 1.
  (* [comment removed for export] *)
  Definition W2 : list (Z * Z) := [(S, S + nalloc); (lo, bv_unsigned sp + -144)].
  Definition FRAME : list cell := ps_frame j0 U P s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 rav.

  (* [comment removed for export] *)
  Definition ps_ctx : Prop :=
    Z.of_nat (length bs) = blen
    /\ bytes_at bsegs m2 CA bs
    /\ rw_cells bsegs m2 (bv_unsigned sp + -144) FRAME
    /\ ps_scan bs blen F0 (off + 1) 0 = Some (e, sk)
    /\ 0 <= off /\ blen < 2^31
    /\ 0 < CA /\ CA + blen <= alloc_ceiling
    /\ AIMG_HI <= S /\ S + nalloc <= alloc_ceiling
    /\ (S + nalloc <= CA \/ CA + blen <= S)
    /\ alloc_ceiling <= lo /\ lo + 160 <= bv_unsigned sp /\ bv_unsigned sp < 2^64
    /\ AIMG_HI <= P /\ P + 56 <= alloc_ceiling /\ AIMG_HI <= U /\ U + 64 <= alloc_ceiling
    /\ shbase_cells m2 /\ text_sh m2 CA blen /\ shadow_ok m2 S nalloc
    /\ sclr S nalloc.      (* [comment removed for export] *)
  Hypothesis CTX : ps_ctx.

  Definition dinv (i oc : Z) : Prop := oc + npairs bs blen F0 (off + 1) i <= i - (off + 1).

  (* [comment removed for export] *)
  Lemma ctx_scan : sk = npairs bs blen F0 (off + 1) e /\ off + 1 <= e < blen /\ at_ bs e = 34.
  Proof. (nelimp CTX 5%nat; intros _ _ _ SC _). pose proof (ps_scan_npairs _ _ _ _ _ _ _ SC). lia. Qed.

  Lemma ctx_arith : Z.of_nat (length bs) = blen /\ 0 <= off /\ off + 1 <= e < blen /\ blen < 2^31
    /\ 0 < CA /\ CA + blen <= alloc_ceiling /\ AIMG_HI <= S /\ S + nalloc <= alloc_ceiling /\ (S + nalloc <= CA \/ CA + blen <= S)
    /\ alloc_ceiling <= lo /\ lo + 160 <= bv_unsigned sp /\ bv_unsigned sp < 2^64
    /\ AIMG_HI <= P /\ P + 56 <= alloc_ceiling /\ AIMG_HI <= U /\ U + 64 <= alloc_ceiling
    /\ 1 <= nalloc <= e - off + 1 /\ 0 <= sk.
  Proof.
    (nelimp ctx_scan 3%nat; intros SK E _).
    (nelimp CTX 19%nat; intros L _ _ SC O B C1 C2 S1 S2 SEP LO1 LO2 SP2 P1 P2 U1 U2 _).
    pose proof (npairs_window bs blen F0 (off + 1) (off + 1) e ltac:(lia)) as [Wa Wb].
    rewrite (npairs_le bs blen F0 (off + 1) (off + 1)) in Wa, Wb by lia. pose proof (bflag_range bs (off + 1)).
    unfold nalloc in *. repeat split; try assumption; lia.
  Qed.

  Lemma ctx_sh : shbase_cells m2 /\ text_sh m2 CA blen /\ shadow_ok m2 S nalloc.
  Proof. (nelimp CTX 22%nat; intros _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ SH1 SH2 SH3 _). exact (conj SH1 (conj SH2 SH3)). Qed.
  Lemma ctx_band : sclr S nalloc.
  Proof. (nelimp CTX 22%nat; intros _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ SB). exact SB. Qed.

  Lemma dinv0 : dinv (off + 1) 0.
  Proof. unfold dinv. rewrite npairs_le by lia. lia. Qed.

  Lemma dinv_step : forall i oc c p, dinv i oc -> off + 1 <= i -> 0 <= c -> p + (c + bflag bs i) / 2 <= c -> dinv (i + c) (oc + p).
  Proof.
    intros i oc c p DI Hi Hc Hp. unfold dinv in *.
    pose proof (npairs_window bs blen F0 (off + 1) i (i + c) ltac:(lia)) as [Wa Wb]. pose proof (bflag_range bs i).
    assert (npairs bs blen F0 (off + 1) (i + c) - npairs bs blen F0 (off + 1) i <= (c + bflag bs i) / 2) by (apply Z.div_le_lower_bound; lia).
    lia.
  Qed.

  Lemma dinv_room : forall i oc L, dinv i oc -> off + 1 <= i <= e -> 2 * L <= e - i + 3 -> oc + L <= nalloc.
  Proof.
    intros i oc L DI Hi HL. unfold dinv, nalloc in *. (nelimp ctx_scan 3%nat; intros SK E _).
    pose proof (npairs_window bs blen F0 (off + 1) i e ltac:(lia)) as [Wa Wb]. pose proof (bflag_range bs i). lia.
  Qed.

  Lemma dinv_end : forall i oc, dinv i oc -> e <= i <= e + 1 -> oc + 1 <= nalloc.
  Proof.
    intros i oc DI Hi. unfold dinv, nalloc in *. (nelimp ctx_scan 3%nat; intros SK E _). (nelimp CTX 5%nat; intros _ _ _ SC _).
    rewrite (ps_scan_npairs_end _ _ _ _ _ _ _ i SC) in DI by lia. lia.
  Qed.

  (* [comment removed for export] *)
  Definition S6 : word := Z_to_bv 64 (Z.shiftr (P + 16) 3 + 2147450880).
  Definition S7 : word := Z_to_bv 64 (Z.shiftr P 3 + 2147450880).

  Definition LSTg (pc : Z) (x1 x5 x6 x10 x11 x12 x13 x14 x15 x16 x17 x20 x21 : word) (i : Z) (mm : word -> option byte) : machine_state :=
    MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp x5 x6 (Z_to_bv 64 92) (Z_to_bv 64 (P + 16)) (Z_to_bv 64 (CA + i))
            x10 x11 x12 x13 x14 x15 x16 x17
            (Z_to_bv 64 S) (Z_to_bv 64 (CA + e)) x20 x21 S6 S7 (Z_to_bv 64 2147450880) (Z_to_bv 64 (CA + e))
            (Z_to_bv 64 JT) (Z_to_bv 64 2) (Z_to_bv 64 83) t4 t5 t6)
       F (Z_to_bv 64 pc) fc None mm (seg_rom bsegs).
  (* [comment removed for export] *)
  Definition LST (pc : Z) (x1 x5 x6 x10 x13 x14 x15 x16 x17 x21 : word) (i oc : Z) (mm : word -> option byte) : machine_state :=
    LSTg pc x1 x5 x6 x10 (Z_to_bv 64 P) (Z_to_bv 64 U) x13 x14 x15 x16 x17 (Z_to_bv 64 (S + oc)) x21 i mm.

  (* [comment removed for export] *)
  Definition lmem (mm : word -> option byte) (buf : list byte) : Prop :=
    u8arr bsegs mm S buf /\ length buf = Z.to_nat nalloc /\ munch W2 m2 mm /\ wmono bsegs m2 mm /\ mem_inv bsegs mm
    /\ stk bsegs mm lo (bv_unsigned sp + -144).

  Definition KPOST : machine_state -> Prop := fun ms' =>
    exists (mm : word -> option byte) (buf : list byte) (x1 x5 x6 x10 x12 x13 x14 x15 x16 x17 x20 x21 : word) (i oc : Z),
      lmem mm buf /\ off + 1 <= i <= e + 1 /\ 0 <= oc /\ oc + 1 <= nalloc
      /\ ( ms' = LSTg 0x85974 x1 x5 x6 (Z_to_bv 64 (S + oc)) (Z_to_bv 64 P) (Z_to_bv 64 U) x13 x14 x15 x16 x17 x20 x21 i mm  (* [comment removed for export] *)
           \/ ms' = LSTg 0x859e4 x1 x5 x6 x10 (Z_to_bv 64 P) x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (S + oc)) x21 i mm ).     (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition LOOPK (k : nat) : Prop :=
    forall (i oc : Z) (mm : word -> option byte) (buf : list byte) (x1 x5 x6 x10 x13 x14 x15 x16 x17 x21 : word),
      e - i <= Z.of_nat k -> off + 1 <= i < e -> dinv i oc -> 0 <= oc -> lmem mm buf ->
      evt bsegs KPOST (LST 0x8559c x1 x5 x6 x10 x13 x14 x15 x16 x17 x21 i oc mm).

  (* [comment removed for export] *)
  Lemma lmem_facts : forall mm buf, lmem mm buf ->
    bytes_at bsegs mm CA bs /\ rw_cells bsegs mm (bv_unsigned sp + -144) FRAME.
  Proof.
    intros mm buf nelH_; (nelim nelH_ 6%nat; intros BUF BL MU WM MI ST). pose proof ctx_arith as A. (nelimp CTX 4%nat; intros L BY2 FR2 _).
    try rewrite alloc_ceiling_eq in A. unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG, W2 in *. split.
    - eapply bytes_at_transport; [exact BY2| exact MU|]. cbn. lia.
    - eapply rw_cells_transport; [exact FR2| exact MU| exact WM|]. cbn. lia.
  Qed.

  Ltac pre := pose proof ctx_arith as ARITH; (nelimp ctx_sh 3%nat; intros SB2 TS2 SO2); pose proof ctx_band as SBND;
              try rewrite alloc_ceiling_eq in ARITH; unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG, W2, nalloc in *.

  (* [comment removed for export] *)
  Lemma exit_ok : forall i oc mm buf x1 x5 x6 x13 x14 x15 x16 x17 x20 x21,
    lmem mm buf -> off + 1 <= i <= e + 1 -> 0 <= oc -> oc + 1 <= nalloc ->
    evt bsegs KPOST (LSTg 0x85974 x1 x5 x6 (Z_to_bv 64 (S + oc)) (Z_to_bv 64 P) (Z_to_bv 64 U) x13 x14 x15 x16 x17 x20 x21 i mm).
  Proof. intros. apply evt_done. unfold KPOST. exists mm, buf, x1, x5, x6, x13, x13, x13. nexists 8%nat. repeat (split; [eassumption|]). left; reflexivity. Qed.

  Lemma exit_fail : forall i oc mm buf x1 x5 x6 x10 x12 x13 x14 x15 x16 x17 x21,
    lmem mm buf -> off + 1 <= i <= e + 1 -> 0 <= oc -> oc + 1 <= nalloc ->
    evt bsegs KPOST (LSTg 0x859e4 x1 x5 x6 x10 (Z_to_bv 64 P) x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (S + oc)) x21 i mm).
  Proof. intros. apply evt_done. unfold KPOST. exists mm, buf, x1, x5, x6, x10, x12, x13, x14, x15, x16, x17, x13. nexists 3%nat. repeat (split; [eassumption|]). right; reflexivity. Qed.

  Section Body.
    Variable k : nat.
    Hypothesis IH : forall k', (k' < k)%nat -> LOOPK k'.

    (* [comment removed for export] *)
    Lemma go_head : forall i oc mm buf x1 x5 x6 x10 x13 x14 x15 x16 x17 x21,
      e - i < Z.of_nat k -> off + 1 <= i < e -> dinv i oc -> 0 <= oc -> lmem mm buf ->
      evt bsegs KPOST (LST 0x8559c x1 x5 x6 x10 x13 x14 x15 x16 x17 x21 i oc mm).
    Proof.
      intros. destruct k as [|k']; [lia|]. eapply (IH k'); [lia| lia| assumption| assumption| assumption| eassumption].
    Qed.

    (* [comment removed for export] *)
    Definition TESTPCS : list Z := [0x85634; 0x85750].

    Lemma tests : forall pc i oc mm buf x1 x5 x6 x13 x14 x15 x16 x17 x21,
      In pc TESTPCS ->
      e - i < Z.of_nat k -> off + 1 <= i <= e + 1 -> dinv i oc -> 0 <= oc -> lmem mm buf ->
      evt bsegs KPOST (LST pc x1 x5 x6 (Z_to_bv 64 (S + oc)) x13 x14 x15 x16 x17 x21 i oc mm).
    Proof.
      intros until x21. intros HIn Hk Hi DI Hoc LM. pre. (nelimp LM 6%nat; intros BUF BL MU WM MI ST).
      assert (EXIT : e <= i -> evt bsegs KPOST (LST 0x85974 x1 x5 x6 (Z_to_bv 64 (S + oc)) x13 x14 x15 x16 x17 x21 i oc mm)).
      { intros He. unfold LST. eapply exit_ok; [exact LM| lia| lia| apply (dinv_end i oc DI); lia]. }
      unfold LST, LSTg in *.
      destruct HIn as [<-|[<-|[]]];
        (zstep; if_cases Kt; zify_cond Kt; [eapply go_head; [lia| lia| exact DI| exact Hoc| exact LM] | zstep; apply EXIT; lia]).
    Qed.

    (* [comment removed for export] *)
    Lemma adv : forall i oc oc' (sl : Z) mm buf x1 x5 x6 x14 x15 x16 x17 x21,
      e - i <= Z.of_nat k -> off + 1 <= i -> i + sl <= e + 1 -> 1 <= sl -> 0 <= oc' -> dinv (i + sl) oc' -> lmem mm buf ->
      evt bsegs KPOST (LST 0x85740 x1 x5 x6 (Z_to_bv 64 (S + oc')) (Z_to_bv 64 sl) x14 x15 x16 x17 x21 i oc mm).
    Proof.
      intros until x21. intros Hk Hi Hsl Hsl1 Hoc' DI LM. pre. (nelimp LM 6%nat; intros BUF BL MU WM MI ST). unfold LST, LSTg.
      zstep. rewrite zb_lxor_ones by lia.                 (* [comment removed for export] *)
      guard1.                                             (* [comment removed for export] *)
      zstep. zstep. replace (CA + i + sl) with (CA + (i + sl)) by lia.
      eapply (tests 0x85750 (i + sl) oc'); [cbn; auto| lia| lia| exact DI| lia| exact LM].
    Qed.

    (* [comment removed for export] *)
    Lemma join : forall i oc (len sl : Z) mm buf x1 x5 x6 x10 x15 x16 x17 x21,
      e - i <= Z.of_nat k -> off + 1 <= i -> i + sl <= e + 1 -> 1 <= sl -> 1 <= len -> 0 <= oc -> oc + len <= nalloc ->
      dinv (i + sl) (oc + len) -> lmem mm buf ->
      evt bsegs KPOST (LST 0x8589c x1 x5 x6 x10 (Z_to_bv 64 sl) (Z_to_bv 64 len) x15 x16 x17 x21 i oc mm).
    Proof.
      intros until x21. intros Hk Hi Hsl Hsl1 Hlen Hoc ROOM DI LM. pre. (nelimp LM 6%nat; intros BUF BL MU WM MI ST). unfold LST, LSTg.
      zstep. replace (len + (S + oc)) with (S + (oc + len)) by lia.
      guard1.                                             (* [comment removed for export] *)
      guard2.                                             (* [comment removed for export] *)
      eapply adv; [lia| lia| exact Hsl| lia| lia| exact DI| exact LM].
    Qed.

    (* [comment removed for export] *)
    Ltac out_store SO BUF idx :=
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
        let SOK := fresh "SOK" in
        pose proof (u8arr_store_ok bsegs mx S _ idx (Z_to_bv 64 (S + idx)) BUF ltac:(rewrite ?upd_length; lia) ltac:(unfold wa; f_equal; lia)) as SOK;
        zstep; rewrite ?le1_lit;
        let BUF' := fresh "BUF" in
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ [Z_to_bv 8 ?v]) _) =>
          pose proof (u8arr_write bsegs mx S _ idx (Z_to_bv 8 v) BUF ltac:(rewrite ?upd_length; lia)) as BUF' end;
        clear BUF; store_done; rename BUF' into BUF
      end.
    Ltac lm_close BUF BL MU WM MI ST :=
      split; [exact BUF|]; split; [rewrite ?upd_length; exact BL|]; split; [exact MU|]; split; [exact WM|]; split; [exact MI| exact ST].

    (* [comment removed for export] *)
    Lemma one_byte : forall i oc (cp : Z) mm buf x1 x5 x6 x10 x13 x14 x15 x16 x17,
      e - i <= Z.of_nat k -> off + 1 <= i -> i + 6 <= e + 1 -> 0 <= cp < 2^64 -> 0 <= oc -> oc + 1 <= nalloc ->
      dinv (i + 6) (oc + 1) -> lmem mm buf ->
      evt bsegs KPOST (LST 0x8587c x1 x5 x6 x10 x13 x14 x15 x16 x17 (Z_to_bv 64 cp) i oc mm).
    Proof.
      intros until x17. intros Hk Hi Hie Hcp Hoc ROOM DI LM. (nelimp LM 6%nat; intros BUF BL MU WM MI ST). pre. unfold LST, LSTg.
      guard1.                                             (* [comment removed for export] *)
      zstep. zstep. pose proof (shadow_ok_shchk1 _ S _ (S + oc) SO2 ltac:(lia)) as CK. asan_chk CK.
      out_store SO2 BUF oc.
      zstep. zstep.
      eapply join; [lia| lia| exact Hie| lia| lia| lia| unfold nalloc; lia| exact DI| lm_close BUF BL MU WM MI ST].
    Qed.

    (* [comment removed for export] *)
    Lemma encode_tail : forall i oc (len sl cp mark : Z) mm buf x1 x5 x6 x10 x16 x17,
      e - i <= Z.of_nat k -> off + 1 <= i -> i + sl <= e + 1 -> 1 <= sl -> 2 <= len <= 4 -> 0 <= cp < 2^32 -> 0 <= mark < 256 -> 0 <= oc -> oc + len <= nalloc ->
      dinv (i + sl) (oc + len) -> lmem mm buf ->
      evt bsegs KPOST (LST 0x8580c x1 x5 x6 x10 (Z_to_bv 64 sl) (Z_to_bv 64 len) (Z_to_bv 64 mark) x16 x17 (Z_to_bv 64 cp) i oc mm).
    Proof.
      intros until x17. intros Hk Hi Hsl Hsl1 Hlen Hcp Hmk Hoc ROOM DI LM. (nelimp LM 6%nat; intros BUF BL MU WM MI ST). pre. unfold LST, LSTg.
      guard1.                                             (* [comment removed for export] *)
      zstep. zstep. rewrite zb_lxor_ones by lia.          (* [comment removed for export] *)
      (* [comment removed for export] *)
      Ltac cont_byte SO BUF ocv j :=
        zstep;                                                                                        (* [comment removed for export] *)
        guard1;                                                                                       (* [comment removed for export] *)
        zstep; replace (S + ocv + j) with (S + (ocv + j)) by lia; zstep; zstep;
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
          let CK := fresh "CK" in
          pose proof (shadow_ok_shchk1 _ S _ (S + (ocv + j)) SO ltac:(lia)) as CK; asan_chk CK;
          zstep; zstep; zstep;
          out_store SO BUF (ocv + j);
          zstep; zstep
        end.
      (* [comment removed for export] *)
      Ltac to_join SO BUF ocv BL MU WM MI ST DI :=
        zstep; if_false; zstep;
        zstep; zstep;
        let CK := fresh "CK" in
        pose proof (shadow_ok_shchk1 _ S _ (S + ocv) SO ltac:(lia)) as CK; asan_chk CK;
        zstep; out_store SO BUF ocv; zstep;
        eapply join; [lia| lia| eassumption| lia| lia| lia| unfold nalloc; lia| exact DI| lm_close BUF BL MU WM MI ST].
      assert (HL : len = 2 \/ len = 3 \/ len = 4) by lia.
      destruct HL as [-> | [-> | ->]].
      - cont_byte SO2 BUF oc 1. to_join SO2 BUF oc BL MU WM MI ST DI.
      - cont_byte SO2 BUF oc 2. zstep. if_true. cont_byte SO2 BUF oc 1. to_join SO2 BUF oc BL MU WM MI ST DI.
      - cont_byte SO2 BUF oc 3. zstep. if_true. cont_byte SO2 BUF oc 2. zstep. if_true. cont_byte SO2 BUF oc 1. to_join SO2 BUF oc BL MU WM MI ST DI.
    Qed.

    (* [comment removed for export] *)
    Ltac until pc := lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 pc) _ _ _ _) => idtac | |- _ => zstep; until pc end.

    (* [comment removed for export] *)
    Definition ESCPCS : list (Z * Z) := [(0x8563c, 8); (0x8565c, 12); (0x856dc, 13); (0x856fc, 10); (0x8571c, 9)].

    Lemma esc_char : forall i oc (c : Z) mm buf x1 x5 x6 x10 x13 x15 x16 x17 x21,
      0 <= c < 256 ->
      e - i <= Z.of_nat k -> off + 1 <= i -> i + 2 <= e + 1 -> 0 <= oc -> oc + 1 <= nalloc ->
      dinv (i + 2) (oc + 1) -> lmem mm buf ->
      evt bsegs KPOST (LST 0x855f0 x1 x5 x6 x10 x13 (Z_to_bv 64 c) x15 x16 x17 x21 i oc mm).
    Proof.
      intros until x21. intros Hc Hk Hi Hie Hoc ROOM DI LM. (nelimp LM 6%nat; intros BUF BL MU WM MI ST). pre. unfold LST, LSTg.
      zstep. replace (S + oc + 1) with (S + (oc + 1)) by lia. guard1.
      zstep. zstep. pose proof (shadow_ok_shchk1 _ S _ (S + oc) SO2 ltac:(lia)) as CK. asan_chk CK.
      out_store SO2 BUF oc.
      zstep. zstep.
      eapply adv; [lia| lia| exact Hie| lia| lia| exact DI| lm_close BUF BL MU WM MI ST].
    Qed.

    Lemma esc_const : forall pc (v : Z) i oc mm buf x1 x5 x6 x10 x13 x14 x15 x16 x17 x21,
      In (pc, v) ESCPCS ->
      e - i <= Z.of_nat k -> off + 1 <= i -> i + 2 <= e + 1 -> 0 <= oc -> oc + 1 <= nalloc ->
      dinv (i + 2) (oc + 1) -> lmem mm buf ->
      evt bsegs KPOST (LST pc x1 x5 x6 x10 x13 x14 x15 x16 x17 x21 i oc mm).
    Proof.
      intros until x21. intros HIn Hk Hi Hie Hoc ROOM DI LM. (nelimp LM 6%nat; intros BUF BL MU WM MI ST). pre. unfold LST, LSTg.
      destruct HIn as [E|[E|[E|[E|[E|[]]]]]]; injection E as <- <-;
        (zstep; replace (S + oc + 1) with (S + (oc + 1)) by lia; guard1;
         zstep; zstep; pose proof (shadow_ok_shchk1 _ S _ (S + oc) SO2 ltac:(lia)) as CK; asan_chk CK;
         until 0x85738%Z;
         out_store SO2 BUF oc;
         zstep;
         eapply adv; [lia| lia| exact Hie| lia| lia| exact DI| lm_close BUF BL MU WM MI ST]).
    Qed.
  End Body.
End PS.


End CeilWrap.
(* [comment removed for export] *)
Ltac guard1 := let G := fresh "G" in zstep; if_cases G; zify_cond G; [exfalso; lia|].
Ltac guard2 := let G := fresh "G" in zstep; if_cases G; zify_cond G; [| exfalso; lia].
End CJ_pstring_A.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require LiaOn.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require CJ_bandM.
Module CJ_pstring_B.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ZBridge.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.LiaOn.SepM.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_bandM OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.BImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.AShadow OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_tree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_phex4.CJ_pbuf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_conv OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_phex4.CJ_parse_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_phex4.CJ_parse_lemmas OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_phex4 CJ_pstring_A.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_pstrA.CJ_shfast.
Local Ltac sh_resolve_if ::= sh_resolve_if_fast.
Local Ltac sh_join v Cv rdk ::= sh_join_fast v Cv rdk.
(* [comment removed for export] *)
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.StoreFast.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.
Local Ltac mem_after_store ::= mem_after_store_cached.
Local Ltac addr_eq_tac ::= addr_eq_tac_cached.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_cached segs m m' MU WM.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Lemma jt_cases : forall c,
  ((c = 34 \/ c = 47 \/ c = 92) /\ jt_off c = 0x645e4)
  \/ (c = 98 /\ jt_off c = 0x64630) \/ (c = 102 /\ jt_off c = 0x64650) \/ (c = 117 /\ jt_off c = 0x64670)
  \/ (c = 114 /\ jt_off c = 0x646d0) \/ (c = 110 /\ jt_off c = 0x646f0) \/ (c = 116 /\ jt_off c = 0x64710)
  \/ jt_off c = 0x649d8.
Proof.
  intros c. unfold jt_off.
  destruct (Z.eqb_spec c 34); [left; split; [lia|reflexivity]|].
  destruct (Z.eqb_spec c 47); [left; split; [lia|reflexivity]|].
  destruct (Z.eqb_spec c 92); [left; split; [lia|reflexivity]|]. cbn [orb].
  destruct (Z.eqb_spec c 98); [do 1 right; left; split; [lia|reflexivity]|].
  destruct (Z.eqb_spec c 102); [do 2 right; left; split; [lia|reflexivity]|].
  destruct (Z.eqb_spec c 117); [do 3 right; left; split; [lia|reflexivity]|].
  destruct (Z.eqb_spec c 114); [do 4 right; left; split; [lia|reflexivity]|].
  destruct (Z.eqb_spec c 110); [do 5 right; left; split; [lia|reflexivity]|].
  destruct (Z.eqb_spec c 116); [do 6 right; left; split; [lia|reflexivity]|].
  do 7 right. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma jt_pc : forall c T, 34 <= c <= 117 -> jt_off c + JT = T ->
  ret_pc (Z_to_bv 64 (bv_unsigned (sx32 (Z_to_bv 64 (jt_off c))) + JT)) = Z_to_bv 64 T.
Proof.
  intros c T Hc HT. pose proof (jt_off_range c).
  rewrite sx32_lit by lia. rewrite unsigned_lit by lia. rewrite HT. unfold JT in HT.
  destruct (jt_cases c) as [[_ E]|[[_ E]|[[_ E]|[[_ E]|[[_ E]|[[_ E]|[[_ E]|E]]]]]]]; rewrite E in HT; subst T;
    (apply ret_pc_even; [lia| reflexivity]).
Qed.

Section PS.
  Variables (sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 rav t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (m2 : word -> option byte) (CA blen off e sk S P U lo : Z) (bs j0 : list byte).
  Hypothesis CTX : ps_ctx sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 rav m2 CA blen off e sk S P U lo bs j0.

  Notation LSTx := (LST sp gp tp t4 t5 t6 F fc CA e S P U).
  Notation LSTG := (LSTg sp gp tp t4 t5 t6 F fc CA e S P U).
  Notation KP := (KPOST sp gp tp t4 t5 t6 F fc m2 CA off e sk S P U lo).
  Notation LM := (lmem sp m2 off e sk S lo).
  Notation DINV := (dinv blen off bs).
  Notation NA := (nalloc off e sk).
  Notation L z := (Z_to_bv 64 z) (only parsing).
  (* [comment removed for export] *)
  Notation LSTc pc x1 x5 x6 x10 x11 x12 x13 x14 x15 x16 x17 x21 i oc mm :=
    (LSTg sp gp tp t4 t5 t6 F fc CA e S P pc x1 x5 x6 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (S + oc)) x21 i mm) (only parsing).

  Ltac ctx := pose proof (ctx_arith _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CTX) as ARITH;
              (nelimp (ctx_sh _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CTX) 3%nat; intros SB2 TS2 SO2);
              pose proof (ctx_band _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CTX) as SBND;   (* [comment removed for export] *)
              try rewrite alloc_ceiling_eq in ARITH; unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in ARITH, SBND; bandM; sepM.
  Ltac lm LMm mm buf :=
    pose proof (lmem_facts _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CTX mm buf LMm) as [BY FR]; unfold FRAME, ps_frame in FR;
    (nelimp LMm 6%nat; intros BUF BL MU WM MI ST).
  Ltac ml := Z.div_mod_to_equations; lia.
  Ltac lm_close BUF BL MU WM MI ST :=
    split; [exact BUF|]; split; [rewrite ?upd_length; exact BL|]; split; [exact MU|]; split; [exact WM|]; split; [exact MI| exact ST].

  Section Body.
    Variable k : nat.
    Hypothesis IH : forall k', (k' < k)%nat -> LOOPK sp gp tp t4 t5 t6 F fc m2 CA blen off e sk S P U lo bs k'.

    (* [comment removed for export] *)
    (* [comment removed for export] *)
    Section U.
      Variables (i oc : Z).
      Hypothesis Hk : e - i <= Z.of_nat k.
      Hypothesis Hi : off + 1 <= i.
      Hypothesis Hie : i + 6 <= e.
      Hypothesis BSL : at_ bs i = 92.
      Hypothesis DI : DINV i oc.
      Hypothesis Hoc : 0 <= oc.

      Lemma bflag_i : bflag bs i = 1.
      Proof. unfold bflag. rewrite BSL. reflexivity. Qed.

      Lemma room4 : oc + 4 <= NA.
      Proof. ctx. eapply (dinv_room _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CTX i oc 4 DI); lia. Qed.

      Lemma dinv_u : forall c p, 6 <= c -> p + (c + 1) / 2 <= c -> DINV (i + c) (oc + p).
      Proof. intros c p Hc Hp. eapply dinv_step; [exact DI| lia| lia| rewrite bflag_i; exact Hp]. Qed.

      Ltac preU LMm mm buf := ctx; lm LMm mm buf; pose proof room4 as ROOM; unfold W2, nalloc in *; unfold LST, LSTg.
      Ltac fail_exit LMm := eapply exit_fail; [exact LMm| lia| lia| unfold nalloc; lia].
      (* [comment removed for export] *)
      Ltac br_fail LMm := let K := fresh "K" in zstep; if_cases K; zify_cond K; try (fail_exit LMm).
      Ltac ugd := let G := fresh "G" in zstep; if_cases G; zify_cond G; try (exfalso; lia).

      (* [comment removed for export] *)
      Ltac call_hex4 d BY SB2 TS2 MU MI ST :=
        zstep;                                                              (* [comment removed for export] *)
        let B4 := fresh "B4" in
        pose proof (bytes_at_window _ CA bs (i + d) 4 BY ltac:(lia) ltac:(lia)) as B4;
        let HX := fresh "HX" in pose proof hex4_spec as HX; unfold hex4_stmt in HX;
        eapply evt_cut;
        [ eapply HX with (lo := lo); rewrite ?unsigned_lit by lia;
          [ exact B4 | apply firstn_skipn_length; lia | try rewrite alloc_ceiling_eq; lia
          | eapply shbase_cells_munch; [exact SB2| exact MU| cbn; lia| cbn; lia]
          | eapply text_sh_sub; [eapply text_sh_munch; [exact TS2| exact MU| lia| lia| cbn; unfold SH, SHADOW_OFFSET; Z.div_mod_to_equations; lia]| lia| lia]
          | exact MI | exact ST | try rewrite alloc_ceiling_eq; lia | unfold PARSE_HEX4_STACK; lia | f_equal; lia ]
        | cbv beta; clear B4 HX ].

      (* [comment removed for export] *)
      Lemma L_cls : forall FC mm buf x1 x5 x6 x11 x12 x13 x14 x15 x16 x17 x21, 0 <= FC < 2^16 -> LM mm buf ->
        evt bsegs KP (LSTc 0x85694 x1 x5 x6 (L FC) x11 x12 x13 x14 x15 x16 x17 x21 i oc mm).
      Proof.
        intros until x21. intros HFC LMm. preU LMm mm buf.
        zstep. zstep. zstep. zstep. if_cases Ksur; zify_cond Ksur.
        - (* [comment removed for export] *)
          zstep. zstep. zstep. ugd.                                     (* [comment removed for export] *)
          zstep. replace (CA + i + 6) with (CA + (i + 6)) by lia.       (* [comment removed for export] *)
          zstep. zstep. zstep. rewrite (bv_lts_small (CA + e - (CA + (i + 6))) 6) by lia.
          if_cases Kl; zify_cond Kl; try (fail_exit LMm).
          zstep. zstep.
          pose proof (TS2 (CA + (i + 6)) ltac:(lia)) as CK6. asan_chk CK6.
          (nelim (text_read mm CA bs (i + 6) (Z_to_bv 64 (CA + (i + 6))) BY ltac:(lia) ltac:(lia) ltac:(unfold wa; f_equal; lia)) 4%nat; intros c6 Hc6 RD6 _).
          zstep. br_fail LMm.
          zstep. ugd.                                                   (* [comment removed for export] *)
          zstep. replace (CA + i + 7) with (CA + (i + 7)) by lia. zstep. zstep.
          pose proof (TS2 (CA + (i + 7)) ltac:(lia)) as CK7. asan_chk CK7.
          (nelim (text_read mm CA bs (i + 7) (Z_to_bv 64 (CA + (i + 7))) BY ltac:(lia) ltac:(lia) ltac:(unfold wa; f_equal; lia)) 4%nat; intros c7 Hc7 RD7 _).
          zstep. zstep. br_fail LMm.
          zstep. ugd.                                                   (* [comment removed for export] *)
          zstep.                                                          (* [comment removed for export] *)
          call_hex4 8 BY SB2 TS2 MU MI ST.
          intros ms' PO.
          (nelim PO 18%nat; intros t0' t1' a1' a2' a3' a4' a5' a6' a7' m3 h -> MUc WMc MI3 ST3 B4 Hh).
          rewrite ?unsigned_lit in MUc by lia. rewrite ?unsigned_lit in ST3 by lia.
          transport_after_call bsegs mm m3 MUc WMc.
          replace (ret_pc (Z_to_bv 64 0x857c8)) with (Z_to_bv 64 0x857c8) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
          (* [comment removed for export] *)
          do 8 zstep. if_cases Kr; zify_cond Kr.
          { eapply exit_fail; [| lia| lia| unfold nalloc; lia].
            split; [eassumption|]. split; [exact BL|]. split; [assumption|]. split; [assumption|]. split; assumption. }
          (* [comment removed for export] *)
          do 9 zstep.
          lazymatch goal with |- context [Z_to_bv 64 (Z.lor ?a (Z.land ?hh 1023) + 65536)] =>
            assert (Ha : 0 <= a < 2^20) by (clear -HFC; rewrite ?Z.shiftr_div_pow2, ?Z.shiftl_mul_pow2 by lia; ml);
            assert (Hb : 0 <= Z.land hh 1023 < 2^20)
              by (clear -Hh; change 1023 with (2^10 - 1); rewrite zb_land_mask by lia; ml);
            pose proof (lor_bound _ _ 20 Ha Hb) as HL;
            assert (CPR : 0 <= Z.lor a (Z.land hh 1023) + 65536 < 2^32) by (clear -HL; lia)
          end.
          eapply encode_tail; [exact CTX| exact IH| lia| lia| lia| lia| lia| exact CPR| lia| lia| unfold nalloc; lia| apply dinv_u; [lia| cbv; discriminate] |].
          split; [eassumption|]. split; [exact BL|]. split; [assumption|]. split; [assumption|]. split; assumption.
        - (* [comment removed for export] *)
          zstep. zstep. zstep. zstep. zstep. br_fail LMm.
          zstep. zstep. if_cases K1; zify_cond K1.
          + (* [comment removed for export] *)
            eapply one_byte; [exact CTX| exact IH| lia| lia| lia| lia| lia| unfold nalloc; lia| apply dinv_u; [lia| cbv; discriminate]| exact LMm].
          + zstep. rewrite (srliw_small FC 11) by lia. zstep. zstep. if_cases K2; zify_cond K2.
            * (* [comment removed for export] *)
              zstep. rewrite (srliw_small FC 16) by lia. zstep. if_cases K3; zify_cond K3; [exfalso; ml|].
              zstep. zstep. zstep.
              eapply encode_tail; [exact CTX| exact IH| lia| lia| lia| lia| lia| lia| lia| lia| unfold nalloc; lia| apply dinv_u; [lia| cbv; discriminate]| exact LMm].
            * zstep. zstep. zstep.
              eapply encode_tail; [exact CTX| exact IH| lia| lia| lia| lia| lia| lia| lia| lia| unfold nalloc; lia| apply dinv_u; [lia| cbv; discriminate]| exact LMm].
      Qed.

      (* [comment removed for export] *)
      Lemma esc_u : forall mm buf x1 x5 x6 x10 x14 x15 x16 x17 x21, LM mm buf ->
        evt bsegs KP (LSTx 0x8567c x1 x5 x6 x10 (Z_to_bv 64 (CA + e - (CA + i))) x14 x15 x16 x17 x21 i oc mm).
      Proof.
        intros until x21. intros LMm. preU LMm mm buf.
        zstep. zstep. if_cases Kl; zify_cond Kl; [exfalso; lia|].
        zstep. ugd.                                                     (* [comment removed for export] *)
        zstep. replace (CA + i + 2) with (CA + (i + 2)) by lia.
        call_hex4 2 BY SB2 TS2 MU MI ST.
        intros ms' PO.
        (nelim PO 18%nat; intros t0' t1' a1' a2' a3' a4' a5' a6' a7' m3 h -> MUc WMc MI3 ST3 B4 Hh).
        rewrite ?unsigned_lit in MUc by lia. rewrite ?unsigned_lit in ST3 by lia.
        transport_after_call bsegs mm m3 MUc WMc.
        replace (ret_pc (Z_to_bv 64 0x85694)) with (Z_to_bv 64 0x85694) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
        eapply L_cls; [exact Hh|].
        split; [eassumption|]. split; [exact BL|]. split; [assumption|]. split; [assumption|]. split; assumption.
      Qed.
    End U.

    (* [comment removed for export] *)
    (* [comment removed for export] *)
    Lemma head_k : LOOPK sp gp tp t4 t5 t6 F fc m2 CA blen off e sk S P U lo bs k.
    Proof.
      unfold LOOPK. intros until x21. intros Hk Hi DI Hoc LMm. ctx. lm LMm mm buf. unfold W2, nalloc in *. unfold LST, LSTg.
      pose proof (dinv_room _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CTX i oc 1 DI ltac:(lia) ltac:(lia)) as ROOM1. unfold nalloc in ROOM1.
      (nelim (text_read mm CA bs i (Z_to_bv 64 (CA + i)) BY ltac:(lia) ltac:(lia) eq_refl) 4%nat; intros b Hb RD Hat).
      pose proof (byte_range b) as Rb.
      zstep. zstep. pose proof (TS2 (CA + i) ltac:(lia)) as CK. asan_chk CK.
      zstep. zstep. if_cases Kbs; zify_cond Kbs.
      - (* [comment removed for export] *)
        zstep. replace (S + oc + 1) with (S + (oc + 1)) by lia. guard1.
        zstep. zstep. pose proof (shadow_ok_shchk1 _ S _ (S + oc) SO2 ltac:(lia)) as CKo. asan_chk CKo.
        zstep. replace (CA + i + 1) with (CA + (i + 1)) by lia.
        pose proof (u8arr_store_ok bsegs _ _ _ oc (Z_to_bv 64 (S + oc)) BUF ltac:(lia) eq_refl) as SOK.
        zstep. rewrite le1_lit.
        pose proof (u8arr_write bsegs _ _ _ oc (Z_to_bv 8 (bv_unsigned b)) BUF ltac:(lia)) as BUF'.
        clear BUF. store_done. rename BUF' into BUF.
        assert (DI' : DINV (i + 1) (oc + 1)).
        { eapply dinv_step; [exact DI| lia| lia|]. unfold bflag. rewrite Hat. replace (bv_unsigned b =? 92) with false by (symmetry; apply Z.eqb_neq; exact Kbs). reflexivity. }
        zstep.
        eapply tests; [exact CTX| exact IH| cbn; auto 10| lia| lia| exact DI'| lia| lm_close BUF BL MU WM MI ST].
      - (* [comment removed for export] *)
        assert (DI2 : DINV (i + 2) (oc + 1)).
        { eapply dinv_step; [exact DI| lia| lia|]. unfold bflag. rewrite Hat, Kbs. cbv. discriminate. }
        zstep. zstep. if_cases Kp.
        { (* [comment removed for export] *)
          eapply exit_fail; [exact LMm| lia| lia| unfold nalloc; lia]. }
        clear Kp.
        zstep. replace (CA + i + 1) with (CA + (i + 1)) by lia.
        (nelim (text_read mm CA bs (i + 1) (Z_to_bv 64 (CA + (i + 1))) BY ltac:(lia) ltac:(lia) ltac:(unfold wa; f_equal; lia)) 4%nat; intros c Hc RDc Hatc).
        pose proof (byte_range c) as Rc.
        zstep. zstep. pose proof (TS2 (CA + (i + 1)) ltac:(lia)) as CK1. asan_chk CK1.
        zstep. zstep. zstep. if_cases Kr; zify_cond Kr.
        { eapply exit_fail; [exact LMm| lia| lia| unfold nalloc; lia]. }
        assert (Hcr : 34 <= bv_unsigned c <= 117) by (clear -Rc Kr; ml).
        zstep. zstep.
        pose proof (jt_read' mm (bv_unsigned c) MI Hcr) as RDj.
        zstep. zstep. zstep.
        destruct (jt_cases (bv_unsigned c)) as [[Hcls E]|[[Hcls E]|[[Hcls E]|[[Hcls E]|[[Hcls E]|[[Hcls E]|[[Hcls E]|E]]]]]]];
          rewrite (jt_pc (bv_unsigned c) _ Hcr ltac:(rewrite E; reflexivity)).
        + eapply esc_char; [exact CTX| exact IH| lia| lia| lia| lia| lia| unfold nalloc; lia| exact DI2| exact LMm].
        + eapply esc_const; [exact CTX| exact IH| cbn; auto 10| lia| lia| lia| lia| unfold nalloc; lia| exact DI2| exact LMm].
        + eapply esc_const; [exact CTX| exact IH| cbn; auto 10| lia| lia| lia| lia| unfold nalloc; lia| exact DI2| exact LMm].
        + (* [comment removed for export] *) destruct (Z_lt_le_dec (e - i) 6) as [SHORT|LONG].
          * (* [comment removed for export] *)
            unfold JT. zstep. zstep. if_cases Kl; zify_cond Kl; [| exfalso; lia].
            eapply exit_fail; [exact LMm| lia| lia| unfold nalloc; lia].
          * eapply esc_u; [lia| lia| lia| rewrite Hat, Kbs; reflexivity| exact DI| lia| exact LMm].
        + eapply esc_const; [exact CTX| exact IH| cbn; auto 10| lia| lia| lia| lia| unfold nalloc; lia| exact DI2| exact LMm].
        + eapply esc_const; [exact CTX| exact IH| cbn; auto 10| lia| lia| lia| lia| unfold nalloc; lia| exact DI2| exact LMm].
        + eapply esc_const; [exact CTX| exact IH| cbn; auto 10| lia| lia| lia| lia| unfold nalloc; lia| exact DI2| exact LMm].
        + (* [comment removed for export] *) eapply exit_fail; [exact LMm| lia| lia| unfold nalloc; lia].
    Qed.
  End Body.

  Theorem dec_loop : forall k, LOOPK sp gp tp t4 t5 t6 F fc m2 CA blen off e sk S P U lo bs k.
  Proof. intros k. induction k as [k IH] using lt_wf_ind. apply head_k. exact IH. Qed.
End PS.


End CeilWrap.
End CJ_pstring_B.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import ShapeAlg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Tac Bytes ZBridge.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require Import LBase LSCPS.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_cost.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require LiaOn.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.LiaOn.SepM.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import CJ_bandM.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require CJ_skipws.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_skipws.CJ_band2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require CJ_skipws.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_skipws.CJ_band.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import BImg RT_defs CJ_iface AShadow CJ_tree.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require CJ_phex4.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_phex4.CJ_pbuf.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import CJ_conv.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require CJ_phex4.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_phex4.CJ_parse_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require CJ_phex4.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_phex4.CJ_parse_lemmas.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import CJ_phex4.
Import CJ_pstring_A.
Import CJ_pstring_B.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require CJ_pstrA.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_pstrA.CJ_shfast.
Local Ltac sh_resolve_if ::= sh_resolve_if_fast.
Local Ltac sh_join v Cv rdk ::= sh_join_fast v Cv rdk.
(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require StoreCache.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.StoreFast.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import StoreCache.
Local Ltac mem_after_store ::= mem_after_store_cached.
Local Ltac addr_eq_tac ::= addr_eq_tac_cached.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_cached segs m m' MU WM.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Ltac fix_lit_store :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) =>
      change (Z_to_le_bytes 8 z) with (le8 (Z_to_bv 64 z)); mem_after_store
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?z)) _) =>
      change (Z_to_le_bytes 4 z) with (le4 (Z_to_bv 64 z)); mem_after_store
  | _ => idtac
  end.
(* [comment removed for export] *)
Ltac ugd := let G := fresh "G" in zstep; if_cases G; zify_cond G; try (exfalso; lia).

Section PSTR.
  Variable AI : art_iface.
  Variable TI : trs_iface.
  (* [comment removed for export] *)
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (m : word -> option byte) (g : lghost) (sp0 SPB : Z) (LB LR : list cblock) (LF : list fframe) (np B : Z).
  Variables (U P CA blen off depth : Z) (bs : list byte) (D n lo : Z).
  Variables (nx : Z) (pv : word) (ch ty : Z) (p1 : word) (vs : Z) (vi p2 vd : word) (ky : Z).
  Hypothesis HPU : Permutation ((U, 64) :: LR) LB.
  Hypothesis HDn : In (D, n) LR /\ D <= CA /\ CA + blen <= D + n.
  Hypothesis LEN : Z.of_nat (length bs) = blen.
  Hypothesis BLEN : blen < 2^31.
  Hypothesis CEIL : alloc_ceiling <= lo.
  Hypothesis LO : lo <= bv_unsigned sp - PARSE_STRING_STACK.
  Hypothesis PLF : In (P - 32, 1) LF.
  Hypothesis PFR : AIMG_HI <= P - 32 /\ P - 32 + 128 <= alloc_ceiling /\ (P - 32) mod 128 = 0.
  Hypothesis UBND : sclr U 64.                  (* [comment removed for export] *)
  Hypothesis PBND : sclr (P - 32) 128.          (* [comment removed for export] *)
  Hypothesis SPF : 0 <= bv_unsigned sp /\ bv_unsigned sp <= SPB /\ SPB < 2^62 /\ bv_unsigned sp + 16 < ASTACK_TOP sp0 /\ sp0 <= 2^47
                   /\ ASTACK_BOTTOM sp0 <= lo /\ bv_unsigned sp mod 16 = 0.
  Hypothesis OFF : 0 <= off < blen.
  Hypothesis TP : tp = wz ATP.
  Hypothesis URNG : ablock_range U 64.
  Hypothesis DRNG : ablock_range D n.
  Hypothesis UD : U + 64 <= D \/ D + n <= U.
  (* [comment removed for export] *)
  Hypothesis PU : U + 64 + 16 <= P - 32 \/ P - 32 + 128 <= U - 16.
  Hypothesis PD : D + n + 16 <= P - 32 \/ P - 32 + 128 <= D - 16.
  Hypothesis BPRE : pstr_cost_pre (blen - off) <= B.
  Hypothesis STM : STAT TI PSTR_TR_MALLOC.
  Hypothesis STF : STAT TI PSTR_TR_FREE.

  Notation SP := (bv_unsigned sp).
  Notation L z := (Z_to_bv 64 z) (only parsing).
  Notation POST := (parse_string_post AI TI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc sp0 SPB LR LF np B U P CA blen off depth bs D n lo m g
                      nx pv ch ty p1 vs vi p2 vd ky).
  (* [comment removed for export] *)
  Notation SAVED := [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  (* [comment removed for export] *)
  Definition CST (pc : Z) (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x25 x26 x27 x28 x29 x30 x31 : word)
      (mm : word -> option byte) : machine_state :=
    MS (mkR x1 (Z_to_bv 64 (SP + -144)) gp tp x5 x6 x7 (Z_to_bv 64 (P + 16)) x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21
            (S6 P) (S7 P) (Z_to_bv 64 2147450880) x25 x26 x27 x28 x29 x30 x31)
       F (Z_to_bv 64 pc) fc None mm (seg_rom bsegs).

  (* [comment removed for export] *)
  Definition MID (m1 : word -> option byte) (mo1 : Model) (g1 : lghost) (LB1 : list cblock) (TRS1 : list (list Z)) (B1 : Z) (errv1 : word) : Prop :=
    ART AI sp0 SPB LB1 LF TRS1 B1 m1 mo1 g1 /\ bytes_at bsegs m1 CA bs /\ rw_cells bsegs m1 AERRNO [C4 errv1]
    /\ mem_inv bsegs m1 /\ stk bsegs m1 lo (SP + -144) /\ ppres sp0 LR LF SP P m m1 /\ gmono g g1 /\ TINV TI np TRS1 /\ pbuf_sh m1 P.

  (* [comment removed for export] *)
  Ltac steq := unfold CST, LST, LSTg, mkR; repeat (lazymatch goal with |- @eq Z _ _ => lia | |- _ => first [reflexivity | progress f_equal] end).
  Ltac dj := cbn [disjoint_from cells_size Cells.csize Nat.add length]; first [lia | split; [lia| exact I]].
  Ltac alia := first [ unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG; rewrite ?alloc_ceiling_eq; unfold AMALLOC_STACK, PARSE_STRING_STACK; lia | sclr_tac2 ].
  (* [comment removed for export] *)
  Ltac eqcells H :=
    lazymatch goal with |- rw_cells _ _ _ ?cs =>
      lazymatch type of H with rw_cells _ _ _ ?cs' =>
        replace cs with cs'; [exact H| unfold pbuf_cells, node_cells, wz; repeat f_equal; lia] end end.
  Ltac lits := (nelimp URNG 4%nat; intros U1 U2 U3 U4); (nelimp DRNG 4%nat; intros D1 D2 D3 D4); (nelimp PFR 3%nat; intros PF1 PF2 PF3); pose proof PBND as PBND'; pose proof UBND as UBND';
               (nelimp SPF 7%nat; intros SP1 SP2 SP3 SP4 SP5 SP6 SP7); pose proof CEIL as CEIL'; pose proof LO as LO';
               try rewrite alloc_ceiling_eq in U4, D4, PF2, CEIL'; unfold sclr, PARSE_STRING_STACK, AMALLOC_STACK, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in *;
               pose proof (bv_unsigned_in_range 64 sp) as SPR; change (bv_modulus 64) with (2^64) in SPR.

  (* [comment removed for export] *)
  Lemma fail0_tail : forall (i off1 : Z) m1 mo1 g1 LB1 TRS1 B1 errv1 (junk : list byte)
      x1 x5 x6 x7 x10 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x25 x26 x27 x28 x29 x30 x31,
    MID m1 mo1 g1 LB1 TRS1 B1 errv1 -> Permutation ((U, 64) :: LR) LB1 ->
    rw_cells bsegs m1 (SP + -144) (CB 40 junk :: SAVED) ->
    pbuf_at m1 P CA blen off1 depth ->
    rw_cells bsegs m1 U (node_cells nx pv ch ty p1 vs vi p2 vd ky) ->
    off <= i <= blen -> B - pstr_fail_cost (blen - off) <= B1 ->
    LSCPS bsegs POST (CST 0x85a08 x1 x5 x6 x7 (Z_to_bv 64 (CA + i)) x10 (Z_to_bv 64 P) x12 x13 x14 x15 x16 x17
                          x18 x19 x20 x21 x25 x26 x27 x28 x29 x30 x31 m1) mo1 g1.
  Proof.
    intros until x31. intros (HL & BY & ERR & MI & ST & PR & GM & TV & PSH) HP1 FR PB ND Hi HB. lits. bandM. sepM.
    pose proof (pbuf_at_bound _ _ _ _ _ _ PB) as PBB. unfold pbuf_at, pbuf_cells in PB. unfold CST, S6, S7. unfold AERRNO, ATP in ERR.
    pose proof (rw_cells_bound bsegs _ _ _ ND) as NDB. rewrite node_cells_size in NDB. unfold node_cells, wz in ND. unfold wz in PB.
    pose proof (bytes_at_bound _ _ _ _ BY) as BYB.
    eapply lscps_step_evt. cbv beta delta [mkR].
    pose proof (munch_refl [(P + 16, P + 24)] m1) as MU. pose proof (wmono_refl bsegs m1) as WM.
    pose proof (sh_zero_shb m1 P (P + 56) P PSH ltac:(lia)) as Z0. asan_chk Z0. clear Z0.       (* [comment removed for export] *)
    zstep. zstep.
    pose proof (sh_zero_shb m1 P (P + 56) (P + 16) PSH ltac:(lia)) as Z16. asan_chk Z16. clear Z16.
    zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
    do 13 zstep. zstep.
    release_frame FR ST (bv_unsigned sp).
    zstep.
    apply evt_done. apply lscps_done. unfold parse_string_post.
    nexists 15%nat. exists m2, 0, i, LB1, [], TRS1, B1, errv1.
    split; [reflexivity|]. split; [unfold wz; rewrite (zxb_zb 0) by lia; reflexivity|].
    split.
    { (* [comment removed for export] *) split; [eapply (art_pbuf_store AI); [exact HL| exact PLF| exact MU| exact WM| lia| lia]|].
      split; [exact HP1|]. split; [apply (proj1 HDn)|]. split; [lia|]. split; [lia|]. split; [exact BY|]. split; [exact LEN|]. split; [exact BLEN|].
      split; [unfold AERRNO, ATP; exact ERR|]. split; [exact MI|].
      split; [exact ST|]. split; [alia|]. split; [exact TV|]. split; [exact PLF|].
      split; [eapply pbuf_sh_high_store; [exact PSH| exact MU| alia| alia| alia]|].
      repeat split; try assumption; alia. }
    split. { eapply ppres_trans; [exact PR|]. eapply ppres_pbuf_store; [exact MU| exact WM| lia| lia]. }
    split; [exact GM|].
    split. { unfold pbuf_at. eqcells PB. }
    split; [lia|]. left. split; [reflexivity|]. split; [reflexivity|]. split; [eqcells ND| exact HB].
  Qed.

  (* [comment removed for export] *)
  Lemma pres_frame : forall LBx m1 m2 cs, cj_pres sp0 LBx LF (SP + -144) m1 m2 ->
    rw_cells bsegs m1 (SP + -144) cs -> Z.of_nat (cells_size cs) = 144 -> rw_cells bsegs m2 (SP + -144) cs.
  Proof. intros LBx m1 m2 cs PR2 FR Hsz. lits. bandM. sepM. eapply cj_pres_rw_cells; [exact PR2| exact FR|]. left. rewrite Hsz. pose proof (ASTACK_TOP_le sp0). lia. Qed.

  Lemma pres_pbuf : forall LBx m1 m2 c l o d, cj_pres sp0 LBx LF (SP + -144) m1 m2 ->
    pbuf_at m1 P c l o d -> pbuf_at m2 P c l o d.
  Proof.
    intros LBx m1 m2 c l o d PR2 PB. unfold pbuf_at in *. eapply cj_pres_rw_cells; [exact PR2| exact PB|].
    do 4 right. left. exists (P - 32), 1. split; [exact PLF|]. rewrite pbuf_cells_size. change (fsz 1) with 128. lia.
  Qed.

  Lemma pres_node : forall LBx m1 m2 cs, cj_pres sp0 LBx LF (SP + -144) m1 m2 -> In (U, 64) LBx ->
    rw_cells bsegs m1 U cs -> Z.of_nat (cells_size cs) = 64 -> rw_cells bsegs m2 U cs.
  Proof. intros LBx m1 m2 cs PR2 HIn ND Hsz. eapply cj_pres_rw_cells; [exact PR2| exact ND|]. do 3 right. left. exists U, 64. rewrite Hsz. split; [exact HIn| lia]. Qed.

  Lemma pres_text : forall LBx m1 m2, cj_pres sp0 LBx LF (SP + -144) m1 m2 -> In (D, n) LBx ->
    bytes_at bsegs m1 CA bs -> bytes_at bsegs m2 CA bs.
  Proof. intros LBx m1 m2 PR2 HIn BY. eapply cj_pres_bytes_at; [exact PR2| exact BY|]. do 3 right. left. exists D, n. rewrite LEN. split; [exact HIn| lia]. Qed.

  Lemma pres_pbuf_sh : forall LBx m1 m2, cj_pres sp0 LBx LF (SP + -144) m1 m2 -> (forall b, In b LR -> In b LBx) ->
    pbuf_sh m1 P -> pbuf_sh m2 P.
  Proof.
    intros LBx m1 m2 PR2 INL PSH. lits. bandM. sepM.
    apply (ppres_pbuf_sh sp0 LR LF SP P m1 m2); [| exact PSH| exact PLF| alia| alia| alia (* [comment removed for export] *)].
    eapply ppres_of_cj_pres; [exact PR2| lia| exact INL].
  Qed.

  (* [comment removed for export] *)
  Lemma dealloc_tail : forall (S k i off1 : Z) m1 mo1 g1 LB2 TRS1 B1 errv1 (junk : list byte)
      x1 x5 x6 x7 x10 x12 x13 x14 x15 x16 x17 x19 x20 x21 x25 x26 x27 x28 x29 x30 x31,
    MID m1 mo1 g1 LB2 TRS1 B1 errv1 -> Permutation ((U, 64) :: (S, k) :: LR) LB2 ->
    rw_cells bsegs m1 (SP + -144) (CB 24 junk :: C8 (Z_to_bv 64 U) :: C8 (Z_to_bv 64 P) :: SAVED) ->
    pbuf_at m1 P CA blen off1 depth ->
    rw_cells bsegs m1 U (node_cells nx pv ch ty p1 vs vi p2 vd ky) ->
    off <= i <= blen -> B - pstr_fail_cost (blen - off) <= B1 - cost_free ->
    LSCPS bsegs POST (CST 0x859e4 x1 x5 x6 x7 (Z_to_bv 64 (CA + i)) x10 (Z_to_bv 64 P) x12 x13 x14 x15 x16 x17
                          (Z_to_bv 64 S) x19 x20 x21 x25 x26 x27 x28 x29 x30 x31 m1) mo1 g1.
  Proof.
    intros until x31. intros (HL & BY & ERR & MI & ST & PR & GM & TV & PSH) HP2 FR PB ND Hi HB. lits. bandM. sepM.
    pose proof (pbuf_at_bound _ _ _ _ _ _ PB) as PBB. pose proof PB as PB0. unfold pbuf_at, pbuf_cells in PB. unfold CST, S6, S7. unfold AERRNO, ATP in ERR.
    unfold wz in PB.
    assert (HP2' : Permutation ((S, k) :: (U, 64) :: LR) LB2) by (eapply Permutation_trans; [apply perm_swap| exact HP2]).
    (nelimp (art_binv AI _ _ _ _ _ _ _ _ _ HL) 4%nat; intros _ _ HB0 _).
    eapply lscps_step_evt. cbv beta delta [mkR].
    zstep. zstep. zstep.
    pose proof (sh_zero_shb m1 P (P + 56) (P + 40) PSH ltac:(lia)) as Z40. asan_chk Z40. clear Z40.
    zstep. zstep. zstep.
    replace (ret_pc (Z_to_bv 64 AFREE)) with (wz AFREE) by (unfold wz, AFREE; symmetry; apply ret_pc_even; [lia| reflexivity]).
    apply evt_done. cbv beta.
    eapply lscps_bind.
    { eapply (art_free_ok AI) with (lo := lo) (A := S) (n := k) (tl := []); rewrite ?unsigned_lit by lia;
        first [ exact HL | eapply perm_in_head; exact HP2' | exact ST | unfold AERRNO, ATP; exact ERR | exact MI | exact TP | reflexivity | alia
              | clear -HB BPRE OFF; unfold pstr_cost_pre, pstr_fail_cost, cost_free in *; lia
              | split; [lia| unfold PC0_FREE; lia]
              | apply uwt_hook_nonfp; lia
              | eapply (tinv_room TI); [exact TV| exact STF] ]. }
    cbv beta. intros ms2 mo2 g2 PO.
    (nelim PO 25%nat; intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m2 TRS2 -> MI2 ST2 ERR2 PR2 GM2 TP2 HL2)
.
    rewrite ?unsigned_lit in ST2, PR2 by lia.
    replace (ret_pc (Z_to_bv 64 0x85a04)) with (Z_to_bv 64 0x85a04) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    pose proof (perm_cb_remove _ _ _ _ HP2' (proj1 (art_nodup AI _ _ _ _ _ _ _ _ _ HL))) as HP1.
    assert (INL : forall b, In b LR -> In b (cb_remove S LB2)) by (intros b Hb; eapply Permutation_in; [exact HP1| right; exact Hb]).
    apply (pres_frame _ _ _ _ PR2) in FR; [| reflexivity].
    apply (pres_pbuf _ _ _ _ _ _ _ PR2) in PB0.
    apply (pres_node _ _ _ _ PR2 ltac:(eapply perm_in_head; exact HP1)) in ND; [| reflexivity].
    apply (pres_text _ _ _ PR2 ltac:(apply INL; apply (proj1 HDn))) in BY.
    eapply lscps_step_evt. cbv beta delta [mkR].
    zstep. apply evt_done.
    apply (rw_cells_merge bsegs m2 _ [] [CB 24 junk; C8 (Z_to_bv 64 U); C8 (Z_to_bv 64 P)]) in FR.
    cbn [cells_size Cells.csize cells_bytes cbytes Nat.add app] in FR.
    eapply (fail0_tail i off1 m2 mo2 g2 (cb_remove S LB2) TRS2 (B1 - cost_free) errv1).
    - split; [exact HL2|]. split; [exact BY|]. split; [unfold AERRNO, ATP; exact ERR2|]. split; [exact MI2|]. split; [exact ST2|].
      split; [eapply ppres_trans; [exact PR| eapply ppres_of_cj_pres; [exact PR2| lia| exact INL]]|].
      split; [eapply gmono_trans; [exact GM| exact GM2]|].
      split; [eapply (tinv_put TI); [exact TV| exact STF| rewrite unsigned_lit in TP2 by lia; exact TP2]|].
      eapply pres_pbuf_sh; [exact PR2| exact INL| exact PSH].
    - exact HP1.
    - exact FR.
    - exact PB0.
    - exact ND.
    - exact Hi.
    - exact HB.
  Qed.

  (* [comment removed for export] *)
  Lemma ok_tail : forall (S e oc off1 : Z) (buf junk : list byte) m1 mo1 g1 LB2 TRS1 B1 errv1
      x1 x5 x6 x7 x9 x13 x14 x15 x16 x17 x19 x20 x21 x26 x27 x28 x29 x30 x31,
    MID m1 mo1 g1 LB2 TRS1 B1 errv1 -> Permutation ((U, 64) :: (S, Z.of_nat (length buf)) :: LR) LB2 ->
    rw_cells bsegs m1 (SP + -144) (CB 24 junk :: C8 (Z_to_bv 64 U) :: C8 (Z_to_bv 64 P) :: SAVED) ->
    pbuf_at m1 P CA blen off1 depth ->
    rw_cells bsegs m1 U (node_cells nx pv ch ty p1 vs vi p2 vd ky) ->
    u8arr bsegs m1 S buf -> 0 <= oc < Z.of_nat (length buf) ->
    ablock_range S (Z.of_nat (length buf)) -> (U + 64 <= S \/ S + Z.of_nat (length buf) <= U) ->
    (D + n <= S \/ S + Z.of_nat (length buf) <= D) -> (S + Z.of_nat (length buf) + 16 <= P - 32 \/ P - 32 + 128 <= S - 16) ->
    off <= e < blen -> 1 <= Z.of_nat (length buf) <= e - off + 1 -> B1 = B - cost_malloc (Z.of_nat (length buf)) ->
    LSCPS bsegs POST (CST 0x85974 x1 x5 x6 x7 x9 (Z_to_bv 64 (S + oc)) (Z_to_bv 64 P) (Z_to_bv 64 U) x13 x14 x15 x16 x17
                          (Z_to_bv 64 S) x19 x20 x21 (Z_to_bv 64 (CA + e)) x26 x27 x28 x29 x30 x31 m1) mo1 g1.
  Proof.
    intros until x31. intros (HL & BY & ERR & MI & ST & PR & GM & TV & PSH) HP2 FR PB ND BUF Hoc SRNG SU SD SPfr He Hk HB1.
    (nelim SRNG 4%nat; intros SR1 SR2 SR3 SR4). lits. bandM. sepM. try rewrite alloc_ceiling_eq in SR4.
    pose proof (pbuf_at_bound _ _ _ _ _ _ PB) as PBB. unfold pbuf_at, pbuf_cells, wz in PB. unfold CST, S6, S7. unfold AERRNO, ATP in ERR.
    pose proof (rw_cells_bound bsegs _ _ _ ND) as NDB. rewrite node_cells_size in NDB. unfold node_cells, wz in ND.
    pose proof (bytes_at_bound _ _ _ _ BY) as BYB.
    assert (HP2' : Permutation ((S, Z.of_nat (length buf)) :: (U, 64) :: LR) LB2) by (eapply Permutation_trans; [apply perm_swap| exact HP2]).
    assert (INS : In (S, Z.of_nat (length buf)) LB2) by (eapply perm_in_head; exact HP2').
    assert (INU : In (U, 64) LB2) by (eapply perm_in_head; exact HP2).
    assert (INLR : forall b, In b LR -> In b LB2) by (intros b Hb; eapply Permutation_in; [exact HP2| right; right; exact Hb]).
    pose proof (art_block_shadow_ok AI _ _ _ _ _ _ _ _ _ _ _ HL INS) as SOS.
    pose proof (art_block_shadow_ok AI _ _ _ _ _ _ _ _ _ _ _ HL INU) as SOU.
    eapply lscps_step_evt. cbv beta delta [mkR].
    (* [comment removed for export] *)
    pose proof (munch_refl [(S + oc, S + oc + 1)] m1) as MU. pose proof (wmono_refl bsegs m1) as WM.
    ugd.
    zstep. zstep. pose proof (shadow_ok_shchk1 m1 S _ (S + oc) SOS ltac:(lia)) as CK. asan_chk CK.
    zstep. replace (Z.land U 7) with 0 by (change 7 with (Z.ones 3); rewrite Z.land_ones by lia; change (2^3) with 8; lia).
    pose proof (u8arr_store_ok bsegs _ _ _ oc (Z_to_bv 64 (S + oc)) BUF ltac:(lia) eq_refl) as SOK.
    zstep. rewrite le1_lit.
    pose proof (u8arr_write bsegs _ _ _ oc (Z_to_bv 8 0) BUF ltac:(lia)) as BUF'. clear BUF. store_done. rename BUF' into BUF.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
    assert (HL2 : ART AI sp0 SPB LB2 LF TRS1 B1 m2 mo1 g1) by (eapply (art_block_store AI); [exact HL| exact INS| exact MU| exact WM| lia| lia]).
    assert (PR2 : ppres sp0 LR LF SP P m m2).
    { eapply ppres_trans; [exact PR|]. eapply (ppres_block_store AI); [exact HL| exact HP2'| intros b Hb; right; exact Hb| alia| lia| exact MU| exact WM| lia| lia]. }
    assert (SOU2 : shadow_ok m2 U 64) by (eapply shadow_ok_high_store; [exact SOU| exact MU| lia| alia| lia| alia]).
    assert (PSH2 : pbuf_sh m2 P) by (eapply pbuf_sh_high_store; [exact PSH| exact MU| alia| alia| alia]).
    clear MU WM SOS SOU.
    ugd.                                                          (* [comment removed for export] *)
    (* [comment removed for export] *)
    pose proof (munch_refl [(U + 24, U + 40)] m2) as MU. pose proof (wmono_refl bsegs m2) as WM.
    zstep. zstep. zstep.
    pose proof (shadow_ok_shchk m2 U 64 (U + 24) 4 SOU2 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(Z.div_mod_to_equations; lia)) as CK4. asan_chk CK4.
    zstep. zstep. fix_lit_store.
    zstep. zstep. zstep.
    pose proof (shadow_ok_shchk m2 U 64 (U + 32) 8 SOU2 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(Z.div_mod_to_equations; lia)) as CK8. asan_chk CK8.
    zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
    assert (HL3 : ART AI sp0 SPB LB2 LF TRS1 B1 m3 mo1 g1) by (eapply (art_block_store AI); [exact HL2| exact INU| exact MU| exact WM| lia| lia]).
    assert (PR3 : ppres sp0 LR LF SP P m m3).
    { eapply ppres_trans; [exact PR2|]. eapply (ppres_block_store AI); [exact HL2| exact HP2| intros b Hb; right; exact Hb| alia| lia| exact MU| exact WM| lia| lia]. }
    assert (PSH3 : pbuf_sh m3 P) by (eapply pbuf_sh_high_store; [exact PSH2| exact MU| alia| alia| alia]).
    clear MU WM HL2 PR2 SOU2 PSH2.
    (* [comment removed for export] *)
    pose proof (munch_refl [(P + 16, P + 24)] m3) as MU. pose proof (wmono_refl bsegs m3) as WM.
    pose proof (sh_zero_shb m3 P (P + 56) P PSH3 ltac:(lia)) as Z0. asan_chk Z0. clear Z0.
    zstep. zstep. zstep. zstep. zstep.
    pose proof (sh_zero_shb m3 P (P + 56) (P + 16) PSH3 ltac:(lia)) as Z16. asan_chk Z16. clear Z16.
    zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m4 end.
    assert (HL4 : ART AI sp0 SPB LB2 LF TRS1 B1 m4 mo1 g1) by (eapply (art_pbuf_store AI); [exact HL3| exact PLF| exact MU| exact WM| lia| lia]).
    assert (PR4 : ppres sp0 LR LF SP P m m4).
    { eapply ppres_trans; [exact PR3|]. eapply ppres_pbuf_store; [exact MU| exact WM| lia| lia]. }
    assert (PSH4 : pbuf_sh m4 P) by (eapply pbuf_sh_high_store; [exact PSH3| exact MU| alia| alia| alia]).
    clear MU WM HL3 PR3 PSH3.
    do 13 zstep. zstep. release_frame FR ST (bv_unsigned sp). zstep.
    apply evt_done. apply lscps_done. unfold parse_string_post.
    nexists 15%nat. exists m4, 1, (e + 1), LB2, [(S, Z.of_nat (length buf))], TRS1, B1, errv1.
    split; [reflexivity|]. split; [reflexivity|].
    split.
    { split; [exact HL4|].
      split; [exact HP2|]. split; [apply (proj1 HDn)|]. split; [lia|]. split; [lia|]. split; [exact BY|]. split; [exact LEN|]. split; [exact BLEN|].
      split; [unfold AERRNO, ATP; exact ERR|]. split; [exact MI|]. split; [exact ST|]. split; [alia|]. split; [exact TV|]. split; [exact PLF|].
      split; [exact PSH4|]. repeat split; try assumption; alia. }
    split; [exact PR4|]. split; [exact GM|].
    split. { unfold pbuf_at. eqcells PB. }
    split; [lia|]. right. split; [reflexivity|]. exists S, (Z.of_nat (length buf)). split; [reflexivity|]. split; [lia|].
    split; [eqcells ND|].
    split.
    { destruct (split_first_nul (upd buf (Z.to_nat oc) (Z_to_bv 8 0)) (Z.to_nat oc)) as (str & tail & E & NI). (* [comment removed for export] *)
      { apply nth_error_upd_same. lia. }
      eapply cj_str_intro; [lia| | exact NI|].
      - rewrite <- E. exact (proj1 BUF).
      - apply (f_equal (@length byte)) in E. rewrite upd_length, length_app in E. cbn [length] in E. lia. }
    split; [lia| exact HB1].
  Qed.

  (* [comment removed for export] *)
  Section Loop1.
    Variables (t4 t5 t6 : word) (m1 : word -> option byte).
    Notation M1 := 18446744073709551615 (only parsing).

    Definition L1 (pc : Z) (x6 x7 x13 x19 x20 x25 x28 : word) : machine_state :=
      MS (mkR ra (Z_to_bv 64 (SP + -144)) gp tp (Z_to_bv 64 34) x6 x7 (Z_to_bv 64 (P + 16)) (Z_to_bv 64 (CA + off + 1)) (Z_to_bv 64 U) (Z_to_bv 64 P)
              (Z_to_bv 64 (CA + off)) x13 (Z_to_bv 64 CA) (Z_to_bv 64 blen) (Z_to_bv 64 92) (Z_to_bv 64 M1)
              s2 x19 x20 s5 (S6 P) (S7 P) (Z_to_bv 64 2147450880) x25 s10 s11 x28 t4 t5 t6)
         F (Z_to_bv 64 pc) fc None m1 (seg_rom bsegs).

    Definition Q1 : machine_state -> Prop := fun ms' =>
      (exists (q sk : Z) (x7 x28 : word),
          ms' = L1 0x85514 (Z_to_bv 64 (Z.shiftr (CA + off + q) 3 + 2147450880)) x7 (Z_to_bv 64 sk)
                   (Z_to_bv 64 (CA + off + q)) (Z_to_bv 64 q) (Z_to_bv 64 (CA + off + q)) x28
          /\ ps_scan bs blen (Z.to_nat blen) (off + 1) 0 = Some (off + q, sk) /\ 1 <= q /\ off + q < blen /\ 0 <= sk <= q)
      \/ (exists x6 x7 x13 x19 x20 x25 x28, ms' = L1 0x85a08 x6 x7 x13 x19 x20 x25 x28).

    Lemma loop1 : bytes_at bsegs m1 CA bs -> mem_inv bsegs m1 -> text_sh m1 CA blen ->
      forall (cnt : nat) (q sk : Z) (x6 x7 x19 x28 : word),
      Z.of_nat cnt = blen - (off + q) -> 1 <= q -> off + q < blen -> 0 <= sk <= q - 1 ->
      (forall r, ps_scan bs blen (Z.to_nat (blen - (off + q))) (off + q) sk = Some r ->
                 ps_scan bs blen (Z.to_nat blen) (off + 1) 0 = Some r) ->
      evt bsegs Q1 (L1 0x854a4 x6 x7 (Z_to_bv 64 sk) x19 (Z_to_bv 64 q) (Z_to_bv 64 (CA + off + q)) x28).
    Proof.
      intros BY1 MI1 TS1. induction cnt as [cnt IH] using lt_wf_ind.
      intros q sk x6 x7 x19 x28 Hcnt Hq Hoq Hsk K. lits. bandM. sepM. pose proof (bytes_at_bound _ _ _ _ BY1) as BYB. unfold L1, S6, S7.
      (nelim (text_read m1 CA bs (off + q) (Z_to_bv 64 (CA + off + q)) BY1 ltac:(lia) ltac:(lia) ltac:(unfold wa; f_equal; lia)) 4%nat; intros b Hb RD Hat).
      pose proof (byte_range b) as Rb.
      assert (STEP : ps_scan bs blen (Z.to_nat (blen - (off + q))) (off + q) sk =
                     (if at_ bs (off + q) =? 34 then Some (off + q, sk)
                      else if at_ bs (off + q) =? 92 then (if blen <=? off + q + 1 then None else ps_scan bs blen (Z.to_nat (blen - (off + q + 1))) (off + q + 2) (sk + 1))
                      else ps_scan bs blen (Z.to_nat (blen - (off + q + 1))) (off + q + 1) sk)).
      { replace (Z.to_nat (blen - (off + q))) with (S (Z.to_nat (blen - (off + q + 1)))) by lia. apply ps_scan_step. lia. }
      rewrite Hat in STEP.
      zstep. replace (CA + off + q) with (CA + off + q) by lia.
      zstep. zstep. pose proof (TS1 (CA + off + q) ltac:(lia)) as CK. asan_chk CK.
      zstep. zstep. if_cases Kbs; zify_cond Kbs.
      - (* [comment removed for export] *)
        ugd.
        zstep. zstep. zstep. zstep. if_cases Ke; zify_cond Ke.
        { apply evt_done. right. nexists 7%nat. reflexivity. }
        zstep. zstep. ugd.
        zstep. zstep. zstep. zstep. if_cases Ke2; zify_cond Ke2.
        + replace (CA + off + (q + 1 + 1)) with (CA + off + (q + 2)) by lia. replace (q + 1 + 1) with (q + 2) by lia.
          eapply (IH (cnt - 2)%nat ltac:(lia) (q + 2) (sk + 1)); [lia| lia| lia| lia|].
          intros r Hr. apply K. rewrite STEP, Kbs. change (92 =? 34) with false. change (92 =? 92) with true. cbv iota.
          replace (blen <=? off + q + 1) with false by (symmetry; apply Z.leb_gt; lia).
          eapply ps_scan_fuel; [| ]. { replace (off + q + 2) with (off + (q + 2)) by lia. exact Hr. } lia.
        + zstep. apply evt_done. right. nexists 7%nat. reflexivity.
      - zstep. if_cases Kq; zify_cond Kq.
        + (* [comment removed for export] *)
          apply evt_done. left. exists q, sk. eexists. eexists. split; [reflexivity|]. split; [| lia].
          apply K. rewrite STEP. rewrite (proj2 (Z.eqb_eq _ _) Kq). reflexivity.
        + (* [comment removed for export] *)
          zstep. ugd.
          zstep. zstep. zstep. zstep. if_cases Ke; zify_cond Ke.
          * replace (CA + off + (q + 1)) with (CA + off + (q + 1)) by lia.
            eapply (IH (cnt - 1)%nat ltac:(lia) (q + 1) sk); [lia| lia| lia| lia|].
            intros r Hr. apply K. rewrite STEP. rewrite (proj2 (Z.eqb_neq _ _) Kq), (proj2 (Z.eqb_neq _ _) Kbs).
            replace (off + (q + 1)) with (off + q + 1) in Hr by lia. exact Hr.
          * zstep. apply evt_done. right. nexists 7%nat. reflexivity.
    Qed.
  End Loop1.

  (* [comment removed for export] *)
  Lemma art_loop_fp : forall S na LB2 TRS1 B1 m3 mm mo1 g1,
    ART AI sp0 SPB LB2 LF TRS1 B1 m3 mo1 g1 -> In (S, na) LB2 ->
    munch [(S, S + na); (lo, SP + -144)] m3 mm -> wmono bsegs m3 mm -> ART AI sp0 SPB LB2 LF TRS1 B1 mm mo1 g1.
  Proof.
    intros S na LB2 TRS1 B1 m3 mm mo1 g1 HL HIn MU WM. lits. bandM. eapply (art_frame AI); [exact HL| exact MU| exact WM|].
    constructor; [| constructor; [| constructor]].
    - do 7 right. left. exists S, na. cbn. split; [exact HIn| lia].
    - right; left. cbn. lia.
  Qed.

  Lemma ppres_loop_fp : forall S na R LB2 TRS1 B1 m3 mm mo1 g1,
    ART AI sp0 SPB LB2 LF TRS1 B1 m3 mo1 g1 -> Permutation ((S, na) :: R) LB2 -> (forall b, In b LR -> In b R) ->
    munch [(S, S + na); (lo, SP + -144)] m3 mm -> wmono bsegs m3 mm -> ppres sp0 LR LF SP P m3 mm.
  Proof.
    intros S na R LB2 TRS1 B1 m3 mm mo1 g1 HL HP HLR MU WM a Ha nelH_; (nelim nelH_ 3%nat; intros Hc _ _). lits. bandM. sepM.
    (nelimp (art_block_range AI _ _ _ _ _ _ _ _ _ _ _ HL (perm_in_head _ _ _ HP)) 4%nat; intros R1 R2 R3 R4).
    try rewrite alloc_ceiling_eq in R4. unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in R1. bandM. sepM.
    split; [| apply WM]. apply MU. rewrite wa_unsigned by exact Ha. cbn.
    destruct Hc as [Hs|[Hi|[(A' & n' & Hin & Hr)|[(Fr & k & Hin & Hr)|Hsh]]]].
    - lia.
    - pose proof (aclient_image_lt a Hi). lia.
    - destruct (lheap_perm_apart AI _ _ _ _ _ _ _ _ _ _ _ _ HL HP A' n' (HLR _ Hin)) as [_ Dj].
      (nelimp (art_block_range AI _ _ _ _ _ _ _ _ _ _ _ HL ltac:(eapply Permutation_in; [exact HP| right; exact (HLR _ Hin)])) 4%nat; intros Q1' _ _ Q4). try rewrite alloc_ceiling_eq in Q4. lia.
    - (nelimp (art_frame_facts AI _ _ _ _ _ _ _ _ _ _ _ HL Hin) 8%nat; intros Hk GAL HF1 HF2 _ _ _ HD).
      try rewrite alloc_ceiling_eq in HF2. unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in HF1. bandM. sepM.
      assert (fsz k = 128 \/ fsz k = 256) by (destruct Hk as [-> | ->]; [left| right]; reflexivity).
      destruct Hr as [Hr|Hr].
      + destruct (HD S na (perm_in_head _ _ _ HP)) as [Dd|Dd]; lia.
      + (* [comment removed for export] *)
        pose proof (frame_sh_in_band Fr k a Hk GAL ltac:(lia) HF2 Hr) as AB.
        pose proof (band_addr_not_block AI _ _ _ _ _ _ _ _ _ S na a HL (perm_in_head _ _ _ HP) AB) as NB. unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in AB. bandM. sepM. clear - AB NB CEIL'. lia.
    - pose proof (stack_sh_in_band _ _ Hsh) as AB.
      pose proof (band_addr_not_block AI _ _ _ _ _ _ _ _ _ S na a HL (perm_in_head _ _ _ HP) AB) as NB. unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in AB. bandM. sepM. clear - AB NB CEIL'. lia.
  Qed.
End PSTR.


End CeilWrap.
(* [comment removed for export] *)
Ltac fix_lit_store :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) =>
      change (Z_to_le_bytes 8 z) with (le8 (Z_to_bv 64 z)); mem_after_store
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?z)) _) =>
      change (Z_to_le_bytes 4 z) with (le4 (Z_to_bv 64 z)); mem_after_store
  | _ => idtac
  end.
Ltac ugd := let G := fresh "G" in zstep; if_cases G; zify_cond G; try (exfalso; lia).
