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
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require UImg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require CJ_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require CJ_tree.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require CJ_phex4.
Module CJ_pstring_A.
(* [comment removed for export] *)
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ZBridge.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.UImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.CJ_tree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.CJ_phex4.CJ_pbuf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.CJ_phex4.CJ_parse_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.CJ_phex4.CJ_parse_lemmas.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Definition ps_frame (j0 : list byte) (s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra : word) : list cell :=
  [CB 8 j0; C8 (Z_to_bv 64 0xdc00); C8 (Z_to_bv 64 0xd800);
   C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Section PS.
  Variables (sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 rav : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (m2 : word -> option byte) (CA blen off e sk S P U : Z) (bs j0 : list byte).

  Definition F0 : nat := Z.to_nat blen.
  Definition nalloc : Z := e - off - sk + 1.
  Definition W2 : list (Z * Z) := [(S, S + nalloc)].
  Definition FRAME : list cell := ps_frame j0 s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 rav.

  (* [comment removed for export] *)
  Definition ps_ctx : Prop :=
    Z.of_nat (length bs) = blen
    /\ bytes_at usegs m2 CA bs
    /\ rw_cells usegs m2 (bv_unsigned sp + -128) FRAME
    /\ ps_scan bs blen F0 (off + 1) 0 = Some (e, sk)
    /\ 0 <= off /\ blen < 2^31
    /\ 0 < CA /\ CA + blen <= alloc_ceiling
    /\ 0 < S /\ S + nalloc <= alloc_ceiling
    /\ (S + nalloc <= CA \/ CA + blen <= S)
    /\ alloc_ceiling + 128 <= bv_unsigned sp /\ bv_unsigned sp < 2^64.
  Hypothesis CTX : ps_ctx.

  Definition dinv (i oc : Z) : Prop := oc + npairs bs blen F0 (off + 1) i <= i - (off + 1).

  (* [comment removed for export] *)
  Lemma ctx_scan : sk = npairs bs blen F0 (off + 1) e /\ off + 1 <= e < blen /\ at_ bs e = 34.
  Proof. destruct CTX as (_ & _ & _ & SC & _). pose proof (ps_scan_npairs _ _ _ _ _ _ _ SC). lia. Qed.

  Lemma ctx_arith : Z.of_nat (length bs) = blen /\ 0 <= off /\ off + 1 <= e < blen /\ blen < 2^31
    /\ 0 < CA /\ CA + blen <= alloc_ceiling /\ 0 < S /\ S + nalloc <= alloc_ceiling /\ (S + nalloc <= CA \/ CA + blen <= S)
    /\ alloc_ceiling + 128 <= bv_unsigned sp < 2^64 /\ 1 <= nalloc <= e - off + 1 /\ 0 <= sk.
  Proof.
    pose proof ctx_scan as (SK & E & _). destruct CTX as (L & _ & _ & SC & O & B & C1 & C2 & S1 & S2 & SEP & SP1 & SP2).
    pose proof (npairs_window bs blen F0 (off + 1) (off + 1) e ltac:(lia)) as [Wa Wb].
    rewrite (npairs_le bs blen F0 (off + 1) (off + 1)) in Wa, Wb by lia. pose proof (bflag_range bs (off + 1)).
    unfold nalloc in *. repeat split; try assumption; lia.
  Qed.

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
    intros i oc L DI Hi HL. unfold dinv, nalloc in *. pose proof ctx_scan as (SK & E & _).
    pose proof (npairs_window bs blen F0 (off + 1) i e ltac:(lia)) as [Wa Wb]. pose proof (bflag_range bs i). lia.
  Qed.

  Lemma dinv_end : forall i oc, dinv i oc -> e <= i <= e + 1 -> oc + 1 <= nalloc.
  Proof.
    intros i oc DI Hi. unfold dinv, nalloc in *. pose proof ctx_scan as (SK & E & _). destruct CTX as (_ & _ & _ & SC & _).
    rewrite (ps_scan_npairs_end _ _ _ _ _ _ _ i SC) in DI by lia. lia.
  Qed.

  (* [comment removed for export] *)
  Definition LST (pc : Z) (x1 x5 x6 x7 x9 x10 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) (i oc : Z) (mm : word -> option byte) : machine_state :=
    MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp x5 x6 x7 (Z_to_bv 64 (S + oc)) x9 x10 (Z_to_bv 64 P) (Z_to_bv 64 U)
            x13 x14 x15 x16 x17
            (Z_to_bv 64 (CA + i)) (Z_to_bv 64 (CA + e)) (Z_to_bv 64 (CA + e)) (Z_to_bv 64 P) (Z_to_bv 64 U)
            (Z_to_bv 64 2) (Z_to_bv 64 92) (Z_to_bv 64 83) (Z_to_bv 64 JT) (Z_to_bv 64 S) x28 x29 x30 x31)
       F (Z_to_bv 64 pc) fc None mm (seg_rom usegs).

  (* [comment removed for export] *)
  Definition LSTc (pc : Z) (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) (i oc : Z) (mm : word -> option byte) : machine_state :=
    MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp x5 x6 x7 (Z_to_bv 64 (S + oc)) x9 x10 x11 x12
            x13 x14 x15 x16 x17
            (Z_to_bv 64 (CA + i)) (Z_to_bv 64 (CA + e)) (Z_to_bv 64 (CA + e)) (Z_to_bv 64 P) (Z_to_bv 64 U)
            (Z_to_bv 64 2) (Z_to_bv 64 92) (Z_to_bv 64 83) (Z_to_bv 64 JT) (Z_to_bv 64 S) x28 x29 x30 x31)
       F (Z_to_bv 64 pc) fc None mm (seg_rom usegs).

  (* [comment removed for export] *)
  Definition lmem (mm : word -> option byte) (buf : list byte) : Prop :=
    u8arr usegs mm S buf /\ length buf = Z.to_nat nalloc /\ munch W2 m2 mm /\ wmono usegs m2 mm /\ mem_inv usegs mm.

  Definition KPOST : machine_state -> Prop := fun ms' =>
    exists (mm : word -> option byte) (buf : list byte) (x1 x5 x6 x7 x9 x10 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) (i oc : Z),
      lmem mm buf /\ off + 1 <= i <= e + 1 /\ 0 <= oc /\ oc + 1 <= nalloc
      /\ ( ms' = LST 0x14fb0 x1 x5 x6 x7 x9 x10 (Z_to_bv 64 (S + oc)) x14 x15 x16 x17 x28 x29 x30 x31 i oc mm   (* [comment removed for export] *)
           \/ ms' = LSTc 0x14fe0 x1 x5 x6 x7 x9 x10 (Z_to_bv 64 P) x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 i oc mm ).   (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition LOOPK (k : nat) : Prop :=
    forall (i oc : Z) (mm : word -> option byte) (buf : list byte) (x1 x5 x6 x7 x9 x10 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
      e - i <= Z.of_nat k -> off + 1 <= i < e -> dinv i oc -> 0 <= oc -> lmem mm buf ->
      evt usegs KPOST (LST 0x14d84 x1 x5 x6 x7 x9 x10 x13 x14 x15 x16 x17 x28 x29 x30 x31 i oc mm).

  (* [comment removed for export] *)
  Lemma lmem_facts : forall mm buf, lmem mm buf ->
    bytes_at usegs mm CA bs /\ rw_cells usegs mm (bv_unsigned sp + -128) FRAME.
  Proof.
    intros mm buf (BUF & BL & MU & WM & MI). pose proof ctx_arith as A. destruct CTX as (L & BY2 & FR2 & _).
    try rewrite alloc_ceiling_eq in A. unfold W2 in MU. split.
    - eapply bytes_at_transport; [exact BY2| exact MU|]. cbn. lia.
    - eapply rw_cells_transport; [exact FR2| exact MU| exact WM|]. cbn. lia.
  Qed.

  Ltac pre := pose proof ctx_arith as ARITH; try rewrite alloc_ceiling_eq in ARITH; unfold W2, nalloc in *.

  (* [comment removed for export] *)
  Lemma exit_ok : forall i oc mm buf x1 x5 x6 x7 x9 x10 x14 x15 x16 x17 x28 x29 x30 x31,
    lmem mm buf -> off + 1 <= i <= e + 1 -> 0 <= oc -> oc + 1 <= nalloc ->
    evt usegs KPOST (LST 0x14fb0 x1 x5 x6 x7 x9 x10 (Z_to_bv 64 (S + oc)) x14 x15 x16 x17 x28 x29 x30 x31 i oc mm).
  Proof. intros. apply evt_done. unfold KPOST. exists mm, buf, x1, x5, x6, x7, x9, x10, x10, x10. do 10 eexists. repeat (split; [eassumption|]). left; reflexivity. Qed.

  Lemma exit_fail : forall i oc mm buf x1 x5 x6 x7 x9 x10 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31,
    lmem mm buf -> off + 1 <= i <= e + 1 -> 0 <= oc -> oc + 1 <= nalloc ->
    evt usegs KPOST (LSTc 0x14fe0 x1 x5 x6 x7 x9 x10 (Z_to_bv 64 P) x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 i oc mm).
  Proof. intros. apply evt_done. unfold KPOST. do 20 eexists. repeat (split; [eassumption|]). right; reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma exit_fail' : forall i oc mm buf x1 x5 x6 x7 x9 x10 x13 x14 x15 x16 x17 x28 x29 x30 x31,
    lmem mm buf -> off + 1 <= i <= e + 1 -> 0 <= oc -> oc + 1 <= nalloc ->
    evt usegs KPOST (LST 0x14fe0 x1 x5 x6 x7 x9 x10 x13 x14 x15 x16 x17 x28 x29 x30 x31 i oc mm).
  Proof. intros. apply (exit_fail i oc mm buf); assumption. Qed.

  Section Body.
    Variable k : nat.
    Hypothesis IH : forall k', (k' < k)%nat -> LOOPK k'.

    (* [comment removed for export] *)
    Lemma go_head : forall i oc mm buf x1 x5 x6 x7 x9 x10 x13 x14 x15 x16 x17 x28 x29 x30 x31,
      e - i < Z.of_nat k -> off + 1 <= i < e -> dinv i oc -> 0 <= oc -> lmem mm buf ->
      evt usegs KPOST (LST 0x14d84 x1 x5 x6 x7 x9 x10 x13 x14 x15 x16 x17 x28 x29 x30 x31 i oc mm).
    Proof.
      intros. destruct k as [|k']; [lia|]. eapply (IH k'); [lia| lia| assumption| assumption| assumption| eassumption].
    Qed.

    (* [comment removed for export] *)
    Lemma advance_tail : forall i oc oc' sl mm buf x1 x5 x6 x7 x9 x14 x15 x16 x17 x28 x29 x30 x31,
      e - i <= Z.of_nat k -> off + 1 <= i -> i + sl <= e + 1 -> 1 <= sl <= 12 -> 0 <= oc' ->
      dinv (i + sl) oc' -> lmem mm buf ->
      evt usegs KPOST (LST 0x14e8c x1 x5 x6 x7 x9 (Z_to_bv 64 sl) (Z_to_bv 64 (S + oc')) x14 x15 x16 x17 x28 x29 x30 x31 i oc mm).
    Proof.
      intros until x31. intros Hk Hi Hsl Hsl1 Hoc DI LM. pose proof LM as (BUF & BL & MU & WM & MI). pre. unfold LST.
      zstep. rewrite zb_lxor_ones by lia. zstep. if_cases Kw; zify_cond Kw; [exfalso; lia|].
      zstep. zstep.
      replace (CA + i + sl) with (CA + (i + sl)) by lia.
      zstep. if_cases Kt; zify_cond Kt.
      - eapply go_head; [lia| lia| exact DI| exact Hoc| exact LM].
      - zstep. eapply exit_ok; [exact LM| lia| lia| apply (dinv_end (i + sl) oc' DI); lia].
    Qed.

    (* [comment removed for export] *)
    Lemma store_tail : forall i oc (c : Z) mm buf x1 x5 x6 x7 x9 x14 x15 x16 x17 x28 x29 x30 x31,
      0 <= c < 256 ->
      e - i <= Z.of_nat k -> off + 1 <= i -> i + 2 <= e + 1 -> 0 <= oc -> oc + 1 <= nalloc ->
      dinv (i + 2) (oc + 1) -> lmem mm buf ->
      evt usegs KPOST (LST 0x14e84 x1 x5 x6 x7 x9 (Z_to_bv 64 c) (Z_to_bv 64 (S + oc + 1)) x14 x15 x16 x17 x28 x29 x30 x31 i oc mm).
    Proof.
      intros until x31. intros Hc Hk Hi Hie Hoc ROOM DI LM. pose proof LM as (BUF & BL & MU & WM & MI). pre. unfold LST.
      pose proof (u8arr_store_ok usegs _ _ _ oc (Z_to_bv 64 (S + oc)) BUF ltac:(lia) eq_refl) as SOK.
      zstep. rewrite le1_lit.
      pose proof (u8arr_write usegs _ _ _ oc (Z_to_bv 8 c) BUF ltac:(lia)) as BUF'.
      clear BUF. store_done. rename BUF' into BUF.
      zstep. replace (S + oc + 1) with (S + (oc + 1)) by lia.
      eapply advance_tail; [lia| lia| lia| lia| lia| exact DI|].
      split; [exact BUF|]. split; [rewrite upd_length; exact BL|]. split; [exact MU|]. split; [exact WM| exact MI].
    Qed.

    (* [comment removed for export] *)
    Definition ESCPCS : list Z := [0x14db4; 0x14de0; 0x14df0; 0x14e58; 0x14e68; 0x14e78].

    Lemma esc_simple : forall pc i oc (c : Z) mm buf x1 x5 x6 x7 x9 x10 x13 x15 x16 x17 x28 x29 x30 x31,
      In pc ESCPCS -> 0 <= c < 256 ->
      e - i <= Z.of_nat k -> off + 1 <= i -> i + 2 <= e + 1 -> 0 <= oc -> oc + 1 <= nalloc ->
      dinv (i + 2) (oc + 1) -> lmem mm buf ->
      evt usegs KPOST (LST pc x1 x5 x6 x7 x9 x10 x13 (Z_to_bv 64 c) x15 x16 x17 x28 x29 x30 x31 i oc mm).
    Proof.
      intros until x31. intros HIn Hc Hk Hi Hie Hoc ROOM DI LM. pose proof LM as (BUF & BL & MU & WM & MI). pre. unfold LST.
      destruct HIn as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]].
      - (* [comment removed for export] *)
        zstep. zstep. if_cases Kg; zify_cond Kg; [exfalso; lia|].
        pose proof (u8arr_store_ok usegs _ _ _ oc (Z_to_bv 64 (S + oc)) BUF ltac:(lia) eq_refl) as SOK.
        zstep. rewrite le1_lit.
        pose proof (u8arr_write usegs _ _ _ oc (Z_to_bv 8 c) BUF ltac:(lia)) as BUF'.
        clear BUF. store_done. rename BUF' into BUF.
        zstep. zstep. replace (S + oc + 1) with (S + (oc + 1)) by lia.
        eapply advance_tail; [lia| lia| lia| lia| lia| exact DI|].
        split; [exact BUF|]. split; [rewrite upd_length; exact BL|]. split; [exact MU|]. split; [exact WM| exact MI].
      - zstep. zstep. if_cases Kg; zify_cond Kg; [exfalso; lia|]. zstep. zstep. eapply store_tail; [lia| lia| lia| lia| lia| unfold nalloc; lia| exact DI| exact LM].
      - zstep. zstep. if_cases Kg; zify_cond Kg; [exfalso; lia|]. zstep. zstep. eapply store_tail; [lia| lia| lia| lia| lia| unfold nalloc; lia| exact DI| exact LM].
      - zstep. zstep. if_cases Kg; zify_cond Kg; [exfalso; lia|]. zstep. zstep. eapply store_tail; [lia| lia| lia| lia| lia| unfold nalloc; lia| exact DI| exact LM].
      - zstep. zstep. if_cases Kg; zify_cond Kg; [exfalso; lia|]. zstep. zstep. eapply store_tail; [lia| lia| lia| lia| lia| unfold nalloc; lia| exact DI| exact LM].
      - zstep. zstep. if_cases Kg; zify_cond Kg; [exfalso; lia|]. zstep. eapply store_tail; [lia| lia| lia| lia| lia| unfold nalloc; lia| exact DI| exact LM].
    Qed.

    (* [comment removed for export] *)
    Ltac cont_byte BUF idx :=
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        let Kg := fresh "Kg" in
        zstep; zstep; if_cases Kg; zify_cond Kg; [exfalso; lia|]; clear Kg;
        zstep; zstep; zstep; zstep;
        lazymatch goal with |- context [Z_to_bv 64 (S + ?o + ?d)] => replace (S + o + d) with (S + idx) by lia | _ => idtac end;
        pose proof (u8arr_store_ok usegs mm S _ idx (Z_to_bv 64 (S + idx)) BUF ltac:(rewrite ?upd_length; lia) eq_refl) as SOK;
        zstep; rewrite le1_lit;
        let BUF' := fresh "BUF" in
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ [Z_to_bv 8 ?v]) _) =>
          pose proof (u8arr_write usegs mm S _ idx (Z_to_bv 8 v) BUF ltac:(rewrite ?upd_length; lia)) as BUF' end;
        clear BUF; store_done; try clear SOK; rename BUF' into BUF;
        zstep; zstep; zstep
      end.

    (* [comment removed for export] *)
    Lemma newptr_tail : forall i oc (len sl : Z) mm buf x1 x5 x6 x7 x9 x14 x15 x16 x17 x28 x29 x30 x31,
      e - i <= Z.of_nat k -> off + 1 <= i -> i + sl <= e + 1 -> 1 <= sl <= 12 -> 1 <= len -> 0 <= oc -> oc + len <= nalloc ->
      dinv (i + sl) (oc + len) -> lmem mm buf ->
      evt usegs KPOST (LST 0x14f78 x1 x5 x6 x7 x9 (Z_to_bv 64 sl) (Z_to_bv 64 len) x14 x15 x16 x17 x28 x29 x30 x31 i oc mm).
    Proof.
      intros until x31. intros Hk Hi Hsl Hsl1 Hlen Hoc ROOM DI LM. pose proof LM as (BUF & BL & MU & WM & MI). pre. unfold LST.
      zstep. zstep. if_cases K1; zify_cond K1; [exfalso; lia|]. zstep. if_cases K2; zify_cond K2; [| exfalso; lia].
      replace (len + (S + oc)) with (S + (oc + len)) by lia.
      eapply advance_tail; [lia| lia| lia| lia| lia| exact DI| exact LM].
    Qed.

    (* [comment removed for export] *)
    Lemma encode_tail : forall i oc (len sl cp mark : Z) mm buf x1 x5 x6 x7 x15 x16 x17 x28 x29 x30 x31,
      e - i <= Z.of_nat k -> off + 1 <= i -> i + sl <= e + 1 -> 1 <= sl <= 12 -> 2 <= len <= 4 -> 0 <= cp -> 0 <= mark < 256 -> 0 <= oc -> oc + len <= nalloc ->
      dinv (i + sl) (oc + len) -> lmem mm buf ->
      evt usegs KPOST (LST 0x14f28 x1 x5 x6 x7 (Z_to_bv 64 cp) (Z_to_bv 64 sl) (Z_to_bv 64 len) (Z_to_bv 64 mark) x15 x16 x17 x28 x29 x30 x31 i oc mm).
    Proof.
      intros until x31. intros Hk Hi Hsl Hsl1 Hlen Hcp Hmk Hoc ROOM DI LM. pose proof LM as (BUF & BL & MU & WM & MI). pre. unfold LST.
      (* [comment removed for export] *)
      Ltac first_byte BUF oc len DI :=
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
          zstep;
          pose proof (u8arr_store_ok usegs mm S _ oc (Z_to_bv 64 (S + oc)) BUF ltac:(rewrite ?upd_length; lia) eq_refl) as SOK;
          zstep; rewrite le1_lit;
          let BUF' := fresh "BUF" in
          lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ [Z_to_bv 8 ?v]) _) =>
            pose proof (u8arr_write usegs mm S _ oc (Z_to_bv 8 v) BUF ltac:(rewrite ?upd_length; lia)) as BUF' end;
          clear BUF; store_done; try clear SOK; rename BUF' into BUF;
          zstep;
          eapply (newptr_tail _ oc len); [lia| lia| lia| lia| lia| lia| unfold nalloc; lia| exact DI|]
        end.
      assert (HL : len = 2 \/ len = 3 \/ len = 4) by lia.
      destruct HL as [-> | [-> | ->]]; zstep; (if_cases K0; zify_cond K0; [exfalso; lia|]); zstep; zstep; rewrite zb_lxor_ones by lia.
      - cont_byte BUF (oc + 1). if_cases KL; zify_cond KL; [exfalso; exact (KL eq_refl)|]. clear KL.
        first_byte BUF oc 2 DI.
        split; [exact BUF|]. split; [rewrite !upd_length; exact BL|]. split; [exact MU|]. split; [exact WM| exact MI].
      - cont_byte BUF (oc + 2). if_cases KL; zify_cond KL; [| exfalso; lia]. clear KL.
        cont_byte BUF (oc + 1). if_cases KL; zify_cond KL; [exfalso; exact (KL eq_refl)|]. clear KL.
        first_byte BUF oc 3 DI.
        split; [exact BUF|]. split; [rewrite !upd_length; exact BL|]. split; [exact MU|]. split; [exact WM| exact MI].
      - cont_byte BUF (oc + 3). if_cases KL; zify_cond KL; [| exfalso; lia]. clear KL.
        cont_byte BUF (oc + 2). if_cases KL; zify_cond KL; [| exfalso; lia]. clear KL.
        cont_byte BUF (oc + 1). if_cases KL; zify_cond KL; [exfalso; exact (KL eq_refl)|]. clear KL.
        first_byte BUF oc 4 DI.
        split; [exact BUF|]. split; [rewrite !upd_length; exact BL|]. split; [exact MU|]. split; [exact WM| exact MI].
    Qed.

    (* [comment removed for export] *)
    Lemma one_byte_tail : forall i oc (cp : Z) mm buf x1 x5 x6 x7 x10 x13 x14 x15 x16 x17 x28 x29 x30 x31,
      e - i <= Z.of_nat k -> off + 1 <= i -> i + 6 <= e + 1 -> 0 <= cp -> 0 <= oc -> oc + 1 <= nalloc ->
      dinv (i + 6) (oc + 1) -> lmem mm buf ->
      evt usegs KPOST (LST 0x14f68 x1 x5 x6 x7 (Z_to_bv 64 cp) x10 x13 x14 x15 x16 x17 x28 x29 x30 x31 i oc mm).
    Proof.
      intros until x31. intros Hk Hi Hsl Hcp Hoc ROOM DI LM. pose proof LM as (BUF & BL & MU & WM & MI). pre. unfold LST.
      zstep. if_cases K0; zify_cond K0; [exfalso; lia|].
      pose proof (u8arr_store_ok usegs _ _ _ oc (Z_to_bv 64 (S + oc)) BUF ltac:(lia) eq_refl) as SOK.
      zstep. rewrite le1_lit.
      pose proof (u8arr_write usegs _ _ _ oc (Z_to_bv 8 cp) BUF ltac:(lia)) as BUF'.
      clear BUF. store_done. try clear SOK. rename BUF' into BUF.
      zstep. zstep.
      eapply (newptr_tail _ oc 1 6); [lia| lia| lia| lia| lia| lia| unfold nalloc; lia| exact DI|].
      split; [exact BUF|]. split; [rewrite upd_length; exact BL|]. split; [exact MU|]. split; [exact WM| exact MI].
    Qed.
  End Body.
End PS.


End CeilWrap.
End CJ_pstring_A.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require NElim.
Module CJ_pstring_B.
(* [comment removed for export] *)
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ZBridge.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.UImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.CJ_tree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.CJ_phex4.CJ_pbuf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.CJ_phex4.CJ_parse_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.CJ_phex4.CJ_parse_lemmas OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.CJ_phex4 CJ_pstring_A.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Lemma jt_cases : forall c,
  ((c = 34 \/ c = 47 \/ c = 92) /\ jt_off c = 0x4794)
  \/ (c = 98 /\ jt_off c = 0x47c0) \/ (c = 102 /\ jt_off c = 0x47d0) \/ (c = 117 /\ jt_off c = 0x47e0)
  \/ (c = 114 /\ jt_off c = 0x4838) \/ (c = 110 /\ jt_off c = 0x4848) \/ (c = 116 /\ jt_off c = 0x4858)
  \/ jt_off c = 0x49c0.
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
  Variables (sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 rav : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (m2 : word -> option byte) (CA blen off e sk S P U : Z) (bs j0 : list byte).
  Hypothesis CTX : ps_ctx sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 rav m2 CA blen off e sk S bs j0.

  Notation LSTx := (LST sp gp tp F fc CA e S P U).
  Notation LSTcx := (LSTc sp gp tp F fc CA e S P U).
  Notation KP := (KPOST sp gp tp F fc m2 CA off e sk S P U).
  Notation LM := (lmem m2 off e sk S).
  Notation DINV := (dinv blen off bs).
  Notation NA := (nalloc off e sk).
  Notation L z := (Z_to_bv 64 z) (only parsing).
  Notation LU := (Z_to_bv 64 U).
  Notation LP := (Z_to_bv 64 P).

  Ltac ctx := pose proof (ctx_arith _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CTX) as ARITH; try rewrite alloc_ceiling_eq in ARITH.
  Ltac lm LMm mm buf :=
    pose proof (lmem_facts _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CTX mm buf LMm) as [BY FR]; unfold FRAME, ps_frame in FR;
    (nelimp LMm 5%nat; intros BUF BL MU WM MI).
  Ltac ml := Z.div_mod_to_equations; lia.

  Section Body.
    Variable k : nat.
    Hypothesis IH : forall k', (k' < k)%nat -> LOOPK sp gp tp F fc m2 CA blen off e sk S P U bs k'.

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
      Proof. ctx. eapply (dinv_room _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CTX i oc 4 DI); lia. Qed.

      Lemma dinv_u : forall c p, 6 <= c -> p + (c + 1) / 2 <= c -> DINV (i + c) (oc + p).
      Proof. intros c p Hc Hp. eapply dinv_step; [exact DI| lia| lia| rewrite bflag_i; exact Hp]. Qed.

      Ltac preU LMm mm buf := ctx; lm LMm mm buf; pose proof room4 as ROOM; unfold W2, nalloc in *; unfold LST, LSTc.

      Ltac fail_exit LMm := first [eapply exit_fail | eapply exit_fail']; [exact LMm| lia| lia| unfold nalloc; lia].

      Ltac nonneg := repeat first [ apply Z.add_nonneg_nonneg
                                  | (apply (proj2 (Z.lor_nonneg _ _)); split)
                                  | apply (proj2 (Z.shiftr_nonneg _ _))
                                  | apply (proj2 (Z.shiftl_nonneg _ _))
                                  | (apply (proj2 (Z.land_nonneg _ _)); first [left; lia | right; lia])
                                  | (apply Z_mod_nonneg_nonneg; [|lia])
                                  | lia ].
      Ltac lmem_now BL := split; [eassumption|]; split; [exact BL|]; split; [assumption|]; split; assumption.

      (* [comment removed for export] *)
      Lemma L_cls : forall (FC : Z) mm buf x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31,
        0 <= FC < 2^16 -> LM mm buf ->
        evt usegs KP (LSTcx 0x14e18 x1 x5 x6 x7 x9 (L FC) x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 i oc mm).
      Proof.
        intros until x31. intros HFC LMm. preU LMm mm buf.
        zstep. zstep. rewrite (land_hi10 FC) by lia. zstep. zstep. if_cases Ksur; zify_cond Ksur.
        - (* [comment removed for export] *)
          zstep. zstep. if_cases Kg1; zify_cond Kg1; [exfalso; lia|].
          zstep. zstep. zstep. zstep. zstep. rewrite (bv_lts_small (CA + e - (CA + i + 6)) 6) by lia.
          if_cases Kl; zify_cond Kl; [fail_exit LMm|].
          (nelim (text_read mm CA bs (i + 6) (Z_to_bv 64 (CA + i + 6)) BY ltac:(lia) ltac:(lia) ltac:(unfold wa; f_equal; lia)) 4%nat; intros c6 Hc6 RD6 _).
          zstep. zstep. if_cases K6; zify_cond K6; [fail_exit LMm|].
          zstep. zstep. if_cases Kg2; zify_cond Kg2; [exfalso; lia|].
          (nelim (text_read mm CA bs (i + 7) (Z_to_bv 64 (CA + i + 7)) BY ltac:(lia) ltac:(lia) ltac:(unfold wa; f_equal; lia)) 4%nat; intros c7 Hc7 RD7 _).
          zstep. zstep. zstep. if_cases K7; zify_cond K7; [fail_exit LMm|].
          zstep. zstep. if_cases Kg3; zify_cond Kg3; [exfalso; lia|].
          zstep. zstep.
          pose proof (bytes_at_window mm CA bs (i + 8) 4 BY ltac:(lia) ltac:(lia)) as B4.
          call hex4_spec.
          1:{ exact B4. } 1:{ apply firstn_skipn_length. lia. } 1:{ exact MI. } 1:{ f_equal. lia. }
          clear B4. intros.
          (* [comment removed for export] *)
          zstep. zstep. zstep. zstep. zstep. if_cases Kr; zify_cond Kr.
          { eapply exit_fail; [lmem_now BL| lia| lia| unfold nalloc; lia]. }
          (* [comment removed for export] *)
          do 10 zstep.
          eapply encode_tail; [exact CTX| exact IH| lia| lia| lia| lia| lia| nonneg| lia| lia| unfold nalloc; lia| apply dinv_u; [lia| cbv; discriminate] | lmem_now BL].
        - zstep. zstep. zstep. if_cases Klow; zify_cond Klow; [fail_exit LMm|].
          zstep. zstep. zstep. if_cases K1; zify_cond K1.
          + (* [comment removed for export] *)
            eapply one_byte_tail; [exact CTX| exact IH| lia| lia| lia| lia| lia| unfold nalloc; lia| apply dinv_u; [lia| cbv; discriminate]| exact LMm].
          + zstep. rewrite (srliw_small FC 11) by lia. zstep. zstep. if_cases K2; zify_cond K2.
            * (* [comment removed for export] *)
              zstep. rewrite (srliw_small FC 16) by lia. zstep. if_cases K3; zify_cond K3; [exfalso; ml|].
              zstep. zstep. zstep.
              eapply encode_tail; [exact CTX| exact IH| lia| lia| lia| lia| lia| lia| lia| lia| unfold nalloc; lia| apply dinv_u; [lia| cbv; discriminate]| exact LMm].
            * zstep. zstep. zstep.
              eapply encode_tail; [exact CTX| exact IH| lia| lia| lia| lia| lia| lia| lia| lia| unfold nalloc; lia| apply dinv_u; [lia| cbv; discriminate]| exact LMm].
      Qed.

      (* [comment removed for export] *)
      Lemma esc_u : forall mm buf x1 x5 x6 x7 x9 x13 x14 x15 x16 x17 x28 x29 x30 x31, LM mm buf ->
        evt usegs KP (LSTx 0x14e00 x1 x5 x6 x7 x9 (Z_to_bv 64 (CA + e - (CA + i))) x13 x14 x15 x16 x17 x28 x29 x30 x31 i oc mm).
      Proof.
        intros until x31. intros LMm. preU LMm mm buf.
        zstep. zstep. if_cases Kl; zify_cond Kl; [exfalso; lia|].
        zstep. zstep. if_cases Kg; zify_cond Kg; [exfalso; lia|].
        zstep. zstep.
        pose proof (bytes_at_window mm CA bs (i + 2) 4 BY ltac:(lia) ltac:(lia)) as B4.
        call hex4_spec.
        1:{ exact B4. } 1:{ apply firstn_skipn_length. lia. } 1:{ exact MI. } 1:{ f_equal. lia. }
        clear B4. intros.
        eapply L_cls; [lia| lmem_now BL].
      Qed.
    End U.

    (* [comment removed for export] *)
    (* [comment removed for export] *)
    Lemma head_k : LOOPK sp gp tp F fc m2 CA blen off e sk S P U bs k.
    Proof.
      unfold LOOPK. intros until x31. intros Hk Hi DI Hoc LMm. ctx. lm LMm mm buf. unfold W2, nalloc in *. unfold LST.
      pose proof (dinv_room _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CTX i oc 1 DI ltac:(lia) ltac:(lia)) as ROOM1. unfold nalloc in ROOM1.
      (nelim (text_read mm CA bs i (Z_to_bv 64 (CA + i)) BY ltac:(lia) ltac:(lia) eq_refl) 4%nat; intros b Hb RD Hat).
      pose proof (byte_range b) as Rb.
      zstep. zstep. if_cases Kbs; zify_cond Kbs.
      - (* [comment removed for export] *)
        zstep. zstep. if_cases Kg; zify_cond Kg; [exfalso; lia|]. zstep.
        pose proof (u8arr_store_ok usegs _ _ _ oc (Z_to_bv 64 (S + oc)) BUF ltac:(lia) eq_refl) as SOK.
        zstep. rewrite le1_lit.
        pose proof (u8arr_write usegs _ _ _ oc (Z_to_bv 8 (bv_unsigned b)) BUF ltac:(lia)) as BUF'.
        clear BUF. store_done. try clear SOK. rename BUF' into BUF.
        assert (DI' : DINV (i + 1) (oc + 1)).
        { eapply dinv_step; [exact DI| lia| lia|]. unfold bflag. rewrite Hat. replace (bv_unsigned b =? 92) with false by (symmetry; apply Z.eqb_neq; exact Kbs). reflexivity. }
        zstep.
        replace (S + oc + 1) with (S + (oc + 1)) by lia. replace (CA + i + 1) with (CA + (i + 1)) by lia.
        zstep. if_cases Kt; zify_cond Kt.
        + eapply go_head; [exact IH| lia| lia| exact DI'| lia|].
          split; [exact BUF|]. split; [rewrite upd_length; exact BL|]. split; [exact MU|]. split; [exact WM| exact MI].
        + zstep. eapply exit_ok; [| lia| lia| eapply (dinv_end _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CTX); [exact DI'| lia]].
          split; [exact BUF|]. split; [rewrite upd_length; exact BL|]. split; [exact MU|]. split; [exact WM| exact MI].
      - (* [comment removed for export] *)
        assert (DI2 : DINV (i + 2) (oc + 1)).
        { eapply dinv_step; [exact DI| lia| lia|]. unfold bflag. rewrite Hat, Kbs. cbv. discriminate. }
        zstep. zstep. if_cases Kp.
        { (* [comment removed for export] *)
          eapply exit_fail'; [exact LMm| lia| lia| unfold nalloc; lia]. }
        clear Kp.
        (nelim (text_read mm CA bs (i + 1) (Z_to_bv 64 (CA + i + 1)) BY ltac:(lia) ltac:(lia) ltac:(unfold wa; f_equal; lia)) 4%nat; intros c Hc RDc Hatc).
        pose proof (byte_range c) as Rc.
        zstep. zstep. zstep. if_cases Kr; zify_cond Kr.
        { eapply exit_fail'; [exact LMm| lia| lia| unfold nalloc; lia]. }
        assert (Hcr : 34 <= bv_unsigned c <= 117) by (clear -Rc Kr; ml).
        zstep. zstep.
        pose proof (jt_read' mm (bv_unsigned c) MI Hcr) as RDj.
        zstep. zstep. zstep.
        destruct (jt_cases (bv_unsigned c)) as [[Hcls E]|[[Hcls E]|[[Hcls E]|[[Hcls E]|[[Hcls E]|[[Hcls E]|[[Hcls E]|E]]]]]]];
          rewrite (jt_pc (bv_unsigned c) _ Hcr ltac:(rewrite E; reflexivity)).
        + eapply esc_simple; [exact CTX| exact IH| cbn; auto 10| lia| lia| lia| lia| lia| unfold nalloc; lia| exact DI2| exact LMm].
        + eapply esc_simple; [exact CTX| exact IH| cbn; auto 10| lia| lia| lia| lia| lia| unfold nalloc; lia| exact DI2| exact LMm].
        + eapply esc_simple; [exact CTX| exact IH| cbn; auto 10| lia| lia| lia| lia| lia| unfold nalloc; lia| exact DI2| exact LMm].
        + (* [comment removed for export] *) destruct (Z_lt_le_dec (e - i) 6) as [SHORT|LONG].
          * (* [comment removed for export] *)
            unfold JT. zstep. zstep. if_cases Kl; zify_cond Kl; [| exfalso; lia].
            eapply exit_fail; [exact LMm| lia| lia| unfold nalloc; lia].
          * eapply esc_u; [lia| lia| lia| rewrite Hat, Kbs; reflexivity| exact DI| lia| exact LMm].
        + eapply esc_simple; [exact CTX| exact IH| cbn; auto 10| lia| lia| lia| lia| lia| unfold nalloc; lia| exact DI2| exact LMm].
        + eapply esc_simple; [exact CTX| exact IH| cbn; auto 10| lia| lia| lia| lia| lia| unfold nalloc; lia| exact DI2| exact LMm].
        + eapply esc_simple; [exact CTX| exact IH| cbn; auto 10| lia| lia| lia| lia| lia| unfold nalloc; lia| exact DI2| exact LMm].
        + (* [comment removed for export] *) eapply exit_fail'; [exact LMm| lia| lia| unfold nalloc; lia].
    Qed.
  End Body.

  Theorem dec_loop : forall k, LOOPK sp gp tp F fc m2 CA blen off e sk S P U bs k.
  Proof. intros k. induction k as [k IH] using lt_wf_ind. apply head_k. exact IH. Qed.
End PS.


End CeilWrap.
End CJ_pstring_B.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import ShapeAlg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Tac Bytes SCPS ZBridge.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require Import UImg CJ_iface CJ_tree.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require CJ_phex4.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.CJ_phex4.CJ_pbuf.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require Import CJ_utraps.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require CJ_phex4.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.CJ_phex4.CJ_parse_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require CJ_phex4.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.CJ_phex4.CJ_parse_lemmas.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require Import CJ_phex4.
Import CJ_pstring_A.
Import CJ_pstring_B.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.
(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import LiaSplit.
Local Ltac lia ::= lia_cj.
Local Ltac flia ::= flia_cj.
Local Ltac simpl_sizes ::= simpl_sizes_cj.
Local Ltac simpl_arr_sizes ::= simpl_arr_sizes_cj.


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

Section PSTR.
  Variable HI : cj_heap_iface.
  (* [comment removed for export] *)
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (m : word -> option byte) (SPB : Z) (LB LR : list cblock) (U P CA blen off depth : Z) (bs : list byte) (D n lo : Z).
  Variables (nx : Z) (pv : word) (ch ty : Z) (p1 : word) (vs : Z) (vi p2 vd : word) (ky : Z).
  Hypothesis HPU : Permutation ((U, 64) :: LR) LB.
  Hypothesis HDn : In (D, n) LR /\ D <= CA /\ CA + blen <= D + n.
  Hypothesis LEN : Z.of_nat (length bs) = blen.
  Hypothesis BLEN : blen < 2^31.
  Hypothesis CEIL : alloc_ceiling <= lo.
  Hypothesis LO : lo <= bv_unsigned sp - PARSE_STRING_STACK.
  Hypothesis PP : bv_unsigned sp <= P /\ P + 56 <= SPB /\ SPB < 2^62 /\ P mod 8 = 0.
  Hypothesis OFF : 0 <= off < blen.
  Hypothesis TP : tp = wz PTP.
  Hypothesis URNG : cblock_range U 64.
  Hypothesis DRNG : cblock_range D n.
  Hypothesis UD : U + 64 <= D \/ D + n <= U.

  Notation SP := (bv_unsigned sp).
  Notation L z := (Z_to_bv 64 z) (only parsing).
  Notation POST := (parse_string_post HI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPB LR U P CA blen off depth bs D n lo m
                      nx pv ch ty p1 vs vi p2 vd ky).
  (* [comment removed for export] *)
  Notation SAVED := [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  (* [comment removed for export] *)
  Definition CST (pc : Z) (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
      (mm : word -> option byte) : machine_state :=
    MS (mkR x1 (Z_to_bv 64 (SP + -128)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
       F (Z_to_bv 64 pc) fc None mm (seg_rom usegs).

  (* [comment removed for export] *)
  Definition MID (m1 : word -> option byte) (mo1 : Model) (LB1 : list cblock) (errv1 : word) : Prop :=
    LHEAP HI SPB LB1 m1 mo1 /\ bytes_at usegs m1 CA bs /\ CJST m1 /\ rw_cells usegs m1 PERRNO [C4 errv1]
    /\ mem_inv usegs m1 /\ stk usegs m1 lo (SP + -128) /\ ppres LR SP P m m1.

  (* [comment removed for export] *)
  Ltac steq := unfold CST, LST, LSTc, mkR; repeat (lazymatch goal with |- @eq Z _ _ => lia | |- _ => first [reflexivity | progress f_equal] end).
  Ltac dj := cbn [disjoint_from cells_size csize Nat.add length]; first [lia | split; [lia| exact I]].
  (* [comment removed for export] *)
  Ltac trc H MU WM := first [ eapply rw_cells_transport in H; [| exact MU| exact WM| dj]
                            | eapply bytes_at_transport in H; [| exact MU| dj] ].
  Ltac alia := rewrite ?alloc_ceiling_eq; unfold RMALLOC_STACK, PARSE_STRING_STACK; lia.
  (* [comment removed for export] *)
  Ltac eqcells H :=
    lazymatch goal with |- rw_cells _ _ _ ?cs =>
      lazymatch type of H with rw_cells _ _ _ ?cs' =>
        replace cs with cs'; [exact H| unfold pbuf_cells, node_cells, wz; repeat f_equal; lia] end end.
  Ltac lits := (nelimp URNG 5%nat; intros U1 U2 U3 U4 U5); (nelimp DRNG 5%nat; intros D1 D2 D3 D4 D5);
               try rewrite alloc_ceiling_eq in *; unfold PARSE_STRING_STACK, RMALLOC_STACK, PIMG_LO, PIMG_HI in *;
               pose proof (bv_unsigned_in_range 64 sp) as SPR; change (bv_modulus 64) with (2^64) in SPR.

  (* [comment removed for export] *)
  Lemma fail0_tail : forall (i off1 : Z) m1 mo1 LB1 errv1 (junk : list byte)
      x1 x5 x6 x7 x8 x9 x10 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31,
    MID m1 mo1 LB1 errv1 -> Permutation ((U, 64) :: LR) LB1 ->
    rw_cells usegs m1 (SP + -128) (CB 24 junk :: SAVED) ->
    pbuf_at m1 P CA blen off1 depth ->
    rw_cells usegs m1 U (node_cells nx pv ch ty p1 vs vi p2 vd ky) ->
    off <= i <= blen ->
    SCPS usegs POST (CST 0x14ff0 x1 x5 x6 x7 x8 x9 x10 (Z_to_bv 64 P) x12 x13 x14 x15 x16 x17
                         (Z_to_bv 64 (CA + i)) x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 m1) mo1.
  Proof.
    intros until x31. intros (HL & BY & CJ & ERR & MI & ST & PR) HP1 FR PB ND Hi. lits.
    pose proof (pbuf_at_bound _ _ _ _ _ _ PB) as PBB. unfold pbuf_at, pbuf_cells in PB. unfold CST. unfold PERRNO in ERR.
    pose proof (rw_cells_bound usegs _ _ _ ND) as NDB. rewrite node_cells_size in NDB. unfold node_cells, wz in ND. unfold wz in PB.
    eapply scps_step_evt; [eapply (lh_mok HI); exact HL|].
    pose proof (munch_refl [(P + 16, P + 24)] m1) as MU. pose proof (wmono_refl usegs m1) as WM.
    zstep. zstep. zstep. zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
    do 13 zstep. zstep.
    release_frame FR ST (bv_unsigned sp).
    zstep.
    apply evt_done. apply scps_done. unfold parse_string_post.
    nexists 15%nat. exists m2, 0, i, LB1, [], errv1.
    split; [reflexivity|]. split; [reflexivity|].
    split.
    { (* [comment removed for export] *) split; [eapply (lheap_frame_store HI); [exact HL| exact MU| exact WM| alia| alia]|].
      split; [exact HP1|]. split; [apply (proj1 HDn)|]. split; [lia|]. split; [lia|]. split; [exact BY|]. split; [exact LEN|]. split; [exact BLEN|].
      split; [eapply CJST_high_store; [exact CJ| exact MU| exact WM| alia]|]. split; [unfold PERRNO; exact ERR|]. split; [exact MI|].
      split; [exact ST|]. split; [alia|]. exact PP. }
    split. { eapply ppres_trans; [exact PR|]. eapply (ppres_pbuf_store HI); [exact HL| intros b Hb; eapply Permutation_in; [exact HP1| right; exact Hb]| exact MU| exact WM| alia| alia| alia]. }
    split. { unfold pbuf_at. eqcells PB. }
    split; [lia|]. left. split; [reflexivity|]. split; [reflexivity| eqcells ND].
  Qed.

  (* [comment removed for export] *)
  Lemma dealloc_tail : forall (S k i off1 : Z) m1 mo1 LB2 errv1 (junk : list byte)
      x1 x5 x6 x7 x8 x9 x10 x12 x13 x14 x15 x16 x17 x19 x20 x22 x23 x24 x25 x26 x28 x29 x30 x31,
    MID m1 mo1 LB2 errv1 -> Permutation ((U, 64) :: (S, k) :: LR) LB2 ->
    rw_cells usegs m1 (SP + -128) (CB 24 junk :: SAVED) ->
    pbuf_at m1 P CA blen off1 depth ->
    rw_cells usegs m1 U (node_cells nx pv ch ty p1 vs vi p2 vd ky) ->
    off <= i <= blen ->
    SCPS usegs POST (CST 0x14fe0 x1 x5 x6 x7 x8 x9 x10 (Z_to_bv 64 P) x12 x13 x14 x15 x16 x17
                         (Z_to_bv 64 (CA + i)) x19 x20 (Z_to_bv 64 P) x22 x23 x24 x25 x26 (Z_to_bv 64 S) x28 x29 x30 x31 m1) mo1.
  Proof.
    intros until x31. intros (HL & BY & CJ & ERR & MI & ST & PR) HP2 FR PB ND Hi. lits.
    pose proof (pbuf_at_bound _ _ _ _ _ _ PB) as PBB. pose proof PB as PB0. unfold pbuf_at, pbuf_cells in PB. unfold CST. unfold PERRNO in ERR.
    unfold wz in PB.
    assert (HP2' : Permutation ((S, k) :: (U, 64) :: LR) LB2) by (eapply Permutation_trans; [apply perm_swap| exact HP2]).
    eapply scps_step_evt; [eapply (lh_mok HI); exact HL|].
    zstep. zstep. zstep.
    replace (ret_pc (Z_to_bv 64 PFREE)) with (wz PFREE) by (unfold wz, PFREE; symmetry; apply ret_pc_even; [lia| reflexivity]).
    apply evt_done. cbv beta.
    eapply scps_bind.
    { eapply (lh_free HI) with (lo := lo) (A := S) (n := k); rewrite ?unsigned_lit by lia;
        first [ exact HL | eapply perm_in_head; exact HP2' | exact ST | exact ERR | exact MI | exact TP | reflexivity | alia ]. }
    cbv beta. intros ms2 mo2 PO.
    (nelim PO 22%nat; intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m2 -> MI2 ST2 ERR2 PR2 HL2)
.
    rewrite ?unsigned_lit in ST2, PR2 by lia.
    replace (ret_pc (Z_to_bv 64 0x14fec)) with (Z_to_bv 64 0x14fec) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    pose proof (perm_cb_remove _ _ _ _ HP2' (lh_nodup HI _ _ _ _ HL)) as HP1.
    assert (INL : forall b, In b LR -> In b (cb_remove S LB2)) by (intros b Hb; eapply Permutation_in; [exact HP1| right; exact Hb]).
    eapply scps_step_evt; [eapply (lh_mok HI); exact HL2|].
    zstep. apply evt_done.
    eapply (fail0_tail i off1 m2 mo2 (cb_remove S LB2) errv1 junk).
    - split; [exact HL2|]. split.
      { eapply cj_pres_bytes_at; [exact PR2| exact BY|]. right; right. exists D, n. split; [apply INL; apply (proj1 HDn)| lia]. }
      split; [eapply CJST_pres; [exact PR2| exact CJ]|]. split; [unfold PERRNO; exact ERR2|]. split; [exact MI2|]. split; [exact ST2|].
      eapply ppres_trans; [exact PR|]. eapply ppres_of_cj_pres; [exact PR2| lia| exact INL].
    - exact HP1.
    - eapply cj_pres_rw_cells; [exact PR2| exact FR| left; lia].
    - unfold pbuf_at. eapply cj_pres_rw_cells; [exact PR2| exact PB0| left; cbn; lia].
    - eapply cj_pres_rw_cells; [exact PR2| exact ND|]. right; right. exists U, 64. split; [eapply perm_in_head; exact HP1| rewrite node_cells_size; lia].
    - exact Hi.
  Qed.

  (* [comment removed for export] *)
  Lemma ok_tail : forall (S e oc off1 : Z) (buf junk : list byte) m1 mo1 LB2 errv1
      x1 x5 x6 x7 x8 x9 x10 x14 x15 x16 x17 x18 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31,
    MID m1 mo1 LB2 errv1 -> Permutation ((U, 64) :: (S, Z.of_nat (length buf)) :: LR) LB2 ->
    rw_cells usegs m1 (SP + -128) (CB 24 junk :: SAVED) ->
    pbuf_at m1 P CA blen off1 depth ->
    rw_cells usegs m1 U (node_cells nx pv ch ty p1 vs vi p2 vd ky) ->
    u8arr usegs m1 S buf -> 0 <= oc < Z.of_nat (length buf) ->
    cblock_range S (Z.of_nat (length buf)) -> (U + 64 <= S \/ S + Z.of_nat (length buf) <= U) ->
    (D + n <= S \/ S + Z.of_nat (length buf) <= D) ->
    off <= e < blen ->
    SCPS usegs POST (CST 0x14fb0 x1 x5 x6 x7 x8 x9 x10 (Z_to_bv 64 P) (Z_to_bv 64 U) (Z_to_bv 64 (S + oc)) x14 x15 x16 x17
                         x18 (Z_to_bv 64 (CA + e)) x20 x21 x22 x23 x24 x25 x26 (Z_to_bv 64 S) x28 x29 x30 x31 m1) mo1.
  Proof.
    intros until x31. intros (HL & BY & CJ & ERR & MI & ST & PR) HP2 FR PB ND BUF Hoc SRNG SU SD He.
    (nelim SRNG 5%nat; intros S1 S2 S3 S4 S5). lits.
    pose proof (pbuf_at_bound _ _ _ _ _ _ PB) as PBB. unfold pbuf_at, pbuf_cells, wz in PB. unfold CST. unfold PERRNO in ERR.
    pose proof (rw_cells_bound usegs _ _ _ ND) as NDB. rewrite node_cells_size in NDB. unfold node_cells, wz in ND.
    pose proof (bytes_at_bound _ _ _ _ BY) as BYB.
    assert (HP2' : Permutation ((S, Z.of_nat (length buf)) :: (U, 64) :: LR) LB2) by (eapply Permutation_trans; [apply perm_swap| exact HP2]).
    assert (INS : In (S, Z.of_nat (length buf)) LB2) by (eapply perm_in_head; exact HP2').
    assert (INU : In (U, 64) LB2) by (eapply perm_in_head; exact HP2).
    assert (INLR : forall b, In b LR -> In b LB2) by (intros b Hb; eapply Permutation_in; [exact HP2| right; right; exact Hb]).
    eapply scps_step_evt; [eapply (lh_mok HI); exact HL|].
    (* [comment removed for export] *)
    zstep. if_cases K0; zify_cond K0; [exfalso; lia|].
    zstep. rewrite (align16_land7 U) by lia.
    pose proof (munch_refl [(S + oc, S + oc + 1)] m1) as MU. pose proof (wmono_refl usegs m1) as WM.
    pose proof (u8arr_store_ok usegs _ _ _ oc (Z_to_bv 64 (S + oc)) BUF ltac:(lia) eq_refl) as SOK.
    zstep. rewrite le1_lit.
    pose proof (u8arr_write usegs _ _ _ oc (Z_to_bv 8 0) BUF ltac:(lia)) as BUF'. clear BUF. store_done. try clear SOK. rename BUF' into BUF.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
    assert (HL2 : LHEAP HI SPB LB2 m2 mo1) by (eapply (lheap_block_store HI); [exact HL| exact INS| exact MU| exact WM| lia| lia]).
    assert (CJ2 : CJST m2) by (eapply (CJST_block_store HI); [exact HL| exact INS| exact CJ| exact MU| exact WM| lia| lia]).
    assert (PR2 : ppres LR SP P m m2).
    { eapply ppres_trans; [exact PR|]. eapply (ppres_block_store HI); [exact HL| exact HP2'| intros b Hb; right; exact Hb| alia| exact MU| exact WM| lia| lia]. }
    clear MU WM.
    zstep. if_cases KA; zify_cond KA; [exfalso; apply KA; reflexivity|].
    (* [comment removed for export] *)
    pose proof (munch_refl [(U + 24, U + 40)] m2) as MU. pose proof (wmono_refl usegs m2) as WM.
    zstep. zstep. zstep. fix_lit_store. zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
    assert (HL3 : LHEAP HI SPB LB2 m3 mo1) by (eapply (lheap_block_store HI); [exact HL2| exact INU| exact MU| exact WM| lia| lia]).
    assert (CJ3 : CJST m3) by (eapply (CJST_block_store HI); [exact HL| exact INU| exact CJ2| exact MU| exact WM| lia| lia]).
    assert (PR3 : ppres LR SP P m m3).
    { eapply ppres_trans; [exact PR2|]. eapply (ppres_block_store HI); [exact HL| exact HP2| intros b Hb; right; exact Hb| alia| exact MU| exact WM| lia| lia]. }
    clear MU WM HL2 CJ2 PR2.
    (* [comment removed for export] *)
    pose proof (munch_refl [(P + 16, P + 24)] m3) as MU. pose proof (wmono_refl usegs m3) as WM.
    zstep. zstep. zstep. zstep. zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m4 end.
    assert (HL4 : LHEAP HI SPB LB2 m4 mo1) by (eapply (lheap_frame_store HI); [exact HL3| exact MU| exact WM| alia| alia]).
    assert (CJ4 : CJST m4) by (eapply CJST_high_store; [exact CJ3| exact MU| exact WM| alia]).
    assert (PR4 : ppres LR SP P m m4).
    { eapply ppres_trans; [exact PR3|]. eapply (ppres_pbuf_store HI); [exact HL| exact INLR| exact MU| exact WM| alia| alia| alia]. }
    clear MU WM HL3 CJ3 PR3.
    do 13 zstep. zstep. release_frame FR ST (bv_unsigned sp). zstep.
    apply evt_done. apply scps_done. unfold parse_string_post.
    nexists 15%nat. exists m4, 1, (e + 1), LB2, [(S, Z.of_nat (length buf))], errv1.
    split; [reflexivity|]. split; [reflexivity|].
    split.
    { split; [exact HL4|].
      split; [exact HP2|]. split; [apply (proj1 HDn)|]. split; [lia|]. split; [lia|]. split; [exact BY|]. split; [exact LEN|]. split; [exact BLEN|].
      split; [exact CJ4|]. split; [unfold PERRNO; exact ERR|]. split; [exact MI|]. split; [exact ST|]. split; [alia|]. exact PP. }
    split; [exact PR4|].
    split. { unfold pbuf_at. eqcells PB. }
    split; [lia|]. right. split; [reflexivity|]. exists S, (Z.of_nat (length buf)). split; [reflexivity|]. split; [lia|].
    split; [eqcells ND|].
    destruct (split_first_nul (upd buf (Z.to_nat oc) (Z_to_bv 8 0)) (Z.to_nat oc)) as (str & tail & E & NI). (* [comment removed for export] *)
    { apply nth_error_upd_same. lia. }
    eapply cj_str_intro; [lia| | exact NI|].
    - rewrite <- E. exact (proj1 BUF).
    - apply (f_equal (@length byte)) in E. rewrite upd_length, length_app in E. cbn [length] in E. lia.
  Qed.

  (* [comment removed for export] *)
  Section Loop1.
    Variables (t2 t3 t4 t5 t6 : word) (m1 : word -> option byte).
    Hypothesis BY1 : bytes_at usegs m1 CA bs.
    Hypothesis MI1 : mem_inv usegs m1.

    Definition L1 (pc : Z) (x6 x8 x15 x19 x20 : word) : machine_state :=
      MS (mkR ra (Z_to_bv 64 (SP + -128)) gp tp (Z_to_bv 64 34) x6 t2 x8 s1 (Z_to_bv 64 U) (Z_to_bv 64 P)
              (Z_to_bv 64 (off + CA)) (Z_to_bv 64 CA) (Z_to_bv 64 blen) x15 (Z_to_bv 64 92) (Z_to_bv 64 (-1))
              (Z_to_bv 64 (off + CA + 1)) x19 x20 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
         F (Z_to_bv 64 pc) fc None m1 (seg_rom usegs).

    Definition Q1 : machine_state -> Prop := fun ms' =>
      (exists (q sk : Z) (x6 : word),
          ms' = L1 0x14d20 x6 (Z_to_bv 64 q) (Z_to_bv 64 sk) (Z_to_bv 64 (off + CA + q)) (Z_to_bv 64 (off + CA + q))
          /\ ps_scan bs blen (Z.to_nat blen) (off + 1) 0 = Some (off + q, sk) /\ 1 <= q /\ off + q < blen /\ 0 <= sk <= q)
      \/ (exists x6 x8 x15 x19 x20, ms' = L1 0x14ff0 x6 x8 x15 x19 x20).

    Lemma loop1 : forall (cnt : nat) (q sk : Z) (x6 x20 : word),
      Z.of_nat cnt = blen - (off + q) -> 1 <= q -> off + q < blen -> 0 <= sk <= q - 1 ->
      (forall r, ps_scan bs blen (Z.to_nat (blen - (off + q))) (off + q) sk = Some r ->
                 ps_scan bs blen (Z.to_nat blen) (off + 1) 0 = Some r) ->
      evt usegs Q1 (L1 0x14cd0 x6 (Z_to_bv 64 q) (Z_to_bv 64 sk) (Z_to_bv 64 (off + CA + q)) x20).
    Proof.
      induction cnt as [cnt IH] using lt_wf_ind.
      intros q sk x6 x20 Hcnt Hq Hoq Hsk K. lits. pose proof (bytes_at_bound _ _ _ _ BY1) as BYB. unfold L1.
      (nelim (text_read m1 CA bs (off + q) (Z_to_bv 64 (off + CA + q)) BY1 ltac:(lia) ltac:(lia) ltac:(unfold wa; f_equal; lia)) 4%nat; intros b Hb RD Hat).
      pose proof (byte_range b) as Rb.
      assert (STEP : ps_scan bs blen (Z.to_nat (blen - (off + q))) (off + q) sk =
                     (if at_ bs (off + q) =? 34 then Some (off + q, sk)
                      else if at_ bs (off + q) =? 92 then (if blen <=? off + q + 1 then None else ps_scan bs blen (Z.to_nat (blen - (off + q + 1))) (off + q + 2) (sk + 1))
                      else ps_scan bs blen (Z.to_nat (blen - (off + q + 1))) (off + q + 1) sk)).
      { replace (Z.to_nat (blen - (off + q))) with (S (Z.to_nat (blen - (off + q + 1)))) by lia. apply ps_scan_step. lia. }
      rewrite Hat in STEP.
      zstep. zstep. zstep. if_cases Kbs; zify_cond Kbs.
      - (* [comment removed for export] *)
        zstep. if_cases Kg1; zify_cond Kg1; [exfalso; lia|].
        zstep. zstep. zstep. zstep. if_cases Ke; zify_cond Ke.
        { apply evt_done. right. nexists 5%nat. reflexivity. }
        zstep. zstep. zstep. if_cases Kg2; zify_cond Kg2; [exfalso; lia|].
        zstep. zstep. zstep. zstep. if_cases Ke2; zify_cond Ke2.
        + replace (off + CA + (q + 1 + 1)) with (off + CA + (q + 2)) by lia. replace (q + 1 + 1) with (q + 2) by lia.
          eapply (IH (cnt - 2)%nat ltac:(lia) (q + 2) (sk + 1)); [lia| lia| lia| lia|].
          intros r Hr. apply K. rewrite STEP, Kbs. change (92 =? 34) with false. change (92 =? 92) with true. cbv iota.
          replace (blen <=? off + q + 1) with false by (symmetry; apply Z.leb_gt; lia).
          eapply ps_scan_fuel; [| ]. { replace (off + q + 2) with (off + (q + 2)) by lia. exact Hr. } lia.
        + zstep. apply evt_done. right. nexists 5%nat. reflexivity.
      - zstep. if_cases Kq; zify_cond Kq.
        + (* [comment removed for export] *)
          apply evt_done. left. exists q, sk. eexists. split; [reflexivity|]. split; [| lia].
          apply K. rewrite STEP. rewrite (proj2 (Z.eqb_eq _ _) Kq). reflexivity.
        + (* [comment removed for export] *)
          zstep. zstep. if_cases Kg1; zify_cond Kg1; [| exfalso; lia].
          zstep. zstep. zstep. zstep. if_cases Ke; zify_cond Ke.
          * eapply (IH (cnt - 1)%nat ltac:(lia) (q + 1) sk); [lia| lia| lia| lia|].
            intros r Hr. apply K. rewrite STEP. rewrite (proj2 (Z.eqb_neq _ _) Kq), (proj2 (Z.eqb_neq _ _) Kbs).
            replace (off + (q + 1)) with (off + q + 1) in Hr by lia. exact Hr.
          * zstep. apply evt_done. right. do 5 eexists. reflexivity.
    Qed.
  End Loop1.

  (* [comment removed for export] *)
  Theorem parse_string_main : forall (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (mo : Model) (errv : word),
    LHEAP HI SPB LB m mo -> bytes_at usegs m CA bs -> CJST m -> rw_cells usegs m PERRNO [C4 errv] -> mem_inv usegs m ->
    stk usegs m lo SP -> ppres LR SP P m m ->
    rw_cells usegs m U (node_cells nx pv ch ty p1 vs vi p2 vd ky) -> pbuf_at m P CA blen off depth ->
    a0 = wz U -> a1 = wz P ->
    SCPS usegs POST (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (wz PARSE_STRING) fc None m (seg_rom usegs)) mo.
  Proof.
    intros until errv. intros HL BY CJ ERR MI ST PR0 ND PB A0 A1. lits.
    unfold wz in A0, A1. subst a0 a1. unfold PARSE_STRING, wz.
    pose proof (pbuf_at_bound _ _ _ _ _ _ PB) as PBB. unfold pbuf_at, pbuf_cells, wz in PB.
    pose proof (rw_cells_bound usegs _ _ _ ND) as NDB. rewrite node_cells_size in NDB. unfold node_cells, wz in ND.
    pose proof (bytes_at_bound _ _ _ _ BY) as BYB. unfold PERRNO in ERR.
    assert (INLR : forall b, In b LR -> In b LB) by (intros b Hb; eapply Permutation_in; [exact HPU| right; exact Hb]).
    eapply scps_step_evt; [eapply (lh_mok HI); exact HL|].
    pose proof (munch_refl [(SP + -128, SP)] m) as MU. pose proof (wmono_refl usegs m) as WM.
    zstep. carve_frame 128%nat ST. do 13 zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    assert (HL1 : LHEAP HI SPB LB m1 mo) by (eapply (lheap_frame_store HI); [exact HL| exact MU| exact WM| alia| alia]).
    assert (CJ1 : CJST m1) by (eapply CJST_high_store; [exact CJ| exact MU| exact WM| alia]).
    assert (PR1 : ppres LR SP P m m1).
    { eapply ppres_trans; [exact PR0|]. eapply (ppres_frame_store HI); [exact HL| exact INLR| exact MU| exact WM| alia| lia]. }
    clear MU WM HL CJ PR0.
    Ltac mid HLx BYx CJx ERRx MIx STx PRx :=
      split; [exact HLx|]; split; [exact BYx|]; split; [exact CJx|]; split; [unfold PERRNO; exact ERRx|];
      split; [exact MIx|]; split; [exact STx| exact PRx].
    (* [comment removed for export] *)
    zstep. rewrite (align8_land7 P) by lia. zstep. if_cases KA; zify_cond KA; [exfalso; apply KA; reflexivity|].
    zstep. zstep. zstep.
    zstep. if_cases KW; zify_cond KW; [exfalso; lia|].
    zstep. zstep. zstep. zstep. if_cases KN; zify_cond KN.
    { exfalso. revert KN. replace (0 <? CA) with true by (symmetry; apply Z.ltb_lt; lia).
      replace (off + CA <? 1) with false by (symmetry; apply Z.ltb_ge; lia). vm_compute. discriminate. }
    zstep. if_cases KZ1; zify_cond KZ1; [exfalso; lia|].
    zstep. if_cases KZ2; zify_cond KZ2; [exfalso; lia|].
    zstep. zstep. if_cases KM1; zify_cond KM1; [exfalso; lia|].
    (* [comment removed for export] *)
    (nelim (text_read m1 CA bs off (Z_to_bv 64 (CA + off)) BY ltac:(lia) ltac:(lia) eq_refl) 4%nat; intros b0 Hb0 RD0 Hat0).
    pose proof (byte_range b0) as Rb0.
    zstep. zstep. zstep. zstep. if_cases K34; zify_cond K34.
    { replace (off + CA + 1) with (CA + (off + 1)) by lia. apply evt_done.
      eapply (fail0_tail (off + 1) off m1 mo LB errv); [mid HL1 BY CJ1 ERR MI ST PR1| exact HPU| exact FR| unfold pbuf_at; eqcells PB| eqcells ND| lia]. }
    zstep. zstep. zstep. if_cases Kend; zify_cond Kend.
    { replace (off + CA + 1) with (CA + (off + 1)) by lia. apply evt_done.
      eapply (fail0_tail (off + 1) off m1 mo LB errv); [mid HL1 BY CJ1 ERR MI ST PR1| exact HPU| exact FR| unfold pbuf_at; eqcells PB| eqcells ND| lia]. }
    do 6 zstep.
    (* [comment removed for export] *)
    eapply evt_cut.
    { eapply (loop1 t2 t3 t4 t5 t6 m1 BY (Z.to_nat (blen - (off + 1))) 1 0); [lia| lia| lia| lia|].
      intros r Hr. eapply ps_scan_fuel; [exact Hr| lia]. }
    intros ms' [(q & sk & x6 & -> & SCAN & Hq & Hoq & Hsk) | (x6 & x8 & x15 & x19 & x20 & ->)]; unfold L1.
    2:{ replace (off + CA + 1) with (CA + (off + 1)) by lia. apply evt_done.
        eapply (fail0_tail (off + 1) off m1 mo LB errv); [mid HL1 BY CJ1 ERR MI ST PR1| exact HPU| exact FR| unfold pbuf_at; eqcells PB| eqcells ND| lia]. }
    (* [comment removed for export] *)
    (nelimp (ps_scan_npairs _ _ _ _ _ _ _ SCAN) 3%nat; intros SKE _ AT34).
    pose proof (npairs_window bs blen (Z.to_nat blen) (off + 1) (off + 1) (off + q) ltac:(lia)) as [Wa Wb].
    rewrite (npairs_le bs blen _ (off + 1) (off + 1)) in Wa, Wb by lia. pose proof (bflag_range bs (off + 1)) as BF.
    zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    replace (ret_pc (Z_to_bv 64 PMALLOC)) with (wz PMALLOC) by (unfold wz, PMALLOC; symmetry; apply ret_pc_even; [lia| reflexivity]).
    apply evt_done. cbv beta.
    eapply scps_bind.
    { pose proof (lh_malloc HI) as LM. unfold malloc_scps_stmt in LM.
      eapply LM with (lo := lo) (n := off + q - off - sk + 1); rewrite ?unsigned_lit by lia;
        first [ exact HL1 | exact ST | exact ERR | exact MI | exact TP | unfold wz; f_equal; lia | alia ]. }
    cbv beta. intros ms2 mo2 PO.
    (nelim PO 23%nat; intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m2 errv2 -> MI2 ST2 ERR2 PR2 RES)
.
    rewrite ?unsigned_lit in ST2, PR2 by lia.
    replace (ret_pc (Z_to_bv 64 0x14d3c)) with (Z_to_bv 64 0x14d3c) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    (* [comment removed for export] *)
    apply (cj_pres_rw_cells _ _ _ _ _ _ PR2) in FR; [| left; lia].
    apply (cj_pres_rw_cells _ _ _ _ _ _ PR2) in PB; [| left; cbn; lia].
    apply (cj_pres_rw_cells _ _ _ _ _ _ PR2) in ND; [| right; right; exists U, 64; split; [eapply perm_in_head; exact HPU| cbn; lia]].
    apply (cj_pres_bytes_at _ _ _ _ _ _ PR2) in BY; [| right; right; exists D, n; split; [apply INLR; apply (proj1 HDn)| lia]].
    apply (CJST_pres _ _ _ _ PR2) in CJ1.
    assert (PR3 : ppres LR SP P m m2) by (eapply ppres_trans; [exact PR1| eapply ppres_of_cj_pres; [exact PR2| lia| exact INLR]]).
    clear PR1 PR2 MI ST HL1 ERR. unfold PERRNO in ERR2.
    destruct RES as [[-> HL2] | (A & jk & -> & ARNG & ANEW & HL2 & BLK)].
    - (* [comment removed for export] *)
      eapply scps_step_evt; [eapply (lh_mok HI); exact HL2|].
      unfold wz. zstep. if_true. zstep. replace (off + CA + 1) with (CA + (off + 1)) by lia. apply evt_done.
      eapply (fail0_tail (off + 1) off m2 mo2 LB errv2); [mid HL2 BY CJ1 ERR2 MI2 ST2 PR3| exact HPU| exact FR| unfold pbuf_at; eqcells PB| eqcells ND| lia].
    - (* [comment removed for export] *)
      (nelimp ARNG 5%nat; intros A1 A2 A3 A4 A5). try rewrite alloc_ceiling_eq in A4. unfold PIMG_LO, PIMG_HI in A5.
      assert (HP2 : Permutation ((U, 64) :: (A, off + q - off - sk + 1) :: LR) ((A, off + q - off - sk + 1) :: LB)).
      { eapply Permutation_trans; [apply perm_swap|]. apply perm_skip. exact HPU. }
      assert (AU : U + 64 <= A \/ A + (off + q - off - sk + 1) <= U).
      { destruct (lh_blocks_disjoint HI _ _ _ _ _ _ _ _ HL2 ltac:(right; eapply perm_in_head; exact HPU) ltac:(left; reflexivity)) as [?|?]; [| lia| lia].
        intros ->. apply ANEW. apply (in_map fst) with (x := (A, 64)). eapply perm_in_head; exact HPU. }
      assert (AD : D + n <= A \/ A + (off + q - off - sk + 1) <= D).
      { destruct (lh_blocks_disjoint HI _ _ _ _ _ _ _ _ HL2 ltac:(right; apply INLR; apply (proj1 HDn)) ltac:(left; reflexivity)) as [?|?]; [| lia| lia].
        intros ->. apply ANEW. apply (in_map fst) with (x := (A, n)). apply INLR, (proj1 HDn). }
      assert (LJ : length jk = Z.to_nat (off + q - off - sk + 1)) by (destruct BLK as [[Hwf _] _]; cbn in Hwf; lia).
      pose proof (u8arr_of_rw_cells usegs m2 A _ jk BLK) as BUF.
      eapply scps_step_evt; [eapply (lh_mok HI); exact HL2|].
      unfold wz. zstep. if_cases Kz; zify_cond Kz; [exfalso; lia|].
      zstep. zstep. zstep. zstep. zstep. zstep. rewrite (bv_lts_small q 2) by lia. if_cases Kq; zify_cond Kq.
      + (* [comment removed for export] *)
        apply evt_done. eapply scps_eq; [| eapply (ok_tail A (off + 1) 0 off jk _ m2 mo2 ((A, off + q - off - sk + 1) :: LB) errv2)].
        { steq. }
        * mid HL2 BY CJ1 ERR2 MI2 ST2 PR3.
        * replace (Z.of_nat (length jk)) with (off + q - off - sk + 1) by lia. exact HP2.
        * exact FR.
        * unfold pbuf_at; eqcells PB.
        * eqcells ND.
        * exact BUF.
        * lia.
        * replace (Z.of_nat (length jk)) with (off + q - off - sk + 1) by lia. exact ARNG.
        * lia.
        * lia.
        * lia.
      + (* [comment removed for export] *)
        pose proof (munch_refl [(SP + -128, SP + -104)] m2) as MU. pose proof (wmono_refl usegs m2) as WM.
        do 7 zstep. zstep. fix_lit_store. zstep. zstep. fix_lit_store.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
        assert (HL3 : LHEAP HI SPB ((A, off + q - off - sk + 1) :: LB) m3 mo2)
          by (eapply (lheap_frame_store HI); [exact HL2| exact MU| exact WM| alia| alia]).
        assert (CJ3 : CJST m3) by (eapply CJST_high_store; [exact CJ1| exact MU| exact WM| alia]).
        assert (PR4 : ppres LR SP P m m3).
        { eapply ppres_trans; [exact PR3|]. eapply (ppres_frame_store HI); [exact HL2| | exact MU| exact WM| alia| lia].
          intros b Hb. right. apply INLR. exact Hb. }
        clear MU WM HL2 CJ1 PR3.
        zstep.
        (* [comment removed for export] *)
        lazymatch type of FR with rw_cells _ _ _ (CB 8 ?j :: C8 ?v1 :: C8 ?v2 :: _) =>
          replace v1 with (Z_to_bv 64 0xdc00) in FR by (apply bv_eq; vm_compute; reflexivity);
          replace v2 with (Z_to_bv 64 0xd800) in FR by (apply bv_eq; vm_compute; reflexivity);
          remember j as j0 eqn:Ej0 in FR; clear Ej0 end.
        assert (CTX : ps_ctx sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra m3 CA blen off (off + q) sk A bs j0).
        { split; [exact LEN|]. split; [exact BY|]. split; [exact FR|]. split; [exact SCAN|]. split; [lia|]. split; [exact BLEN|].
          split; [lia|]. split; [alia|]. split; [lia|]. unfold nalloc. split; [alia|]. split; [lia|]. alia. }
        eapply evt_cut.
        { eapply evt_eq.
          2:{ pose proof (dec_loop sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra F fc m3 CA blen off (off + q) sk A P U bs j0 CTX (Z.to_nat (off + q - (off + 1)))) as DL.
              unfold LOOPK in DL. eapply (DL (off + 1) 0 m3 jk); [lia| lia| eapply dinv0; exact CTX| lia|].
              split; [exact BUF|]. split; [unfold nalloc; exact LJ|]. split; [apply munch_refl|]. split; [apply wmono_refl| exact MI2]. }
          steq. }
        intros ms' KP.
        (nelim KP 25%nat; intros mm buf x1' x5' x6' x7' x9' x10' x12' x13' x14' x15' x16' x17' x28' x29' x30' x31' i oc LMm Hi Hoc ROOM [-> | ->]);
          unfold LST, LSTc; (nelimp LMm 5%nat; intros BUFm BLm MUm WMm MIm); unfold W2, nalloc in MUm, BLm, ROOM.
        * (* [comment removed for export] *)
          apply evt_done.
          pose proof FR as FRm. trc FRm MUm WMm.
          apply (rw_cells_merge usegs mm (SP + -128) [] [CB 8 j0; C8 (Z_to_bv 64 0xdc00); C8 (Z_to_bv 64 0xd800)] SAVED) in FRm. cbn [app cells_size cells_bytes csize cbytes Nat.add] in FRm.
          pose proof PB as PBm. trc PBm MUm WMm. pose proof ND as NDm. trc NDm MUm WMm. pose proof ERR2 as ERRm. trc ERRm MUm WMm.
          pose proof BY as BYm. trc BYm MUm WMm.
          eapply (ok_tail A (off + q) oc off buf _ mm mo2 ((A, off + q - off - sk + 1) :: LB) errv2).
          -- split. { eapply (lheap_block_store HI); [exact HL3| left; reflexivity| exact MUm| exact WMm| lia| lia]. }
             split; [exact BYm|].
             split. { eapply (CJST_block_store HI); [exact HL3| left; reflexivity| exact CJ3| exact MUm| exact WMm| lia| lia]. }
             split; [unfold PERRNO; exact ERRm|].
             split; [exact MIm|]. split. { eapply stk_transport_disjoint; [exact ST2| exact MUm| exact WMm| dj]. }
             eapply ppres_trans; [exact PR4|]. eapply (ppres_block_store HI); [exact HL3| apply perm_skip; exact HPU| intros b Hb; right; exact Hb| alia| exact MUm| exact WMm| lia| lia].
          -- replace (Z.of_nat (length buf)) with (off + q - off - sk + 1) by lia. exact HP2.
          -- exact FRm.
          -- unfold pbuf_at. eqcells PBm.
          -- eqcells NDm.
          -- exact BUFm.
          -- lia.
          -- replace (Z.of_nat (length buf)) with (off + q - off - sk + 1) by lia. exact ARNG.
          -- lia.
          -- lia.
          -- lia.
        * (* [comment removed for export] *)
          apply evt_done.
          pose proof FR as FRm. trc FRm MUm WMm.
          apply (rw_cells_merge usegs mm (SP + -128) [] [CB 8 j0; C8 (Z_to_bv 64 0xdc00); C8 (Z_to_bv 64 0xd800)] SAVED) in FRm. cbn [app cells_size cells_bytes csize cbytes Nat.add] in FRm.
          pose proof PB as PBm. trc PBm MUm WMm. pose proof ND as NDm. trc NDm MUm WMm. pose proof ERR2 as ERRm. trc ERRm MUm WMm.
          pose proof BY as BYm. trc BYm MUm WMm.
          eapply (dealloc_tail A (off + q - off - sk + 1) i off mm mo2 ((A, off + q - off - sk + 1) :: LB) errv2).
          -- split. { eapply (lheap_block_store HI); [exact HL3| left; reflexivity| exact MUm| exact WMm| lia| lia]. }
             split; [exact BYm|].
             split. { eapply (CJST_block_store HI); [exact HL3| left; reflexivity| exact CJ3| exact MUm| exact WMm| lia| lia]. }
             split; [unfold PERRNO; exact ERRm|].
             split; [exact MIm|]. split. { eapply stk_transport_disjoint; [exact ST2| exact MUm| exact WMm| dj]. }
             eapply ppres_trans; [exact PR4|]. eapply (ppres_block_store HI); [exact HL3| apply perm_skip; exact HPU| intros b Hb; right; exact Hb| alia| exact MUm| exact WMm| lia| lia].
          -- exact HP2.
          -- exact FRm.
          -- unfold pbuf_at. eqcells PBm.
          -- eqcells NDm.
          -- lia.
  Qed.
End PSTR.

Theorem parse_string_spec : forall HI, parse_string_stmt HI.
Proof.
  intros HI. unfold parse_string_stmt. intros until ky.
  intros (HL & HPU & HD & DCA & CAD & BY & LEN & BLEN & CJ & ERR & MI & ST & CEIL & SPP & PSPB) ND PB OFF LO TP A0 A1.
  assert (INU : In (U, 64) LB) by (eapply perm_in_head; exact HPU).
  assert (IND : In (D, n) LB) by (eapply Permutation_in; [exact HPU| right; exact HD]).
  assert (UD : U <> D).
  { intros ->. pose proof (lh_nodup HI _ _ _ _ HL) as NDP.
    apply (NoDup_map_fst_perm _ _ (Permutation_sym HPU)) in NDP. rewrite NoDup_ListNoDup in NDP. cbn in NDP.
    inversion NDP; subst. apply H1. apply (in_map fst) in HD. exact HD. }
  eapply parse_string_main; try eassumption.
  - split; [exact HD| split; [exact DCA| exact CAD]].
  - split; [exact SPP| exact PSPB].
  - eapply (lh_block_range HI); [exact HL| exact INU].
  - eapply (lh_block_range HI); [exact HL| exact IND].
  - destruct (lh_blocks_disjoint HI _ _ _ _ _ _ _ _ HL INU IND UD); lia.
  - apply ppres_refl.
Qed.


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
