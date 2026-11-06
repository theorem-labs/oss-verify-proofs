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
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require PImg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require CJ_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require CJ_tree.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require CJ_phex4.
Module CJ_pstring_A.
(* [comment removed for export] *)
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.PImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.CJ_tree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.CJ_phex4.CJ_pbuf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.CJ_phex4.CJ_parse_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.CJ_phex4.CJ_parse_lemmas.
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
    /\ bytes_at psegs m2 CA bs
    /\ rw_cells psegs m2 (bv_unsigned sp + -128) FRAME
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
  Definition LST (pc : Z) (x5 x6 x7 x12 x13 x14 x15 x16 x17 x26 x28 : word) (i oc : Z) (mm : word -> option byte) : machine_state :=
    MS (mkR (Z_to_bv 64 6) (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp x5 x6 x7 (Z_to_bv 64 (CA + i)) (Z_to_bv 64 (CA + e))
            (Z_to_bv 64 S) (Z_to_bv 64 P) x12 x13 x14 x15 x16 x17
            (Z_to_bv 64 (CA + e)) (Z_to_bv 64 P) (Z_to_bv 64 U) (Z_to_bv 64 92) (Z_to_bv 64 83) (Z_to_bv 64 9) (Z_to_bv 64 JT)
            (Z_to_bv 64 10) x26 (Z_to_bv 64 (S + oc)) x28 (Z_to_bv 64 8) (Z_to_bv 64 12) (Z_to_bv 64 13))
       F (Z_to_bv 64 pc) fc None mm (seg_rom psegs).

  (* [comment removed for export] *)
  Definition lmem (mm : word -> option byte) (buf : list byte) : Prop :=
    u8arr psegs mm S buf /\ length buf = Z.to_nat nalloc /\ munch W2 m2 mm /\ wmono psegs m2 mm /\ mem_inv psegs mm.

  Definition KPOST : machine_state -> Prop := fun ms' =>
    exists (mm : word -> option byte) (buf : list byte) (x5 x6 x7 x12 x13 x14 x15 x16 x17 x26 x28 : word) (i oc : Z),
      lmem mm buf /\ off + 1 <= i <= e + 1 /\ 0 <= oc /\ oc + 1 <= nalloc
      /\ ( ms' = LST 0x13ec4 x5 x6 x7 x12 (Z_to_bv 64 U) x14 x15 x16 x17 x26 x28 i oc mm      (* [comment removed for export] *)
           \/ ms' = LST 0x13ee8 x5 x6 x7 x12 x13 x14 x15 x16 x17 x26 x28 i oc mm ).          (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition LOOPK (k : nat) : Prop :=
    forall (i oc : Z) (mm : word -> option byte) (buf : list byte) (x5 x6 x7 x12 x14 x15 x16 x17 x26 x28 : word),
      e - i <= Z.of_nat k -> off + 1 <= i < e -> dinv i oc -> 0 <= oc -> lmem mm buf ->
      evt psegs KPOST (LST 0x13be0 x5 x6 x7 x12 (Z_to_bv 64 U) x14 x15 x16 x17 x26 x28 i oc mm).

  (* [comment removed for export] *)
  Lemma lmem_facts : forall mm buf, lmem mm buf ->
    bytes_at psegs mm CA bs /\ rw_cells psegs mm (bv_unsigned sp + -128) FRAME.
  Proof.
    intros mm buf (BUF & BL & MU & WM & MI). pose proof ctx_arith as A. destruct CTX as (L & BY2 & FR2 & _).
    try rewrite alloc_ceiling_eq in A. unfold W2 in MU. split.
    - eapply bytes_at_transport; [exact BY2| exact MU|]. cbn. lia.
    - eapply rw_cells_transport; [exact FR2| exact MU| exact WM|]. cbn. lia.
  Qed.

  Ltac pre := pose proof ctx_arith as ARITH; try rewrite alloc_ceiling_eq in ARITH; unfold W2, nalloc in *.

  (* [comment removed for export] *)
  Lemma exit_ok : forall i oc mm buf x5 x6 x7 x12 x14 x15 x16 x17 x26 x28,
    lmem mm buf -> off + 1 <= i <= e + 1 -> 0 <= oc -> oc + 1 <= nalloc ->
    evt psegs KPOST (LST 0x13ec4 x5 x6 x7 x12 (Z_to_bv 64 U) x14 x15 x16 x17 x26 x28 i oc mm).
  Proof. intros. apply evt_done. unfold KPOST. exists mm, buf, x5, x6, x7, x12, x12. do 8 eexists. repeat (split; [eassumption|]). left; reflexivity. Qed.

  Lemma exit_fail : forall i oc mm buf x5 x6 x7 x12 x13 x14 x15 x16 x17 x26 x28,
    lmem mm buf -> off + 1 <= i <= e + 1 -> 0 <= oc -> oc + 1 <= nalloc ->
    evt psegs KPOST (LST 0x13ee8 x5 x6 x7 x12 x13 x14 x15 x16 x17 x26 x28 i oc mm).
  Proof. intros. apply evt_done. unfold KPOST. do 15 eexists. repeat (split; [eassumption|]). right; reflexivity. Qed.

  Section Body.
    Variable k : nat.
    Hypothesis IH : forall k', (k' < k)%nat -> LOOPK k'.

    (* [comment removed for export] *)
    Lemma go_head : forall i oc mm buf x5 x6 x7 x12 x14 x15 x16 x17 x26 x28,
      e - i < Z.of_nat k -> off + 1 <= i < e -> dinv i oc -> 0 <= oc -> lmem mm buf ->
      evt psegs KPOST (LST 0x13be0 x5 x6 x7 x12 (Z_to_bv 64 U) x14 x15 x16 x17 x26 x28 i oc mm).
    Proof.
      intros. destruct k as [|k']; [lia|]. eapply (IH k'); [lia| lia| assumption| assumption| assumption| eassumption].
    Qed.

    (* [comment removed for export] *)
    Definition TESTPCS : list Z := [0x13c20; 0x13c38; 0x13c50; 0x13c90; 0x13ca8; 0x13cc0; 0x13e94].

    Lemma tests : forall pc i oc mm buf x5 x6 x7 x12 x14 x15 x16 x17 x26 x28,
      In pc TESTPCS ->
      e - i < Z.of_nat k -> off + 1 <= i <= e + 1 -> dinv i oc -> 0 <= oc -> lmem mm buf ->
      evt psegs KPOST (LST pc x5 x6 x7 x12 (Z_to_bv 64 U) x14 x15 x16 x17 x26 x28 i oc mm).
    Proof.
      intros until x28. intros HIn Hk Hi DI Hoc LM. pre. pose proof LM as (BUF & BL & MU & WM & MI).
      assert (EXIT : e <= i -> evt psegs KPOST (LST 0x13ec4 x5 x6 x7 x12 (Z_to_bv 64 U) x14 x15 x16 x17 x26 x28 i oc mm)).
      { intros He. eapply exit_ok; [exact LM| lia| lia| apply (dinv_end i oc DI); lia]. }
      unfold LST in *.
      destruct HIn as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]];
        (zstep; if_cases Kt; zify_cond Kt; [eapply go_head; [lia| lia| exact DI| exact Hoc| exact LM] | zstep; apply EXIT; lia]).
    Qed.

    (* [comment removed for export] *)
    Lemma first_byte_tail : forall i oc (len sl : Z) (v : word) mm buf x5 x6 x7 x15 x16 x17 x28,
      e - i <= Z.of_nat k -> off + 1 <= i -> i + sl <= e + 1 -> 1 <= sl -> 1 <= len -> 0 <= oc -> oc + len <= nalloc ->
      dinv (i + sl) (oc + len) -> lmem mm buf ->
      evt psegs KPOST (LST 0x13e88 x5 x6 x7 (Z_to_bv 64 sl) (Z_to_bv 64 U) (Z_to_bv 64 len) x15 x16 x17 v x28 i oc mm).
    Proof.
      intros until x28. intros Hk Hi Hsl Hsl1 Hlen Hoc ROOM DI LM. pose proof LM as (BUF & BL & MU & WM & MI). pre. unfold LST.
      pose proof (u8arr_store_ok psegs _ _ _ oc (Z_to_bv 64 (S + oc)) BUF ltac:(lia) eq_refl) as SOK.
      zstep. rewrite <- (Z_to_bv_bv_unsigned v), le1_lit.
      pose proof (u8arr_write psegs _ _ _ oc (Z_to_bv 8 (bv_unsigned v)) BUF ltac:(lia)) as BUF'.
      clear BUF. store_done. rename BUF' into BUF.
      zstep. zstep.
      replace (S + oc + len) with (S + (oc + len)) by lia. replace (CA + i + sl) with (CA + (i + sl)) by lia.
      eapply tests; [cbn; auto 10| lia| lia| exact DI| lia|].
      split; [exact BUF|]. split; [rewrite upd_length; exact BL|]. split; [exact MU|]. split; [exact WM| exact MI].
    Qed.

    (* [comment removed for export] *)
    Lemma encode_tail : forall i oc (len sl cp mark : Z) mm buf x5 x6 x7 x16 x17 x28,
      e - i <= Z.of_nat k -> off + 1 <= i -> i + sl <= e + 1 -> 1 <= sl -> 2 <= len <= 4 -> 0 <= cp < 2^32 -> 0 <= mark < 256 -> 0 <= oc -> oc + len <= nalloc ->
      dinv (i + sl) (oc + len) -> lmem mm buf ->
      evt psegs KPOST (LST 0x13e58 x5 x6 x7 (Z_to_bv 64 sl) (Z_to_bv 64 U) (Z_to_bv 64 len) (Z_to_bv 64 mark) x16 x17 (Z_to_bv 64 cp) x28 i oc mm).
    Proof.
      intros until x28. intros Hk Hi Hsl Hsl1 Hlen Hcp Hmk Hoc ROOM DI LM. pose proof LM as (BUF & BL & MU & WM & MI). pre. unfold LST.
      (* [comment removed for export] *)
      Ltac cont_byte BUF oc idx :=
        lazymatch goal with |- evt _ _ (MS ?R _ _ _ _ ?mm _) =>
          pose proof (u8arr_store_ok psegs mm S _ idx (Z_to_bv 64 (S + idx)) BUF ltac:(rewrite ?upd_length; lia) eq_refl) as SOK;
          zstep; zstep; zstep; zstep;
          replace (S + oc + (idx - oc)) with (S + idx) by lia;
          zstep; rewrite le1_lit;
          let BUF' := fresh "BUF" in
          lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ [Z_to_bv 8 ?v]) _) =>
            pose proof (u8arr_write psegs mm S _ idx (Z_to_bv 8 v) BUF ltac:(rewrite ?upd_length; lia)) as BUF' end;
          clear BUF; store_done; rename BUF' into BUF;
          zstep; zstep; zstep
        end.
      assert (HL : len = 2 \/ len = 3 \/ len = 4) by lia.
      destruct HL as [-> | [-> | ->]]; zstep; zstep; zstep.
      - cont_byte BUF oc (oc + 1). if_cases K1; zify_cond K1; [exfalso; lia|].
        zstep. eapply first_byte_tail; [lia| lia| lia| lia| lia| lia| unfold nalloc; lia| exact DI|].
        split; [exact BUF|]. split; [rewrite !upd_length; exact BL|]. split; [exact MU|]. split; [exact WM| exact MI].
      - cont_byte BUF oc (oc + 2). if_cases K1; zify_cond K1; [| exfalso; lia].
        cont_byte BUF oc (oc + 1). if_cases K2; zify_cond K2; [exfalso; lia|].
        zstep. eapply first_byte_tail; [lia| lia| lia| lia| lia| lia| unfold nalloc; lia| exact DI|].
        split; [exact BUF|]. split; [rewrite !upd_length; exact BL|]. split; [exact MU|]. split; [exact WM| exact MI].
      - cont_byte BUF oc (oc + 3). if_cases K1; zify_cond K1; [| exfalso; lia].
        cont_byte BUF oc (oc + 2). if_cases K2; zify_cond K2; [| exfalso; lia].
        cont_byte BUF oc (oc + 1). if_cases K3; zify_cond K3; [exfalso; lia|].
        zstep. eapply first_byte_tail; [lia| lia| lia| lia| lia| lia| unfold nalloc; lia| exact DI|].
        split; [exact BUF|]. split; [rewrite !upd_length; exact BL|]. split; [exact MU|]. split; [exact WM| exact MI].
    Qed.

    (* [comment removed for export] *)
    Definition ESCPCS : list Z := [0x13c10; 0x13c28; 0x13c40; 0x13c80; 0x13c98; 0x13cb0].

    Lemma esc_simple : forall pc i oc (c : Z) mm buf x5 x6 x7 x12 x15 x16 x17 x26 x28,
      In pc ESCPCS -> 0 <= c < 256 ->
      e - i <= Z.of_nat k -> off + 1 <= i -> i + 2 <= e + 1 -> 0 <= oc -> oc + 1 <= nalloc ->
      dinv (i + 2) (oc + 1) -> lmem mm buf ->
      evt psegs KPOST (LST pc x5 x6 x7 x12 (Z_to_bv 64 U) (Z_to_bv 64 c) x15 x16 x17 x26 x28 i oc mm).
    Proof.
      intros until x28. intros HIn Hc Hk Hi Hie Hoc ROOM DI LM. pose proof LM as (BUF & BL & MU & WM & MI). pre. unfold LST.
      destruct HIn as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]];
        (pose proof (u8arr_store_ok psegs _ _ _ oc (Z_to_bv 64 (S + oc)) BUF ltac:(lia) eq_refl) as SOK;
         zstep; rewrite le1_lit;
         let BUF' := fresh "BUF" in
         lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mx _ [Z_to_bv 8 ?v]) _) =>
           pose proof (u8arr_write psegs mx S _ oc (Z_to_bv 8 v) BUF ltac:(lia)) as BUF' end;
         clear BUF; store_done; rename BUF' into BUF;
         zstep; zstep; zstep;
         replace (S + oc + 1) with (S + (oc + 1)) by lia; replace (CA + i + 2) with (CA + (i + 2)) by lia;
         eapply tests; [cbn; auto 10| lia| lia| exact DI| lia|];
         split; [exact BUF|]; split; [rewrite upd_length; exact BL|]; split; [exact MU|]; split; [exact WM| exact MI]).
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
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.PImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.CJ_tree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.CJ_phex4.CJ_pbuf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.CJ_phex4.CJ_parse_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.CJ_phex4.CJ_parse_lemmas OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.CJ_phex4 CJ_pstring_A.
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
  ((c = 34 \/ c = 47 \/ c = 92) /\ jt_off c = 0x3608)
  \/ (c = 98 /\ jt_off c = 0x3620) \/ (c = 102 /\ jt_off c = 0x3638) \/ (c = 117 /\ jt_off c = 0x3650)
  \/ (c = 114 /\ jt_off c = 0x3678) \/ (c = 110 /\ jt_off c = 0x3690) \/ (c = 116 /\ jt_off c = 0x36a8)
  \/ jt_off c = 0x38e0.
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
  Notation KP := (KPOST sp gp tp F fc m2 CA off e sk S P U).
  Notation LM := (lmem m2 off e sk S).
  Notation DINV := (dinv blen off bs).
  Notation NA := (nalloc off e sk).
  Notation L z := (Z_to_bv 64 z) (only parsing).
  Notation LU := (Z_to_bv 64 U).

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
      Variables (i oc : Z) (mm : word -> option byte) (buf : list byte).
      Hypothesis Hk : e - i <= Z.of_nat k.
      Hypothesis Hi : off + 1 <= i.
      Hypothesis Hie : i + 6 <= e.
      Hypothesis BSL : at_ bs i = 92.
      Hypothesis DI : DINV i oc.
      Hypothesis Hoc : 0 <= oc.
      Hypothesis LMm : LM mm buf.

      Lemma bflag_i : bflag bs i = 1.
      Proof. unfold bflag. rewrite BSL. reflexivity. Qed.

      Lemma room4 : oc + 4 <= NA.
      Proof. ctx. eapply (dinv_room _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CTX i oc 4 DI); lia. Qed.

      Lemma dinv_u : forall c p, 6 <= c -> p + (c + 1) / 2 <= c -> DINV (i + c) (oc + p).
      Proof. intros c p Hc Hp. eapply dinv_step; [exact DI| lia| lia| rewrite bflag_i; exact Hp]. Qed.

      Ltac preU := ctx; lm LMm mm buf; pose proof room4 as ROOM; unfold W2, nalloc in *; unfold LST.

      Ltac fail_exit := eapply exit_fail; [exact LMm| lia| lia| unfold nalloc; lia].

      (* [comment removed for export] *)
      Lemma L_cls : forall FC x5 x6 x7 x12 x14 x15 x16 x17 x28, 0 <= FC < 2^16 ->
        evt psegs KP (LSTx 0x13d8c x5 x6 x7 x12 LU x14 x15 x16 x17 (Z_to_bv 64 FC) x28 i oc mm).
      Proof.
        intros until x28. intros HFC. preU.
        zstep. zstep. zstep. if_cases Ksur; zify_cond Ksur.
        - (* [comment removed for export] *)
          zstep. zstep. zstep. rewrite (bv_lts_small (CA + e - (CA + i + 6)) 6) by lia.
          if_cases Kl; zify_cond Kl; [fail_exit|].
          (nelim (text_read mm CA bs (i + 6) (Z_to_bv 64 (CA + i + 6)) BY ltac:(lia) ltac:(lia) ltac:(unfold wa; f_equal; lia)) 4%nat; intros c6 Hc6 RD6 _).
          zstep. zstep. if_cases K6; zify_cond K6; [fail_exit|].
          (nelim (text_read mm CA bs (i + 7) (Z_to_bv 64 (CA + i + 7)) BY ltac:(lia) ltac:(lia) ltac:(unfold wa; f_equal; lia)) 4%nat; intros c7 Hc7 RD7 _).
          zstep. zstep. zstep. if_cases K7; zify_cond K7; [fail_exit|].
          zstep. zstep. zstep. zstep.
          pose proof (bytes_at_window mm CA bs (i + 8) 4 BY ltac:(lia) ltac:(lia)) as B4.
          call hex4_spec.
          1:{ exact B4. } 1:{ apply firstn_skipn_length. lia. } 1:{ exact MI. } 1:{ f_equal. lia. }
          clear B4. intros.
          (* [comment removed for export] *)
          do 8 zstep. zstep. zstep. zstep. zstep. if_cases Kr; zify_cond Kr.
          { eapply exit_fail; [| lia| lia| unfold nalloc; lia].
            split; [eassumption|]. split; [exact BL|]. split; [assumption|]. split; assumption. }
          (* [comment removed for export] *)
          do 10 zstep.
          lazymatch goal with |- context [Z_to_bv 64 (Z.lor ?a (Z.land ?h 1023) + 65536)] =>
            assert (Ha : 0 <= a < 2^20) by (clear -HFC; rewrite ?Z.shiftr_div_pow2, ?Z.shiftl_mul_pow2 by lia; ml);
            assert (Hb : 0 <= Z.land h 1023 < 2^20)
              by (match goal with H1 : 0 <= h, H2 : h < _ |- _ => clear -H1 H2 end;
                  change 1023 with (2^10 - 1); rewrite zb_land_mask by lia; ml);
            pose proof (lor_bound _ _ 20 Ha Hb) as HL;
            assert (CPR : 0 <= Z.lor a (Z.land h 1023) + 65536 < 2^32) by (clear -HL; lia)
          end.
          eapply encode_tail; [exact CTX| exact IH| lia| lia| lia| lia| lia| exact CPR| lia| lia| unfold nalloc; lia| apply dinv_u; [lia| cbv; discriminate] |].
          split; [eassumption|]. split; [exact BL|]. split; [assumption|]. split; assumption.
        - zstep. zstep. if_cases Klow; zify_cond Klow; [fail_exit|].
          zstep. zstep. if_cases K1; zify_cond K1.
          + (* [comment removed for export] *) zstep. zstep. zstep.
            eapply first_byte_tail; [exact CTX| exact IH| lia| lia| lia| lia| lia| lia| unfold nalloc; lia| apply dinv_u; [lia| cbv; discriminate]| exact LMm].
          + zstep. rewrite (srliw_small FC 11) by lia. zstep. zstep. if_cases K2; zify_cond K2.
            * (* [comment removed for export] *)
              zstep. rewrite (srliw_small FC 16) by lia. zstep. if_cases K3; zify_cond K3; [exfalso; ml|].
              zstep. zstep. zstep.
              eapply encode_tail; [exact CTX| exact IH| lia| lia| lia| lia| lia| lia| lia| lia| unfold nalloc; lia| apply dinv_u; [lia| cbv; discriminate]| exact LMm].
            * zstep. zstep. zstep.
              eapply encode_tail; [exact CTX| exact IH| lia| lia| lia| lia| lia| lia| lia| lia| unfold nalloc; lia| apply dinv_u; [lia| cbv; discriminate]| exact LMm].
      Qed.

      (* [comment removed for export] *)
      Lemma L_inv : forall x5 x6 x7 x12 x14 x15 x16 x17 x26 x28,
        evt psegs KP (LSTx 0x13dc0 x5 x6 x7 x12 LU x14 x15 x16 x17 x26 x28 i oc mm).
      Proof.
        intros. preU. zstep. zstep. zstep. zstep.
        eapply first_byte_tail; [exact CTX| exact IH| lia| lia| lia| lia| lia| lia| unfold nalloc; lia| apply dinv_u; [lia| cbv; discriminate]| exact LMm].
      Qed.

      (* [comment removed for export] *)
      Section Hex.
        Variables (c0 c1 c2 c3 : byte).
        Hypothesis Hc0 : nth_error bs (Z.to_nat (i + 2)) = Some c0.
        Hypothesis Hc1 : nth_error bs (Z.to_nat (i + 3)) = Some c1.
        Hypothesis Hc2 : nth_error bs (Z.to_nat (i + 4)) = Some c2.
        Hypothesis Hc3 : nth_error bs (Z.to_nat (i + 5)) = Some c3.
        Notation K0 := (bv_unsigned c0). Notation K1 := (bv_unsigned c1).
        Notation K2 := (bv_unsigned c2). Notation K3 := (bv_unsigned c3).

        Ltac bytes := pose proof (byte_range c0); pose proof (byte_range c1); pose proof (byte_range c2); pose proof (byte_range c3).

        (* [comment removed for export] *)
        Lemma L_comb : forall (J0 J1 J2 J3 : Z) x26 x28,
          0 <= K0 + J0 <= 15 -> 0 <= K1 + J1 <= 15 -> 0 <= K2 + J2 <= 15 -> 0 <= K3 + J3 <= 15 ->
          evt psegs KP (LSTx 0x13d64 (L J3) (L J2) (L K3) (L K0) LU (L J1) (L J0) (L K1) (L K2) x26 x28 i oc mm).
        Proof.
          intros until x28. intros D0 D1 D2 D3. preU. bytes. do 10 zstep.
          lazymatch goal with |- context [Z_to_bv 64 (?a + (K3 + J3))] =>
            replace (Z_to_bv 64 (a + (K3 + J3))) with (Z_to_bv 64 ((K0 + J0) * 4096 + (K1 + J1) * 256 + (K2 + J2) * 16 + (K3 + J3)))
              by (apply Z_to_bv_eqm; clear -D0 D1 D2 D3; rewrite ?zb_shiftl_mul by lia; ml)
          end.
          apply L_cls. lia.
        Qed.

        (* [comment removed for export] *)
        Lemma L_c3 : forall (J0 J1 J2 : Z) x7 x26 x28,
          0 <= K0 + J0 <= 15 -> 0 <= K1 + J1 <= 15 -> 0 <= K2 + J2 <= 15 ->
          evt psegs KP (LSTx 0x13d38 (L (-48)) (L J2) x7 (L K0) LU (L J1) (L J0) (L K1) (L K2) x26 x28 i oc mm).
        Proof.
          intros until x28. intros D0 D1 D2. preU. bytes.
          (nelim (text_read mm CA bs (i + 5) (Z_to_bv 64 (CA + i + 5)) BY ltac:(lia) ltac:(lia) ltac:(unfold wa; f_equal; lia)) 4%nat; intros c3' Hc3' RD3 _).
          rewrite Hc3 in Hc3'. injection Hc3' as <-.
          zstep. zstep. zstep. if_cases Ka; zify_cond Ka; [apply L_comb; clear -D0 D1 D2 Ka H H0 H1 H2; ml|].
          zstep. zstep. if_cases Kb; zify_cond Kb.
          - zstep. zstep. zstep. if_cases Kc; zify_cond Kc; [apply L_inv|]. zstep. apply L_comb; clear -D0 D1 D2 Ka Kb Kc H H0 H1 H2; ml.
          - zstep. zstep. apply L_comb; clear -D0 D1 D2 Ka Kb H H0 H1 H2; ml.
        Qed.

        (* [comment removed for export] *)
        Lemma L_c2 : forall (J0 J1 : Z) x5 x6 x7 x17 x26 x28,
          0 <= K0 + J0 <= 15 -> 0 <= K1 + J1 <= 15 ->
          evt psegs KP (LSTx 0x13d04 x5 x6 x7 (L K0) LU (L J1) (L J0) (L K1) x17 x26 x28 i oc mm).
        Proof.
          intros until x28. intros D0 D1. preU. bytes.
          (nelim (text_read mm CA bs (i + 4) (Z_to_bv 64 (CA + i + 4)) BY ltac:(lia) ltac:(lia) ltac:(unfold wa; f_equal; lia)) 4%nat; intros c2' Hc2' RD2 _).
          rewrite Hc2 in Hc2'. injection Hc2' as <-.
          zstep. zstep. zstep. zstep. zstep. if_cases Ka; zify_cond Ka; [apply L_c3; clear -D0 D1 Ka H H0 H1 H2; ml|].
          zstep. zstep. if_cases Kb; zify_cond Kb.
          - zstep. zstep. zstep. if_cases Kc; zify_cond Kc; [apply L_inv|]. zstep. apply L_c3; clear -D0 D1 Ka Kb Kc H H0 H1 H2; ml.
          - zstep. zstep. apply L_c3; clear -D0 D1 Ka Kb H H0 H1 H2; ml.
        Qed.

        (* [comment removed for export] *)
        Lemma L_c1 : forall (J0 : Z) x5 x6 x7 x16 x17 x26 x28,
          0 <= K0 + J0 <= 15 ->
          evt psegs KP (LSTx 0x13cd8 x5 x6 x7 (L K0) LU (L (-48)) (L J0) x16 x17 x26 x28 i oc mm).
        Proof.
          intros until x28. intros D0. preU. bytes.
          (nelim (text_read mm CA bs (i + 3) (Z_to_bv 64 (CA + i + 3)) BY ltac:(lia) ltac:(lia) ltac:(unfold wa; f_equal; lia)) 4%nat; intros c1' Hc1' RD1 _).
          rewrite Hc1 in Hc1'. injection Hc1' as <-.
          zstep. zstep. zstep. if_cases Ka; zify_cond Ka; [apply L_c2; clear -D0 Ka H H0 H1 H2; ml|].
          zstep. zstep. if_cases Kb; zify_cond Kb.
          - zstep. zstep. zstep. if_cases Kc; zify_cond Kc; [apply L_inv|]. zstep. apply L_c2; clear -D0 Ka Kb Kc H H0 H1 H2; ml.
          - zstep. zstep. apply L_c2; clear -D0 Ka Kb H H0 H1 H2; ml.
        Qed.

        (* [comment removed for export] *)
        Lemma L_c0 : forall x5 x6 x7 x12 x14 x15 x16 x17 x26 x28,
          evt psegs KP (LSTx 0x13c5c x5 x6 x7 x12 LU x14 x15 x16 x17 x26 x28 i oc mm).
        Proof.
          intros. preU. bytes.
          (nelim (text_read mm CA bs (i + 2) (Z_to_bv 64 (CA + i + 2)) BY ltac:(lia) ltac:(lia) ltac:(unfold wa; f_equal; lia)) 4%nat; intros c0' Hc0' RD0 _).
          rewrite Hc0 in Hc0'. injection Hc0' as <-.
          zstep. zstep. zstep. zstep. zstep. if_cases Ka; zify_cond Ka; [apply L_c1; clear -Ka H H0 H1 H2; ml|].
          zstep. zstep. if_cases Kb; zify_cond Kb.
          - zstep. zstep. zstep. if_cases Kc; zify_cond Kc; [apply L_inv|]. zstep. apply L_c1; clear -Ka Kb Kc H H0 H1 H2; ml.
          - zstep. zstep. apply L_c1; clear -Ka Kb H H0 H1 H2; ml.
        Qed.
      End Hex.

      (* [comment removed for export] *)
      Lemma esc_u : forall x5 x6 x7 x14 x15 x16 x17 x26 x28,
        evt psegs KP (LSTx 0x13c58 x5 x6 x7 (Z_to_bv 64 (CA + e - (CA + i))) LU x14 x15 x16 x17 x26 x28 i oc mm).
      Proof.
        intros. preU.
        destruct (nth_error_lt_some bs (Z.to_nat (i + 2)) ltac:(lia)) as [c0 Hc0].
        destruct (nth_error_lt_some bs (Z.to_nat (i + 3)) ltac:(lia)) as [c1 Hc1].
        destruct (nth_error_lt_some bs (Z.to_nat (i + 4)) ltac:(lia)) as [c2 Hc2].
        destruct (nth_error_lt_some bs (Z.to_nat (i + 5)) ltac:(lia)) as [c3 Hc3].
        zstep. if_cases Kl; zify_cond Kl; [exfalso; lia|].
        eapply L_c0; eassumption.
      Qed.
    End U.

    (* [comment removed for export] *)
    (* [comment removed for export] *)
    Lemma head_k : LOOPK sp gp tp F fc m2 CA blen off e sk S P U bs k.
    Proof.
      unfold LOOPK. intros until x28. intros Hk Hi DI Hoc LMm. ctx. lm LMm mm buf. unfold W2, nalloc in *. unfold LST.
      pose proof (dinv_room _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CTX i oc 1 DI ltac:(lia) ltac:(lia)) as ROOM1. unfold nalloc in ROOM1.
      (nelim (text_read mm CA bs i (Z_to_bv 64 (CA + i)) BY ltac:(lia) ltac:(lia) eq_refl) 4%nat; intros b Hb RD Hat).
      pose proof (byte_range b) as Rb.
      zstep. zstep. if_cases Kbs; zify_cond Kbs.
      - (* [comment removed for export] *)
        pose proof (u8arr_store_ok psegs _ _ _ oc (Z_to_bv 64 (S + oc)) BUF ltac:(lia) eq_refl) as SOK.
        zstep. rewrite le1_lit.
        pose proof (u8arr_write psegs _ _ _ oc (Z_to_bv 8 (bv_unsigned b)) BUF ltac:(lia)) as BUF'.
        clear BUF. store_done. rename BUF' into BUF.
        assert (DI' : DINV (i + 1) (oc + 1)).
        { eapply dinv_step; [exact DI| lia| lia|]. unfold bflag. rewrite Hat. replace (bv_unsigned b =? 92) with false by (symmetry; apply Z.eqb_neq; exact Kbs). reflexivity. }
        zstep. zstep. zstep.
        replace (S + oc + 1) with (S + (oc + 1)) by lia. replace (CA + i + 1) with (CA + (i + 1)) by lia.
        if_cases Kt; zify_cond Kt.
        + eapply exit_ok; [| lia| lia| eapply (dinv_end _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CTX); [exact DI'| lia]].
          split; [exact BUF|]. split; [rewrite upd_length; exact BL|]. split; [exact MU|]. split; [exact WM| exact MI].
        + eapply go_head; [exact IH| lia| lia| exact DI'| lia|].
          split; [exact BUF|]. split; [rewrite upd_length; exact BL|]. split; [exact MU|]. split; [exact WM| exact MI].
      - (* [comment removed for export] *)
        assert (DI2 : DINV (i + 2) (oc + 1)).
        { eapply dinv_step; [exact DI| lia| lia|]. unfold bflag. rewrite Hat, Kbs. cbv. discriminate. }
        zstep. zstep. if_cases Kp.
        { (* [comment removed for export] *)
          eapply exit_fail; [exact LMm| lia| lia| unfold nalloc; lia]. }
        clear Kp.
        (nelim (text_read mm CA bs (i + 1) (Z_to_bv 64 (CA + i + 1)) BY ltac:(lia) ltac:(lia) ltac:(unfold wa; f_equal; lia)) 4%nat; intros c Hc RDc Hatc).
        pose proof (byte_range c) as Rc.
        zstep. zstep. zstep. if_cases Kr; zify_cond Kr.
        { eapply exit_fail; [exact LMm| lia| lia| unfold nalloc; lia]. }
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
            unfold JT. zstep. if_cases Kl; zify_cond Kl; [| exfalso; lia].
            eapply exit_fail; [exact LMm| lia| lia| unfold nalloc; lia].
          * eapply esc_u; [lia| lia| lia| rewrite Hat, Kbs; reflexivity| exact DI| lia| exact LMm].
        + eapply esc_simple; [exact CTX| exact IH| cbn; auto 10| lia| lia| lia| lia| lia| unfold nalloc; lia| exact DI2| exact LMm].
        + eapply esc_simple; [exact CTX| exact IH| cbn; auto 10| lia| lia| lia| lia| lia| unfold nalloc; lia| exact DI2| exact LMm].
        + eapply esc_simple; [exact CTX| exact IH| cbn; auto 10| lia| lia| lia| lia| lia| unfold nalloc; lia| exact DI2| exact LMm].
        + (* [comment removed for export] *) eapply exit_fail; [exact LMm| lia| lia| unfold nalloc; lia].
    Qed.
  End Body.

  Theorem dec_loop : forall k, LOOPK sp gp tp F fc m2 CA blen off e sk S P U bs k.
  Proof. intros k. induction k as [k IH] using lt_wf_ind. apply head_k. exact IH. Qed.
End PS.


End CeilWrap.
End CJ_pstring_B.

(* [comment removed for export] *)
From Stdlib Require Permutation.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require SCPS.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require FP.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require CJ_pvalue_A.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require LiaSplit.
Module CJ_pobject_ctx.
(* [comment removed for export] *)
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SCPS OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.FP.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.PImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.CJ_tree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.CJ_phex4.CJ_pbuf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.CJ_pvalue_A.CJ_delete OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.CJ_phex4.CJ_parse_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.CJ_phex4.CJ_parse_lemmas OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.CJ_pvalue_A.CJ_pvalue_lemmas OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.CJ_pvalue_A.CJ_pvalue_ctx OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.CJ_pvalue_A.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.
(* [comment removed for export] *)
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.LiaSplit.
Local Ltac lia ::= lia_cj.
Local Ltac flia ::= flia_cj.
Local Ltac simpl_sizes ::= simpl_sizes_cj.
Local Ltac simpl_arr_sizes ::= simpl_arr_sizes_cj.


(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Ltac fix_lit_store :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) =>
      change (Z_to_le_bytes 8 z) with (le8 (Z_to_bv 64 z)); mem_after_store
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?z)) _) =>
      change (Z_to_le_bytes 4 z) with (le4 (Z_to_bv 64 z)); mem_after_store
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ _) _) => mem_after_store
  | _ => idtac
  end.

Section PO.
  Variable HI : cj_heap_iface.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word).
  Variables (m : word -> option byte) (SPB : Z) (LB LR : list cblock) (U P CA blen off depth : Z) (bs : list byte) (D n lo : Z).
  Variables (nx : Z) (pv : word) (ty : Z) (p1 : word) (vi p2 vd : word) (ky : Z).
  Hypothesis PVC : pv_pure sp tp SPB LB LR U P CA blen off depth bs D n lo.

  Notation SP := (bv_unsigned sp).
  Notation POST := (POSTV HI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m SPB LR U P CA blen off depth bs D n lo nx pv ty p1 vi p2 vd ky).

  Definition SAVEDO : list cell := [C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  Definition CSTO (pc : Z) (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x28 x29 x30 x31 : word)
      (Fx : bvmap 5 word) (fcx : bv 32) (mm : word -> option byte) : machine_state :=
    MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 s9 s10 s11 x28 x29 x30 x31)
       Fx (Z_to_bv 64 pc) fcx None mm (seg_rom psegs).

  Definition MIDO (m1 : word -> option byte) (mo1 : Model) (LB1 : list cblock) (errv1 : word) : Prop :=
    LHEAP HI SPB LB1 m1 mo1 /\ bytes_at psegs m1 CA bs /\ CJST m1 /\ rw_cells psegs m1 PERRNO [C4 errv1]
    /\ mem_inv psegs m1 /\ stk psegs m1 lo (bv_unsigned sp + -80) /\ ppres LR (bv_unsigned sp) P m m1.

  Ltac lits := pose proof (pvc_lits _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ PVC) as (HPU & HDn & LEN & BLEN & CEIL & LO & PP & OFF & DEP & TP & URNG & DRNG & UD & SPR).
  Ltac alia := rewrite ?alloc_ceiling_eq; unfold DELETE_STACK, PARSE_STACK, PARSE_STRING_STACK; unfold RMALLOC_STACK; lia.
  Ltac zfeq := repeat (lazymatch goal with |- @eq Z _ _ => lia | |- _ => first [reflexivity | progress f_equal] end).
  Ltac eqcells H :=
    lazymatch goal with |- rw_cells _ _ _ ?cs =>
      lazymatch type of H with rw_cells _ _ _ ?cs' =>
        replace cs with cs'; [exact H| unfold pbuf_cells, node_cells, wz; zfeq] end end.

  (* [comment removed for export] *)
  Lemma epilogue_run_o : forall x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x28 x29 x30 x31 Fx fcx mm,
    rw_cells psegs mm (SP + -80) SAVEDO ->
    evt psegs (fun ms' => ms' = MS (mkR ra sp gp tp x5 x6 x7 s0 s1 x10 x11 x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                                 Fx (ret_pc ra) fcx None mm (seg_rom psegs))
        (CSTO 0x1420c x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x28 x29 x30 x31 Fx fcx mm).
  Proof.
    intros. lits. unfold CSTO, SAVEDO in *.
    do 12 zstep. apply evt_done. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma ret0_epi_o : forall (off1 depth1 : Z) m1 mo1 LB1 errv1 Fx fcx
      x1 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x28 x29 x30 x31,
    MIDO m1 mo1 LB1 errv1 -> Permutation ((U, 64) :: LR) LB1 ->
    rw_cells psegs m1 (SP + -80) SAVEDO ->
    pbuf_at m1 P CA blen off1 depth1 ->
    rw_cells psegs m1 U (node_cells nx pv 0 ty p1 0 vi p2 vd ky) ->
    Fagree F Fx -> frm0 fcx ->
    SCPS psegs POST (CSTO 0x1420c x1 x5 x6 x7 x8 x9 (Z_to_bv 64 0) x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x28 x29 x30 x31 Fx fcx m1) mo1.
  Proof.
    intros until x31. intros (HL & BY & CJ & ERR & MI & ST & PR) HP1 FR PB ND FA FRM. lits. unfold CSTO.
    eapply scps_step_evt; [eapply (lh_mok HI); exact HL|].
    eapply evt_cut; [apply epilogue_run_o; exact FR|]. intros ms' ->.
    unfold SAVEDO in FR. release_frame FR ST (bv_unsigned sp).
    apply evt_done. apply scps_done. unfold POSTV, parse_value_post.
    do 17 eexists. exists m1, 0, off1, depth1, LB1, [], errv1.
    split; [reflexivity|]. split; [reflexivity|]. split; [exact FA|]. split; [exact FRM|].
    split.
    { split; [exact HL|]. split; [exact HP1|].
      split; [apply (proj1 HDn)|]. split; [lia|]. split; [lia|]. split; [exact BY|]. split; [exact LEN|]. split; [exact BLEN|].
      split; [exact CJ|]. split; [exact ERR|]. split; [exact MI|]. split; [exact ST|]. split; [try rewrite alloc_ceiling_eq; exact CEIL|]. exact PP. }
    split; [exact PR|]. split; [exact PB|]. left. split; [reflexivity|]. split; [reflexivity| exact ND].
  Qed.

  Lemma ret0_o : forall (off1 depth1 : Z) m1 mo1 LB1 errv1 Fx fcx
      x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x28 x29 x30 x31,
    MIDO m1 mo1 LB1 errv1 -> Permutation ((U, 64) :: LR) LB1 ->
    rw_cells psegs m1 (SP + -80) SAVEDO ->
    pbuf_at m1 P CA blen off1 depth1 ->
    rw_cells psegs m1 U (node_cells nx pv 0 ty p1 0 vi p2 vd ky) ->
    Fagree F Fx -> frm0 fcx ->
    SCPS psegs POST (CSTO 0x14208 x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x28 x29 x30 x31 Fx fcx m1) mo1.
  Proof.
    intros until x31. intros MIDm HP1 FR PB ND FA FRM. pose proof MIDm as (HL & _). lits. unfold CSTO.
    eapply scps_step_evt; [eapply (lh_mok HI); exact HL|].
    zstep. apply evt_done. eapply ret0_epi_o; [exact MIDm| exact HP1| exact FR| exact PB| exact ND| exact FA| exact FRM].
  Qed.

  (* [comment removed for export] *)
  Notation dch := (dch depth).

  (* [comment removed for export] *)
  Lemma fail_o : forall (off1 depth1 head : Z) (X : list cblock) (dd : nat) m1 mo1 LBX errv1 Fx fcx
      x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x28 x29 x30 x31,
    MIDO m1 mo1 LBX errv1 -> Permutation ((U, 64) :: X ++ LR) LBX ->
    cj_chain CJ_ANY m1 dd head X -> Z.of_nat dd <= 1000 - depth ->
    rw_cells psegs m1 (SP + -80) SAVEDO ->
    pbuf_at m1 P CA blen off1 depth1 ->
    rw_cells psegs m1 U (node_cells nx pv 0 ty p1 0 vi p2 vd ky) ->
    Fagree F Fx -> frm0 fcx ->
    SCPS psegs POST (CSTO 0x14200 x1 x5 x6 x7 x8 (Z_to_bv 64 head) x10 x11 x12 x13 x14 x15 x16 x17
                         x18 x19 x20 x21 x22 x23 x24 x28 x29 x30 x31 Fx fcx m1) mo1.
  Proof.
    intros until x31. intros (HL & BY & CJ & ERR & MI & ST & PR) HPX CH Hdd FR PB ND FA FRM. lits. unfold CSTO.
    pose proof (pbuf_at_bound _ _ _ _ _ _ PB) as PBB. pose proof (rw_cells_bound psegs _ _ _ ND) as NDB. rewrite node_cells_size in NDB.
    assert (HPX' : Permutation (X ++ (U, 64) :: LR) LBX).
    { eapply Permutation_trans; [| exact HPX]. apply Permutation_sym. apply Permutation_middle. }
    eapply scps_step_evt; [eapply (lh_mok HI); exact HL|].
    zstep. zstep.
    replace (ret_pc (Z_to_bv 64 0x12720)) with (wz DELETE_ENTRY) by (unfold wz, DELETE_ENTRY; symmetry; apply ret_pc_even; [lia| reflexivity]).
    apply evt_done. cbv beta.
    eapply scps_bind.
    { pose proof (cjson_delete_spec HI dd) as DS. unfold delete_spec_at in DS.
      eapply DS with (lo := lo); clear DS; rewrite ?unsigned_lit by lia;
        first [ exact HL | exact CH | exact HPX' | exact CJ | exact ST | exact ERR | exact MI | exact TP | reflexivity | alia ]. }
    cbv beta. intros ms2 mo2 PO'.
    destruct PO' as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 & LR2
                    & -> & MI2 & ST2 & CJ2 & ERR2 & HL2 & HP2 & PR2).
    rewrite ?unsigned_lit in ST2, PR2 by lia.
    replace (ret_pc (Z_to_bv 64 0x14208)) with (Z_to_bv 64 0x14208) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    apply (cj_pres_rw_cells _ _ _ _ _ _ PR2) in FR; [| left; cbn; lia].
    pose proof PB as PB'. unfold pbuf_at in PB'. apply (cj_pres_rw_cells _ _ _ _ _ _ PR2) in PB'; [| left; cbn; lia].
    apply (cj_pres_rw_cells _ _ _ _ _ _ PR2) in ND; [| right; right; exists U, 64; split; [left; reflexivity| rewrite node_cells_size; lia]].
    apply (cj_pres_bytes_at _ _ _ _ _ _ PR2) in BY; [| right; right; exists D, n; split; [right; apply (proj1 HDn)| lia]].
    eapply ret0_o; [| apply Permutation_sym; exact HP2| exact FR| exact PB'| exact ND| exact FA| exact FRM].
    split; [exact HL2|]. split; [exact BY|]. split; [exact CJ2|]. split; [exact ERR2|]. split; [exact MI2|]. split; [exact ST2|].
    eapply ppres_trans; [exact PR|]. eapply ppres_of_cj_pres; [exact PR2| lia| intros b Hb; right; exact Hb].
  Qed.

  (* [comment removed for export] *)
  Lemma fail_o' : forall (off1 depth1 head : Z) (X : list cblock) (dd : nat) m1 mo1 LBX errv1 Fx fcx
      x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x22 x23 x24 x28 x29 x30 x31,
    MIDO m1 mo1 LBX errv1 -> Permutation ((U, 64) :: X ++ LR) LBX ->
    cj_chain CJ_ANY m1 dd head X -> Z.of_nat dd <= 1000 - depth ->
    rw_cells psegs m1 (SP + -80) SAVEDO ->
    pbuf_at m1 P CA blen off1 depth1 ->
    rw_cells psegs m1 U (node_cells nx pv 0 ty p1 0 vi p2 vd ky) ->
    Fagree F Fx -> frm0 fcx ->
    SCPS psegs POST (CSTO 0x141fc x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
                         x18 x19 x20 (Z_to_bv 64 head) x22 x23 x24 x28 x29 x30 x31 Fx fcx m1) mo1.
  Proof.
    intros until x31. intros MIDm HPX CH Hdd FR PB ND FA FRM. pose proof MIDm as (HL & _). lits. unfold CSTO.
    eapply scps_step_evt; [eapply (lh_mok HI); exact HL|].
    zstep. apply evt_done. eapply fail_o; [exact MIDm| exact HPX| exact CH| exact Hdd| exact FR| exact PB| exact ND| exact FA| exact FRM].
  Qed.

  (* [comment removed for export] *)
  Lemma obj_success : forall (o2 head : Z) (X : list cblock) m1 mo1 LBX errv1 Fx fcx
      x1 x5 x6 x7 x8 x9 x13 x14 x15 x16 x17 x18 x19 x20 x22 x23 x24 x28 x29 x30 x31,
    MIDO m1 mo1 LBX errv1 -> Permutation ((U, 64) :: X ++ LR) LBX ->
    cj_chain CJ_PRINTABLE m1 (S dch) head X -> depth <= 999 ->
    rw_cells psegs m1 (SP + -80) SAVEDO ->
    pbuf_at m1 P CA blen o2 depth ->
    rw_cells psegs m1 U (node_cells nx pv 0 ty p1 0 vi p2 vd ky) ->
    off <= o2 < blen ->
    Fagree F Fx -> frm0 fcx ->
    SCPS psegs POST (CSTO 0x13ffc x1 x5 x6 x7 x8 x9 (Z_to_bv 64 U) (Z_to_bv 64 P) (Z_to_bv 64 o2) x13 x14 x15 x16 x17
                         x18 x19 x20 (Z_to_bv 64 head) x22 x23 x24 x28 x29 x30 x31 Fx fcx m1) mo1.
  Proof.
    intros until x31. intros (HL & BY & CJ & ERR & MI & ST & PR) HPX CH Hd FR PB ND Ho FA FRM. lits. unfold CSTO.
    pose proof (pbuf_at_bound _ _ _ _ _ _ PB) as PBB. pose proof (rw_cells_bound psegs _ _ _ ND) as NDB. rewrite node_cells_size in NDB.
    unfold pbuf_at, pbuf_cells, wz in PB. unfold node_cells, wz in ND. unfold PERRNO in ERR. unfold SAVEDO in FR.
    assert (INU : In (U, 64) LBX) by (eapply perm_in_head; exact HPX).
    eapply scps_step_evt; [eapply (lh_mok HI); exact HL|].
    zstep. zstep.
    (* [comment removed for export] *)
    pose proof (munch_refl [(U + 16, U + 24)] m1) as MU. pose proof (wmono_refl psegs m1) as WM.
    zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
    assert (HL2 : LHEAP HI SPB LBX m2 mo1) by (eapply (lheap_block_store HI); [exact HL| exact INU| exact MU| exact WM| lia| lia]).
    assert (CJ2 : CJST m2) by (eapply (CJST_block_store HI); [exact HL| exact INU| exact CJ| exact MU| exact WM| lia| lia]).
    assert (PR2 : ppres LR SP P m m2).
    { eapply ppres_trans; [exact PR|]. eapply (ppres_block_store HI); [exact HL| exact HPX| intros b Hb; apply in_or_app; right; exact Hb| alia| exact MU| exact WM| lia| lia]. }
    assert (CH2 : cj_chain CJ_PRINTABLE m2 (S dch) head X).
    { eapply cj_chain_frame; [exact CH| exact MU| exact WM|].
      intros A k Hin. cbn. split; [|exact I].
      destruct (lheap_perm_apart HI _ _ _ _ _ _ _ HL HPX A k ltac:(apply in_or_app; left; exact Hin)) as [_ DJ]. lia. }
    clear MU WM HL CJ PR CH.
    (* [comment removed for export] *)
    pose proof (munch_refl [(U + 24, U + 28)] m2) as MU. pose proof (wmono_refl psegs m2) as WM.
    zstep. fix_lit_store.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
    assert (HL3 : LHEAP HI SPB LBX m3 mo1) by (eapply (lheap_block_store HI); [exact HL2| exact INU| exact MU| exact WM| lia| lia]).
    assert (CJ3 : CJST m3) by (eapply (CJST_block_store HI); [exact HL2| exact INU| exact CJ2| exact MU| exact WM| lia| lia]).
    assert (PR3 : ppres LR SP P m m3).
    { eapply ppres_trans; [exact PR2|]. eapply (ppres_block_store HI); [exact HL2| exact HPX| intros b Hb; apply in_or_app; right; exact Hb| alia| exact MU| exact WM| lia| lia]. }
    assert (CH3 : cj_chain CJ_PRINTABLE m3 (S dch) head X).
    { eapply cj_chain_frame; [exact CH2| exact MU| exact WM|].
      intros A k Hin. cbn. split; [|exact I].
      destruct (lheap_perm_apart HI _ _ _ _ _ _ _ HL2 HPX A k ltac:(apply in_or_app; left; exact Hin)) as [_ DJ]. lia. }
    clear MU WM HL2 CJ2 PR2 CH2.
    (* [comment removed for export] *)
    pose proof (munch_refl [(P + 16, P + 24)] m3) as MU. pose proof (wmono_refl psegs m3) as WM.
    zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m4 end.
    assert (HL4 : LHEAP HI SPB LBX m4 mo1) by (eapply (lheap_frame_store HI); [exact HL3| exact MU| exact WM| alia| alia]).
    assert (CJ4 : CJST m4) by (eapply CJST_high_store; [exact CJ3| exact MU| exact WM| alia]).
    assert (PR4 : ppres LR SP P m m4).
    { eapply ppres_trans; [exact PR3|]. eapply (ppres_pbuf_store HI); [exact HL3| intros b Hb; eapply Permutation_in; [exact HPX| right; apply in_or_app; right; exact Hb]| exact MU| exact WM| alia| alia| alia]. }
    assert (CH4 : cj_chain CJ_PRINTABLE m4 (S dch) head X).
    { eapply cj_chain_frame; [exact CH3| exact MU| exact WM|].
      intros A k Hin. cbn. split; [|exact I].
      pose proof (lh_block_range HI _ _ _ _ _ _ HL3 ltac:(eapply Permutation_in; [exact HPX| right; apply in_or_app; left; exact Hin])) as (_ & _ & _ & R4 & _).
      try rewrite alloc_ceiling_eq in R4. lia. }
    clear MU WM HL3 CJ3 PR3 CH3.
    zstep. zstep.
    eapply evt_cut; [apply epilogue_run_o; exact FR|]. intros ms' ->.
    release_frame FR ST (bv_unsigned sp).
    apply evt_done. apply scps_done. unfold POSTV, parse_value_post.
    do 17 eexists. exists m4, 1, (o2 + 1), depth, LBX, ([] ++ X), errv1.
    split; [reflexivity|]. split; [reflexivity|]. split; [exact FA|]. split; [exact FRM|].
    split.
    { split; [exact HL4|]. split; [exact HPX|].
      split; [apply (proj1 HDn)|]. split; [lia|]. split; [lia|]. split; [exact BY|]. split; [exact LEN|]. split; [exact BLEN|].
      split; [exact CJ4|]. split; [unfold PERRNO; exact ERR|]. split; [exact MI|]. split; [exact ST|]. split; [try rewrite alloc_ceiling_eq; exact CEIL|]. exact PP. }
    split; [exact PR4|].
    split. { unfold pbuf_at. eqcells PB. }
    right. split; [reflexivity|]. split; [reflexivity|]. split; [lia|].
    exists head, 64, 0. do 2 eexists. exists (S dch), [], X. split; [reflexivity|].
    split; [eqcells ND|]. split; [cbn; auto 10|]. split; [apply cj_str_null|]. split; [exact CH4|]. unfold CJ_pvalue_A.dch. lia.
  Qed.

  (* [comment removed for export] *)
  Definition obj_inv (m1 : word -> option byte) (head cur : Z) (X : list cblock) : Prop :=
    (head = 0 /\ X = [])
    \/ (head <> 0 /\ cur <> 0 /\ exists B1 Bv Bk Bc (chc tyc vsc kyc : Z) (pvc p1c vic p2c vdc : word),
          X = B1 ++ (cur, 64) :: Bv ++ Bk ++ Bc
          /\ cj_lseg CJ_PRINTABLE m1 dch head cur B1
          /\ rw_cells psegs m1 cur (node_cells 0 pvc chc tyc p1c vsc vic p2c vdc kyc)
          /\ CJ_PRINTABLE tyc /\ cj_str m1 vsc Bv /\ cj_str m1 kyc Bk /\ cj_chain CJ_PRINTABLE m1 dch chc Bc).

  Lemma obj_inv_chain : forall m1 head cur X, obj_inv m1 head cur X -> cj_chain CJ_PRINTABLE m1 (S dch) head X.
  Proof.
    intros m1 head cur X [[-> ->]|(NZ & NZc & B1 & Bv & Bk & Bc & chc & tyc & vsc & kyc & pvc & p1c & vic & p2c & vdc & -> & SEG & ND & TY & SV & SK & CH)].
    - apply cj_chain_nil.
    - apply cj_lseg_chain0. eapply cj_lseg_snoc; eauto. apply CJ_PRINTABLE_range. exact TY.
  Qed.

  Lemma obj_inv_magree : forall m1 m2 head cur X, obj_inv m1 head cur X -> magree (in_cblock X) m1 m2 -> obj_inv m2 head cur X.
  Proof.
    intros m1 m2 head cur X [[-> ->]|(NZ & NZc & B1 & Bv & Bk & Bc & chc & tyc & vsc & kyc & pvc & p1c & vic & p2c & vdc & -> & SEG & ND & TY & SV & SK & CH)] MA.
    - left. auto.
    - right. split; [exact NZ|]. split; [exact NZc|]. exists B1, Bv, Bk, Bc, chc, tyc, vsc, kyc, pvc, p1c, vic, p2c, vdc. split; [reflexivity|].
      split. { eapply cj_lseg_magree; [exact SEG| exact MA|]. intros a Ha. rewrite in_cblock_app. left. exact Ha. }
      split. { eapply rw_cells_magree; [exact MA| exact ND|]. rewrite node_cells_size. intros a Ha. rewrite in_cblock_app, in_cblock_cons. right. left. lia. }
      split; [exact TY|].
      split. { eapply cj_str_magree; [exact MA| exact SV|]. intros a Ha. rewrite in_cblock_app, in_cblock_cons, in_cblock_app. right. right. left. exact Ha. }
      split. { eapply cj_str_magree; [exact MA| exact SK|]. intros a Ha. rewrite in_cblock_app, in_cblock_cons, !in_cblock_app. right. right. right. left. exact Ha. }
      eapply cj_chain_magree; [exact CH| exact MA|]. intros a Ha. rewrite in_cblock_app, in_cblock_cons, !in_cblock_app. right. right. right. right. exact Ha.
  Qed.

  (* [comment removed for export] *)
  Variable nfuel : nat.
  Definition OLOOP (c : nat) : Prop :=
    forall (o head cur : Z) (X : list cblock) m1 mo1 LBX errv1 Fx fcx
           x1 x5 x6 x7 x8 x12 x13 x14 x15 x16 x17 x21 x22 x23 x28 x29 x30 x31,
      Z.of_nat c = blen - o -> off <= o < blen -> depth <= 999 ->
      MIDO m1 mo1 LBX errv1 -> Permutation ((U, 64) :: X ++ LR) LBX -> obj_inv m1 head cur X ->
      rw_cells psegs m1 (SP + -80) SAVEDO ->
      pbuf_at m1 P CA blen o (depth + 1) ->
      rw_cells psegs m1 U (node_cells nx pv 0 ty p1 0 vi p2 vd ky) ->
      Fagree F Fx -> frm0 fcx ->
      SCPS psegs POST (CSTO 0x14044 x1 x5 x6 x7 x8 (Z_to_bv 64 head) (Z_to_bv 64 U) (Z_to_bv 64 P) x12 x13 x14 x15 x16 x17
                           (Z_to_bv 64 32) (Z_to_bv 64 58) (Z_to_bv 64 44) x21 x22 x23 (Z_to_bv 64 cur) x28 x29 x30 x31 Fx fcx m1) mo1.
End PO.


End CeilWrap.
(* [comment removed for export] *)
Ltac fix_lit_store :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) =>
      change (Z_to_le_bytes 8 z) with (le8 (Z_to_bv 64 z)); mem_after_store
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?z)) _) =>
      change (Z_to_le_bytes 4 z) with (le4 (Z_to_bv 64 z)); mem_after_store
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ _) _) => mem_after_store
  | _ => idtac
  end.
End CJ_pobject_ctx.

(* [comment removed for export] *)
Module CJ_pobject_ws.
(* [comment removed for export] *)
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SCPS OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.FP.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.PImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.CJ_tree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.CJ_phex4.CJ_pbuf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.CJ_phex4.CJ_skipws OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.CJ_phex4.CJ_parse_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.CJ_phex4.CJ_parse_lemmas OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.CJ_pvalue_A.CJ_pvalue_lemmas OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.CJ_pvalue_A.CJ_pvalue_ctx CJ_pobject_ctx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.
(* [comment removed for export] *)
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.LiaSplit.
Local Ltac lia ::= lia_cj.
Local Ltac flia ::= flia_cj.
Local Ltac simpl_sizes ::= simpl_sizes_cj.
Local Ltac simpl_arr_sizes ::= simpl_arr_sizes_cj.


(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section WS.
  Variable HI : cj_heap_iface.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word).
  Variables (m : word -> option byte) (SPB : Z) (LB LR : list cblock) (U P CA blen off depth : Z) (bs : list byte) (D n lo : Z).
  Hypothesis PVC : pv_pure sp tp SPB LB LR U P CA blen off depth bs D n lo.

  Notation SP := (bv_unsigned sp).
  Notation CST := (CSTO sp gp tp s9 s10 s11).
  Ltac lits := pose proof (pvc_lits _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ PVC) as (HPU & HDn & LEN & BLEN & CEIL & LO & PP & OFF & DEP & TP & URNG & DRNG & UD & SPR).

  (* [comment removed for export] *)
  Definition ws_mem (m0 m2 : word -> option byte) (r d : Z) : Prop :=
    rw_cells psegs m2 P (pbuf_cells CA blen r d) /\ bytes_at psegs m2 CA bs /\ mem_inv psegs m2
    /\ munch [(P + 16, P + 24)] m0 m2 /\ wmono psegs m0 m2.

  Lemma fin_stop' : forall i b, 0 <= i < blen -> nth_error bs (Z.to_nat i) = Some b -> 32 < bv_unsigned b -> fin blen bs i = i.
  Proof. intros. lits. eapply (fin_stop P CA); eauto. lia. Qed.
  Lemma fin_ws' : forall i b, 0 <= i < blen -> nth_error bs (Z.to_nat i) = Some b -> bv_unsigned b <= 32 ->
    fin blen bs i = (if i + 1 =? blen then blen - 1 else fin blen bs (i + 1)).
  Proof. intros. lits. eapply (fin_ws P CA); eauto; lia. Qed.

  (* [comment removed for export] *)
  Ltac ws_body IH cnt i PB BY MI MU WM nex :=
    pose proof (bytes_at_bound _ _ _ _ BY) as BYB;
    pose proof (rw_cells_bound psegs _ _ _ PB) as PBB; rewrite pbuf_cells_size in PBB;
    unfold pbuf_cells, wz in PB; unfold CSTO;
    let b := fresh "b" in let Hn := fresh "Hn" in
    destruct (nth_error bs (Z.to_nat i)) as [b|] eqn:Hn; [| apply nth_error_None in Hn; lia];
    pose proof (u8ro_read psegs _ CA bs i b _ BY Hn ltac:(lia) eq_refl) as RD;
    pose proof (byte_range b) as Rb;
    zstep; zstep; zstep;
    let K := fresh "K" in let K2 := fresh "K2" in
    if_cases K; zify_cond K;
    [ (* [comment removed for export] *)
      zstep; if_cases K2; zify_cond K2; [| exfalso; lia];
      apply evt_done; nex;
      split; [rewrite ?(fin_stop' i b) by first [lia | exact Hn]; reflexivity|];
      split; [unfold pbuf_cells, wz; rewrite (fin_stop' i b) by first [lia | exact Hn]; exact PB|];
      split; [exact BY|]; split; [exact MI|]; split; [exact MU| exact WM]
    | (* [comment removed for export] *)
      zstep; zstep; zstep; if_cases K2; zify_cond K2;
      [ replace (CA + i + 1) with (CA + (i + 1)) by lia;
        rewrite (fin_ws' i b) by first [lia | exact Hn]; destruct (Z.eqb_spec (i + 1) blen); [exfalso; lia|];
        eapply (IH (cnt - 1)%nat ltac:(lia) (i + 1)); [lia| lia| unfold pbuf_cells, wz; exact PB| exact BY| exact MI| exact MU| exact WM]
      | zstep; zstep; zstep;
        rewrite (fin_ws' i b) by first [lia | exact Hn]; destruct (Z.eqb_spec (i + 1) blen); [| exfalso; lia];
        apply evt_done; nex;
        split; [try replace (blen - 1) with (blen + -1) by lia; reflexivity|];
        split; [unfold pbuf_cells, wz; replace (blen - 1) with (blen + -1) by lia; exact PB|];
        split; [exact BY|]; split; [exact MI|]; split; [exact MU| exact WM] ] ].

  (* [comment removed for export] *)
  Lemma ws1 : forall (cnt : nat) (i d : Z) (m0 m1 : word -> option byte) Fx fcx
      x1 x5 x6 x7 x8 x9 x10 x13 x17 x18 x19 x20 x21 x22 x23 x24 x28 x29 x30 x31,
    Z.of_nat cnt = blen - i -> 0 <= i < blen ->
    rw_cells psegs m1 P (pbuf_cells CA blen i d) -> bytes_at psegs m1 CA bs -> mem_inv psegs m1 ->
    munch [(P + 16, P + 24)] m0 m1 -> wmono psegs m0 m1 ->
    evt psegs (fun ms' => exists x17' m2,
                 ms' = CST 0x13fe0 x1 x5 x6 x7 x8 x9 x10 (Z_to_bv 64 P) (Z_to_bv 64 (fin blen bs i)) x13 (Z_to_bv 64 blen) (Z_to_bv 64 CA) (Z_to_bv 64 32) x17'
                          x18 x19 x20 x21 x22 x23 x24 x28 x29 x30 x31 Fx fcx m2
                 /\ ws_mem m0 m2 (fin blen bs i) d)
        (CST 0x13fb0 x1 x5 x6 x7 x8 x9 x10 (Z_to_bv 64 P) (Z_to_bv 64 i) x13 (Z_to_bv 64 blen) (Z_to_bv 64 CA) (Z_to_bv 64 32) x17
             x18 x19 x20 x21 x22 x23 x24 x28 x29 x30 x31 Fx fcx m1).
  Proof.
    induction cnt as [cnt IH] using lt_wf_ind.
    intros until x31. intros Hc Hi PB BY MI MU WM. unfold ws_mem. lits. ws_body IH cnt i PB BY MI MU WM ltac:(do 2 eexists).
  Qed.

  (* [comment removed for export] *)
  Lemma ws2 : forall (cnt : nat) (i d : Z) (m0 m1 : word -> option byte) Fx fcx
      x1 x5 x6 x7 x8 x9 x14 x15 x16 x17 x19 x20 x21 x22 x23 x24 x28 x29 x30 x31,
    Z.of_nat cnt = blen - i -> 0 <= i < blen ->
    rw_cells psegs m1 P (pbuf_cells CA blen i d) -> bytes_at psegs m1 CA bs -> mem_inv psegs m1 ->
    munch [(P + 16, P + 24)] m0 m1 -> wmono psegs m0 m1 ->
    evt psegs (fun ms' => exists x10' x12' x14' m2,
                 ms' = CST 0x140dc x1 x5 x6 x7 x8 x9 x10' (Z_to_bv 64 P) x12' (Z_to_bv 64 CA) x14' x15 x16 x17
                          (Z_to_bv 64 32) x19 x20 x21 x22 x23 x24 x28 x29 x30 x31 Fx fcx m2
                 /\ ws_mem m0 m2 (fin blen bs i) d)
        (CST 0x140b4 x1 x5 x6 x7 x8 x9 (Z_to_bv 64 blen) (Z_to_bv 64 P) (Z_to_bv 64 i) (Z_to_bv 64 CA) x14 x15 x16 x17
             (Z_to_bv 64 32) x19 x20 x21 x22 x23 x24 x28 x29 x30 x31 Fx fcx m1).
  Proof.
    induction cnt as [cnt IH] using lt_wf_ind.
    intros until x31. intros Hc Hi PB BY MI MU WM. unfold ws_mem. lits. ws_body IH cnt i PB BY MI MU WM ltac:(do 4 eexists).
  Qed.

  (* [comment removed for export] *)
  Lemma ws3 : forall (cnt : nat) (i d : Z) (m0 m1 : word -> option byte) Fx fcx
      x1 x5 x6 x7 x8 x9 x14 x15 x16 x17 x19 x20 x21 x22 x23 x24 x28 x29 x30 x31,
    Z.of_nat cnt = blen - i -> 0 <= i < blen ->
    rw_cells psegs m1 P (pbuf_cells CA blen i d) -> bytes_at psegs m1 CA bs -> mem_inv psegs m1 ->
    munch [(P + 16, P + 24)] m0 m1 -> wmono psegs m0 m1 ->
    evt psegs (fun ms' => exists x14' m2,
                 ms' = CST 0x14128 x1 x5 x6 x7 x8 x9 (Z_to_bv 64 blen) (Z_to_bv 64 P) (Z_to_bv 64 CA) (Z_to_bv 64 (fin blen bs i)) x14' x15 x16 x17
                          (Z_to_bv 64 32) x19 x20 x21 x22 x23 x24 x28 x29 x30 x31 Fx fcx m2
                 /\ ws_mem m0 m2 (fin blen bs i) d)
        (CST 0x14100 x1 x5 x6 x7 x8 x9 (Z_to_bv 64 blen) (Z_to_bv 64 P) (Z_to_bv 64 CA) (Z_to_bv 64 i) x14 x15 x16 x17
             (Z_to_bv 64 32) x19 x20 x21 x22 x23 x24 x28 x29 x30 x31 Fx fcx m1).
  Proof.
    induction cnt as [cnt IH] using lt_wf_ind.
    intros until x31. intros Hc Hi PB BY MI MU WM. unfold ws_mem. lits. ws_body IH cnt i PB BY MI MU WM ltac:(do 2 eexists).
  Qed.

  (* [comment removed for export] *)
  Lemma ws4 : forall (cnt : nat) (i d : Z) (m0 m1 : word -> option byte) Fx fcx
      x1 x5 x6 x7 x8 x9 x14 x15 x16 x17 x19 x20 x21 x22 x23 x24 x28 x29 x30 x31,
    Z.of_nat cnt = blen - i -> 0 <= i < blen ->
    rw_cells psegs m1 P (pbuf_cells CA blen i d) -> bytes_at psegs m1 CA bs -> mem_inv psegs m1 ->
    munch [(P + 16, P + 24)] m0 m1 -> wmono psegs m0 m1 ->
    evt psegs (fun ms' => exists x10' x13' x14' m2,
                 ms' = CST 0x14178 x1 x5 x6 x7 x8 x9 x10' (Z_to_bv 64 P) (Z_to_bv 64 CA) x13' x14' x15 x16 x17
                          (Z_to_bv 64 32) x19 x20 x21 x22 x23 x24 x28 x29 x30 x31 Fx fcx m2
                 /\ ws_mem m0 m2 (fin blen bs i) d)
        (CST 0x14150 x1 x5 x6 x7 x8 x9 (Z_to_bv 64 blen) (Z_to_bv 64 P) (Z_to_bv 64 CA) (Z_to_bv 64 i) x14 x15 x16 x17
             (Z_to_bv 64 32) x19 x20 x21 x22 x23 x24 x28 x29 x30 x31 Fx fcx m1).
  Proof.
    induction cnt as [cnt IH] using lt_wf_ind.
    intros until x31. intros Hc Hi PB BY MI MU WM. unfold ws_mem. lits. ws_body IH cnt i PB BY MI MU WM ltac:(do 4 eexists).
  Qed.

  (* [comment removed for export] *)
  Lemma ws5 : forall (cnt : nat) (i d : Z) (m0 m1 : word -> option byte) Fx fcx
      x1 x5 x6 x7 x8 x9 x10 x15 x16 x17 x19 x20 x21 x22 x23 x24 x28 x29 x30 x31,
    Z.of_nat cnt = blen - i -> 0 <= i < blen ->
    rw_cells psegs m1 P (pbuf_cells CA blen i d) -> bytes_at psegs m1 CA bs -> mem_inv psegs m1 ->
    munch [(P + 16, P + 24)] m0 m1 -> wmono psegs m0 m1 ->
    evt psegs (fun ms' => exists x15' m2,
                 ms' = CST 0x141c8 x1 x5 x6 x7 x8 x9 x10 (Z_to_bv 64 P) (Z_to_bv 64 (fin blen bs i)) (Z_to_bv 64 CA) (Z_to_bv 64 blen) x15' x16 x17
                          (Z_to_bv 64 32) x19 x20 x21 x22 x23 x24 x28 x29 x30 x31 Fx fcx m2
                 /\ ws_mem m0 m2 (fin blen bs i) d)
        (CST 0x141a0 x1 x5 x6 x7 x8 x9 x10 (Z_to_bv 64 P) (Z_to_bv 64 i) (Z_to_bv 64 CA) (Z_to_bv 64 blen) x15 x16 x17
             (Z_to_bv 64 32) x19 x20 x21 x22 x23 x24 x28 x29 x30 x31 Fx fcx m1).
  Proof.
    induction cnt as [cnt IH] using lt_wf_ind.
    intros until x31. intros Hc Hi PB BY MI MU WM. unfold ws_mem. lits. ws_body IH cnt i PB BY MI MU WM ltac:(do 2 eexists).
  Qed.
End WS.


End CeilWrap.
End CJ_pobject_ws.

(* [comment removed for export] *)
Module CJ_pstring_C.
(* [comment removed for export] *)
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SCPS.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.PImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.CJ_tree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.CJ_phex4.CJ_pbuf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.CJ_phex4.CJ_parse_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.CJ_phex4.CJ_parse_lemmas OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.CJ_phex4 CJ_pstring_A CJ_pstring_B.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.
(* [comment removed for export] *)
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.LiaSplit.
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
  Hypothesis PP : bv_unsigned sp <= P /\ P + 56 <= SPB /\ SPB < 2^62.
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
       F (Z_to_bv 64 pc) fc None mm (seg_rom psegs).

  (* [comment removed for export] *)
  Definition MID (m1 : word -> option byte) (mo1 : Model) (LB1 : list cblock) (errv1 : word) : Prop :=
    LHEAP HI SPB LB1 m1 mo1 /\ bytes_at psegs m1 CA bs /\ CJST m1 /\ rw_cells psegs m1 PERRNO [C4 errv1]
    /\ mem_inv psegs m1 /\ stk psegs m1 lo (SP + -128) /\ ppres LR SP P m m1.

  (* [comment removed for export] *)
  Ltac steq := unfold CST, LST, mkR; repeat (lazymatch goal with |- @eq Z _ _ => lia | |- _ => first [reflexivity | progress f_equal] end).
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
      x1 x5 x6 x7 x9 x10 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31,
    MID m1 mo1 LB1 errv1 -> Permutation ((U, 64) :: LR) LB1 ->
    rw_cells psegs m1 (SP + -128) (CB 24 junk :: SAVED) ->
    pbuf_at m1 P CA blen off1 depth ->
    rw_cells psegs m1 U (node_cells nx pv ch ty p1 vs vi p2 vd ky) ->
    off <= i <= blen ->
    SCPS psegs POST (CST 0x13ef4 x1 x5 x6 x7 (Z_to_bv 64 (CA + i)) x9 x10 (Z_to_bv 64 P) x12 x13 x14 x15 x16 x17
                         x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 m1) mo1.
  Proof.
    intros until x31. intros (HL & BY & CJ & ERR & MI & ST & PR) HP1 FR PB ND Hi. lits.
    pose proof (pbuf_at_bound _ _ _ _ _ _ PB) as PBB. unfold pbuf_at, pbuf_cells in PB. unfold CST. unfold PERRNO in ERR.
    pose proof (rw_cells_bound psegs _ _ _ ND) as NDB. rewrite node_cells_size in NDB. unfold node_cells, wz in ND. unfold wz in PB.
    eapply scps_step_evt; [eapply (lh_mok HI); exact HL|].
    pose proof (munch_refl [(P + 16, P + 24)] m1) as MU. pose proof (wmono_refl psegs m1) as WM.
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
      x1 x5 x6 x7 x9 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31,
    MID m1 mo1 LB2 errv1 -> Permutation ((U, 64) :: (S, k) :: LR) LB2 ->
    rw_cells psegs m1 (SP + -128) (CB 24 junk :: SAVED) ->
    pbuf_at m1 P CA blen off1 depth ->
    rw_cells psegs m1 U (node_cells nx pv ch ty p1 vs vi p2 vd ky) ->
    off <= i <= blen ->
    SCPS psegs POST (CST 0x13ee8 x1 x5 x6 x7 (Z_to_bv 64 (CA + i)) x9 (Z_to_bv 64 S) (Z_to_bv 64 P) x12 x13 x14 x15 x16 x17
                         x18 (Z_to_bv 64 P) x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 m1) mo1.
  Proof.
    intros until x31. intros (HL & BY & CJ & ERR & MI & ST & PR) HP2 FR PB ND Hi. lits.
    pose proof (pbuf_at_bound _ _ _ _ _ _ PB) as PBB. pose proof PB as PB0. unfold pbuf_at, pbuf_cells in PB. unfold CST. unfold PERRNO in ERR.
    unfold wz in PB.
    assert (HP2' : Permutation ((S, k) :: (U, 64) :: LR) LB2) by (eapply Permutation_trans; [apply perm_swap| exact HP2]).
    eapply scps_step_evt; [eapply (lh_mok HI); exact HL|].
    zstep. zstep.
    replace (ret_pc (Z_to_bv 64 PFREE)) with (wz PFREE) by (unfold wz, PFREE; symmetry; apply ret_pc_even; [lia| reflexivity]).
    apply evt_done. cbv beta.
    eapply scps_bind.
    { eapply (lh_free HI) with (lo := lo) (A := S) (n := k); rewrite ?unsigned_lit by lia;
        first [ exact HL | eapply perm_in_head; exact HP2' | exact ST | exact ERR | exact MI | exact TP | reflexivity | alia ]. }
    cbv beta. intros ms2 mo2 PO.
    (nelim PO 22%nat; intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m2 -> MI2 ST2 ERR2 PR2 HL2)
.
    rewrite ?unsigned_lit in ST2, PR2 by lia.
    replace (ret_pc (Z_to_bv 64 0x13ef0)) with (Z_to_bv 64 0x13ef0) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
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
      x1 x5 x6 x7 x8 x12 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31,
    MID m1 mo1 LB2 errv1 -> Permutation ((U, 64) :: (S, Z.of_nat (length buf)) :: LR) LB2 ->
    rw_cells psegs m1 (SP + -128) (CB 24 junk :: SAVED) ->
    pbuf_at m1 P CA blen off1 depth ->
    rw_cells psegs m1 U (node_cells nx pv ch ty p1 vs vi p2 vd ky) ->
    u8arr psegs m1 S buf -> 0 <= oc < Z.of_nat (length buf) ->
    cblock_range S (Z.of_nat (length buf)) -> (U + 64 <= S \/ S + Z.of_nat (length buf) <= U) ->
    (D + n <= S \/ S + Z.of_nat (length buf) <= D) ->
    off <= e < blen ->
    SCPS psegs POST (CST 0x13ec4 x1 x5 x6 x7 x8 (Z_to_bv 64 (CA + e)) (Z_to_bv 64 S) (Z_to_bv 64 P) x12 (Z_to_bv 64 U) x14 x15 x16 x17
                         x18 x19 x20 x21 x22 x23 x24 x25 x26 (Z_to_bv 64 (S + oc)) x28 x29 x30 x31 m1) mo1.
  Proof.
    intros until x31. intros (HL & BY & CJ & ERR & MI & ST & PR) HP2 FR PB ND BUF Hoc SRNG SU SD He.
    (nelim SRNG 5%nat; intros S1 S2 S3 S4 S5). lits.
    pose proof (pbuf_at_bound _ _ _ _ _ _ PB) as PBB. unfold pbuf_at, pbuf_cells, wz in PB. unfold CST. unfold PERRNO in ERR.
    pose proof (rw_cells_bound psegs _ _ _ ND) as NDB. rewrite node_cells_size in NDB. unfold node_cells, wz in ND.
    pose proof (bytes_at_bound _ _ _ _ BY) as BYB.
    assert (HP2' : Permutation ((S, Z.of_nat (length buf)) :: (U, 64) :: LR) LB2) by (eapply Permutation_trans; [apply perm_swap| exact HP2]).
    assert (INS : In (S, Z.of_nat (length buf)) LB2) by (eapply perm_in_head; exact HP2').
    assert (INU : In (U, 64) LB2) by (eapply perm_in_head; exact HP2).
    assert (INLR : forall b, In b LR -> In b LB2) by (intros b Hb; eapply Permutation_in; [exact HP2| right; right; exact Hb]).
    eapply scps_step_evt; [eapply (lh_mok HI); exact HL|].
    (* [comment removed for export] *)
    pose proof (munch_refl [(S + oc, S + oc + 1)] m1) as MU. pose proof (wmono_refl psegs m1) as WM.
    pose proof (u8arr_store_ok psegs _ _ _ oc (Z_to_bv 64 (S + oc)) BUF ltac:(lia) eq_refl) as SOK.
    zstep. rewrite le1_lit.
    pose proof (u8arr_write psegs _ _ _ oc (Z_to_bv 8 0) BUF ltac:(lia)) as BUF'. clear BUF. store_done. rename BUF' into BUF.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
    assert (HL2 : LHEAP HI SPB LB2 m2 mo1) by (eapply (lheap_block_store HI); [exact HL| exact INS| exact MU| exact WM| lia| lia]).
    assert (CJ2 : CJST m2) by (eapply (CJST_block_store HI); [exact HL| exact INS| exact CJ| exact MU| exact WM| lia| lia]).
    assert (PR2 : ppres LR SP P m m2).
    { eapply ppres_trans; [exact PR|]. eapply (ppres_block_store HI); [exact HL| exact HP2'| intros b Hb; right; exact Hb| alia| exact MU| exact WM| lia| lia]. }
    clear MU WM.
    (* [comment removed for export] *)
    pose proof (munch_refl [(U + 24, U + 40)] m2) as MU. pose proof (wmono_refl psegs m2) as WM.
    zstep. zstep. zstep. fix_lit_store. zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
    assert (HL3 : LHEAP HI SPB LB2 m3 mo1) by (eapply (lheap_block_store HI); [exact HL2| exact INU| exact MU| exact WM| lia| lia]).
    assert (CJ3 : CJST m3) by (eapply (CJST_block_store HI); [exact HL| exact INU| exact CJ2| exact MU| exact WM| lia| lia]).
    assert (PR3 : ppres LR SP P m m3).
    { eapply ppres_trans; [exact PR2|]. eapply (ppres_block_store HI); [exact HL| exact HP2| intros b Hb; right; exact Hb| alia| exact MU| exact WM| lia| lia]. }
    clear MU WM HL2 CJ2 PR2.
    (* [comment removed for export] *)
    pose proof (munch_refl [(P + 16, P + 24)] m3) as MU. pose proof (wmono_refl psegs m3) as WM.
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
    Variables (t1 t2 t3 t4 t5 t6 : word) (m1 : word -> option byte).
    Hypothesis BY1 : bytes_at psegs m1 CA bs.
    Hypothesis MI1 : mem_inv psegs m1.

    Definition L1 (pc : Z) (x5 x9 x15 x18 x22 : word) : machine_state :=
      MS (mkR ra (Z_to_bv 64 (SP + -128)) gp tp x5 t1 t2 (Z_to_bv 64 (CA + off + 1)) x9 (Z_to_bv 64 U) (Z_to_bv 64 P)
              (Z_to_bv 64 (CA + off)) (Z_to_bv 64 CA) (Z_to_bv 64 blen) x15 (Z_to_bv 64 92) (Z_to_bv 64 34)
              x18 s3 s4 x22 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
         F (Z_to_bv 64 pc) fc None m1 (seg_rom psegs).

    Definition Q1 : machine_state -> Prop := fun ms' =>
      (exists (q sk : Z) (x5 : word),
          ms' = L1 0x13b54 x5 (Z_to_bv 64 (CA + off + q)) (Z_to_bv 64 sk) (Z_to_bv 64 (CA + off + q)) (Z_to_bv 64 q)
          /\ ps_scan bs blen (Z.to_nat blen) (off + 1) 0 = Some (off + q, sk) /\ 1 <= q /\ off + q < blen /\ 0 <= sk <= q)
      \/ (exists x5 x9 x15 x18 x22, ms' = L1 0x13ef4 x5 x9 x15 x18 x22).

    Lemma loop1 : forall (cnt : nat) (q sk : Z) (x5 x18 : word),
      Z.of_nat cnt = blen - (off + q) -> 1 <= q -> off + q < blen -> 0 <= sk <= q - 1 ->
      (forall r, ps_scan bs blen (Z.to_nat (blen - (off + q))) (off + q) sk = Some r ->
                 ps_scan bs blen (Z.to_nat blen) (off + 1) 0 = Some r) ->
      evt psegs Q1 (L1 0x13b20 x5 (Z_to_bv 64 (CA + off + q)) (Z_to_bv 64 sk) x18 (Z_to_bv 64 q)).
    Proof.
      induction cnt as [cnt IH] using lt_wf_ind.
      intros q sk x5 x18 Hcnt Hq Hoq Hsk K. lits. pose proof (bytes_at_bound _ _ _ _ BY1) as BYB. unfold L1.
      (nelim (text_read m1 CA bs (off + q) (Z_to_bv 64 (CA + off + q)) BY1 ltac:(lia) ltac:(lia) ltac:(unfold wa; f_equal; lia)) 4%nat; intros b Hb RD Hat).
      pose proof (byte_range b) as Rb.
      assert (STEP : ps_scan bs blen (Z.to_nat (blen - (off + q))) (off + q) sk =
                     (if at_ bs (off + q) =? 34 then Some (off + q, sk)
                      else if at_ bs (off + q) =? 92 then (if blen <=? off + q + 1 then None else ps_scan bs blen (Z.to_nat (blen - (off + q + 1))) (off + q + 2) (sk + 1))
                      else ps_scan bs blen (Z.to_nat (blen - (off + q + 1))) (off + q + 1) sk)).
      { replace (Z.to_nat (blen - (off + q))) with (S (Z.to_nat (blen - (off + q + 1)))) by lia. apply ps_scan_step. lia. }
      rewrite Hat in STEP.
      zstep. zstep. zstep. if_cases Kbs; zify_cond Kbs.
      - (* [comment removed for export] *)
        zstep. if_cases Kq; zify_cond Kq.
        + (* [comment removed for export] *)
          apply evt_done. left. exists q, sk. eexists. split; [reflexivity|]. split; [| lia].
          apply K. rewrite STEP. rewrite (proj2 (Z.eqb_eq _ _) Kq). reflexivity.
        + zstep. zstep. zstep. zstep. if_cases Ke; zify_cond Ke.
          { apply evt_done. right. nexists 5%nat. reflexivity. }
          replace (CA + off + (q + 1)) with (CA + off + (q + 1)) by lia.
          eapply (IH (cnt - 1)%nat ltac:(lia) (q + 1) sk); [lia| lia| lia| lia|].
          intros r Hr. apply K. rewrite STEP. rewrite (proj2 (Z.eqb_neq _ _) Kq), (proj2 (Z.eqb_neq _ _) Kbs).
          replace (off + (q + 1)) with (off + q + 1) in Hr by lia. exact Hr.
      - (* [comment removed for export] *)
        zstep. zstep. zstep. zstep. if_cases Ke; zify_cond Ke.
        { apply evt_done. right. nexists 5%nat. reflexivity. }
        zstep. zstep. zstep. zstep. zstep. if_cases Ke2; zify_cond Ke2.
        + replace (CA + off + (q + 1 + 1)) with (CA + off + (q + 2)) by lia. replace (q + 1 + 1) with (q + 2) by lia.
          eapply (IH (cnt - 2)%nat ltac:(lia) (q + 2) (sk + 1)); [lia| lia| lia| lia|].
          intros r Hr. apply K. rewrite STEP, Kbs. change (92 =? 34) with false. change (92 =? 92) with true. cbv iota.
          replace (blen <=? off + q + 1) with false by (symmetry; apply Z.leb_gt; lia).
          eapply ps_scan_fuel; [| ]. { replace (off + q + 2) with (off + (q + 2)) by lia. exact Hr. } lia.
        + zstep. apply evt_done. right. nexists 5%nat. reflexivity.
    Qed.
  End Loop1.

  (* [comment removed for export] *)
  Theorem parse_string_main : forall (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (mo : Model) (errv : word),
    LHEAP HI SPB LB m mo -> bytes_at psegs m CA bs -> CJST m -> rw_cells psegs m PERRNO [C4 errv] -> mem_inv psegs m ->
    stk psegs m lo SP -> ppres LR SP P m m ->
    rw_cells psegs m U (node_cells nx pv ch ty p1 vs vi p2 vd ky) -> pbuf_at m P CA blen off depth ->
    a0 = wz U -> a1 = wz P ->
    SCPS psegs POST (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (wz PARSE_STRING) fc None m (seg_rom psegs)) mo.
  Proof.
    intros until errv. intros HL BY CJ ERR MI ST PR0 ND PB A0 A1. lits.
    unfold wz in A0, A1. subst a0 a1. unfold PARSE_STRING, wz.
    pose proof (pbuf_at_bound _ _ _ _ _ _ PB) as PBB. unfold pbuf_at, pbuf_cells, wz in PB.
    pose proof (rw_cells_bound psegs _ _ _ ND) as NDB. rewrite node_cells_size in NDB. unfold node_cells, wz in ND.
    pose proof (bytes_at_bound _ _ _ _ BY) as BYB. unfold PERRNO in ERR.
    assert (INLR : forall b, In b LR -> In b LB) by (intros b Hb; eapply Permutation_in; [exact HPU| right; exact Hb]).
    eapply scps_step_evt; [eapply (lh_mok HI); exact HL|].
    pose proof (munch_refl [(SP + -128, SP)] m) as MU. pose proof (wmono_refl psegs m) as WM.
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
    zstep. zstep. zstep.
    (nelim (text_read m1 CA bs off (Z_to_bv 64 (CA + off)) BY ltac:(lia) ltac:(lia) eq_refl) 4%nat; intros b0 Hb0 RD0 Hat0).
    pose proof (byte_range b0) as Rb0.
    zstep. zstep. zstep. zstep. if_cases K34; zify_cond K34.
    { replace (CA + off + 1) with (CA + (off + 1)) by lia. apply evt_done.
      eapply (fail0_tail (off + 1) off m1 mo LB errv); [mid HL1 BY CJ1 ERR MI ST PR1| exact HPU| exact FR| unfold pbuf_at; eqcells PB| eqcells ND| lia]. }
    zstep. zstep. zstep. if_cases Kend; zify_cond Kend.
    { replace (CA + off + 1) with (CA + (off + 1)) by lia. apply evt_done.
      eapply (fail0_tail (off + 1) off m1 mo LB errv); [mid HL1 BY CJ1 ERR MI ST PR1| exact HPU| exact FR| unfold pbuf_at; eqcells PB| eqcells ND| lia]. }
    do 6 zstep.
    (* [comment removed for export] *)
    eapply evt_cut.
    { eapply (loop1 t1 t2 t3 t4 t5 t6 m1 BY (Z.to_nat (blen - (off + 1))) 1 0); [lia| lia| lia| lia|].
      intros r Hr. eapply ps_scan_fuel; [exact Hr| lia]. }
    intros ms' [(q & sk & x5 & -> & SCAN & Hq & Hoq & Hsk) | (x5 & x9 & x15 & x18 & x22 & ->)]; unfold L1.
    2:{ replace (CA + off + 1) with (CA + (off + 1)) by lia. apply evt_done.
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
    replace (ret_pc (Z_to_bv 64 0x13b70)) with (Z_to_bv 64 0x13b70) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
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
      unfold wz. zstep. if_true. zstep. replace (CA + off + 1) with (CA + (off + 1)) by lia. apply evt_done.
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
      pose proof (u8arr_of_rw_cells psegs m2 A _ jk BLK) as BUF.
      eapply scps_step_evt; [eapply (lh_mok HI); exact HL2|].
      unfold wz. zstep. if_cases Kz; zify_cond Kz; [exfalso; lia|].
      zstep. zstep. zstep. zstep. zstep. rewrite (bv_lts_small q 2) by lia. if_cases Kq; zify_cond Kq.
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
        pose proof (munch_refl [(SP + -128, SP + -104)] m2) as MU. pose proof (wmono_refl psegs m2) as WM.
        do 13 zstep. zstep. fix_lit_store. zstep. zstep. fix_lit_store.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
        assert (HL3 : LHEAP HI SPB ((A, off + q - off - sk + 1) :: LB) m3 mo2)
          by (eapply (lheap_frame_store HI); [exact HL2| exact MU| exact WM| alia| alia]).
        assert (CJ3 : CJST m3) by (eapply CJST_high_store; [exact CJ1| exact MU| exact WM| alia]).
        assert (PR4 : ppres LR SP P m m3).
        { eapply ppres_trans; [exact PR3|]. eapply (ppres_frame_store HI); [exact HL2| | exact MU| exact WM| alia| lia].
          intros b Hb. right. apply INLR. exact Hb. }
        clear MU WM HL2 CJ1 PR3.
        zstep. zstep.
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
        (nelim KP 20%nat; intros mm buf x5' x6 x7 x12 x13 x14 x15 x16 x17 x26 x28 i oc LMm Hi Hoc ROOM [-> | ->]);
          unfold LST; (nelimp LMm 5%nat; intros BUFm BLm MUm WMm MIm); unfold W2, nalloc in MUm, BLm, ROOM.
        * (* [comment removed for export] *)
          apply evt_done.
          pose proof FR as FRm. trc FRm MUm WMm.
          apply (rw_cells_merge psegs mm (SP + -128) [] [CB 8 j0; C8 (Z_to_bv 64 0xdc00); C8 (Z_to_bv 64 0xd800)] SAVED) in FRm. cbn [app cells_size cells_bytes csize cbytes Nat.add] in FRm.
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
          apply (rw_cells_merge psegs mm (SP + -128) [] [CB 8 j0; C8 (Z_to_bv 64 0xdc00); C8 (Z_to_bv 64 0xd800)] SAVED) in FRm. cbn [app cells_size cells_bytes csize cbytes Nat.add] in FRm.
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
End CJ_pstring_C.

(* [comment removed for export] *)
Module CJ_pobject_L.
(* [comment removed for export] *)
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SCPS OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.FP.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.PImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.CJ_tree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.CJ_phex4.CJ_pbuf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.CJ_phex4.CJ_skipws OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.CJ_pvalue_A.CJ_delete OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.CJ_phex4.CJ_parse_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.CJ_phex4.CJ_parse_lemmas CJ_pstring_C OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.CJ_pvalue_A.CJ_pvalue_lemmas OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.CJ_pvalue_A.CJ_pvalue_ctx OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.CJ_pvalue_A CJ_pobject_ctx CJ_pobject_ws.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.
(* [comment removed for export] *)
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.LiaSplit.
Local Ltac lia ::= lia_cj.
Local Ltac flia ::= flia_cj.
Local Ltac simpl_sizes ::= simpl_sizes_cj.
Local Ltac simpl_arr_sizes ::= simpl_arr_sizes_cj.


(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section POL.
  Variable HI : cj_heap_iface.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word).
  Variables (m : word -> option byte) (SPB : Z) (LB LR : list cblock) (U P CA blen off depth : Z) (bs : list byte) (D n lo : Z).
  Variables (nx : Z) (pv : word) (ty : Z) (p1 : word) (vi p2 vd : word) (ky : Z).
  Hypothesis PVC : pv_pure sp tp SPB LB LR U P CA blen off depth bs D n lo.
  Variable nfuel : nat.
  Hypothesis FUEL : blen - off <= Z.of_nat nfuel.
  Hypothesis PVREC : forall nf, (nf < nfuel)%nat -> parse_value_at HI nf.

  Notation SP := (bv_unsigned sp).
  Notation CST := (CSTO sp gp tp s9 s10 s11).
  Notation POST := (POSTV HI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m SPB LR U P CA blen off depth bs D n lo nx pv ty p1 vi p2 vd ky).
  Notation MID := (MIDO HI sp m SPB LR P CA bs lo).
  Notation SAVED := (SAVEDO ra s0 s1 s2 s3 s4 s5 s6 s7 s8).
  Notation dch := (dch depth).
  Notation OLOOPc := (OLOOP HI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m SPB LR U P CA blen off depth bs D n lo nx pv ty p1 vi p2 vd ky).
  Notation WSM := (ws_mem P CA blen bs).

  Ltac zfeq := repeat (lazymatch goal with |- @eq Z _ _ => lia | |- _ => first [reflexivity | progress f_equal] end).
  Ltac eqcells H :=
    lazymatch goal with |- rw_cells _ _ _ ?cs =>
      lazymatch type of H with rw_cells _ _ _ ?cs' =>
        replace cs with cs'; [exact H| unfold pbuf_cells, node_cells, wz; zfeq] end end.
  Ltac dj := cbn [disjoint_from cells_size csize Nat.add length];
             repeat match goal with H : length ?l = _ |- context [length ?l] => rewrite H end;
             first [lia | split; [lia| exact I]].
  Ltac trc H MU WM := first [ eapply rw_cells_transport in H; [| exact MU| exact WM| dj]
                            | eapply bytes_at_transport in H; [| exact MU| dj]
                            | eapply u8arr_transport in H; [| exact MU| exact WM| dj]
                            | eapply stk_transport_disjoint in H; [| exact MU| exact WM| dj] ].
  Ltac lits := (nelimp (pvc_lits _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ PVC) 14%nat; intros HPU HDn LEN BLEN CEIL LO PP OFF DEP TP URNG DRNG UD SPR).
  Ltac alia := rewrite ?alloc_ceiling_eq; unfold DELETE_STACK, PARSE_STACK, PARSE_STRING_STACK; unfold RMALLOC_STACK; lia.

  (* [comment removed for export] *)
  Lemma zero_node_run_o : forall x1 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x28 x29 x30 x31 Fx fcx mm (A : Z) (junk : list byte),
    rw_cells psegs mm A [CB 64 junk] -> mem_inv psegs mm ->
    evt psegs (fun ms' => exists mm',
                 ms' = CST 0x14084 x1 x5 x6 x7 (Z_to_bv 64 A) x9 (Z_to_bv 64 A) x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 (Z_to_bv 64 A) x22 x23 x24 x28 x29 x30 x31 Fx fcx mm'
                 /\ munch [(A, A + 64)] mm mm' /\ wmono psegs mm mm' /\ mem_inv psegs mm'
                 /\ rw_cells psegs mm' A (node_cells 0 (wz 0) 0 0 (wz 0) 0 (wz 0) (wz 0) (wz 0) 0))
        (CST 0x1405c x1 x5 x6 x7 x8 x9 (Z_to_bv 64 A) x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x28 x29 x30 x31 Fx fcx mm).
  Proof using PVC nfuel.
    intros until junk. intros BLK MI. lits. unfold CSTO.
    pose proof (rw_cells_bound psegs _ _ _ BLK) as AB. cbn [cells_size csize Nat.add] in AB.
    pose proof (munch_refl [(A, A + 64)] mm) as MU. pose proof (wmono_refl psegs mm) as WM.
    zstep. do 8 (zstep; fix_lit_store). zstep.
    apply evt_done. eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
    apply zero_node_cells. exact BLK.
  Qed.

  (* [comment removed for export] *)
  Lemma close_o : forall (o3 hd A : Z) (Xall : list cblock) m1 mo1 LBX errv1 Fx fcx
      x1 x5 x6 x7 x9 x13 x14 x15 x16 x17 x18 x19 x20 x22 x23 x24 x28 x29 x30 x31,
    MID m1 mo1 LBX errv1 -> Permutation ((U, 64) :: Xall ++ LR) LBX ->
    hd <> 0 -> cj_chain CJ_PRINTABLE m1 (S dch) hd Xall -> depth <= 999 ->
    rw_cells psegs m1 (SP + -80) SAVED ->
    pbuf_at m1 P CA blen o3 (depth + 1) ->
    rw_cells psegs m1 U (node_cells nx pv 0 ty p1 0 vi p2 vd ky) ->
    off <= o3 < blen -> Fagree F Fx -> frm0 fcx ->
    SCPS psegs POST (CST 0x141e8 x1 x5 x6 x7 (Z_to_bv 64 A) x9 (Z_to_bv 64 U) (Z_to_bv 64 P) (Z_to_bv 64 o3) x13 x14 x15 x16 x17
                         x18 x19 x20 (Z_to_bv 64 hd) x22 x23 x24 x28 x29 x30 x31 Fx fcx m1) mo1.
  Proof.
    intros until x31. intros MIDm HPX HNZ CH Hd FR PB ND Ho FA FRM. lits. unfold CSTO.
    (nelimp MIDm 7%nat; intros HL BY CJ ERR MI ST PR).
    pose proof (pbuf_at_bound _ _ _ _ _ _ PB) as PBB. pose proof (rw_cells_bound psegs _ _ _ ND) as NDB. rewrite node_cells_size in NDB.
    pose proof (bytes_at_bound _ _ _ _ BY) as BYB.
    assert (INLR : forall b, In b LR -> In b LBX) by (intros b Hb; eapply Permutation_in; [exact HPX| right; apply in_or_app; right; exact Hb]).
    assert (INX : forall b, In b Xall -> In b LBX) by (intros b Hb; eapply Permutation_in; [exact HPX| right; apply in_or_app; left; exact Hb]).
    unfold pbuf_at, pbuf_cells, wz in PB. unfold node_cells, wz in ND. unfold PERRNO in ERR. unfold SAVEDO in FR.
    eapply scps_step_evt; [eapply (lh_mok HI); exact HL|].
    (* [comment removed for export] *)
    pose proof (munch_refl [(P + 24, P + 32)] m1) as MU. pose proof (wmono_refl psegs m1) as WM.
    zstep. zstep. zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
    assert (HL2 : LHEAP HI SPB LBX m2 mo1) by (eapply (lheap_frame_store HI); [exact HL| exact MU| exact WM| alia| alia]).
    assert (CJ2 : CJST m2) by (eapply CJST_high_store; [exact CJ| exact MU| exact WM| alia]).
    assert (PR2 : ppres LR SP P m m2).
    { eapply ppres_trans; [exact PR|]. eapply (ppres_pbuf_store HI); [exact HL| exact INLR| exact MU| exact WM| alia| alia| alia]. }
    assert (CH2 : cj_chain CJ_PRINTABLE m2 (S dch) hd Xall).
    { eapply cj_chain_frame; [exact CH| exact MU| exact WM|].
      intros A' k Hin. cbn. split; [|exact I].
      (nelimp (lh_block_range HI _ _ _ _ _ _ HL (INX _ Hin)) 5%nat; intros _ _ _ R4 _). try rewrite alloc_ceiling_eq in R4. lia. }
    clear MU WM HL CJ PR CH.
    (* [comment removed for export] *)
    (nelim (cj_chain_cons_inv _ _ _ _ _ CH2 HNZ) 24%nat; intros d0 nxh pvh chh tyh p1h vsh vih p2h vdh kyh Bvh Bkh Bch Bnh Ed NDH TYH HTh SVh SKh CHCh CHNh EX)
.
    rewrite EX in HPX, INX.
    assert (HPh : Permutation ((hd, 64) :: (Bvh ++ Bkh ++ Bch ++ Bnh) ++ (U, 64) :: LR) LBX).
    { eapply Permutation_trans; [apply perm_pick_head| exact HPX]. }
    (nelimp (lh_block_range HI _ _ _ _ _ _ HL2 (perm_in_head _ _ _ HPh)) 5%nat; intros H1 H2 H3 H4 H5).
    try rewrite alloc_ceiling_eq in H4. unfold PIMG_LO, PIMG_HI in H5.
    destruct (lheap_perm_apart HI _ _ _ _ _ _ _ HL2 HPh U 64 ltac:(apply in_or_app; right; left; reflexivity)) as [_ HU].
    destruct (lheap_perm_apart HI _ _ _ _ _ _ _ HL2 HPh D n ltac:(apply in_or_app; right; right; exact (proj1 HDn))) as [_ HD].
    unfold node_cells, wz in NDH.
    pose proof (munch_refl [(hd + 8, hd + 16)] m2) as MU. pose proof (wmono_refl psegs m2) as WM.
    zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
    assert (INH : In (hd, 64) LBX) by (eapply perm_in_head; exact HPh).
    assert (HL3 : LHEAP HI SPB LBX m3 mo1) by (eapply (lheap_block_store HI); [exact HL2| exact INH| exact MU| exact WM| lia| lia]).
    assert (CJ3 : CJST m3) by (eapply (CJST_block_store HI); [exact HL2| exact INH| exact CJ2| exact MU| exact WM| lia| lia]).
    assert (PR3 : ppres LR SP P m m3).
    { eapply ppres_trans; [exact PR2|]. eapply (ppres_block_store HI); [exact HL2| exact HPh| intros b Hb; apply in_or_app; right; right; exact Hb| alia| exact MU| exact WM| lia| lia]. }
    assert (CH3 : cj_chain CJ_PRINTABLE m3 (S dch) hd Xall).
    { rewrite EX, Ed. eapply (cj_chain_relink HI); [exact HL2| exact HPh| exact HNZ| exact TYH| exact HTh| exact SVh| exact SKh| exact CHCh| exact CHNh| exact MU| exact WM| eqcells NDH]. }
    clear MU WM HL2 CJ2 PR2 CH2 SVh SKh CHCh CHNh. rewrite <- EX in HPX.
    zstep. apply evt_done.
    eapply obj_success; [exact PVC| | exact HPX| exact CH3| exact Hd| exact FR| unfold pbuf_at; eqcells PB| eqcells ND| exact Ho| exact FA| exact FRM].
    split; [exact HL3|]. split; [exact BY|]. split; [exact CJ3|]. split; [unfold PERRNO; exact ERR|]. split; [exact MI|]. split; [exact ST| exact PR3].
  Qed.

  Notation FAILO := (fail_o' HI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m SPB LB LR U P CA blen off depth bs D n lo nx pv ty p1 vi p2 vd ky PVC).

  (* [comment removed for export] *)
  Lemma after_ws5 : forall (c : nat), (forall c', (c' < c)%nat -> OLOOPc c') ->
    forall (o o3 hd A : Z) (pvA : word) (chA tyA vsA kyA : Z) (viA vdA : word) (X Bv Bk Bc : list cblock) m1 mo1 LBX errv1 Fx fcx
           x1 x5 x6 x7 x9 x15 x16 x17 x21' x24 x28 x29 x30 x31,
      Z.of_nat c = blen - o -> off <= o -> o < o3 <= blen -> depth <= 999 ->
      MID m1 mo1 LBX errv1 -> Permutation ((U, 64) :: (X ++ (A, 64) :: Bv ++ Bk ++ Bc) ++ LR) LBX ->
      hd <> 0 -> A <> 0 -> cj_lseg CJ_PRINTABLE m1 dch hd A X ->
      rw_cells psegs m1 A (node_cells 0 pvA chA tyA (wz 0) vsA viA (wz 0) vdA kyA) ->
      CJ_PRINTABLE tyA -> cj_str m1 vsA Bv -> cj_str m1 kyA Bk -> cj_chain CJ_PRINTABLE m1 dch chA Bc ->
      rw_cells psegs m1 (SP + -80) SAVED ->
      pbuf_at m1 P CA blen o3 (depth + 1) ->
      rw_cells psegs m1 U (node_cells nx pv 0 ty p1 0 vi p2 vd ky) ->
      Fagree F Fx -> frm0 fcx -> x21' = Z_to_bv 64 hd ->
      SCPS psegs POST (CST 0x141c8 x1 x5 x6 x7 (Z_to_bv 64 A) x9 (Z_to_bv 64 U) (Z_to_bv 64 P) (Z_to_bv 64 o3) (Z_to_bv 64 CA) (Z_to_bv 64 blen) x15 x16 x17
                           (Z_to_bv 64 32) (Z_to_bv 64 58) (Z_to_bv 64 44) x21' (Z_to_bv 64 U) (Z_to_bv 64 P) x24 x28 x29 x30 x31 Fx fcx m1) mo1.
  Proof.
    intros c IHc. intros until x31. intros Hc Ho Ho3 Hd MIDm HPX HNZ ANZ SEG NDA HTA SVA SKA CHA FR PB ND FA FRM ->. lits. unfold CSTO.
    (nelimp MIDm 7%nat; intros HL BY CJ ERR MI ST PR).
    pose proof (pbuf_at_bound _ _ _ _ _ _ PB) as PBB. pose proof (bytes_at_bound _ _ _ _ BY) as BYB.
    assert (CH : cj_chain CJ_PRINTABLE m1 (S dch) hd (X ++ (A, 64) :: Bv ++ Bk ++ Bc)).
    { eapply cj_lseg_chain; [exact SEG|]. eapply cj_chain_one; [exact ANZ| exact NDA| apply CJ_PRINTABLE_range; exact HTA| exact HTA| exact SVA| exact SKA| exact CHA]. }
    assert (FAIL : forall x12' x13' x14' x9' x24',
      SCPS psegs POST (CST 0x141fc x1 x5 x6 x7 (Z_to_bv 64 A) x9' (Z_to_bv 64 U) (Z_to_bv 64 P) x12' x13' x14' x15 x16 x17
                           (Z_to_bv 64 32) (Z_to_bv 64 58) (Z_to_bv 64 44) (Z_to_bv 64 hd) (Z_to_bv 64 U) (Z_to_bv 64 P) x24' x28 x29 x30 x31 Fx fcx m1) mo1).
    { intros. eapply FAILO; [exact MIDm| exact HPX| eapply cj_chain_any; exact CH| unfold dch; lia| exact FR| exact PB| exact ND| exact FA| exact FRM]. }
    unfold CSTO in FAIL.
    pose proof PB as PB'. unfold pbuf_at, pbuf_cells, wz in PB.
    eapply scps_step_evt; [eapply (lh_mok HI); exact HL|].
    zstep. if_cases Kend; zify_cond Kend.
    { (* [comment removed for export] *) apply evt_done. apply FAIL. }
    zstep.
    (nelim (text_read m1 CA bs o3 (Z_to_bv 64 (CA + o3)) BY ltac:(lia) ltac:(lia) eq_refl) 4%nat; intros b Hb RD Hat).
    pose proof (byte_range b) as Rb.
    zstep. zstep. zstep. zstep. if_cases Kc; zify_cond Kc.
    { (* [comment removed for export] *)
      apply evt_done. pose proof (IHc (Z.to_nat (blen - o3)) ltac:(lia)) as IH. unfold OLOOP, CSTO in IH.
      eapply (IH o3 hd A (X ++ (A, 64) :: Bv ++ Bk ++ Bc) m1 mo1 LBX errv1); [lia| lia| exact Hd| exact MIDm| exact HPX| | exact FR| exact PB'| exact ND| exact FA| exact FRM].
      right. split; [exact HNZ|]. split; [exact ANZ|]. exists X, Bv, Bk, Bc, chA, tyA, vsA, kyA, pvA, (wz 0), viA, (wz 0), vdA.
      split; [reflexivity|]. split; [exact SEG|]. split; [exact NDA|]. split; [exact HTA|]. split; [exact SVA|]. split; [exact SKA| exact CHA]. }
    zstep. zstep. if_cases K125; zify_cond K125.
    { (* [comment removed for export] *) apply evt_done. apply FAIL. }
    (* [comment removed for export] *)
    apply evt_done. eapply close_o; [exact MIDm| exact HPX| exact HNZ| exact CH| exact Hd| exact FR| exact PB'| exact ND| lia| exact FA| exact FRM].
  Qed.

  (* [comment removed for export] *)
  Lemma after_val : forall (c : nat), (forall c', (c' < c)%nat -> OLOOPc c') ->
    forall (o o4 hd A KS k : Z) (pvA : word) (X : list cblock) (r off5 depth5 : Z) (X5 : list cblock) m1 mo1 LBX errv1 Fx fcx
           x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x21' x24 x28 x29 x30 x31,
      Z.of_nat c = blen - o -> off <= o -> o < o4 -> depth <= 999 ->
      MID m1 mo1 LBX errv1 -> Permutation ((A, 64) :: X5 ++ (KS, k) :: (U, 64) :: X ++ LR) LBX ->
      hd <> 0 -> A <> 0 -> cj_lseg CJ_PRINTABLE m1 dch hd A X -> cj_str m1 KS [(KS, k)] ->
      rw_cells psegs m1 (SP + -80) SAVED ->
      pbuf_at m1 P CA blen off5 depth5 ->
      rw_cells psegs m1 U (node_cells nx pv 0 ty p1 0 vi p2 vd ky) ->
      Fagree F Fx -> frm0 fcx -> x21' = Z_to_bv 64 hd ->
      ( (r = 0 /\ X5 = [] /\ rw_cells psegs m1 A (node_cells 0 pvA 0 16 (wz 0) 0 (wz 0) (wz 0) (wz 0) KS))
        \/ (r = 1 /\ depth5 = depth + 1 /\ o4 <= off5 <= blen
             /\ exists (ch ty' vs : Z) (vi' vd' : word) (dc : nat) (Bv Bc : list cblock),
                  X5 = Bv ++ Bc
                  /\ rw_cells psegs m1 A (node_cells 0 pvA ch ty' (wz 0) vs vi' (wz 0) vd' KS)
                  /\ CJ_PRINTABLE ty' /\ cj_str m1 vs Bv /\ cj_chain CJ_PRINTABLE m1 dc ch Bc
                  /\ Z.of_nat dc + (depth + 1) <= 1000) ) ->
      SCPS psegs POST (CST 0x14180 x1 x5 x6 x7 (Z_to_bv 64 A) x9 (Z_to_bv 64 r) x11 x12 x13 x14 x15 x16 x17
                           (Z_to_bv 64 32) (Z_to_bv 64 58) (Z_to_bv 64 44) x21' (Z_to_bv 64 U) (Z_to_bv 64 P) x24 x28 x29 x30 x31 Fx fcx m1) mo1.
  Proof.
    intros c IHc. intros until x31. intros Hc Ho Ho4 Hd MIDm HPX HNZ ANZ SEG SK FR PB ND FA FRM -> RES. lits. unfold CSTO.
    (nelimp MIDm 7%nat; intros HL BY CJ ERR MI ST PR).
    pose proof (pbuf_at_bound _ _ _ _ _ _ PB) as PBB. pose proof (bytes_at_bound _ _ _ _ BY) as BYB.
    pose proof (rw_cells_bound psegs _ _ _ ND) as NDB. rewrite node_cells_size in NDB.
    assert (INLR : forall b, In b LR -> In b LBX) by (intros b Hb; eapply Permutation_in; [exact HPX| right; apply in_or_app; right; right; right; apply in_or_app; right; exact Hb]).
    assert (INX : forall b, In b X -> In b LBX) by (intros b Hb; eapply Permutation_in; [exact HPX| right; apply in_or_app; right; right; right; apply in_or_app; left; exact Hb]).
    assert (INS : In (KS, k) LBX) by (eapply Permutation_in; [exact HPX| right; apply in_or_app; right; left; reflexivity]).
    (nelimp (lh_block_range HI _ _ _ _ _ _ HL (perm_in_head _ _ _ HPX)) 5%nat; intros A1 A2 A3 A4 A5).
    try rewrite alloc_ceiling_eq in A4. unfold PIMG_LO, PIMG_HI in A5.
    eapply scps_step_evt; [eapply (lh_mok HI); exact HL|].
    destruct RES as [(-> & -> & NDA) | (-> & -> & Ho5 & chA & tyA & vsA & viA & vdA & dc & Bv & Bc & -> & NDA & HTA & SVA & CHA & Hdc)].
    - (* [comment removed for export] *)
      zstep. if_true. apply evt_done.
      assert (CH : cj_chain CJ_ANY m1 (S dch) hd (X ++ (A, 64) :: [] ++ [(KS, k)] ++ [])).
      { eapply cj_lseg_chain; [eapply cj_lseg_mono; [exact SEG| intros; exact I| lia]|].
        eapply cj_chain_one; [exact ANZ| exact NDA| lia| exact I| apply cj_str_null| exact SK| apply cj_chain_nil]. }
      cbn [app] in CH.
      eapply FAILO; [exact MIDm| | exact CH| unfold dch; lia| exact FR| exact PB| exact ND| exact FA| exact FRM].
      eapply Permutation_trans; [| exact HPX]. apply Permutation_sym. apply (perm_new_done (U, 64) (A, 64) [(KS, k)] X LR).
    - (* [comment removed for export] *)
      pose proof (rw_cells_bound psegs _ _ _ NDA) as NAB. rewrite node_cells_size in NAB.
      assert (HPX' : Permutation ((U, 64) :: (X ++ (A, 64) :: Bv ++ [(KS, k)] ++ Bc) ++ LR) LBX).
      { eapply Permutation_trans; [| exact HPX]. apply Permutation_sym. apply perm_new_done_k. }
      pose proof PB as PB'. unfold pbuf_at, pbuf_cells, wz in PB. unfold node_cells, wz in ND. unfold node_cells, wz in NDA. unfold PERRNO in ERR. unfold SAVEDO in FR.
      assert (CHA' : cj_chain CJ_PRINTABLE m1 dch chA Bc) by (eapply cj_chain_mono_d; [exact CHA| unfold dch; lia]).
      clear CHA.
      zstep. if_false. zstep. zstep. zstep. zstep. zstep. zstep. if_cases KC; zify_cond KC; [exfalso; lia|].
      zstep. if_cases Kend; zify_cond Kend.
      + (* [comment removed for export] *)
        apply evt_done.
        eapply (after_ws5 c IHc o off5 hd A pvA chA tyA vsA KS viA vdA X Bv [(KS, k)] Bc m1 mo1 LBX errv1);
          [exact Hc| exact Ho| lia| exact Hd| exact MIDm| exact HPX'| exact HNZ| exact ANZ| exact SEG| eqcells NDA| exact HTA| exact SVA| exact SK| exact CHA'| exact FR| exact PB'| eqcells ND| exact FA| exact FRM| reflexivity].
      + pose proof (fin_off0 blen off5 bs LEN ltac:(lia)) as FO.
        eapply evt_cut.
        { eapply (ws5 sp gp tp s9 s10 s11 SPB LB LR U P CA blen off depth bs D n lo PVC (Z.to_nat (blen - off5)) off5 (depth + 1) m1 m1);
            [lia| lia| exact PB| exact BY| exact MI| apply munch_refl| apply wmono_refl]. }
        intros ms' nelH_; (nelim nelH_ 8%nat; intros x15' m2 -> PB2 BY2 MI2 MU2 WM2). unfold CSTO. rewrite <- FO in PB2 |- *.
        trc FR MU2 WM2. trc ND MU2 WM2. trc NDA MU2 WM2. trc ERR MU2 WM2. trc ST MU2 WM2.
        assert (HL2 : LHEAP HI SPB LBX m2 mo1) by (eapply (lheap_frame_store HI); [exact HL| exact MU2| exact WM2| alia| alia]).
        assert (CJ2 : CJST m2) by (eapply CJST_high_store; [exact CJ| exact MU2| exact WM2| alia]).
        assert (PR2 : ppres LR SP P m m2).
        { eapply ppres_trans; [exact PR|]. eapply (ppres_pbuf_store HI); [exact HL| exact INLR| exact MU2| exact WM2| alia| alia| alia]. }
        assert (BLK : forall A' k', In (A', k') LBX -> disjoint_from [(P + 16, P + 24)] A' k').
        { intros A' k' Hin. cbn. split; [|exact I].
          (nelimp (lh_block_range HI _ _ _ _ _ _ HL Hin) 5%nat; intros _ _ _ R4 _). try rewrite alloc_ceiling_eq in R4. lia. }
        assert (SEG2 : cj_lseg CJ_PRINTABLE m2 dch hd A X).
        { eapply cj_lseg_frame; [exact SEG| exact MU2| exact WM2|]. intros A' k' Hin. apply BLK. apply INX. exact Hin. }
        assert (SK2 : cj_str m2 KS [(KS, k)]).
        { eapply cj_str_frame; [exact SK| exact MU2| exact WM2|]. intros A' k' [E|[]]. inversion E; subst. apply BLK. exact INS. }
        assert (SVA2 : cj_str m2 vsA Bv).
        { eapply cj_str_frame; [exact SVA| exact MU2| exact WM2|]. intros A' k' Hin. apply BLK.
          eapply Permutation_in; [exact HPX|]. right. apply in_or_app. left. apply in_or_app. left. exact Hin. }
        assert (CHA2 : cj_chain CJ_PRINTABLE m2 dch chA Bc).
        { eapply cj_chain_frame; [exact CHA'| exact MU2| exact WM2|]. intros A' k' Hin. apply BLK.
          eapply Permutation_in; [exact HPX|]. right. apply in_or_app. left. apply in_or_app. right. exact Hin. }
        pose proof (skipws_off_range bs off5 ltac:(rewrite LEN; lia)) as OR. rewrite LEN in OR.
        apply evt_done.
        eapply (after_ws5 c IHc o (skipws_off bs off5) hd A pvA chA tyA vsA KS viA vdA X Bv [(KS, k)] Bc m2 mo1 LBX errv1);
          [exact Hc| exact Ho| lia| exact Hd| | exact HPX'| exact HNZ| exact ANZ| exact SEG2| eqcells NDA| exact HTA| exact SVA2| exact SK2| exact CHA2| exact FR| unfold pbuf_at; exact PB2| eqcells ND| exact FA| exact FRM| reflexivity].
        split; [exact HL2|]. split; [exact BY2|]. split; [exact CJ2|]. split; [unfold PERRNO; exact ERR|]. split; [exact MI2|]. split; [exact ST| exact PR2].
  Qed.

  (* [comment removed for export] *)
  Lemma key_done : forall (c : nat), (forall c', (c' < c)%nat -> OLOOPc c') ->
    forall (o o3 hd A KS k : Z) (pvA : word) (X : list cblock) m1 mo1 LBX errv1 Fx fcx
           x1 x5 x6 x7 x9 x14 x15 x16 x17 x21' x24 x28 x29 x30 x31,
      Z.of_nat c = blen - o -> off <= o -> o < o3 <= blen -> depth <= 999 ->
      MID m1 mo1 LBX errv1 -> Permutation ((A, 64) :: (KS, k) :: (U, 64) :: X ++ LR) LBX ->
      hd <> 0 -> A <> 0 -> cj_lseg CJ_PRINTABLE m1 dch hd A X -> cj_str m1 KS [(KS, k)] ->
      rw_cells psegs m1 A (node_cells 0 pvA 0 16 (wz 0) KS (wz 0) (wz 0) (wz 0) 0) ->
      rw_cells psegs m1 (SP + -80) SAVED ->
      pbuf_at m1 P CA blen o3 (depth + 1) ->
      rw_cells psegs m1 U (node_cells nx pv 0 ty p1 0 vi p2 vd ky) ->
      Fagree F Fx -> frm0 fcx -> x21' = Z_to_bv 64 hd ->
      SCPS psegs POST (CST 0x14128 x1 x5 x6 x7 (Z_to_bv 64 A) x9 (Z_to_bv 64 blen) (Z_to_bv 64 P) (Z_to_bv 64 CA) (Z_to_bv 64 o3) x14 x15 x16 x17
                           (Z_to_bv 64 32) (Z_to_bv 64 58) (Z_to_bv 64 44) x21' (Z_to_bv 64 U) (Z_to_bv 64 P) x24 x28 x29 x30 x31 Fx fcx m1) mo1.
  Proof.
    intros c IHc. intros until x31. intros Hc Ho Ho3 Hd MIDm HPX HNZ ANZ SEG SK NDA FR PB ND FA FRM ->. lits. unfold CSTO.
    (nelimp MIDm 7%nat; intros HL BY CJ ERR MI ST PR).
    pose proof (pbuf_at_bound _ _ _ _ _ _ PB) as PBB. pose proof (bytes_at_bound _ _ _ _ BY) as BYB.
    pose proof (rw_cells_bound psegs _ _ _ ND) as NDB. rewrite node_cells_size in NDB.
    pose proof (rw_cells_bound psegs _ _ _ NDA) as NAB. rewrite node_cells_size in NAB.
    assert (INLR : forall b, In b LR -> In b LBX) by (intros b Hb; eapply Permutation_in; [exact HPX| right; right; right; apply in_or_app; right; exact Hb]).
    assert (INX : forall b, In b X -> In b LBX) by (intros b Hb; eapply Permutation_in; [exact HPX| right; right; right; apply in_or_app; left; exact Hb]).
    assert (INS : In (KS, k) LBX) by (eapply Permutation_in; [exact HPX| right; left; reflexivity]).
    (nelimp (lh_block_range HI _ _ _ _ _ _ HL (perm_in_head _ _ _ HPX)) 5%nat; intros A1 A2 A3 A4 A5).
    try rewrite alloc_ceiling_eq in A4. unfold PIMG_LO, PIMG_HI in A5.
    assert (APART : forall A' n', In (A', n') ((KS, k) :: (U, 64) :: X ++ LR) -> A' <> A /\ (A' + n' <= A \/ A + 64 <= A')).
    { intros A' n' Hin. eapply (lheap_perm_apart HI); [exact HL| exact HPX| exact Hin]. }
    destruct (APART U 64 ltac:(right; left; reflexivity)) as [_ AU]. destruct (APART D n ltac:(right; right; apply in_or_app; right; exact (proj1 HDn))) as [_ AD].
    pose proof PB as PB'. unfold pbuf_at, pbuf_cells, wz in PB. unfold node_cells, wz in ND. unfold node_cells, wz in NDA. unfold PERRNO in ERR. unfold SAVEDO in FR.
    eapply scps_step_evt; [eapply (lh_mok HI); exact HL|].
    (* [comment removed for export] *)
    pose proof (munch_refl [(A + 32, A + 64)] m1) as MU. pose proof (wmono_refl psegs m1) as WM.
    zstep. zstep. fix_lit_store. zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
    assert (HL2 : LHEAP HI SPB LBX m2 mo1) by (eapply (lheap_block_store HI); [exact HL| eapply perm_in_head; exact HPX| exact MU| exact WM| lia| lia]).
    assert (CJ2 : CJST m2) by (eapply (CJST_block_store HI); [exact HL| eapply perm_in_head; exact HPX| exact CJ| exact MU| exact WM| lia| lia]).
    assert (PR2 : ppres LR SP P m m2).
    { eapply ppres_trans; [exact PR|]. eapply (ppres_block_store HI); [exact HL| exact HPX| intros b Hb; right; right; apply in_or_app; right; exact Hb| alia| exact MU| exact WM| lia| lia]. }
    assert (DJ : forall A' n', In (A', n') ((KS, k) :: (U, 64) :: X ++ LR) -> disjoint_from [(A + 32, A + 64)] A' n').
    { intros A' n' Hin. cbn. split; [|exact I]. destruct (APART A' n' Hin). lia. }
    assert (SEG2 : cj_lseg CJ_PRINTABLE m2 dch hd A X).
    { eapply cj_lseg_frame; [exact SEG| exact MU| exact WM|]. intros A' n' Hin. apply DJ. right; right. apply in_or_app. left. exact Hin. }
    assert (SK2 : cj_str m2 KS [(KS, k)]).
    { eapply cj_str_frame; [exact SK| exact MU| exact WM|]. intros A' n' [E|[]]. inversion E; subst. apply DJ. left. reflexivity. }
    assert (MID2 : MID m2 mo1 LBX errv1).
    { split; [exact HL2|]. split; [exact BY|]. split; [exact CJ2|]. split; [unfold PERRNO; exact ERR|]. split; [exact MI|]. split; [exact ST| exact PR2]. }
    clear MU WM HL CJ PR SEG SK DJ MIDm.
    (* [comment removed for export] *)
    assert (CH : cj_chain CJ_ANY m2 (S dch) hd (X ++ (A, 64) :: [] ++ [(KS, k)] ++ [])).
    { eapply cj_lseg_chain; [eapply cj_lseg_mono; [exact SEG2| intros; exact I| lia]|].
      eapply cj_chain_one; [exact ANZ| eqcells NDA| lia| exact I| apply cj_str_null| exact SK2| apply cj_chain_nil]. }
    cbn [app] in CH.
    assert (HPXf : Permutation ((U, 64) :: (X ++ (A, 64) :: [(KS, k)]) ++ LR) LBX).
    { eapply Permutation_trans; [| exact HPX]. apply Permutation_sym. apply (perm_new_done (U, 64) (A, 64) [(KS, k)] X LR). }
    assert (FAIL : forall x13' x14' m', m' = m2 ->
      SCPS psegs POST (CST 0x141fc x1 x5 x6 x7 (Z_to_bv 64 A) x9 (Z_to_bv 64 blen) (Z_to_bv 64 P) (Z_to_bv 64 CA) x13' x14' x15 x16 x17
                           (Z_to_bv 64 32) (Z_to_bv 64 58) (Z_to_bv 64 44) (Z_to_bv 64 hd) (Z_to_bv 64 U) (Z_to_bv 64 P) x24 x28 x29 x30 x31 Fx fcx m') mo1).
    { intros x13' x14' m' ->. eapply FAILO; [exact MID2| exact HPXf| exact CH| unfold dch; lia| exact FR| unfold pbuf_at; eqcells PB| eqcells ND| exact FA| exact FRM]. }
    unfold CSTO in FAIL.
    (* [comment removed for export] *)
    zstep. if_cases Kend; zify_cond Kend.
    { apply evt_done. apply FAIL. reflexivity. }
    zstep.
    (nelim (text_read m2 CA bs o3 (Z_to_bv 64 (CA + o3)) BY ltac:(lia) ltac:(lia) eq_refl) 4%nat; intros b Hb RD _).
    pose proof (byte_range b) as Rb.
    zstep. zstep. if_cases K58; zify_cond K58.
    { apply evt_done. apply FAIL. reflexivity. }
    clear FAIL CH HPXf.
    (* [comment removed for export] *)
    (nelimp MID2 7%nat; intros HL _ CJ _ _ _ PR).
    pose proof (munch_refl [(P + 16, P + 24)] m2) as MU. pose proof (wmono_refl psegs m2) as WM.
    zstep. zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
    assert (BLK : forall A' k', In (A', k') LBX -> disjoint_from [(P + 16, P + 24)] A' k').
    { intros A' k' Hin. cbn. split; [|exact I].
      (nelimp (lh_block_range HI _ _ _ _ _ _ HL Hin) 5%nat; intros _ _ _ R4 _). try rewrite alloc_ceiling_eq in R4. lia. }
    (* [comment removed for export] *)
    assert (JOIN : forall x10' x13' x14' m4,
      rw_cells psegs m4 P (pbuf_cells CA blen (skipws_off bs (o3 + 1)) (depth + 1)) -> bytes_at psegs m4 CA bs -> mem_inv psegs m4 ->
      munch [(P + 16, P + 24)] m3 m4 -> wmono psegs m3 m4 ->
      evt psegs (fun ms' => SCPS psegs POST ms' mo1)
        (CST 0x14178 x1 x5 x6 x7 (Z_to_bv 64 A) x9 x10' (Z_to_bv 64 P) (Z_to_bv 64 CA) x13' x14' x15 x16 x17
             (Z_to_bv 64 32) (Z_to_bv 64 58) (Z_to_bv 64 44) (Z_to_bv 64 hd) (Z_to_bv 64 U) (Z_to_bv 64 P) x24 x28 x29 x30 x31 Fx fcx m4)).
    { intros x10' x13' x14' m4 PB4 BY4 MI4 MU4 WM4. unfold CSTO.
      pose proof (munch_trans _ _ _ _ MU MU4) as MU24. pose proof (wmono_trans _ _ _ _ WM WM4) as WM24.
      pose proof FR as FR4. trc FR4 MU4 WM4. pose proof ND as ND4. trc ND4 MU4 WM4. pose proof NDA as NDA4. trc NDA4 MU4 WM4.
      pose proof ERR as ERR4. trc ERR4 MU4 WM4. pose proof ST as ST4. trc ST4 MU4 WM4.
      assert (HL4 : LHEAP HI SPB LBX m4 mo1) by (eapply (lheap_frame_store HI); [exact HL| exact MU24| exact WM24| alia| alia]).
      assert (CJ4 : CJST m4) by (eapply CJST_high_store; [exact CJ| exact MU24| exact WM24| alia]).
      assert (PR4 : ppres LR SP P m m4).
      { eapply ppres_trans; [exact PR|]. eapply (ppres_pbuf_store HI); [exact HL| exact INLR| exact MU24| exact WM24| alia| alia| alia]. }
      assert (SEG4 : cj_lseg CJ_PRINTABLE m4 dch hd A X).
      { eapply cj_lseg_frame; [exact SEG2| exact MU24| exact WM24|]. intros A' k' Hin. apply BLK. apply INX. exact Hin. }
      assert (SK4 : cj_str m4 KS [(KS, k)]).
      { eapply cj_str_frame; [exact SK2| exact MU24| exact WM24|]. intros A' k' [E|[]]. inversion E; subst. apply BLK. exact INS. }
      assert (O4 : o3 + 1 <= skipws_off bs (o3 + 1) <= blen).
      { destruct (Z.eq_dec (o3 + 1) blen) as [E|NE].
        - rewrite skipws_off_noop by lia. lia.
        - pose proof (skipws_off_range bs (o3 + 1)) as OR. rewrite LEN in OR. lia. }
      set (o4 := skipws_off bs (o3 + 1)) in *.
      (* [comment removed for export] *)
      zstep. zstep.
      assert (PI : parse_inv HI m4 mo1 SPB LBX [] ((KS, k) :: (U, 64) :: X ++ LR) A P CA blen bs D n lo (SP + -80) errv1).
      { split; [exact HL4|]. split; [exact HPX|]. split; [right; right; apply in_or_app; right; exact (proj1 HDn)|].
        split; [lia|]. split; [lia|]. split; [exact BY4|]. split; [exact LEN|]. split; [exact BLEN|]. split; [exact CJ4|].
        split; [unfold PERRNO; exact ERR4|]. split; [exact MI4|]. split; [exact ST4|]. split; [alia|]. lia. }
      apply evt_done. cbv beta.
      eapply scps_bind.
      { pose proof (PVREC (Z.to_nat (blen - o4)) ltac:(lia)) as PVS. unfold parse_value_at in PVS.
        eapply PVS with (U := A) (P := P) (off := o4) (depth := depth + 1) (nx := 0) (ty := 16) (ky := KS); clear PVS; rewrite ?unsigned_lit by lia;
          first [exact PI | unfold pbuf_at; exact PB4 | eqcells NDA4 | exact FRM | exact TP | reflexivity | alia ]. }
      cbv beta. intros ms5 mo5 PO'.
      (nelim PO' 32%nat; intros t0' t1' t2' a0' a1_ a2_ a3_ a4_ a5_ a6_ a7' t3' t4' t5' t6' F5 fc5 m5 r off5 depth5 LB5 X5 errv5 -> -> FA5 FRM5 PI5 PR5 PB5 RES)
.
      rewrite ?unsigned_lit in PI5, PR5 by lia.
      replace (ret_pc (Z_to_bv 64 0x14180)) with (Z_to_bv 64 0x14180) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      (nelim PI5 13%nat; intros HL5 HP5 _ _ _ BY5 _ _ CJ5 ERR5 MI5 ST5 _).
      apply (ppres_rw_cells_stack _ _ _ _ _ _ _ PR5) in FR4; [| lia| cbn; lia].
      apply (ppres_rw_cells_block _ _ _ _ _ _ _ U 64 PR5) in ND4; [| right; left; reflexivity| lia| cbn; lia].
      apply (ppres_cj_lseg _ _ _ _ _ _ _ _ _ _ PR5) in SEG4; [| intros b' Hb'; right; right; apply in_or_app; left; exact Hb'].
      apply (ppres_cj_str _ _ _ _ _ _ _ PR5) in SK4; [| intros b' [E|[]]; inversion E; subst; left; reflexivity].
      assert (PR6 : ppres LR SP P m m5).
      { eapply ppres_trans; [exact PR4|]. eapply ppres_weaken; [exact PR5| lia| intros b' Hb'; right; right; apply in_or_app; right; exact Hb']. }
      unfold wz. eapply (after_val c IHc o o4 hd A KS k pvA X r off5 depth5 X5 m5 mo5 LB5 errv5);
        [exact Hc| lia| lia| exact Hd| | exact HP5| exact HNZ| exact ANZ| exact SEG4| exact SK4| exact FR4| exact PB5| eqcells ND4| eapply Fagree_trans; [exact FA| exact FA5]| exact FRM5| reflexivity| exact RES].
      split; [exact HL5|]. split; [exact BY5|]. split; [exact CJ5|]. split; [exact ERR5|]. split; [exact MI5|]. split; [exact ST5| exact PR6]. }
    zstep. if_cases Kskip; zify_cond Kskip.
    - (* [comment removed for export] *)
      eapply JOIN; [| exact BY| exact MI| apply munch_refl| apply wmono_refl]. rewrite skipws_off_noop by lia. unfold pbuf_cells, wz. exact PB.
    - pose proof (fin_off0 blen (o3 + 1) bs LEN ltac:(lia)) as FO.
      eapply evt_cut.
      { eapply (ws4 sp gp tp s9 s10 s11 SPB LB LR U P CA blen off depth bs D n lo PVC (Z.to_nat (blen - (o3 + 1))) (o3 + 1) (depth + 1) m3 m3);
          [lia| lia| unfold pbuf_cells, wz; exact PB| exact BY| exact MI| apply munch_refl| apply wmono_refl]. }
      intros ms' nelH_; (nelim nelH_ 10%nat; intros x10' x13' x14' m4 -> PB4 BY4 MI4 MU4 WM4). rewrite <- FO in PB4.
      eapply JOIN; [exact PB4| exact BY4| exact MI4| exact MU4| exact WM4].
  Qed.

  (* [comment removed for export] *)
  Lemma after_key : forall (c : nat), (forall c', (c' < c)%nat -> OLOOPc c') ->
    forall (o o1 hd A : Z) (pvA : word) (X : list cblock) (r off2 : Z) (X2 : list cblock) m1 mo1 LBX errv1 Fx fcx
           x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x21' x24 x28 x29 x30 x31,
      Z.of_nat c = blen - o -> off <= o -> o < o1 -> depth <= 999 ->
      MID m1 mo1 LBX errv1 -> Permutation ((A, 64) :: X2 ++ (U, 64) :: X ++ LR) LBX ->
      hd <> 0 -> A <> 0 -> cj_lseg CJ_PRINTABLE m1 dch hd A X ->
      rw_cells psegs m1 (SP + -80) SAVED ->
      pbuf_at m1 P CA blen off2 (depth + 1) -> o1 <= off2 <= blen ->
      rw_cells psegs m1 U (node_cells nx pv 0 ty p1 0 vi p2 vd ky) ->
      Fagree F Fx -> frm0 fcx -> x21' = Z_to_bv 64 hd ->
      ( (r = 0 /\ X2 = [] /\ rw_cells psegs m1 A (node_cells 0 pvA 0 0 (wz 0) 0 (wz 0) (wz 0) (wz 0) 0))
        \/ (r = 1 /\ exists (KS k : Z), X2 = [(KS, k)] /\ KS <> 0
              /\ rw_cells psegs m1 A (node_cells 0 pvA 0 16 (wz 0) KS (wz 0) (wz 0) (wz 0) 0)
              /\ cj_str m1 KS [(KS, k)]) ) ->
      SCPS psegs POST (CST 0x140e4 x1 x5 x6 x7 (Z_to_bv 64 A) x9 (Z_to_bv 64 r) x11 x12 x13 x14 x15 x16 x17
                           (Z_to_bv 64 32) (Z_to_bv 64 58) (Z_to_bv 64 44) x21' (Z_to_bv 64 U) (Z_to_bv 64 P) x24 x28 x29 x30 x31 Fx fcx m1) mo1.
  Proof.
    intros c IHc. intros until x31. intros Hc Ho Ho1 Hd MIDm HPX HNZ ANZ SEG FR PB Ho2 ND FA FRM -> RES. lits. unfold CSTO.
    (nelimp MIDm 7%nat; intros HL BY CJ ERR MI ST PR).
    pose proof (pbuf_at_bound _ _ _ _ _ _ PB) as PBB. pose proof (bytes_at_bound _ _ _ _ BY) as BYB.
    pose proof (rw_cells_bound psegs _ _ _ ND) as NDB. rewrite node_cells_size in NDB.
    assert (INLR : forall b, In b LR -> In b LBX) by (intros b Hb; eapply Permutation_in; [exact HPX| right; apply in_or_app; right; right; apply in_or_app; right; exact Hb]).
    assert (INX : forall b, In b X -> In b LBX) by (intros b Hb; eapply Permutation_in; [exact HPX| right; apply in_or_app; right; right; apply in_or_app; left; exact Hb]).
    (nelimp (lh_block_range HI _ _ _ _ _ _ HL (perm_in_head _ _ _ HPX)) 5%nat; intros A1 A2 A3 A4 A5).
    try rewrite alloc_ceiling_eq in A4. unfold PIMG_LO, PIMG_HI in A5.
    eapply scps_step_evt; [eapply (lh_mok HI); exact HL|].
    destruct RES as [(-> & -> & NDA) | (-> & KS & k & -> & KNZ & NDA & SK)].
    - (* [comment removed for export] *)
      zstep. if_true. apply evt_done.
      assert (CH : cj_chain CJ_ANY m1 (S dch) hd (X ++ (A, 64) :: [] ++ [] ++ [])).
      { eapply cj_lseg_chain; [eapply cj_lseg_mono; [exact SEG| intros; exact I| lia]|].
        eapply cj_chain_one; [exact ANZ| exact NDA| lia| exact I| apply cj_str_null| apply cj_str_null| apply cj_chain_nil]. }
      cbn [app] in CH.
      eapply FAILO; [exact MIDm| | exact CH| unfold dch; lia| exact FR| exact PB| exact ND| exact FA| exact FRM].
      eapply Permutation_trans; [| exact HPX]. apply Permutation_sym. apply (perm_new_done (U, 64) (A, 64) [] X LR).
    - (* [comment removed for export] *)
      pose proof (rw_cells_bound psegs _ _ _ NDA) as NAB. rewrite node_cells_size in NAB.
      assert (INS : In (KS, k) LBX) by (eapply Permutation_in; [exact HPX| right; left; reflexivity]).
      pose proof PB as PB'. unfold pbuf_at, pbuf_cells, wz in PB. unfold node_cells, wz in ND. unfold node_cells, wz in NDA. unfold PERRNO in ERR. unfold SAVEDO in FR.
      zstep. if_false. zstep. zstep. zstep. zstep. zstep. if_cases KC; zify_cond KC; [exfalso; lia|].
      zstep. if_cases Kend; zify_cond Kend.
      + (* [comment removed for export] *)
        apply evt_done.
        eapply (key_done c IHc o off2 hd A KS k pvA X m1 mo1 LBX errv1);
          [exact Hc| exact Ho| lia| exact Hd| exact MIDm| exact HPX| exact HNZ| exact ANZ| exact SEG| exact SK| eqcells NDA| exact FR| exact PB'| eqcells ND| exact FA| exact FRM| reflexivity].
      + pose proof (fin_off0 blen off2 bs LEN ltac:(lia)) as FO.
        eapply evt_cut.
        { eapply (ws3 sp gp tp s9 s10 s11 SPB LB LR U P CA blen off depth bs D n lo PVC (Z.to_nat (blen - off2)) off2 (depth + 1) m1 m1);
            [lia| lia| exact PB| exact BY| exact MI| apply munch_refl| apply wmono_refl]. }
        intros ms' nelH_; (nelim nelH_ 8%nat; intros x14' m2 -> PB2 BY2 MI2 MU2 WM2). unfold CSTO. rewrite <- FO in PB2 |- *.
        trc FR MU2 WM2. trc ND MU2 WM2. trc NDA MU2 WM2. trc ERR MU2 WM2. trc ST MU2 WM2.
        assert (HL2 : LHEAP HI SPB LBX m2 mo1) by (eapply (lheap_frame_store HI); [exact HL| exact MU2| exact WM2| alia| alia]).
        assert (CJ2 : CJST m2) by (eapply CJST_high_store; [exact CJ| exact MU2| exact WM2| alia]).
        assert (PR2 : ppres LR SP P m m2).
        { eapply ppres_trans; [exact PR|]. eapply (ppres_pbuf_store HI); [exact HL| exact INLR| exact MU2| exact WM2| alia| alia| alia]. }
        assert (BLK : forall A' k', In (A', k') LBX -> disjoint_from [(P + 16, P + 24)] A' k').
        { intros A' k' Hin. cbn. split; [|exact I].
          (nelimp (lh_block_range HI _ _ _ _ _ _ HL Hin) 5%nat; intros _ _ _ R4 _). try rewrite alloc_ceiling_eq in R4. lia. }
        assert (SEG2 : cj_lseg CJ_PRINTABLE m2 dch hd A X).
        { eapply cj_lseg_frame; [exact SEG| exact MU2| exact WM2|]. intros A' k' Hin. apply BLK. apply INX. exact Hin. }
        assert (SK2 : cj_str m2 KS [(KS, k)]).
        { eapply cj_str_frame; [exact SK| exact MU2| exact WM2|]. intros A' k' [E|[]]. inversion E; subst. apply BLK. exact INS. }
        pose proof (skipws_off_range bs off2 ltac:(rewrite LEN; lia)) as OR. rewrite LEN in OR.
        apply evt_done.
        eapply (key_done c IHc o (skipws_off bs off2) hd A KS k pvA X m2 mo1 LBX errv1);
          [exact Hc| exact Ho| lia| exact Hd| | exact HPX| exact HNZ| exact ANZ| exact SEG2| exact SK2| eqcells NDA| exact FR| unfold pbuf_at; exact PB2| eqcells ND| exact FA| exact FRM| reflexivity].
        split; [exact HL2|]. split; [exact BY2|]. split; [exact CJ2|]. split; [unfold PERRNO; exact ERR|]. split; [exact MI2|]. split; [exact ST| exact PR2].
  Qed.

  (* [comment removed for export] *)
  Lemma do_key : forall (c : nat), (forall c', (c' < c)%nat -> OLOOPc c') ->
    forall (o hd A : Z) (pvA : word) (X : list cblock) m2 mo2 LBX2 errv2 Fx fcx
           x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x21' x24 x28 x29 x30 x31,
      Z.of_nat c = blen - o -> off <= o < blen -> depth <= 999 ->
      MID m2 mo2 LBX2 errv2 -> Permutation ((A, 64) :: (U, 64) :: X ++ LR) LBX2 ->
      hd <> 0 ->
      cj_lseg CJ_PRINTABLE m2 dch hd A X ->
      rw_cells psegs m2 A (node_cells 0 pvA 0 0 (wz 0) 0 (wz 0) (wz 0) (wz 0) 0) ->
      rw_cells psegs m2 (SP + -80) SAVED ->
      pbuf_at m2 P CA blen o (depth + 1) ->
      rw_cells psegs m2 U (node_cells nx pv 0 ty p1 0 vi p2 vd ky) ->
      Fagree F Fx -> frm0 fcx -> x21' = Z_to_bv 64 hd ->
      SCPS psegs POST (CST 0x14094 x1 x5 x6 x7 (Z_to_bv 64 A) x9 x10 x11 x12 x13 x14 x15 x16 x17
                           (Z_to_bv 64 32) (Z_to_bv 64 58) (Z_to_bv 64 44) x21' (Z_to_bv 64 U) (Z_to_bv 64 P) x24 x28 x29 x30 x31 Fx fcx m2) mo2.
  Proof.
    intros c IHc. intros until x31. intros Hc Ho Hd MIDm HPX HNZ SEG NDA FR PB ND FA FRM ->. lits. unfold CSTO.
    (nelimp MIDm 7%nat; intros HL BY CJ ERR MI ST PR).
    pose proof (pbuf_at_bound _ _ _ _ _ _ PB) as PBB. pose proof (rw_cells_bound psegs _ _ _ ND) as NDB. rewrite node_cells_size in NDB.
    pose proof (rw_cells_bound psegs _ _ _ NDA) as NAB. rewrite node_cells_size in NAB.
    pose proof (bytes_at_bound _ _ _ _ BY) as BYB.
    (nelimp (lh_block_range HI _ _ _ _ _ _ HL (perm_in_head _ _ _ HPX)) 5%nat; intros A1 A2 A3 A4 A5).
    try rewrite alloc_ceiling_eq in A4. unfold PIMG_LO, PIMG_HI in A5.
    assert (INLR : forall b, In b LR -> In b LBX2) by (intros b Hb; eapply Permutation_in; [exact HPX| right; right; apply in_or_app; right; exact Hb]).
    assert (INX : forall b, In b X -> In b LBX2) by (intros b Hb; eapply Permutation_in; [exact HPX| right; right; apply in_or_app; left; exact Hb]).
    assert (BLK : forall A' k, In (A', k) LBX2 -> disjoint_from [(P + 16, P + 24)] A' k).
    { intros A' k Hin. cbn. split; [|exact I].
      (nelimp (lh_block_range HI _ _ _ _ _ _ HL Hin) 5%nat; intros _ _ _ R4 _). try rewrite alloc_ceiling_eq in R4. lia. }
    pose proof PB as PB'. unfold pbuf_at, pbuf_cells, wz in PB. unfold node_cells, wz in ND. unfold node_cells, wz in NDA. unfold PERRNO in ERR. unfold SAVEDO in FR.
    eapply scps_step_evt; [eapply (lh_mok HI); exact HL|].
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. if_cases Kend; zify_cond Kend.
    { apply evt_done.
      assert (CH : cj_chain CJ_ANY m2 (S dch) hd (X ++ (A, 64) :: [] ++ [] ++ [])).
      { eapply cj_lseg_chain; [eapply cj_lseg_mono; [exact SEG| intros; exact I| lia]|].
        eapply cj_chain_one; [lia| eqcells NDA| lia| exact I| apply cj_str_null| apply cj_str_null| apply cj_chain_nil]. }
      cbn [app] in CH.
      eapply FAILO; [exact MIDm| | exact CH| unfold dch; lia| exact FR| exact PB'| eqcells ND| exact FA| exact FRM].
      eapply Permutation_trans; [| exact HPX]. apply Permutation_sym. apply (perm_new_done (U, 64) (A, 64) [] X LR). }
    (* [comment removed for export] *)
    pose proof (munch_refl [(P + 16, P + 24)] m2) as MU. pose proof (wmono_refl psegs m2) as WM.
    zstep. zstep. zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
    zstep. if_cases KC; zify_cond KC; [exfalso; lia|].
    (* [comment removed for export] *)
    pose proof (fin_off0 blen (o + 1) bs LEN ltac:(lia)) as FO.
    eapply evt_cut.
    { eapply (ws2 sp gp tp s9 s10 s11 SPB LB LR U P CA blen off depth bs D n lo PVC (Z.to_nat (blen - (o + 1))) (o + 1) (depth + 1) m3 m3);
        [lia| lia| unfold pbuf_cells, wz; exact PB| exact BY| exact MI| apply munch_refl| apply wmono_refl]. }
    intros ms' nelH_; (nelim nelH_ 10%nat; intros x10' x12' x14' m4 -> PB4 BY4 MI4 MU4 WM4). unfold CSTO. rewrite <- FO in PB4.
    clear PB BY MI.
    pose proof (munch_trans _ _ _ _ MU MU4) as MU24. pose proof (wmono_trans _ _ _ _ WM WM4) as WM24.
    trc FR MU4 WM4. trc ND MU4 WM4. trc NDA MU4 WM4. trc ERR MU4 WM4. trc ST MU4 WM4.
    assert (HL4 : LHEAP HI SPB LBX2 m4 mo2) by (eapply (lheap_frame_store HI); [exact HL| exact MU24| exact WM24| alia| alia]).
    assert (CJ4 : CJST m4) by (eapply CJST_high_store; [exact CJ| exact MU24| exact WM24| alia]).
    assert (PR4 : ppres LR SP P m m4).
    { eapply ppres_trans; [exact PR|]. eapply (ppres_pbuf_store HI); [exact HL| exact INLR| exact MU24| exact WM24| alia| alia| alia]. }
    assert (SEG4 : cj_lseg CJ_PRINTABLE m4 dch hd A X).
    { eapply cj_lseg_frame; [exact SEG| exact MU24| exact WM24|]. intros A' k Hin. apply BLK. apply INX. exact Hin. }
    clear MU WM MU4 WM4 MU24 WM24 HL CJ PR SEG m3.
    pose proof (skipws_off_range bs (o + 1) ltac:(rewrite LEN; lia)) as OR. rewrite LEN in OR.
    set (o1 := skipws_off bs (o + 1)) in *.
    (* [comment removed for export] *)
    zstep. zstep.
    assert (PI : parse_inv HI m4 mo2 SPB LBX2 [] ((U, 64) :: X ++ LR) A P CA blen bs D n lo (SP + -80) errv2).
    { split; [exact HL4|]. split; [exact HPX|]. split; [right; apply in_or_app; right; exact (proj1 HDn)|].
      split; [lia|]. split; [lia|]. split; [exact BY4|]. split; [exact LEN|]. split; [exact BLEN|]. split; [exact CJ4|].
      split; [unfold PERRNO; exact ERR|]. split; [exact MI4|]. split; [exact ST|]. split; [alia|]. lia. }
    apply evt_done. cbv beta.
    eapply scps_bind.
    { pose proof (parse_string_spec HI) as PS. unfold parse_string_stmt in PS.
      eapply PS with (U := A) (P := P) (off := o1) (depth := depth + 1) (nx := 0) (ch := 0) (ty := 0) (vs := 0) (ky := 0); clear PS; rewrite ?unsigned_lit by lia;
        first [exact PI | unfold pbuf_at; exact PB4 | eqcells NDA | exact TP | reflexivity | alia ]. }
    cbv beta. intros ms5 mo5 PO'.
    (nelim PO' 28%nat; intros t0' t1' t2' a0' a1_ a2_ a3_ a4_ a5_ a6_ a7' t3' t4' t5' t6' m5 r off2 LB5 X2 errv5 -> -> PI5 PR5 PB5 Ho2 RES)
.
    rewrite ?unsigned_lit in PI5, PR5 by lia.
    replace (ret_pc (Z_to_bv 64 0x140e4)) with (Z_to_bv 64 0x140e4) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    (nelim PI5 13%nat; intros HL5 HP5 _ _ _ BY5 _ _ CJ5 ERR5 MI5 ST5 _).
    apply (ppres_rw_cells_stack _ _ _ _ _ _ _ PR5) in FR; [| lia| cbn; lia].
    apply (ppres_rw_cells_block _ _ _ _ _ _ _ U 64 PR5) in ND; [| left; reflexivity| lia| cbn; lia].
    apply (ppres_cj_lseg _ _ _ _ _ _ _ _ _ _ PR5) in SEG4; [| intros b Hb; right; apply in_or_app; left; exact Hb].
    assert (PR6 : ppres LR SP P m m5).
    { eapply ppres_trans; [exact PR4|]. eapply ppres_weaken; [exact PR5| lia| intros b Hb; right; apply in_or_app; right; exact Hb]. }
    unfold wz. eapply (after_key c IHc o o1 hd A pvA X r off2 X2 m5 mo5 LB5 errv5);
      [exact Hc| lia| lia| exact Hd| | exact HP5| exact HNZ| lia| exact SEG4| exact FR| exact PB5| exact Ho2| eqcells ND| exact FA| exact FRM| reflexivity| ].
    - split; [exact HL5|]. split; [exact BY5|]. split; [exact CJ5|]. split; [exact ERR5|]. split; [exact MI5|]. split; [exact ST5| exact PR6].
    - destruct RES as [(-> & -> & NDR)|(-> & KS & k & -> & KNZ & NDR & SK)].
      + left. split; [reflexivity|]. split; [reflexivity| exact NDR].
      + right. split; [reflexivity|]. exists KS, k. split; [reflexivity|]. split; [exact KNZ|]. split; [exact NDR| exact SK].
  Qed.

  (* [comment removed for export] *)
  Lemma loop_body_o : forall (c : nat), (forall c', (c' < c)%nat -> OLOOPc c') -> OLOOPc c.
  Proof.
    intros c IHc. unfold OLOOP. intros until x31. intros Hc Ho Hd MIDm HPX OI FR PB ND FA FRM. lits. unfold CSTO.
    (nelimp MIDm 7%nat; intros HL BY CJ ERR MI ST PR).
    pose proof (pbuf_at_bound _ _ _ _ _ _ PB) as PBB. pose proof (rw_cells_bound psegs _ _ _ ND) as NDB. rewrite node_cells_size in NDB.
    pose proof (bytes_at_bound _ _ _ _ BY) as BYB.
    assert (INLR : forall b, In b LR -> In b LBX) by (intros b Hb; eapply Permutation_in; [exact HPX| right; apply in_or_app; right; exact Hb]).
    assert (INX : forall b, In b X -> In b LBX) by (intros b Hb; eapply Permutation_in; [exact HPX| right; apply in_or_app; left; exact Hb]).
    assert (INU : In (U, 64) LBX) by (eapply perm_in_head; exact HPX).
    pose proof PB as PB'. unfold pbuf_at, pbuf_cells, wz in PB. unfold node_cells, wz in ND. unfold PERRNO in ERR. unfold SAVEDO in FR.
    eapply scps_step_evt; [eapply (lh_mok HI); exact HL|].
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep.
    replace (ret_pc (Z_to_bv 64 PMALLOC)) with (wz PMALLOC) by (unfold wz, PMALLOC; symmetry; apply ret_pc_even; [lia| reflexivity]).
    apply evt_done. cbv beta.
    eapply scps_bind.
    { pose proof (lh_malloc HI) as LM. unfold malloc_scps_stmt in LM.
      eapply LM with (lo := lo) (n := 64); rewrite ?unsigned_lit by lia;
        first [ exact HL | exact ST | exact ERR | exact MI | exact TP | reflexivity | alia ]. }
    cbv beta. intros ms2 mo2 PO'.
    (nelim PO' 23%nat; intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m2 errv2 -> MI2 ST2 ERR2 PR2 RES)
.
    rewrite ?unsigned_lit in ST2, PR2 by lia.
    replace (ret_pc (Z_to_bv 64 0x14058)) with (Z_to_bv 64 0x14058) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    apply (cj_pres_rw_cells _ _ _ _ _ _ PR2) in FR; [| left; cbn; lia].
    apply (cj_pres_rw_cells _ _ _ _ _ _ PR2) in PB; [| left; cbn; lia].
    pose proof PB' as PB2. unfold pbuf_at in PB2. apply (cj_pres_rw_cells _ _ _ _ _ _ PR2) in PB2; [| left; cbn; lia]. clear PB'.
    apply (cj_pres_rw_cells _ _ _ _ _ _ PR2) in ND; [| right; right; exists U, 64; split; [exact INU| cbn; lia]].
    apply (cj_pres_bytes_at _ _ _ _ _ _ PR2) in BY; [| right; right; exists D, n; split; [apply INLR; apply (proj1 HDn)| lia]].
    apply (CJST_pres _ _ _ _ PR2) in CJ.
    apply (obj_inv_magree _ m1 m2) in OI; [| eapply magree_blocks_of_cj_pres; [exact PR2| exact INX]].
    assert (PR3 : ppres LR SP P m m2) by (eapply ppres_trans; [exact PR| eapply ppres_of_cj_pres; [exact PR2| lia| exact INLR]]).
    clear PR PR2 MI ST HL ERR. unfold PERRNO in ERR2.
    destruct RES as [[-> HL2] | (A & jk & -> & ARNG & ANEW & HL2 & BLK)].
    - (* [comment removed for export] *)
      eapply scps_step_evt; [eapply (lh_mok HI); exact HL2|].
      (nelimp (cj_chain_ptr_range _ _ _ _ _ (obj_inv_chain _ _ _ _ _ OI)) 3%nat; intros HR1 _ HR2).
      unfold wz. zstep. if_true. zstep. if_cases Kh; zify_cond Kh.
      + (* [comment removed for export] *)
        apply evt_done. eapply fail_o; [exact PVC| | exact HPX| eapply cj_chain_any; eapply obj_inv_chain; exact OI| unfold dch; lia| exact FR| unfold pbuf_at; exact PB2| eqcells ND| exact FA| exact FRM].
        split; [exact HL2|]. split; [exact BY|]. split; [exact CJ|]. split; [unfold PERRNO; exact ERR2|]. split; [exact MI2|]. split; [exact ST2| exact PR3].
      + (* [comment removed for export] *)
        destruct OI as [[_ ->]|(NZ & _)]; [| exfalso; exact (NZ Kh)]. cbn [app] in HPX.
        zstep. apply evt_done. eapply ret0_o; [exact PVC| | exact HPX| exact FR| unfold pbuf_at; exact PB2| eqcells ND| exact FA| exact FRM].
        split; [exact HL2|]. split; [exact BY|]. split; [exact CJ|]. split; [unfold PERRNO; exact ERR2|]. split; [exact MI2|]. split; [exact ST2| exact PR3].
    - (* [comment removed for export] *)
      (nelimp ARNG 5%nat; intros A1 A2 A3 A4 A5). try rewrite alloc_ceiling_eq in A4. unfold PIMG_LO, PIMG_HI in A5.
      assert (APART : forall A' n', In (A', n') LBX -> A' <> A /\ (A' + n' <= A \/ A + 64 <= A')).
      { intros A' n' Hin. eapply (lheap_perm_apart HI); [exact HL2| apply Permutation_refl| exact Hin]. }
      destruct (APART U 64 INU) as [_ AU]. destruct (APART D n (INLR _ (proj1 HDn))) as [_ AD].
      eapply scps_step_evt; [eapply (lh_mok HI); exact HL2|].
      unfold wz. zstep. if_cases Kz; zify_cond Kz; [exfalso; lia|].
      eapply evt_cut; [eapply zero_node_run_o; [exact BLK| exact MI2]|].
      intros ms' nelH_; (nelim nelH_ 6%nat; intros m3 -> MU3 WM3 MI3 NDA). unfold CSTO.
      trc FR MU3 WM3. trc PB MU3 WM3. trc ND MU3 WM3. trc ERR2 MU3 WM3. trc BY MU3 WM3. trc ST2 MU3 WM3.
      apply (obj_inv_magree _ m2 m3) in OI.
      2:{ eapply magree_blocks_of_munch; [exact MU3| exact WM3|]. intros A' n' Hin. cbn. split; [|exact I]. destruct (APART A' n' (INX _ Hin)). lia. }
      assert (HL3 : LHEAP HI SPB ((A, 64) :: LBX) m3 mo2) by (eapply (lheap_block_store HI); [exact HL2| left; reflexivity| exact MU3| exact WM3| lia| lia]).
      assert (CJ3 : CJST m3) by (eapply (CJST_block_store HI); [exact HL2| left; reflexivity| exact CJ| exact MU3| exact WM3| lia| lia]).
      assert (PR4 : ppres LR SP P m m3).
      { eapply ppres_trans; [exact PR3|]. eapply (ppres_block_store HI); [exact HL2| apply Permutation_refl| exact INLR| alia| exact MU3| exact WM3| lia| lia]. }
      clear MU3 WM3 MI2 CJ PR3 BLK.
      (nelimp (cj_chain_ptr_range _ _ _ _ _ (obj_inv_chain _ _ _ _ _ OI)) 3%nat; intros HR1 _ HR2).
      zstep. if_cases Kh; zify_cond Kh.
      + (* [comment removed for export] *)
        destruct OI as [[_ ->]|(NZ & _)]; [| exfalso; exact (NZ Kh)]. cbn [app] in HPX.
        apply evt_done. eapply (do_key c IHc o A A (wz 0) [] m3 mo2 ((A, 64) :: LBX) errv2);
          [exact Hc| exact Ho| exact Hd| | apply perm_skip; exact HPX| lia| apply cj_lseg_nil| exact NDA| exact FR| unfold pbuf_at; eqcells PB| eqcells ND| exact FA| exact FRM| reflexivity].
        split; [exact HL3|]. split; [exact BY|]. split; [exact CJ3|]. split; [unfold PERRNO; exact ERR2|]. split; [exact MI3|]. split; [exact ST2| exact PR4].
      + (* [comment removed for export] *)
        destruct OI as [[E _]|(NZ & NZc & B1 & Bv & Bk & Bc & chc & tyc & vsc & kyc & pvc & p1c & vic & p2c & vdc & -> & SEG & NDC & TYC & SVC & SKC & CHC)]; [exfalso; exact (Kh E)|].
        assert (HPcur : Permutation ((cur, 64) :: (A, 64) :: (B1 ++ Bv ++ Bk ++ Bc) ++ (U, 64) :: LR) ((A, 64) :: LBX)).
        { eapply Permutation_trans; [apply perm_swap|]. apply perm_skip. eapply Permutation_trans; [apply perm_pick_mid| exact HPX]. }
        (nelimp (lh_block_range HI _ _ _ _ _ _ HL3 (perm_in_head _ _ _ HPcur)) 5%nat; intros C1 C2 C3 C4 C5).
        try rewrite alloc_ceiling_eq in C4. unfold PIMG_LO, PIMG_HI in C5.
        assert (CPART : forall A' n', In (A', n') ((A, 64) :: (B1 ++ Bv ++ Bk ++ Bc) ++ (U, 64) :: LR) -> A' <> cur /\ (A' + n' <= cur \/ cur + 64 <= A')).
        { intros A' n' Hin. eapply (lheap_perm_apart HI); [exact HL3| exact HPcur| exact Hin]. }
        destruct (CPART A 64 ltac:(left; reflexivity)) as [_ CA'].
        destruct (CPART U 64 ltac:(right; apply in_or_app; right; left; reflexivity)) as [_ CU].
        destruct (CPART D n ltac:(right; apply in_or_app; right; right; exact (proj1 HDn))) as [_ CD].
        pose proof (rw_cells_bound psegs _ _ _ NDC) as NCB. rewrite node_cells_size in NCB.
        unfold node_cells, wz in NDC. unfold node_cells, wz in NDA.
        (* [comment removed for export] *)
        pose proof (munch_refl [(cur, cur + 8)] m3) as MU. pose proof (wmono_refl psegs m3) as WM.
        zstep.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m4 end.
        assert (INC : In (cur, 64) ((A, 64) :: LBX)) by (eapply perm_in_head; exact HPcur).
        assert (HL4 : LHEAP HI SPB ((A, 64) :: LBX) m4 mo2) by (eapply (lheap_block_store HI); [exact HL3| exact INC| exact MU| exact WM| lia| lia]).
        assert (CJ4 : CJST m4) by (eapply (CJST_block_store HI); [exact HL3| exact INC| exact CJ3| exact MU| exact WM| lia| lia]).
        assert (PR5 : ppres LR SP P m m4).
        { eapply ppres_trans; [exact PR4|]. eapply (ppres_block_store HI); [exact HL3| exact HPcur| intros b Hb; right; apply in_or_app; right; right; exact Hb| alia| exact MU| exact WM| lia| lia]. }
        assert (DJ : forall A' n', In (A', n') (B1 ++ Bv ++ Bk ++ Bc) -> disjoint_from [(cur, cur + 8)] A' n').
        { intros A' n' Hin. cbn. split; [|exact I]. destruct (CPART A' n' ltac:(right; apply in_or_app; left; exact Hin)). lia. }
        assert (SEG4 : cj_lseg CJ_PRINTABLE m4 dch head cur B1).
        { eapply cj_lseg_frame; [exact SEG| exact MU| exact WM|]. intros A' n' Hin. apply DJ. apply in_or_app. left. exact Hin. }
        assert (SVC4 : cj_str m4 vsc Bv).
        { eapply cj_str_frame; [exact SVC| exact MU| exact WM|]. intros A' n' Hin. apply DJ. apply in_or_app. right. apply in_or_app. left. exact Hin. }
        assert (SKC4 : cj_str m4 kyc Bk).
        { eapply cj_str_frame; [exact SKC| exact MU| exact WM|]. intros A' n' Hin. apply DJ. apply in_or_app. right. apply in_or_app. right. apply in_or_app. left. exact Hin. }
        assert (CHC4 : cj_chain CJ_PRINTABLE m4 dch chc Bc).
        { eapply cj_chain_frame; [exact CHC| exact MU| exact WM|]. intros A' n' Hin. apply DJ. apply in_or_app. right. apply in_or_app. right. apply in_or_app. right. exact Hin. }
        clear MU WM HL3 CJ3 PR4 SEG SVC SKC CHC DJ.
        (* [comment removed for export] *)
        pose proof (munch_refl [(A + 8, A + 16)] m4) as MU. pose proof (wmono_refl psegs m4) as WM.
        zstep.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m5 end.
        assert (HL5 : LHEAP HI SPB ((A, 64) :: LBX) m5 mo2) by (eapply (lheap_block_store HI); [exact HL4| left; reflexivity| exact MU| exact WM| lia| lia]).
        assert (CJ5 : CJST m5) by (eapply (CJST_block_store HI); [exact HL4| left; reflexivity| exact CJ4| exact MU| exact WM| lia| lia]).
        assert (PR6 : ppres LR SP P m m5).
        { eapply ppres_trans; [exact PR5|]. eapply (ppres_block_store HI); [exact HL4| apply Permutation_refl| exact INLR| alia| exact MU| exact WM| lia| lia]. }
        assert (DJ : forall A' n', In (A', n') (B1 ++ Bv ++ Bk ++ Bc) -> disjoint_from [(A + 8, A + 16)] A' n').
        { intros A' n' Hin. cbn. split; [|exact I].
          destruct (APART A' n') as [_ ?]; [| lia]. apply INX. apply in_app_or in Hin. apply in_or_app. destruct Hin as [Hin|Hin]; [left; exact Hin| right; right; exact Hin]. }
        assert (SEG5 : cj_lseg CJ_PRINTABLE m5 dch head cur B1).
        { eapply cj_lseg_frame; [exact SEG4| exact MU| exact WM|]. intros A' n' Hin. apply DJ. apply in_or_app. left. exact Hin. }
        assert (SVC5 : cj_str m5 vsc Bv).
        { eapply cj_str_frame; [exact SVC4| exact MU| exact WM|]. intros A' n' Hin. apply DJ. apply in_or_app. right. apply in_or_app. left. exact Hin. }
        assert (SKC5 : cj_str m5 kyc Bk).
        { eapply cj_str_frame; [exact SKC4| exact MU| exact WM|]. intros A' n' Hin. apply DJ. apply in_or_app. right. apply in_or_app. right. apply in_or_app. left. exact Hin. }
        assert (CHC5 : cj_chain CJ_PRINTABLE m5 dch chc Bc).
        { eapply cj_chain_frame; [exact CHC4| exact MU| exact WM|]. intros A' n' Hin. apply DJ. apply in_or_app. right. apply in_or_app. right. apply in_or_app. right. exact Hin. }
        clear MU WM HL4 CJ4 PR5 SEG4 SVC4 SKC4 CHC4 DJ.
        zstep. apply evt_done.
        eapply (do_key c IHc o head A (Z_to_bv 64 cur) (B1 ++ (cur, 64) :: Bv ++ Bk ++ Bc) m5 mo2 ((A, 64) :: LBX) errv2);
          [exact Hc| exact Ho| exact Hd| | apply perm_skip; exact HPX| exact NZ| | eqcells NDA| exact FR| unfold pbuf_at; eqcells PB| eqcells ND| exact FA| exact FRM| reflexivity].
        * split; [exact HL5|]. split; [exact BY|]. split; [exact CJ5|]. split; [unfold PERRNO; exact ERR2|]. split; [exact MI3|]. split; [exact ST2| exact PR6].
        * eapply cj_lseg_snoc; [exact SEG5| exact NZc| eqcells NDC| apply CJ_PRINTABLE_range; exact TYC| exact TYC| exact SVC5| exact SKC5| exact CHC5].
  Qed.

  Theorem oloop : forall c, OLOOPc c.
  Proof. induction c as [c IH] using lt_wf_ind. apply loop_body_o. exact IH. Qed.
End POL.


End CeilWrap.
End CJ_pobject_L.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import ShapeAlg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Tac Bytes SCPS FP.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import PImg CJ_iface CJ_tree.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require CJ_phex4.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.CJ_phex4.CJ_pbuf.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require CJ_phex4.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.CJ_phex4.CJ_skipws.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require CJ_pvalue_A.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.CJ_pvalue_A.CJ_delete.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require CJ_phex4.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.CJ_phex4.CJ_parse_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require CJ_phex4.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.CJ_phex4.CJ_parse_lemmas.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require CJ_pvalue_A.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.CJ_pvalue_A.CJ_pvalue_lemmas.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require CJ_pvalue_A.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.CJ_pvalue_A.CJ_pvalue_ctx.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import CJ_pvalue_A.
Import CJ_pobject_ctx.
Import CJ_pobject_ws.
Import CJ_pobject_L.
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

Section POE.
  Variable HI : cj_heap_iface.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word).
  Variables (m : word -> option byte) (SPB : Z) (LB LR : list cblock) (U P CA blen off depth : Z) (bs : list byte) (D n lo : Z).
  Variables (nx : Z) (pv : word) (ty : Z) (p1 : word) (vi p2 vd : word) (ky : Z).
  Hypothesis PVC : pv_pure sp tp SPB LB LR U P CA blen off depth bs D n lo.
  Variable nfuel : nat.
  Hypothesis FUEL : blen - off <= Z.of_nat nfuel.
  Hypothesis PVREC : forall nf, (nf < nfuel)%nat -> parse_value_at HI nf.

  Notation SP := (bv_unsigned sp).
  Notation CST := (CSTO sp gp tp s9 s10 s11).
  Notation POST := (POSTV HI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m SPB LR U P CA blen off depth bs D n lo nx pv ty p1 vi p2 vd ky).
  Notation MID := (MIDO HI sp m SPB LR P CA bs lo).
  Notation SAVED := (SAVEDO ra s0 s1 s2 s3 s4 s5 s6 s7 s8).
  Notation dch := (dch depth).

  Ltac zfeq := repeat (lazymatch goal with |- @eq Z _ _ => lia | |- _ => first [reflexivity | progress f_equal] end).
  Ltac eqcells H :=
    lazymatch goal with |- rw_cells _ _ _ ?cs =>
      lazymatch type of H with rw_cells _ _ _ ?cs' =>
        replace cs with cs'; [exact H| unfold pbuf_cells, node_cells, wz; zfeq] end end.
  Ltac dj := cbn [disjoint_from cells_size csize Nat.add length];
             repeat match goal with H : length ?l = _ |- context [length ?l] => rewrite H end;
             first [lia | split; [lia| exact I]].
  Ltac trc H MU WM := first [ eapply rw_cells_transport in H; [| exact MU| exact WM| dj]
                            | eapply bytes_at_transport in H; [| exact MU| dj]
                            | eapply u8arr_transport in H; [| exact MU| exact WM| dj]
                            | eapply stk_transport_disjoint in H; [| exact MU| exact WM| dj] ].
  Ltac lits := pose proof (pvc_lits _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ PVC) as (HPU & HDn & LEN & BLEN & CEIL & LO & PP & OFF & DEP & TP & URNG & DRNG & UD & SPR).
  Ltac alia := rewrite ?alloc_ceiling_eq; unfold DELETE_STACK, PARSE_STACK, PARSE_STRING_STACK; unfold RMALLOC_STACK; lia.

  (* [comment removed for export] *)
  Lemma ret0_noframe : forall (off1 depth1 : Z) m1 mo errv x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 fc,
    LHEAP HI SPB LB m1 mo -> bytes_at psegs m1 CA bs -> CJST m1 -> rw_cells psegs m1 PERRNO [C4 errv] -> mem_inv psegs m1 ->
    stk psegs m1 lo SP -> ppres LR SP P m m1 ->
    pbuf_at m1 P CA blen off1 depth1 ->
    rw_cells psegs m1 U (node_cells nx pv 0 ty p1 0 vi p2 vd ky) -> frm0 fc ->
    POST (MS (mkR ra sp gp tp x5 x6 x7 s0 s1 (Z_to_bv 64 0) x11 x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
             F (ret_pc ra) fc None m1 (seg_rom psegs)) mo.
  Proof.
    intros until fc. intros HL BY CJ ERR MI ST PR PB ND FRM. lits. unfold POSTV, parse_value_post.
    do 17 eexists. exists m1, 0, off1, depth1, LB, [], errv.
    split; [reflexivity|]. split; [reflexivity|]. split; [apply Fagree_refl|]. split; [exact FRM|].
    split.
    { split; [exact HL|]. split; [exact HPU|].
      split; [apply (proj1 HDn)|]. split; [lia|]. split; [lia|]. split; [exact BY|]. split; [exact LEN|]. split; [exact BLEN|].
      split; [exact CJ|]. split; [exact ERR|]. split; [exact MI|]. split; [exact ST|]. split; [try rewrite alloc_ceiling_eq; exact CEIL|]. exact PP. }
    split; [exact PR|]. split; [exact PB|]. left. split; [reflexivity|]. split; [reflexivity| exact ND].
  Qed.

  Lemma po_body : forall (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (fc : bv 32) (mo : Model) (errv : word),
    LHEAP HI SPB LB m mo -> bytes_at psegs m CA bs -> CJST m -> rw_cells psegs m PERRNO [C4 errv] -> mem_inv psegs m ->
    stk psegs m lo SP ->
    rw_cells psegs m U (node_cells nx pv 0 ty p1 0 vi p2 vd ky) -> pbuf_at m P CA blen off depth ->
    frm0 fc -> a0 = wz U -> a1 = wz P ->
    SCPS psegs POST (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (wz PARSE_OBJECT) fc None m (seg_rom psegs)) mo.
  Proof.
    intros until errv. intros HL BY CJ ERR MI ST ND PB FRM A0 A1. lits. pose proof (ppres_refl LR SP P m) as PR0.
    unfold wz in A0, A1. subst a0 a1. unfold PARSE_OBJECT, wz.
    pose proof (pbuf_at_bound _ _ _ _ _ _ PB) as PBB. unfold pbuf_at, pbuf_cells, wz in PB.
    pose proof (rw_cells_bound psegs _ _ _ ND) as NDB. rewrite node_cells_size in NDB. unfold node_cells, wz in ND.
    pose proof (bytes_at_bound _ _ _ _ BY) as BYB. unfold PERRNO in ERR.
    assert (INLR : forall b, In b LR -> In b LB) by (intros b Hb; eapply Permutation_in; [exact HPU| right; exact Hb]).
    assert (INU : In (U, 64) LB) by (eapply perm_in_head; exact HPU).
    eapply scps_step_evt; [eapply (lh_mok HI); exact HL|].
    (* [comment removed for export] *)
    zstep. zstep. zstep. if_cases Kd; zify_cond Kd.
    { zstep. zstep. apply evt_done. apply scps_done.
      eapply ret0_noframe; [exact HL| exact BY| exact CJ| unfold PERRNO; exact ERR| exact MI| exact ST| exact PR0| unfold pbuf_at; eqcells PB| eqcells ND| exact FRM]. }
    (* [comment removed for export] *)
    pose proof (munch_refl [(P + 24, P + 32)] m) as MU. pose proof (wmono_refl psegs m) as WM.
    zstep. zstep. zstep. zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    assert (HL1 : LHEAP HI SPB LB m1 mo) by (eapply (lheap_frame_store HI); [exact HL| exact MU| exact WM| alia| alia]).
    assert (CJ1 : CJST m1) by (eapply CJST_high_store; [exact CJ| exact MU| exact WM| alia]).
    assert (PR1 : ppres LR SP P m m1).
    { eapply ppres_trans; [exact PR0|]. eapply (ppres_pbuf_store HI); [exact HL| exact INLR| exact MU| exact WM| alia| alia| alia]. }
    clear MU WM HL CJ PR0.
    zstep. if_cases Kend; zify_cond Kend.
    { zstep. zstep. apply evt_done. apply scps_done.
      eapply ret0_noframe; [exact HL1| exact BY| exact CJ1| unfold PERRNO; exact ERR| exact MI| exact ST| exact PR1| unfold pbuf_at; eqcells PB| eqcells ND| exact FRM]. }
    (* [comment removed for export] *)
    pose proof (munch_refl [(SP + -80, SP)] m1) as MU. pose proof (wmono_refl psegs m1) as WM.
    zstep. carve_frame 80%nat ST. do 10 zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
    assert (HL2 : LHEAP HI SPB LB m2 mo) by (eapply (lheap_frame_store HI); [exact HL1| exact MU| exact WM| alia| alia]).
    assert (CJ2 : CJST m2) by (eapply CJST_high_store; [exact CJ1| exact MU| exact WM| alia]).
    assert (PR2 : ppres LR SP P m m2).
    { eapply ppres_trans; [exact PR1|]. eapply (ppres_frame_store HI); [exact HL1| exact INLR| exact MU| exact WM| alia| lia]. }
    clear MU WM HL1 CJ1 PR1 m1.
    assert (MID2 : MID m2 mo LB errv).
    { split; [exact HL2|]. split; [exact BY|]. split; [exact CJ2|]. split; [unfold PERRNO; exact ERR|]. split; [exact MI|]. split; [exact ST| exact PR2]. }
    (* [comment removed for export] *)
    zstep. zstep.
    destruct (text_read m2 CA bs off (Z_to_bv 64 (CA + off)) BY ltac:(lia) ltac:(lia) eq_refl) as (b & Hb & RD & _).
    pose proof (byte_range b) as Rb.
    zstep. zstep. zstep. if_cases K123; zify_cond K123.
    { apply evt_done. eapply ret0_o; [exact PVC| exact MID2| exact HPU| exact FR| unfold pbuf_at; eqcells PB| eqcells ND| apply Fagree_refl| exact FRM]. }
    (* [comment removed for export] *)
    pose proof (munch_refl [(P + 16, P + 24)] m2) as MU. pose proof (wmono_refl psegs m2) as WM.
    zstep. zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
    assert (BLK : forall A' k, In (A', k) LB -> disjoint_from [(P + 16, P + 24)] A' k).
    { intros A' k Hin. cbn. split; [|exact I].
      pose proof (lh_block_range HI _ _ _ _ _ _ HL2 Hin) as (_ & _ & _ & R4 & _). try rewrite alloc_ceiling_eq in R4. lia. }
    (* [comment removed for export] *)
    assert (JOIN : forall x16' x17' m4,
      rw_cells psegs m4 P (pbuf_cells CA blen (skipws_off bs (off + 1)) (depth + 1)) -> bytes_at psegs m4 CA bs -> mem_inv psegs m4 ->
      munch [(P + 16, P + 24)] m3 m4 -> wmono psegs m3 m4 ->
      evt psegs (fun ms' => SCPS psegs POST ms' mo)
        (CST 0x13fe0 ra t0 t1 t2 s0 s1 (Z_to_bv 64 U) (Z_to_bv 64 P) (Z_to_bv 64 (skipws_off bs (off + 1))) (Z_to_bv 64 depth) (Z_to_bv 64 blen) (Z_to_bv 64 CA) x16' x17'
             s2 s3 s4 s5 s6 s7 s8 t3 t4 t5 t6 F fc m4)).
    { intros x16' x17' m4 PB4 BY4 MI4 MU4 WM4. unfold CSTO.
      pose proof (munch_trans _ _ _ _ MU MU4) as MU24. pose proof (wmono_trans _ _ _ _ WM WM4) as WM24.
      pose proof FR as FR4. trc FR4 MU4 WM4. pose proof ND as ND4. trc ND4 MU4 WM4.
      pose proof ERR as ERR4. trc ERR4 MU4 WM4. pose proof ST as ST4. trc ST4 MU4 WM4.
      assert (HL4 : LHEAP HI SPB LB m4 mo) by (eapply (lheap_frame_store HI); [exact HL2| exact MU24| exact WM24| alia| alia]).
      assert (CJ4 : CJST m4) by (eapply CJST_high_store; [exact CJ2| exact MU24| exact WM24| alia]).
      assert (PR4 : ppres LR SP P m m4).
      { eapply ppres_trans; [exact PR2|]. eapply (ppres_pbuf_store HI); [exact HL2| exact INLR| exact MU24| exact WM24| alia| alia| alia]. }
      clear MU4 WM4 MU24 WM24.
      assert (O2 : off + 1 <= skipws_off bs (off + 1) <= blen).
      { destruct (Z.eq_dec (off + 1) blen) as [E|NE].
        - rewrite skipws_off_noop by lia. lia.
        - pose proof (skipws_off_range bs (off + 1)) as OR. rewrite LEN in OR. lia. }
      set (o2 := skipws_off bs (off + 1)) in *.
      pose proof (rw_cells_bound psegs _ _ _ PB4) as PBB4. rewrite pbuf_cells_size in PBB4. unfold pbuf_cells, wz in PB4.
      (* [comment removed for export] *)
      zstep. if_cases Kend2; zify_cond Kend2.
      { (* [comment removed for export] *)
        pose proof (munch_refl [(P + 16, P + 24)] m4) as MU5. pose proof (wmono_refl psegs m4) as WM5.
        zstep. zstep. zstep.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m5 end.
        zstep. apply evt_done. eapply (ret0_epi_o HI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m SPB LB LR U P CA blen off depth bs D n lo nx pv ty p1 vi p2 vd ky PVC (o2 - 1) (depth + 1) m5 mo LB errv);
          [| exact HPU| exact FR4| unfold pbuf_at; eqcells PB4| eqcells ND4| apply Fagree_refl| exact FRM].
        split. { eapply (lheap_frame_store HI); [exact HL4| exact MU5| exact WM5| alia| alia]. }
        split; [exact BY4|]. split. { eapply CJST_high_store; [exact CJ4| exact MU5| exact WM5| alia]. }
        split; [unfold PERRNO; exact ERR4|]. split; [exact MI4|]. split; [exact ST4|].
        eapply ppres_trans; [exact PR4|]. eapply (ppres_pbuf_store HI); [exact HL4| exact INLR| exact MU5| exact WM5| alia| alia| alia]. }
      zstep.
      destruct (text_read m4 CA bs o2 (Z_to_bv 64 (CA + o2)) BY4 ltac:(lia) ltac:(lia) eq_refl) as (c2 & Hc2 & RD2 & _).
      pose proof (byte_range c2) as Rc2.
      zstep. zstep. zstep. if_cases K125; zify_cond K125.
      - (* [comment removed for export] *)
        pose proof (munch_refl [(P + 16, P + 24)] m4) as MU5. pose proof (wmono_refl psegs m4) as WM5.
        zstep. zstep. zstep. zstep. zstep. zstep.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m5 end.
        zstep. apply evt_done.
        pose proof (oloop HI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m SPB LB LR U P CA blen off depth bs D n lo nx pv ty p1 vi p2 vd ky PVC nfuel FUEL PVREC (Z.to_nat (blen - (o2 - 1)))) as OL.
        unfold OLOOP, CSTO in OL.
        eapply (OL (o2 - 1) 0 0 [] m5 mo LB errv); [lia| lia| lia| | exact HPU| left; split; reflexivity| exact FR4| unfold pbuf_at; eqcells PB4| eqcells ND4| apply Fagree_refl| exact FRM].
        split. { eapply (lheap_frame_store HI); [exact HL4| exact MU5| exact WM5| alia| alia]. }
        split; [exact BY4|]. split. { eapply CJST_high_store; [exact CJ4| exact MU5| exact WM5| alia]. }
        split; [unfold PERRNO; exact ERR4|]. split; [exact MI4|]. split; [exact ST4|].
        eapply ppres_trans; [exact PR4|]. eapply (ppres_pbuf_store HI); [exact HL4| exact INLR| exact MU5| exact WM5| alia| alia| alia].
      - (* [comment removed for export] *)
        pose proof (munch_refl [(P + 24, P + 32)] m4) as MU5. pose proof (wmono_refl psegs m4) as WM5.
        zstep. zstep.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m5 end.
        apply evt_done.
        eapply (obj_success HI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m SPB LB LR U P CA blen off depth bs D n lo nx pv ty p1 vi p2 vd ky PVC o2 0 [] m5 mo LB errv);
          [| exact HPU| apply cj_chain_nil| lia| exact FR4| unfold pbuf_at; eqcells PB4| eqcells ND4| lia| apply Fagree_refl| exact FRM].
        split. { eapply (lheap_frame_store HI); [exact HL4| exact MU5| exact WM5| alia| alia]. }
        split; [exact BY4|]. split. { eapply CJST_high_store; [exact CJ4| exact MU5| exact WM5| alia]. }
        split; [unfold PERRNO; exact ERR4|]. split; [exact MI4|]. split; [exact ST4|].
        eapply ppres_trans; [exact PR4|]. eapply (ppres_pbuf_store HI); [exact HL4| exact INLR| exact MU5| exact WM5| alia| alia| alia]. }
    zstep. if_cases Kskip; zify_cond Kskip.
    - replace (Z_to_bv 64 (off + 1)) with (Z_to_bv 64 (skipws_off bs (off + 1))) by (rewrite skipws_off_noop by lia; reflexivity).
      eapply JOIN; [| exact BY| exact MI| apply munch_refl| apply wmono_refl]. rewrite skipws_off_noop by lia. unfold pbuf_cells, wz. exact PB.
    - zstep.
      pose proof (fin_off0 blen (off + 1) bs LEN ltac:(lia)) as FO.
      eapply evt_cut.
      { eapply (ws1 sp gp tp s9 s10 s11 SPB LB LR U P CA blen off depth bs D n lo PVC (Z.to_nat (blen - (off + 1))) (off + 1) (depth + 1) m3 m3);
          [lia| lia| unfold pbuf_cells, wz; exact PB| exact BY| exact MI| apply munch_refl| apply wmono_refl]. }
      intros ms' (x17' & m4 & -> & PB4 & BY4 & MI4 & MU4 & WM4). rewrite <- FO in PB4 |- *.
      eapply JOIN; [exact PB4| exact BY4| exact MI4| exact MU4| exact WM4].
  Qed.
End POE.

(* [comment removed for export] *)
Theorem po_step : forall HI nfuel,
  (forall nf, (nf < nfuel)%nat -> parse_value_at HI nf) -> parse_object_at HI nfuel.
Proof.
  intros HI nfuel PVREC. unfold parse_object_at. intros until ky.
  intros (HL & HPU & HD & DCA & CAD & BY & LEN & BLEN & CJ & ERR & MI & ST & CEIL & SPP & PSPB & SPB62) ND PB OFF DEP FUEL LO FRM TP A0 A1.
  assert (INU : In (U, 64) LB) by (eapply perm_in_head; exact HPU).
  assert (IND : In (D, n) LB) by (eapply Permutation_in; [exact HPU| right; exact HD]).
  assert (UD : U <> D).
  { intros ->. pose proof (lh_nodup HI _ _ _ _ HL) as NDP.
    apply (NoDup_map_fst_perm _ _ (Permutation_sym HPU)) in NDP. rewrite NoDup_ListNoDup in NDP. cbn in NDP.
    inversion NDP; subst. apply H1. apply (in_map fst) in HD. exact HD. }
  eapply (po_body HI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m SPB LB LR U P CA blen off depth bs D n lo nx pv ty p1 vi p2 vd ky);
    [| exact FUEL| exact PVREC| exact HL| exact BY| exact CJ| exact ERR| exact MI| exact ST| exact ND| exact PB| exact FRM| exact A0| exact A1].
  split; [exact HPU|]. split; [split; [exact HD| split; [exact DCA| exact CAD]]|]. split; [exact LEN|]. split; [exact BLEN|].
  split; [exact CEIL|]. split; [exact LO|]. split; [split; [exact SPP| split; [exact PSPB| exact SPB62]]|]. split; [exact OFF|]. split; [exact DEP|].
  split; [exact TP|]. split; [eapply (lh_block_range HI); [exact HL| exact INU]|]. split; [eapply (lh_block_range HI); [exact HL| exact IND]|].
  destruct (lh_blocks_disjoint HI _ _ _ _ _ _ _ _ HL INU IND UD); lia.
Qed.




End CeilWrap.
