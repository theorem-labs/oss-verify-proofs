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
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require LiaOn.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require AImg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_defs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require AShadow.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_tree.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_phex4.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_conv.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require NElim.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_pstrA.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require StoreCache.
Module CJ_pstring_A.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.LiaOn.SepM.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AShadow OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_tree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_phex4.CJ_pbuf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_conv OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_phex4.CJ_parse_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_phex4.CJ_parse_lemmas.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_pstrA.CJ_shfast.
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
Definition ps_frame (j0 : list byte) (U P : Z) (s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra : word) : list cell :=
  [CB 8 j0; C8 (Z_to_bv 64 0xdc00); C8 (Z_to_bv 64 0xd800); C8 (Z_to_bv 64 U); C8 (Z_to_bv 64 P);
   C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Section PS.
  Variables (sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 rav : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (m2 : word -> option byte) (CA blen off e sk S P U lo : Z) (bs j0 : list byte).

  Definition F0 : nat := Z.to_nat blen.
  Definition nalloc : Z := e - off - sk + 1.
  (* [comment removed for export] *)
  Definition W2 : list (Z * Z) := [(S, S + nalloc); (lo, bv_unsigned sp + -144)].
  Definition FRAME : list cell := ps_frame j0 U P s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 rav.

  (* [comment removed for export] *)
  Definition ps_ctx : Prop :=
    Z.of_nat (length bs) = blen
    /\ bytes_at asegs m2 CA bs
    /\ rw_cells asegs m2 (bv_unsigned sp + -144) FRAME
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
  Definition S4 : word := Z_to_bv 64 (Z.shiftr (P + 16) 3 + 2147450880).
  Definition S5 : word := Z_to_bv 64 (Z.shiftr P 3 + 2147450880).

  Definition LST (pc : Z) (x5 x6 x7 x12 x13 x14 x15 x16 x17 x25 x28 : word) (i oc : Z) (mm : word -> option byte) : machine_state :=
    MS (mkR (Z_to_bv 64 13) (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp x5 x6 x7 (Z_to_bv 64 (P + 16)) (Z_to_bv 64 (CA + i))
            (Z_to_bv 64 S) (Z_to_bv 64 P) x12 x13 x14 x15 x16 x17
            (Z_to_bv 64 (CA + e)) (Z_to_bv 64 (S + oc)) S4 S5 (Z_to_bv 64 2147450880) (Z_to_bv 64 (CA + e))
            (Z_to_bv 64 10) x25 (Z_to_bv 64 92) (Z_to_bv 64 JT) x28 (Z_to_bv 64 83) (Z_to_bv 64 8) (Z_to_bv 64 12))
       F (Z_to_bv 64 pc) fc None mm (seg_rom asegs).

  (* [comment removed for export] *)
  Definition lmem (mm : word -> option byte) (buf : list byte) : Prop :=
    u8arr asegs mm S buf /\ length buf = Z.to_nat nalloc /\ munch W2 m2 mm /\ wmono asegs m2 mm /\ mem_inv asegs mm
    /\ stk asegs mm lo (bv_unsigned sp + -144).

  Definition KPOST : machine_state -> Prop := fun ms' =>
    exists (mm : word -> option byte) (buf : list byte) (x5 x6 x7 x12 x13 x14 x15 x16 x17 x25 x28 : word) (i oc : Z),
      lmem mm buf /\ off + 1 <= i <= e + 1 /\ 0 <= oc /\ oc + 1 <= nalloc
      /\ ( ms' = LST 0x8604c x5 x6 x7 x12 (Z_to_bv 64 U) x14 x15 x16 x17 x25 x28 i oc mm      (* [comment removed for export] *)
           \/ ms' = LST 0x860b0 x5 x6 x7 x12 x13 x14 x15 x16 x17 x25 x28 i oc mm ).          (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition LOOPK (k : nat) : Prop :=
    forall (i oc : Z) (mm : word -> option byte) (buf : list byte) (x5 x6 x12 x14 x15 x16 x17 x25 : word),
      e - i <= Z.of_nat k -> off + 1 <= i < e -> dinv i oc -> 0 <= oc -> lmem mm buf ->
      evt asegs KPOST (LST 0x85b44 x5 x6 (Z_to_bv 64 6) x12 (Z_to_bv 64 U) x14 x15 x16 x17 x25 (Z_to_bv 64 9) i oc mm).

  (* [comment removed for export] *)
  Lemma lmem_facts : forall mm buf, lmem mm buf ->
    bytes_at asegs mm CA bs /\ rw_cells asegs mm (bv_unsigned sp + -144) FRAME.
  Proof.
    intros mm buf nelH_; (nelim nelH_ 6%nat; intros BUF BL MU WM MI ST). pose proof ctx_arith as A. (nelimp CTX 4%nat; intros L BY2 FR2 _).
    try rewrite alloc_ceiling_eq in A. unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG, W2 in *. split.
    - eapply bytes_at_transport; [exact BY2| exact MU|]. cbn. lia.
    - eapply rw_cells_transport; [exact FR2| exact MU| exact WM|]. cbn. lia.
  Qed.

  Ltac pre := pose proof ctx_arith as ARITH; (nelimp ctx_sh 3%nat; intros SB2 TS2 SO2); pose proof ctx_band as SBND;
              try rewrite alloc_ceiling_eq in ARITH; unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG, W2, nalloc in *.

  (* [comment removed for export] *)
  Lemma exit_ok : forall i oc mm buf x5 x6 x7 x12 x14 x15 x16 x17 x25 x28,
    lmem mm buf -> off + 1 <= i <= e + 1 -> 0 <= oc -> oc + 1 <= nalloc ->
    evt asegs KPOST (LST 0x8604c x5 x6 x7 x12 (Z_to_bv 64 U) x14 x15 x16 x17 x25 x28 i oc mm).
  Proof. intros. apply evt_done. unfold KPOST. exists mm, buf, x5, x6, x7, x12, x12. nexists 8%nat. repeat (split; [eassumption|]). left; reflexivity. Qed.

  Lemma exit_fail : forall i oc mm buf x5 x6 x7 x12 x13 x14 x15 x16 x17 x25 x28,
    lmem mm buf -> off + 1 <= i <= e + 1 -> 0 <= oc -> oc + 1 <= nalloc ->
    evt asegs KPOST (LST 0x860b0 x5 x6 x7 x12 x13 x14 x15 x16 x17 x25 x28 i oc mm).
  Proof. intros. apply evt_done. unfold KPOST. nexists 15%nat. repeat (split; [eassumption|]). right; reflexivity. Qed.

  Section Body.
    Variable k : nat.
    Hypothesis IH : forall k', (k' < k)%nat -> LOOPK k'.

    (* [comment removed for export] *)
    Lemma go_head : forall i oc mm buf x5 x6 x12 x14 x15 x16 x17 x25,
      e - i < Z.of_nat k -> off + 1 <= i < e -> dinv i oc -> 0 <= oc -> lmem mm buf ->
      evt asegs KPOST (LST 0x85b44 x5 x6 (Z_to_bv 64 6) x12 (Z_to_bv 64 U) x14 x15 x16 x17 x25 (Z_to_bv 64 9) i oc mm).
    Proof.
      intros. destruct k as [|k']; [lia|]. eapply (IH k'); [lia| lia| assumption| assumption| assumption| eassumption].
    Qed.

    (* [comment removed for export] *)
    Definition TESTPCS : list Z := [0x85b30; 0x85bb8; 0x85bdc; 0x85c04; 0x85c58; 0x85c80; 0x85ca8; 0x85f64].

    Lemma tests : forall pc i oc mm buf x5 x6 x12 x14 x15 x16 x17 x25,
      In pc TESTPCS ->
      e - i < Z.of_nat k -> off + 1 <= i <= e + 1 -> dinv i oc -> 0 <= oc -> lmem mm buf ->
      evt asegs KPOST (LST pc x5 x6 (Z_to_bv 64 6) x12 (Z_to_bv 64 U) x14 x15 x16 x17 x25 (Z_to_bv 64 9) i oc mm).
    Proof.
      intros until x25. intros HIn Hk Hi DI Hoc LM. pre. (nelimp LM 6%nat; intros BUF BL MU WM MI ST).
      assert (EXIT : e <= i -> evt asegs KPOST (LST 0x8604c x5 x6 (Z_to_bv 64 6) x12 (Z_to_bv 64 U) x14 x15 x16 x17 x25 (Z_to_bv 64 9) i oc mm)).
      { intros He. eapply exit_ok; [exact LM| lia| lia| apply (dinv_end i oc DI); lia]. }
      unfold LST in *.
      sepM. destruct HIn as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]];
        (zstep; if_cases Kt; zify_cond Kt; [eapply go_head; [lia| lia| exact DI| exact Hoc| exact LM] | zstep; apply EXIT; lia]).
    Qed.

    (* [comment removed for export] *)
    Lemma first_byte_tail : forall i oc (len sl : Z) (v : word) mm buf x5 x6 x12 x16 x17,
      e - i <= Z.of_nat k -> off + 1 <= i -> i + sl <= e + 1 -> 1 <= sl -> 1 <= len -> 0 <= oc -> oc + len <= nalloc ->
      dinv (i + sl) (oc + len) -> lmem mm buf ->
      evt asegs KPOST (LST 0x85f48 x5 x6 (Z_to_bv 64 6) x12 (Z_to_bv 64 U) (Z_to_bv 64 sl) (Z_to_bv 64 len) x16 x17 v (Z_to_bv 64 9) i oc mm).
    Proof.
      intros until x17. intros Hk Hi Hsl Hsl1 Hlen Hoc ROOM DI LM. (nelimp LM 6%nat; intros BUF BL MU WM MI ST). pre. unfold LST.
      zstep. zstep.
      pose proof (shadow_ok_shchk1 m2 S _ (S + oc) SO2 ltac:(lia)) as CK. asan_chk CK.
      pose proof (u8arr_store_ok asegs _ _ _ oc (Z_to_bv 64 (S + oc)) BUF ltac:(lia) eq_refl) as SOK.
      zstep. rewrite <- (Z_to_bv_bv_unsigned v), le1_lit.
      pose proof (u8arr_write asegs _ _ _ oc (Z_to_bv 8 (bv_unsigned v)) BUF ltac:(lia)) as BUF'.
      clear BUF. store_done. rename BUF' into BUF.
      zstep. zstep.
      replace (S + oc + len) with (S + (oc + len)) by lia. replace (CA + i + sl) with (CA + (i + sl)) by lia.
      eapply tests; [cbn; auto 10| lia| lia| exact DI| lia|].
      split; [exact BUF|]. split; [rewrite upd_length; exact BL|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact ST].
    Qed.

    (* [comment removed for export] *)
    Lemma encode_tail : forall i oc (len sl cp mark : Z) mm buf x5 x6 x7 x12 x17,
      e - i <= Z.of_nat k -> off + 1 <= i -> i + sl <= e + 1 -> 1 <= sl -> 2 <= len <= 4 -> 0 <= cp < 2^32 -> 0 <= mark < 256 -> 0 <= oc -> oc + len <= nalloc ->
      dinv (i + sl) (oc + len) -> lmem mm buf ->
      evt asegs KPOST (LST 0x85ed8 x5 x6 x7 x12 (Z_to_bv 64 U) (Z_to_bv 64 sl) (Z_to_bv 64 len) (Z_to_bv 64 mark) x17 (Z_to_bv 64 cp) (Z_to_bv 64 9) i oc mm).
    Proof.
      intros until x17. intros Hk Hi Hsl Hsl1 Hlen Hcp Hmk Hoc ROOM DI LM. (nelimp LM 6%nat; intros BUF BL MU WM MI ST). pre. unfold LST.
      (* [comment removed for export] *)
      Ltac cont_byte SO BUF idx :=
        zstep; zstep;
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
          let CK := fresh "CK" in
          pose proof (shadow_ok_shchk1 _ S _ (S + idx) SO ltac:(lia)) as CK; asan_chk CK;
          pose proof (u8arr_store_ok asegs mx S _ idx (Z_to_bv 64 (S + idx)) BUF ltac:(rewrite ?upd_length; lia) ltac:(unfold wa; f_equal; lia)) as SOK;
          zstep; zstep; zstep; zstep; zstep;
          zstep; rewrite le1_lit;
          let BUF' := fresh "BUF" in
          lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ [Z_to_bv 8 ?v]) _) =>
            pose proof (u8arr_write asegs mx S _ idx (Z_to_bv 8 v) BUF ltac:(rewrite ?upd_length; lia)) as BUF' end;
          clear BUF; store_done; rename BUF' into BUF;
          zstep; zstep; zstep
        end.
      Ltac to_first BUF BL MU WM MI ST DI :=
        if_false; zstep; zstep; zstep; zstep;
        eapply first_byte_tail; [lia| lia| lia| lia| lia| lia| unfold nalloc; lia| exact DI|];
        split; [exact BUF|]; split; [rewrite ?upd_length; exact BL|]; split; [exact MU|]; split; [exact WM|]; split; [exact MI| exact ST].
      assert (HL : len = 2 \/ len = 3 \/ len = 4) by lia.
      destruct HL as [-> | [-> | ->]]; zstep; zstep; zstep; zstep.
      - sepM. cont_byte SO2 BUF (oc + 1). to_first BUF BL MU WM MI ST DI.
      - sepM. cont_byte SO2 BUF (oc + 2). if_true. sepM. cont_byte SO2 BUF (oc + 1). to_first BUF BL MU WM MI ST DI.
      - sepM. cont_byte SO2 BUF (oc + 3). if_true. sepM. cont_byte SO2 BUF (oc + 2). if_true. sepM. cont_byte SO2 BUF (oc + 1). to_first BUF BL MU WM MI ST DI.
    Qed.

    (* [comment removed for export] *)
    Definition ESCPCS : list Z := [0x85b10; 0x85b98; 0x85be4; 0x85c38; 0x85c60; 0x85c88].

    Lemma esc_simple : forall pc i oc (c : Z) mm buf x5 x6 x14 x15 x16 x17 x25,
      In pc ESCPCS -> 0 <= c < 256 ->
      e - i <= Z.of_nat k -> off + 1 <= i -> i + 2 <= e + 1 -> 0 <= oc -> oc + 1 <= nalloc ->
      dinv (i + 2) (oc + 1) -> lmem mm buf ->
      evt asegs KPOST (LST pc x5 x6 (Z_to_bv 64 6) (Z_to_bv 64 c) (Z_to_bv 64 U) x14 x15 x16 x17 x25 (Z_to_bv 64 9) i oc mm).
    Proof.
      intros until x25. intros HIn Hc Hk Hi Hie Hoc ROOM DI LM. (nelimp LM 6%nat; intros BUF BL MU WM MI ST). pre. unfold LST.
      sepM. destruct HIn as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]];
        (zstep; zstep;
         pose proof (shadow_ok_shchk1 _ S _ (S + oc) SO2 ltac:(lia)) as CK; asan_chk CK;
         pose proof (u8arr_store_ok asegs _ _ _ oc (Z_to_bv 64 (S + oc)) BUF ltac:(lia) eq_refl) as SOK;
         zstep; rewrite le1_lit;
         let BUF' := fresh "BUF" in
         lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mx _ [Z_to_bv 8 ?v]) _) =>
           pose proof (u8arr_write asegs mx S _ oc (Z_to_bv 8 v) BUF ltac:(lia)) as BUF' end;
         clear BUF; store_done; rename BUF' into BUF;
         zstep; zstep; zstep;
         replace (S + oc + 1) with (S + (oc + 1)) by lia; replace (CA + i + 2) with (CA + (i + 2)) by lia;
         eapply tests; [cbn; auto 10| lia| lia| exact DI| lia|];
         split; [exact BUF|]; split; [rewrite upd_length; exact BL|]; split; [exact MU|]; split; [exact WM|]; split; [exact MI| exact ST]).
    Qed.
  End Body.
End PS.


End CeilWrap.
End CJ_pstring_A.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import ShapeAlg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Tac Bytes.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require LiaOn.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.LiaOn.SepM.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import CJ_bandM AImg RT_defs CJ_iface AShadow CJ_tree.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_phex4.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_phex4.CJ_pbuf.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import CJ_conv.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_phex4.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_phex4.CJ_parse_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_phex4.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_phex4.CJ_parse_lemmas.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import CJ_phex4.
Import CJ_pstring_A.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_pstrA.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_pstrA.CJ_shfast.
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
(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require RegFold.
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step.simp_regs ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.RegFold.simp_regs_raw.
(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require StepFast.
#[local] Ltac2 Set OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StepFast.SF.sf_mode := 0.
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Lemma jt_cases : forall c,
  ((c = 34 \/ c = 47 \/ c = 92) /\ jt_off c = 0x64b0c)
  \/ (c = 98 /\ jt_off c = 0x64b94) \/ (c = 102 /\ jt_off c = 0x64be0) \/ (c = 117 /\ jt_off c = 0x64c08)
  \/ (c = 114 /\ jt_off c = 0x64c34) \/ (c = 110 /\ jt_off c = 0x64c5c) \/ (c = 116 /\ jt_off c = 0x64c84)
  \/ jt_off c = 0x650ac.
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
  Variables (m2 : word -> option byte) (CA blen off e sk S P U lo : Z) (bs j0 : list byte).
  Hypothesis CTX : ps_ctx sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 rav m2 CA blen off e sk S P U lo bs j0.

  Notation LSTx := (LST sp gp tp F fc CA e S P).
  Notation KP := (KPOST sp gp tp F fc m2 CA off e sk S P U lo).
  Notation LM := (lmem sp m2 off e sk S lo).
  Notation DINV := (dinv blen off bs).
  Notation NA := (nalloc off e sk).
  Notation L z := (Z_to_bv 64 z) (only parsing).
  Notation LU := (Z_to_bv 64 U).

  Ltac ctx := pose proof (ctx_arith _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CTX) as ARITH;
              (nelimp (ctx_sh _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CTX) 3%nat; intros SB2 TS2 SO2);
              pose proof (ctx_band _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CTX) as SBND;   (* [comment removed for export] *)
              try rewrite alloc_ceiling_eq in ARITH; unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in ARITH, SBND; bandM; sepM.
  Ltac lm LMm mm buf :=
    pose proof (lmem_facts _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CTX mm buf LMm) as [BY FR]; unfold FRAME, ps_frame in FR;
    (nelimp LMm 6%nat; intros BUF BL MU WM MI ST).
  Ltac ml := Z.div_mod_to_equations; lia.

  Section Body.
    Variable k : nat.
    Hypothesis IH : forall k', (k' < k)%nat -> LOOPK sp gp tp F fc m2 CA blen off e sk S P U lo bs k'.

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
      Proof. ctx. eapply (dinv_room _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CTX i oc 4 DI); lia. Qed.

      Lemma dinv_u : forall c p, 6 <= c -> p + (c + 1) / 2 <= c -> DINV (i + c) (oc + p).
      Proof. intros c p Hc Hp. eapply dinv_step; [exact DI| lia| lia| rewrite bflag_i; exact Hp]. Qed.

      Ltac preU := ctx; lm LMm mm buf; pose proof room4 as ROOM; unfold W2, nalloc in *; unfold LST.

      Ltac fail_exit := eapply exit_fail; [exact LMm| lia| lia| unfold nalloc; lia].

      (* [comment removed for export] *)
      Lemma L_cls : forall FC x5 x6 x7 x12 x14 x15 x16 x17, 0 <= FC < 2^16 ->
        evt asegs KP (LSTx 0x85dec x5 x6 x7 x12 LU x14 x15 x16 x17 (Z_to_bv 64 FC) (Z_to_bv 64 9) i oc mm).
      Proof.
        intros until x17. intros HFC. preU.
        zstep. zstep. zstep. if_cases Ksur; zify_cond Ksur.
        - (* [comment removed for export] *)
          zstep. zstep. zstep. zstep. rewrite (bv_lts_small (CA + e - (CA + i + 6)) 6) by lia.
          if_cases Kl; zify_cond Kl; [fail_exit|].
          zstep. zstep.
          pose proof (TS2 (CA + i + 6) ltac:(lia)) as CK6. asan_chk CK6.
          (nelim (text_read mm CA bs (i + 6) (Z_to_bv 64 (CA + i + 6)) BY ltac:(lia) ltac:(lia) ltac:(unfold wa; f_equal; lia)) 4%nat; intros c6 Hc6 RD6 _).
          zstep. zstep. if_cases K6; zify_cond K6; [fail_exit|].
          zstep. zstep. zstep.
          pose proof (TS2 (CA + i + 7) ltac:(lia)) as CK7. asan_chk CK7.
          (nelim (text_read mm CA bs (i + 7) (Z_to_bv 64 (CA + i + 7)) BY ltac:(lia) ltac:(lia) ltac:(unfold wa; f_equal; lia)) 4%nat; intros c7 Hc7 RD7 _).
          zstep. zstep. zstep. if_cases K7; zify_cond K7; [fail_exit|].
          zstep. zstep. zstep. zstep.
          pose proof (bytes_at_window mm CA bs (i + 8) 4 BY ltac:(lia) ltac:(lia)) as B4.
          eapply evt_cut.
          { eapply hex4_spec with (lo := lo); rewrite ?unsigned_lit by lia.
            - exact B4. - apply firstn_skipn_length; lia. - try rewrite alloc_ceiling_eq; lia.
            - eapply shbase_cells_munch; [exact SB2| exact MU| cbn; lia| cbn; lia].
            - eapply text_sh_sub; [eapply text_sh_munch; [exact TS2| exact MU| lia| lia| cbn; unfold SH, SHADOW_OFFSET; Z.div_mod_to_equations; lia]| lia| lia].
            - exact MI. - exact ST. - try rewrite alloc_ceiling_eq; lia. - unfold PARSE_HEX4_STACK; lia. - f_equal; lia. }
          cbv beta. clear B4. intros ms' PO.
          (nelim PO 18%nat; intros t0' t1' a1' a2' a3' a4' a5' a6' a7' m3 h -> MUc WMc MI3 ST3 B4 Hh).
          rewrite ?unsigned_lit in MUc by lia. rewrite ?unsigned_lit in ST3 by lia.
          transport_after_call asegs mm m3 MUc WMc.
          replace (ret_pc (Z_to_bv 64 0x85e7c)) with (Z_to_bv 64 0x85e7c) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
          (* [comment removed for export] *)
          do 14 zstep. if_cases Kr; zify_cond Kr.
          { eapply exit_fail; [| lia| lia| unfold nalloc; lia].
            split; [eassumption|]. split; [exact BL|]. split; [assumption|]. split; [assumption|]. split; assumption. }
          (* [comment removed for export] *)
          do 9 zstep.
          lazymatch goal with |- context [Z_to_bv 64 (Z.lor ?a (Z.land ?h 1023) + 65536)] =>
            assert (Ha : 0 <= a < 2^20) by (clear -HFC; rewrite ?Z.shiftr_div_pow2, ?Z.shiftl_mul_pow2 by lia; ml);
            assert (Hb : 0 <= Z.land h 1023 < 2^20)
              by (clear -Hh; change 1023 with (2^10 - 1); rewrite zb_land_mask by lia; ml);
            pose proof (lor_bound _ _ 20 Ha Hb) as HL;
            assert (CPR : 0 <= Z.lor a (Z.land h 1023) + 65536 < 2^32) by (clear -HL; lia)
          end.
          eapply encode_tail; [exact CTX| exact IH| lia| lia| lia| lia| lia| exact CPR| lia| lia| unfold nalloc; lia| apply dinv_u; [lia| cbv; discriminate] |].
          split; [eassumption|]. split; [exact BL|]. split; [assumption|]. split; [assumption|]. split; assumption.
        - zstep. zstep. zstep. if_cases Klow; zify_cond Klow; [fail_exit|].
          zstep. zstep. if_cases K1; zify_cond K1.
          + (* [comment removed for export] *) zstep. zstep.
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
      Lemma L_inv : forall pc x5 x6 x7 x12 x14 x15 x16 x17 x25,
        (pc = 0x85dac /\ x7 = Z_to_bv 64 6) \/ pc = 0x85f38 ->
        evt asegs KP (LSTx pc x5 x6 x7 x12 LU x14 x15 x16 x17 x25 (Z_to_bv 64 9) i oc mm).
      Proof.
        intros until x25. intros Hpc. preU.
        destruct Hpc as [[-> ->]| ->].
        - zstep. zstep. zstep. zstep.
          eapply first_byte_tail; [exact CTX| exact IH| lia| lia| lia| lia| lia| lia| unfold nalloc; lia| apply dinv_u; [lia| cbv; discriminate]| exact LMm].
        - zstep. zstep. zstep. zstep.
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
        Lemma L_comb : forall (J0 J1 J2 J3 : Z) x25,
          0 <= K0 + J0 <= 15 -> 0 <= K1 + J1 <= 15 -> 0 <= K2 + J2 <= 15 -> 0 <= K3 + J3 <= 15 ->
          evt asegs KP (LSTx 0x85dc4 (L K2) (L J2) (L J3) (L K3) LU (L K0) (L J0) (L K1) (L J1) x25 (L 9) i oc mm).
        Proof.
          intros until x25. intros D0 D1 D2 D3. preU. bytes. do 10 zstep.
          lazymatch goal with |- evt _ _ (MS (TNode _ _ (TNode _ _ (TNode _ (Some (Z_to_bv 64 ?fc')) _))) _ _ _ _ _ _) => idtac end.
          lazymatch goal with |- context [Z_to_bv 64 (?a + (K3 + J3))] =>
            replace (Z_to_bv 64 (a + (K3 + J3))) with (Z_to_bv 64 ((K0 + J0) * 4096 + (K1 + J1) * 256 + (K2 + J2) * 16 + (K3 + J3)))
              by (apply Z_to_bv_eqm; clear -D0 D1 D2 D3; rewrite ?zb_shiftl_mul by lia; ml)
          end.
          apply L_cls. lia.
        Qed.

        (* [comment removed for export] *)
        Lemma L_c3 : forall (J0 J1 J2 : Z) x12,
          0 <= K0 + J0 <= 15 -> 0 <= K1 + J1 <= 15 -> 0 <= K2 + J2 <= 15 ->
          evt asegs KP (LSTx 0x85d6c (L K2) (L J2) (L 6) x12 LU (L K0) (L J0) (L K1) (L J1) (L 6) (L 9) i oc mm).
        Proof.
          intros until x12. intros D0 D1 D2. preU. bytes.
          (nelim (text_read mm CA bs (i + 5) (Z_to_bv 64 (CA + i + 5)) BY ltac:(lia) ltac:(lia) ltac:(unfold wa; f_equal; lia)) 4%nat; intros c3' Hc3' RD3 _).
          rewrite Hc3 in Hc3'. injection Hc3' as <-.
          zstep. zstep. zstep. pose proof (TS2 (CA + i + 5) ltac:(lia)) as CK. asan_chk CK.
          zstep. zstep. zstep. if_cases Ka; zify_cond Ka.
          - (* [comment removed for export] *) zstep. zstep. zstep. if_cases Kb; zify_cond Kb.
            + (* [comment removed for export] *) zstep. zstep. zstep. if_cases Kc; zify_cond Kc; [apply L_inv; right; reflexivity|].
              zstep. apply L_comb; clear -D0 D1 D2 Ka Kb Kc H H0 H1 H2; ml.
            + zstep. zstep. apply L_comb; clear -D0 D1 D2 Ka Kb H H0 H1 H2; ml.
          - zstep. zstep. zstep. apply L_comb; clear -D0 D1 D2 Ka H H0 H1 H2; ml.
        Qed.

        (* [comment removed for export] *)
        Lemma L_c2 : forall (J0 J1 : Z) x5 x6 x12 x25,
          0 <= K0 + J0 <= 15 -> 0 <= K1 + J1 <= 15 ->
          evt asegs KP (LSTx 0x85d18 x5 x6 (L 6) x12 LU (L K0) (L J0) (L K1) (L J1) x25 (L 9) i oc mm).
        Proof.
          intros until x25. intros D0 D1. preU. bytes.
          (nelim (text_read mm CA bs (i + 4) (Z_to_bv 64 (CA + i + 4)) BY ltac:(lia) ltac:(lia) ltac:(unfold wa; f_equal; lia)) 4%nat; intros c2' Hc2' RD2 _).
          rewrite Hc2 in Hc2'. injection Hc2' as <-.
          zstep. zstep. zstep. pose proof (TS2 (CA + i + 4) ltac:(lia)) as CK. asan_chk CK.
          zstep. zstep. zstep. if_cases Ka; zify_cond Ka.
          - zstep. zstep. if_cases Kb; zify_cond Kb.
            + zstep. zstep. zstep. if_cases Kc; zify_cond Kc; [apply L_inv; left; split; reflexivity|].
              zstep. zstep. apply L_c3; clear -D0 D1 Ka Kb Kc H H0 H1 H2; ml.
            + zstep. zstep. zstep. apply L_c3; clear -D0 D1 Ka Kb H H0 H1 H2; ml.
          - zstep. zstep. zstep. apply L_c3; clear -D0 D1 Ka H H0 H1 H2; ml.
        Qed.

        (* [comment removed for export] *)
        Lemma L_c1 : forall (J0 : Z) x5 x6 x12 x16 x17 x25,
          0 <= K0 + J0 <= 15 ->
          evt asegs KP (LSTx 0x85cd0 x5 x6 (L 6) x12 LU (L K0) (L J0) x16 x17 x25 (L 9) i oc mm).
        Proof.
          intros until x25. intros D0. preU. bytes.
          (nelim (text_read mm CA bs (i + 3) (Z_to_bv 64 (CA + i + 3)) BY ltac:(lia) ltac:(lia) ltac:(unfold wa; f_equal; lia)) 4%nat; intros c1' Hc1' RD1 _).
          rewrite Hc1 in Hc1'. injection Hc1' as <-.
          zstep. zstep. zstep. pose proof (TS2 (CA + i + 3) ltac:(lia)) as CK. asan_chk CK.
          zstep. zstep. zstep. if_cases Ka; zify_cond Ka.
          - zstep. zstep. if_cases Kb; zify_cond Kb.
            + zstep. zstep. zstep. if_cases Kc; zify_cond Kc; [apply L_inv; left; split; reflexivity|].
              zstep. apply L_c2; clear -D0 Ka Kb Kc H H0 H1 H2; ml.
            + zstep. zstep. apply L_c2; clear -D0 Ka Kb H H0 H1 H2; ml.
          - zstep. zstep. apply L_c2; clear -D0 Ka H H0 H1 H2; ml.
        Qed.

        (* [comment removed for export] *)
        Lemma L_c0 : forall x5 x6 x12 x14 x15 x16 x17 x25,
          evt asegs KP (LSTx 0x85c10 x5 x6 (L 6) x12 LU x14 x15 x16 x17 x25 (L 9) i oc mm).
        Proof.
          intros. preU. bytes.
          (nelim (text_read mm CA bs (i + 2) (Z_to_bv 64 (CA + i + 2)) BY ltac:(lia) ltac:(lia) ltac:(unfold wa; f_equal; lia)) 4%nat; intros c0' Hc0' RD0 _).
          rewrite Hc0 in Hc0'. injection Hc0' as <-.
          zstep. zstep. zstep. pose proof (TS2 (CA + i + 2) ltac:(lia)) as CK. asan_chk CK.
          zstep. zstep. zstep. if_cases Ka; zify_cond Ka.
          - zstep. zstep. if_cases Kb; zify_cond Kb.
            + zstep. zstep. zstep. if_cases Kc; zify_cond Kc; [apply L_inv; left; split; reflexivity|].
              zstep. apply L_c1; clear -Ka Kb Kc H H0 H1 H2; ml.
            + zstep. zstep. apply L_c1; clear -Ka Kb H H0 H1 H2; ml.
          - zstep. zstep. apply L_c1; clear -Ka H H0 H1 H2; ml.
        Qed.
      End Hex.

      (* [comment removed for export] *)
      Lemma esc_u : forall x5 x6 x12 x15 x16 x17 x25,
        evt asegs KP (LSTx 0x85c0c x5 x6 (L 6) x12 LU (Z_to_bv 64 (CA + e - (CA + i))) x15 x16 x17 x25 (L 9) i oc mm).
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
    Lemma head_k : LOOPK sp gp tp F fc m2 CA blen off e sk S P U lo bs k.
    Proof.
      unfold LOOPK. intros until x25. intros Hk Hi DI Hoc LMm. ctx. lm LMm mm buf. unfold W2, nalloc in *. unfold LST.
      pose proof (dinv_room _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CTX i oc 1 DI ltac:(lia) ltac:(lia)) as ROOM1. unfold nalloc in ROOM1.
      (nelim (text_read mm CA bs i (Z_to_bv 64 (CA + i)) BY ltac:(lia) ltac:(lia) eq_refl) 4%nat; intros b Hb RD Hat).
      pose proof (byte_range b) as Rb.
      zstep. zstep. pose proof (TS2 (CA + i) ltac:(lia)) as CK. asan_chk CK.
      zstep. zstep. if_cases Kbs; zify_cond Kbs.
      - (* [comment removed for export] *)
        zstep. zstep. pose proof (shadow_ok_shchk1 _ S _ (S + oc) SO2 ltac:(lia)) as CKo. asan_chk CKo.
        pose proof (u8arr_store_ok asegs _ _ _ oc (Z_to_bv 64 (S + oc)) BUF ltac:(lia) eq_refl) as SOK.
        zstep. rewrite le1_lit.
        pose proof (u8arr_write asegs _ _ _ oc (Z_to_bv 8 (bv_unsigned b)) BUF ltac:(lia)) as BUF'.
        clear BUF. store_done. rename BUF' into BUF.
        assert (DI' : DINV (i + 1) (oc + 1)).
        { eapply dinv_step; [exact DI| lia| lia|]. unfold bflag. rewrite Hat. replace (bv_unsigned b =? 92) with false by (symmetry; apply Z.eqb_neq; exact Kbs). reflexivity. }
        zstep. zstep.
        replace (S + oc + 1) with (S + (oc + 1)) by lia. replace (CA + i + 1) with (CA + (i + 1)) by lia.
        eapply tests; [exact CTX| exact IH| cbn; auto 10| lia| lia| exact DI'| lia|].
        split; [exact BUF|]. split; [rewrite upd_length; exact BL|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact ST].
      - (* [comment removed for export] *)
        assert (DI2 : DINV (i + 2) (oc + 1)).
        { eapply dinv_step; [exact DI| lia| lia|]. unfold bflag. rewrite Hat, Kbs. cbv. discriminate. }
        zstep. zstep. if_cases Kp.
        { (* [comment removed for export] *)
          eapply exit_fail; [exact LMm| lia| lia| unfold nalloc; lia]. }
        clear Kp.
        (nelim (text_read mm CA bs (i + 1) (Z_to_bv 64 (CA + i + 1)) BY ltac:(lia) ltac:(lia) ltac:(unfold wa; f_equal; lia)) 4%nat; intros c Hc RDc Hatc).
        pose proof (byte_range c) as Rc.
        zstep. zstep. zstep. pose proof (TS2 (CA + i + 1) ltac:(lia)) as CK1. asan_chk CK1.
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

  Theorem dec_loop : forall k, LOOPK sp gp tp F fc m2 CA blen off e sk S P U lo bs k.
  Proof. intros k. induction k as [k IH] using lt_wf_ind. apply head_k. exact IH. Qed.
End PS.


End CeilWrap.
