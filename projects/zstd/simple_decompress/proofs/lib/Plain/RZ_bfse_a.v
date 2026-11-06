(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdSeqTable ZdSeqBuild ZdSeqBuildThm.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import StrFun STRW_tac WStr FseWalkKit FseWalkMem FseRdKit MemRange ZdCellKit ZdWalkKit ZdSeqBuildW ZdSeqBuildW2.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Plain Require Import PImg RZ_blk_iface RZ_bfse_defs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.


Section A.
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : fmem)
            (SPV lo DT NC BASE BITS W maxSV tl : Z) (k : seq_kind) (wlen : nat) (norm : list Z).
  Hypothesis HY : bf_hyps SPV lo DT NC BASE BITS W maxSV tl k wlen norm.
  Notation POST t := (bf_post ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV DT W tl wlen lo m t).
  Notation ST pc mm xra x5 x6 x7 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 x28 x29 x30 x31 :=
    (MS (mkR xra (Z_to_bv 64 (SPV + -128)) gp tp x5 x6 x7 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom psegs)).
  Notation BFm := (BF ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m SPV lo DT NC BASE BITS W tl k wlen norm).

  Lemma size_rng : 32 <= 2^tl <= 512.
  Proof.
    open_bh HY. assert (2^5 <= 2^tl) by (apply Z.pow_le_mono_r; lia).
    assert (2^tl <= 2^9) by (apply Z.pow_le_mono_r; destruct k; cbn [kind_maxLog] in *; lia).
    change (2^5) with 32 in *. change (2^9) with 512 in *. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma bf_epi : forall m1 fast w8 w16 cells symNext spread xra x5 x6 x7 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 x28 x29 x30 x31,
    BFm (Z_to_bv 64 fast) (Z_to_bv 64 tl) w8 w16 cells symNext spread m1 -> 0 <= fast <= 1 ->
    evt psegs (POST (mkST fast tl cells))
      (ST 0x16b7c m1 xra x5 x6 x7 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 x28 x29 x30 x31).
  Proof.
    intros until x31. intros I HF. open_bh HY. open_bf I. pose proof size_rng as SZ.
    do 13 zstep. zstep.
    release_frame FR STK SPV.
    zstep. apply evt_done. unfold bf_post.
    do 15 eexists. exists m1.
    exists (u16s (map (Z_to_bv 64) symNext) ++ map (Z_to_bv 8) spread).
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact STK|].
    split; [apply table_u8arr; assumption|].
    unfold FseNCount.Zlength in *.
    split.
    - apply u8arr_app. split; [exact SNX|]. rewrite u16s_length, length_map.
      replace (W + Z.of_nat (2 * length symNext)) with (W + 106) by lia. exact SPRD.
    - rewrite length_app, u16s_length, !length_map. lia.
  Qed.

  (* [comment removed for export] *)
  Notation ST3 pc mm xra xs0 xs1 xa0 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 x28 x29 x30 x31 :=
    (ST pc mm xra (Z_to_bv 64 858993459) (Z_to_bv 64 252645135) (Z_to_bv 64 16843009) xs0 xs1 xa0 (Z_to_bv 64 (DT + 12 + 8 * 2^tl)) (Z_to_bv 64 (2^tl))
        (Z_to_bv 64 BASE) (Z_to_bv 64 BITS) (Z_to_bv 64 tl) (Z_to_bv 64 W) (Z_to_bv 64 1431655765)
        xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 x28 x29 x30 x31).

  (* [comment removed for export] *)
  Lemma bf_p3_body : forall (t : seq_table) m1 h0 h1 w8 w16 u cells symNext spread xra xs0 xs1 xa0 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 x28 x29 x30 x31,
    BFm h0 h1 w8 w16 cells symNext spread m1 ->
    0 <= u < 2^tl ->
    good norm maxSV (ss_base (cell_nth cells u)) ->
    1 <= Znth (ss_base (cell_nth cells u)) symNext < 2 * 2^tl ->
    xa0 = Z_to_bv 64 (DT + 12 + 8 * u) ->
    (forall m2 y28 y29 y30 y31,
       BFm h0 h1 w8 w16 (set_cell u (build_one tl (kind_base k) (kind_bits k) (ss_base (cell_nth cells u)) (Znth (ss_base (cell_nth cells u)) symNext)) cells)
           (Zupd (ss_base (cell_nth cells u)) ((Znth (ss_base (cell_nth cells u)) symNext + 1) mod 2^16) symNext) spread m2 ->
       evt psegs (POST t) (ST3 0x16b78 m2 xra xs0 xs1 (Z_to_bv 64 (DT + 12 + 8 * u + 8)) xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 y28 y29 y30 y31)) ->
    evt psegs (POST t) (ST3 0x16ad0 m1 xra xs0 xs1 xa0 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 x28 x29 x30 x31).
  Proof.
    intros until x31; intros I HU GU NSR -> KONT; open_bh HY; pose proof size_rng as SZ; open_bf I.
    unfold FseNCount.Zlength in *.
    set (sym := ss_base (cell_nth cells u)) in *.
    lazymatch goal with |- _ => let a := cur_mem_addr in
      pose proof (u8arr_readn psegs _ (DT + 8) _ (8 * u + 4) 4 a CEL ltac:(lia) ltac:(rewrite cellsB_length; lia) ltac:(addr_tac)) as RD end.
    rewrite (cellsB_read_base cells u ltac:(unfold FseNCount.Zlength; lia)) in RD. fold sym in RD.
    zstep.
    assert (SYR : 0 <= sym <= maxSV) by (destruct GU; lia).
    assert (MSV52 : maxSV <= 52) by (destruct k; cbn [kind_max] in *; lia).
    rewrite (zx32w_small sym) by lia.
    zstep. zstep.
    lazymatch goal with |- _ => let a := cur_mem_addr in
      pose proof (u16_znth psegs m1 W symNext sym a (proj1 SNX) ltac:(lia) ltac:(addr_tac)) as RD2 end.
    zstep.
    set (ns := Znth sym symNext) in *.
    rewrite (zx16_u ns) by lia.
    zstep.
    replace (W + sym ≪ 1) with (W + 2 * sym) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
    assert (LBASE : Z.of_nat (length (kind_base k)) <= 53) by (destruct k; vm_compute; discriminate).
    assert (LBITS : Z.of_nat (length (kind_bits k)) <= 53) by (destruct k; vm_compute; discriminate).
    snst SNX sym (ns + 1) ((ns + 1) mod 2^16).
    (* [comment removed for export] *)
    zstep. zstep. set (sa := Z.lor ns (ns ≫ 1)). zstep. zstep. set (sb := Z.lor sa (sa ≫ 2)). zstep. zstep. set (sc := Z.lor sb (sb ≫ 4)).
    zstep. zstep. zstep.
    lazymatch goal with |- _ => let v := reg_val 29 in lazymatch v with Z_to_bv 64 ?e => change e with (smear16 ns) end end.
    rewrite (smear16_ok ns) by lia.
    set (L := Z.log2 ns) in *.
    assert (HL : 0 <= L <= 10).
    { subst L. split; [apply Z.log2_nonneg|]. assert (Z.log2 ns < 11); [|lia]. apply Z.log2_lt_pow2; [lia|]. change (2^11) with 2048. lia. }
    zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    lazymatch goal with |- _ => let v := reg_val 29 in lazymatch v with Z_to_bv 64 ?e =>
      replace e with L by (clear - HL; clearbody L;
        assert (C : L = 0 \/ L = 1 \/ L = 2 \/ L = 3 \/ L = 4 \/ L = 5 \/ L = 6 \/ L = 7 \/ L = 8 \/ L = 9 \/ L = 10) by lia;
        destruct C as [E|[E|[E|[E|[E|[E|[E|[E|[E|[E|E]]]]]]]]]]; rewrite E; vm_compute; reflexivity) end end.
    assert (LTL : L <= tl).
    { subst L. assert (Z.log2 ns < tl + 1); [|lia]. apply Z.log2_lt_pow2; [lia|]. rewrite Z.pow_add_r by lia. lia. }
    assert (TL9 : tl <= 9) by (destruct k; cbn [kind_maxLog] in *; lia).
    zstep.
    rewrite ?(Z.mod_small tl 18446744073709551616) by lia. rewrite (swrap32_small (tl - L)) by lia.
    zstep.
    rewrite (shiftl_mod32 ns (tl - L)) by lia.
    pose proof (shl_hb_range ns tl ltac:(lia) ltac:(lia) LTL) as NSB. fold L in NSB.
    rewrite (swrap32_small (ns * 2^(tl - L))) by lia.
    zstep.
    rewrite (swrap32_small (ns * 2^(tl - L) - 2^tl)) by lia.
    set (nxt := ns * 2^(tl - L) - 2^tl) in *.
    cst CEL u 0 2%nat cellsB_store_next (2^16).
    cst CEL u 3 1%nat cellsB_store_nbBits (2^8).
    assert (LKB : Z.of_nat (length (kind_bits k)) = kind_max k + 1 /\ Z.of_nat (length (kind_base k)) = kind_max k + 1) by (destruct k; split; reflexivity).
    lazymatch goal with |- _ => let a := cur_mem_addr in
      pose proof (u8ro_read psegs m0 BITS _ sym _ a BITSB (nth_error_map_Znth (Z_to_bv 8) (kind_bits k) sym ltac:(lia)) ltac:(lia) ltac:(addr_tac)) as RD3 end.
    zstep.
    assert (FBITS : Forall (fun v => 0 <= v < 256) (kind_bits k)) by (destruct k; repeat constructor; lia).
    assert (FBASE : Forall (fun v => 0 <= v < 2147483648) (kind_base k)) by (destruct k; repeat constructor; lia).
    pose proof (Forall_Znth _ _ sym FBITS ltac:(lia)) as RBITS. pose proof (Forall_Znth _ _ sym FBASE ltac:(lia)) as RBASE. cbv beta in RBITS, RBASE.
    cbv beta. rewrite (byte_lit (Znth sym (kind_bits k))) by lia.
    lazymatch goal with |- _ => let a := cur_mem_addr in
      pose proof (u32ro_read psegs m0 BASE _ sym _ a BASEB (nth_error_map_Znth (Z_to_bv 64) (kind_base k) sym ltac:(lia)) ltac:(lia) ltac:(unfold wa; f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia)) as RD4 end.
    zstep.
    rewrite (sx32w_small (Znth sym (kind_base k))) by lia.
    cst CEL u 2 1%nat cellsB_store_nbAdd (2^8).
    cst CEL u 4 4%nat cellsB_store_base (2^32).
    zstep.
    rewrite set_cell_fields in CEL by (unfold FseNCount.Zlength; lia).
    assert (CE : {| ss_next := nxt mod 2 ^ 16; ss_nbAdd := Znth sym (kind_bits k) mod 2 ^ 8; ss_nbBits := (tl - L) mod 2 ^ 8;
                    ss_base := Znth sym (kind_base k) mod 2 ^ 32 |} = build_one tl (kind_base k) (kind_bits k) sym ns).
    { unfold build_one. fold L. subst nxt. change (2^8) with 256. rewrite (Z.mod_small (tl - L) 256) by lia.
      rewrite (Z.mod_small (Znth sym (kind_bits k)) 256) by lia. rewrite (Z.mod_small (Znth sym (kind_base k)) (2^32)) by lia. reflexivity. }
    rewrite CE in CEL. clear CE.
    assert (CLEN' : zlenF (set_cell u (build_one tl (kind_base k) (kind_bits k) sym ns) cells) = 2^tl)
      by (unfold FseNCount.Zlength; rewrite set_cell_length; exact CLEN).
    assert (SNLEN' : zlenF (upd_nat (Z.to_nat sym) ((ns + 1) mod 2 ^ 16) symNext) = 53)
      by (unfold FseNCount.Zlength; rewrite FseLemmas.upd_nat_length; exact SNLEN).
    eapply KONT. unfold Zupd. close_bf.
  Qed.

  (* [comment removed for export] *)
  Lemma bf_p3_loop : forall (f : nat) m1 fast w8 w16 u cells symNext spread cellsF snF xra xs0 xs1 xa0 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 x28 x29 x30 x31,
    BFm (Z_to_bv 64 fast) (Z_to_bv 64 tl) w8 w16 cells symNext spread m1 -> 0 <= fast <= 1 ->
    0 <= u -> u + Z.of_nat (S f) = 2^tl ->
    (forall v, u <= v < 2^tl -> good norm maxSV (ss_base (cell_nth cells v))) ->
    (forall s, good norm maxSV s -> snext0 norm s <= Znth s symNext <= snext0 norm s + u) ->
    build_cells (S f) tl (kind_base k) (kind_bits k) u cells symNext = (cellsF, snF) ->
    xa0 = Z_to_bv 64 (DT + 12 + 8 * u) ->
    evt psegs (POST (mkST fast tl cellsF))
      (ST3 0x16ad0 m1 xra xs0 xs1 xa0 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 x28 x29 x30 x31).
  Proof.
    induction f as [|f IH]; intros until x31; intros I HF HU HUF GOODC SNB BC ->; open_bh HY; pose proof size_rng as SZ.
    all: assert (GU := GOODC u ltac:(lia)).
    all: assert (TL9 : 5 <= tl <= 9) by (destruct k; cbn [kind_maxLog] in *; lia).
    all: assert (NSR : 1 <= Znth (ss_base (cell_nth cells u)) symNext < 2 * 2^tl)
           by (pose proof (SNB _ GU); pose proof (snext0_good norm maxSV tl TL9 NLEN NGE NSUM _ GU); lia).
    - eapply bf_p3_body with (u := u); [exact I | lia | exact GU | exact NSR | reflexivity |].
      intros m2 y28 y29 y30 y31 I2.
      cbn [build_cells] in BC. injection BC as <- <-.
      zstep. if_cases K; zify_cond K; [exfalso; lia|].
      eapply bf_epi; [exact I2 | exact HF].
    - eapply bf_p3_body with (u := u); [exact I | lia | exact GU | exact NSR | reflexivity |].
      intros m2 y28 y29 y30 y31 I2.
      set (sym := ss_base (cell_nth cells u)) in *. set (ns := Znth sym symNext) in *.
      assert (E : build_cells (S (S f)) tl (kind_base k) (kind_bits k) u cells symNext
                  = build_cells (S f) tl (kind_base k) (kind_bits k) (u + 1)
                      (set_cell u (build_one tl (kind_base k) (kind_bits k) sym ns) cells) (Zupd sym ((ns + 1) mod 2^16) symNext)) by reflexivity.
      rewrite E in BC. clear E.
      zstep. if_cases K; zify_cond K; [|exfalso; lia].
      replace (DT + 12 + 8 * u + 8) with (DT + 12 + 8 * (u + 1)) by lia.
      eapply (IH m2 fast w8 w16 (u + 1)); [exact I2 | exact HF | lia | lia | | | exact BC | reflexivity].
      + intros v Hv. rewrite cell_nth_set_cell_other by lia. apply GOODC. lia.
      + intros s GS. destruct I as (_ & _ & _ & _ & SNLEN & _). unfold FseNCount.Zlength in SNLEN.
        assert (SYR : 0 <= sym <= 52) by (destruct GU; destruct k; cbn [kind_max] in *; lia).
        rewrite (Znth_Zupd_eq tl TL9) by (unfold FseNCount.Zlength; destruct GS; lia).
        pose proof (SNB s GS) as B. destruct (Z.eqb_spec s sym) as [->|NE].
        * fold ns in B. rewrite Z.mod_small by (change (2^16) with 65536; lia). lia.
        * lia.
  Qed.
End A.
