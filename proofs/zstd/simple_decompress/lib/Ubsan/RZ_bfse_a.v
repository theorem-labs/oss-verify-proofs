(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdSeqTable ZdSeqBuild ZdSeqBuildThm.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import StrFun STRW_tac WStr FseWalkKit FseWalkMem FseRdKit MemRange ZdCellKit ZdWalkKit ZdSeqBuildW ZdSeqBuildW2.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg RZ_blk_iface RZ_bfse_defs seqH_kit seqH_kit_fse.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.


Section A.
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : fmem)
            (SPV lo DT NC BASE BITS W maxSV tl : Z) (k : seq_kind) (wlen : nat) (norm : list Z).
  Hypothesis HY : bf_hyps SPV lo DT NC BASE BITS W maxSV tl k wlen norm.
  Hypothesis AL : bf_al DT W NC BASE.
  Notation POST t := (bf_post ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV DT W tl wlen lo m t).
  Notation ST pc mm xra x5 x6 x7 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 x28 x29 x30 x31 :=
    (MS (mkR xra (Z_to_bv 64 (SPV + -128)) gp tp x5 x6 x7 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom usegs)).
  Notation BFm := (BFU ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m SPV lo DT NC BASE BITS W tl k wlen norm).

  Lemma size_rng : 32 <= 2^tl <= 512.
  Proof.
    open_bh HY. assert (2^5 <= 2^tl) by (apply Z.pow_le_mono_r; lia).
    assert (2^tl <= 2^9) by (apply Z.pow_le_mono_r; destruct k; cbn [kind_maxLog] in *; lia).
    change (2^5) with 32 in *. change (2^9) with 512 in *. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma bf_epi : forall m1 fast w8 w16 cells symNext spread xra x5 x6 x7 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 x28 x29 x30 x31,
    BFm (Z_to_bv 64 fast) (Z_to_bv 64 tl) w8 w16 cells symNext spread m1 -> 0 <= fast <= 1 ->
    evt usegs (POST (mkST fast tl cells))
      (ST 0x172bc m1 xra x5 x6 x7 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 x28 x29 x30 x31).
  Proof.
    intros until x31. intros I HF. open_bh HY. open_bfu I. pose proof size_rng as SZ.
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
  Notation ST3 pc mm xra x7 xs1 xa0 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 :=
    (ST pc mm xra (Z_to_bv 64 (18446744073709551615 - W)) (Z_to_bv 64 (2^tl)) x7 (Z_to_bv 64 1) xs1 xa0 (Z_to_bv 64 31) (Z_to_bv 64 1)
        (Z_to_bv 64 BASE) (Z_to_bv 64 BITS) (Z_to_bv 64 tl) (Z_to_bv 64 W) (Z_to_bv 64 (DT + 8))
        xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 (Z_to_bv 64 1431655765) (Z_to_bv 64 858993459) (Z_to_bv 64 252645135) (Z_to_bv 64 16843009)).

  (* [comment removed for export] *)
  Lemma bf_p3_body : forall (t : seq_table) m1 h0 h1 w8 w16 u cells symNext spread xra xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11,
    BFm h0 h1 w8 w16 cells symNext spread m1 ->
    0 <= u < 2^tl ->
    good norm maxSV (ss_base (cell_nth cells u)) ->
    1 <= Znth (ss_base (cell_nth cells u)) symNext < 2 * 2^tl ->
    (forall m2 ys2 ys3 ys4 ys5,
       BFm h0 h1 w8 w16 (set_cell u (build_one tl (kind_base k) (kind_bits k) (ss_base (cell_nth cells u)) (Znth (ss_base (cell_nth cells u)) symNext)) cells)
           (Zupd (ss_base (cell_nth cells u)) ((Znth (ss_base (cell_nth cells u)) symNext + 1) mod 2^16) symNext) spread m2 ->
       evt usegs (POST t) (ST3 0x172b8 m2 xra (Z_to_bv 64 (2^tl - u + -1)) (Z_to_bv 64 (DT + 8 + 8 * u + 8)) (Z_to_bv 64 (DT + 12 + 8 * u + 8))
                               ys2 ys3 ys4 ys5 xs6 xs7 xs8 xs9 xs10 xs11)) ->
    evt usegs (POST t) (ST3 0x171c0 m1 xra (Z_to_bv 64 (2^tl - u)) (Z_to_bv 64 (DT + 8 + 8 * u)) (Z_to_bv 64 (DT + 12 + 8 * u))
                            xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11).
  Proof.
    intros until xs11; intros I HU GU NSR KONT; open_bh HY; pose proof size_rng as SZ; open_bfu I. pose proof AL as (DTA & WAL & NCA & BASEA).
    unfold FseNCount.Zlength in *.
    set (sym := ss_base (cell_nth cells u)) in *.
    zstep. uck.
    lazymatch goal with |- _ => let a := cur_mem_addr in
      pose proof (u8arr_readn usegs _ (DT + 8) _ (8 * u + 4) 4 a CEL ltac:(lia) ltac:(rewrite cellsB_length; lia) ltac:(addr_tac)) as RD end.
    rewrite (cellsB_read_base cells u ltac:(unfold FseNCount.Zlength; lia)) in RD. fold sym in RD.
    zstep.
    assert (SYR : 0 <= sym <= maxSV) by (destruct GU; lia).
    assert (MSV52 : maxSV <= 52) by (destruct k; cbn [kind_max] in *; lia).
    rewrite (zx32w_small sym) by lia.
    zstep. replace (sym ≪ 1) with (2 * sym) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
    zstep. uck. zstep.
    lazymatch goal with |- _ => let a := cur_mem_addr in
      pose proof (u16_znth usegs m1 W symNext sym a (proj1 SNX) ltac:(lia) ltac:(addr_tac)) as RD2 end.
    zstep.
    set (ns := Znth sym symNext) in *.
    rewrite (zx16_u ns) by lia.
    zstep.
    assert (LBASE : Z.of_nat (length (kind_base k)) <= 53) by (destruct k; vm_compute; discriminate).
    assert (LBITS : Z.of_nat (length (kind_bits k)) <= 53) by (destruct k; vm_compute; discriminate).
    snst SNX sym (ns + 1) ((ns + 1) mod 2^16).
    zstep. uck. zstep. uck.
    (* [comment removed for export] *)
    zstep. zstep. set (sa := Z.lor ns (ns ≫ 1)). zstep. zstep. set (sb := Z.lor sa (sa ≫ 2)). zstep. zstep. set (sc := Z.lor sb (sb ≫ 4)).
    zstep. zstep. zstep.
    lazymatch goal with |- _ => let v := reg_val 20 in lazymatch v with Z_to_bv 64 ?e => change e with (smear16 ns) end end.
    rewrite (smear16_ok ns) by lia.
    set (L := Z.log2 ns) in *.
    assert (HL : 0 <= L <= 10).
    { subst L. split; [apply Z.log2_nonneg|]. assert (Z.log2 ns < 11); [|lia]. apply Z.log2_lt_pow2; [lia|]. change (2^11) with 2048. lia. }
    zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    zstep. zstep. zstep. zstep.
    lazymatch goal with |- _ => let v := reg_val 20 in lazymatch v with Z_to_bv 64 ?e =>
      replace e with L by (clear - HL; clearbody L;
        assert (C : L = 0 \/ L = 1 \/ L = 2 \/ L = 3 \/ L = 4 \/ L = 5 \/ L = 6 \/ L = 7 \/ L = 8 \/ L = 9 \/ L = 10) by lia;
        destruct C as [E|[E|[E|[E|[E|[E|[E|[E|[E|[E|E]]]]]]]]]]; rewrite E; vm_compute; reflexivity) end end.
    assert (LTL : L <= tl).
    { subst L. assert (Z.log2 ns < tl + 1); [|lia]. apply Z.log2_lt_pow2; [lia|]. rewrite Z.pow_add_r by lia. lia. }
    assert (TL9 : tl <= 9) by (destruct k; cbn [kind_maxLog] in *; lia).
    zstep.
    rewrite ?(Z.mod_small tl 18446744073709551616) by lia. rewrite (swrap32_small (tl - L)) by lia.
    zstep.
    replace (Z.land (tl - L) 255) with (tl - L) by (change 255 with (Z.ones 8); rewrite Z.land_ones by lia; symmetry; apply Z.mod_small; change (2^8) with 256; lia).
    cst CEL u 3 1%nat cellsB_store_nbBits (2^8).
    zstep. uck.
    zstep.
    rewrite (shiftl_mod32 ns (tl - L)) by lia.
    pose proof (shl_hb_range ns tl ltac:(lia) ltac:(lia) LTL) as NSB. fold L in NSB.
    rewrite (swrap32_small (ns * 2^(tl - L))) by lia.
    zstep.
    rewrite (swrap32_small (ns * 2^(tl - L) - 2^tl)) by lia.
    set (nxt := ns * 2^(tl - L) - 2^tl) in *.
    zstep.
    cst CEL u 0 2%nat cellsB_store_next (2^16).
    zstep. uck.
    zstep. replace (BITS + sym <? 1) with false by (symmetry; apply Z.ltb_ge; lia). cbn [Z.b2z].
    zstep. zstep. uck. zstep. uck.
    assert (LKB : Z.of_nat (length (kind_bits k)) = kind_max k + 1 /\ Z.of_nat (length (kind_base k)) = kind_max k + 1) by (destruct k; split; reflexivity).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => let a := cur_mem_addr in
      pose proof (u8ro_read usegs mx BITS _ sym _ a BITSB (nth_error_map_Znth (Z_to_bv 8) (kind_bits k) sym ltac:(lia)) ltac:(lia) ltac:(addr_tac)) as RD3 end.
    zstep.
    assert (FBITS : Forall (fun v => 0 <= v < 256) (kind_bits k)) by (destruct k; repeat constructor; lia).
    assert (FBASE : Forall (fun v => 0 <= v < 2147483648) (kind_base k)) by (destruct k; repeat constructor; lia).
    pose proof (Forall_Znth _ _ sym FBITS ltac:(lia)) as RBITS. pose proof (Forall_Znth _ _ sym FBASE ltac:(lia)) as RBASE. cbv beta in RBITS, RBASE.
    cbv beta. rewrite (byte_lit (Znth sym (kind_bits k))) by lia.
    zstep. replace (sym ≪ 2) with (4 * sym) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
    zstep.
    cst CEL u 2 1%nat cellsB_store_nbAdd (2^8).
    zstep. uck.
    zstep. replace (BASE + 4 * sym <? 1) with false by (symmetry; apply Z.ltb_ge; lia). cbn [Z.b2z].
    zstep. zstep. uck. zstep. uck. zstep. zstep. uck.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => let a := cur_mem_addr in
      pose proof (u32ro_read usegs mx BASE _ sym _ a BASEB (nth_error_map_Znth (Z_to_bv 64) (kind_base k) sym ltac:(lia)) ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD4 end.
    zstep.
    rewrite (sx32w_small (Znth sym (kind_base k))) by lia.
    zstep. zstep.
    cst CEL u 4 4%nat cellsB_store_base (2^32).
    zstep.
    rewrite set_cell_fields_u in CEL by (unfold FseNCount.Zlength; lia).
    assert (CE : {| ss_next := nxt mod 2 ^ 16; ss_nbAdd := Znth sym (kind_bits k) mod 2 ^ 8; ss_nbBits := (tl - L) mod 2 ^ 8;
                    ss_base := Znth sym (kind_base k) mod 2 ^ 32 |} = build_one tl (kind_base k) (kind_bits k) sym ns).
    { unfold build_one. fold L. subst nxt. change (2^8) with 256. rewrite (Z.mod_small (tl - L) 256) by lia.
      rewrite (Z.mod_small (Znth sym (kind_bits k)) 256) by lia. rewrite (Z.mod_small (Znth sym (kind_base k)) (2^32)) by lia. reflexivity. }
    rewrite CE in CEL. clear CE.
    assert (CLEN' : zlenF (set_cell u (build_one tl (kind_base k) (kind_bits k) sym ns) cells) = 2^tl)
      by (unfold FseNCount.Zlength; rewrite set_cell_length; exact CLEN).
    assert (SNLEN' : zlenF (upd_nat (Z.to_nat sym) ((ns + 1) mod 2 ^ 16) symNext) = 53)
      by (unfold FseNCount.Zlength; rewrite FseLemmas.upd_nat_length; exact SNLEN).
    eapply KONT. unfold Zupd. close_bfu.
  Qed.

  (* [comment removed for export] *)
  Lemma bf_p3_loop : forall (f : nat) m1 fast w8 w16 u cells symNext spread cellsF snF xra x7 xs1 xa0 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11,
    BFm (Z_to_bv 64 fast) (Z_to_bv 64 tl) w8 w16 cells symNext spread m1 -> 0 <= fast <= 1 ->
    0 <= u -> u + Z.of_nat (S f) = 2^tl ->
    (forall v, u <= v < 2^tl -> good norm maxSV (ss_base (cell_nth cells v))) ->
    (forall s, good norm maxSV s -> snext0 norm s <= Znth s symNext <= snext0 norm s + u) ->
    build_cells (S f) tl (kind_base k) (kind_bits k) u cells symNext = (cellsF, snF) ->
    x7 = Z_to_bv 64 (2^tl - u) -> xs1 = Z_to_bv 64 (DT + 8 + 8 * u) -> xa0 = Z_to_bv 64 (DT + 12 + 8 * u) ->
    evt usegs (POST (mkST fast tl cellsF))
      (ST3 0x171c0 m1 xra x7 xs1 xa0 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11).
  Proof.
    induction f as [|f IH]; intros until xs11; intros I HF HU HUF GOODC SNB BC -> -> ->; open_bh HY; pose proof size_rng as SZ.
    all: assert (GU := GOODC u ltac:(lia)).
    all: assert (TL9 : 5 <= tl <= 9) by (destruct k; cbn [kind_maxLog] in *; lia).
    all: assert (NSR : 1 <= Znth (ss_base (cell_nth cells u)) symNext < 2 * 2^tl)
           by (pose proof (SNB _ GU); pose proof (snext0_good norm maxSV tl TL9 NLEN NGE NSUM _ GU); lia).
    - eapply bf_p3_body with (u := u); [exact I | lia | exact GU | exact NSR |].
      intros m2 ys2 ys3 ys4 ys5 I2.
      cbn [build_cells] in BC. injection BC as <- <-.
      zstep. if_cases K; zify_cond K; [exfalso; lia|].
      eapply bf_epi; [exact I2 | exact HF].
    - eapply bf_p3_body with (u := u); [exact I | lia | exact GU | exact NSR |].
      intros m2 ys2 ys3 ys4 ys5 I2.
      set (sym := ss_base (cell_nth cells u)) in *. set (ns := Znth sym symNext) in *.
      assert (E : build_cells (S (S f)) tl (kind_base k) (kind_bits k) u cells symNext
                  = build_cells (S f) tl (kind_base k) (kind_bits k) (u + 1)
                      (set_cell u (build_one tl (kind_base k) (kind_bits k) sym ns) cells) (Zupd sym ((ns + 1) mod 2^16) symNext)) by reflexivity.
      rewrite E in BC. clear E.
      zstep. if_cases K; zify_cond K; [|exfalso; lia].
      eapply (IH m2 fast w8 w16 (u + 1)); [exact I2 | exact HF | lia | lia | | | exact BC | f_equal; lia | f_equal; lia | f_equal; lia].
      + intros v Hv. rewrite cell_nth_set_cell_other by lia. apply GOODC. lia.
      + intros s GS. destruct I as (_ & _ & _ & _ & SNLEN & _). unfold FseNCount.Zlength in SNLEN.
        assert (SYR : 0 <= sym <= 52) by (destruct GU; destruct k; cbn [kind_max] in *; lia).
        rewrite (Znth_Zupd_eq tl TL9) by (unfold FseNCount.Zlength; destruct GS; lia).
        pose proof (SNB s GS) as B. destruct (Z.eqb_spec s sym) as [->|NE].
        * fold ns in B. rewrite Z.mod_small by (change (2^16) with 65536; lia). lia.
        * lia.
  Qed.
End A.
