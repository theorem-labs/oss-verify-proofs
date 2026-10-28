(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount FseLemmas HufPure_FseDecomp HufPure_FseDecompRT.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import FseWalkKit FseWalkMem FseRdKit HufWalkKit STRW_tac.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Ubsan Require Import UImg RF_huf_tbl_iface RF_huf_tbl_kit RF_huf_fdw_kit.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition hsep (P : Prop) : Prop := P.
Ltac djs := first [ lia | match goal with H : hsep (_ \/ _) |- _ =>
  let H' := fresh in pose proof H as H'; unfold hsep in H'; destruct H'; lia end ].
Ltac slia_sep := first [ exact I | djs | split; [djs|exact I] ].

Definition STOPS : list Z := [0x1fdd0; 0x1fe08; 0x1fe1c; 0x1feac; 0x1ffa0; 0x20030; 0x20450; 0x207b8;
                              0x207dc; 0x207ec; 0x20808; 0x20d28].
Ltac in_stops p := let b := eval vm_compute in (existsb (Z.eqb p) STOPS) in lazymatch b with true => idtac end.
Ltac dead := fail.
Ltac wk1 := lazymatch goal with
  | |- evt _ _ (MS _ _ (Z_to_bv 64 0x20828) _ _ _ _) => fail
  | |- evt _ _ (MS _ _ (Z_to_bv 64 ?p) _ _ _ _) => tryif in_stops p then fail else zstep
  | |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) => let K := fresh "K" in if_cases K; zify_cond K; try dead
  end.
Ltac kn := repeat match goal with
  | H : context [Z.shiftl ?a ?n] |- _ => rewrite (Z.shiftl_mul_pow2 a n) in H by lia
  | H : context [Z.shiftr ?a ?n] |- _ => rewrite (Z.shiftr_div_pow2 a n) in H by lia
  | |- context [Z.shiftl ?a ?n] => rewrite (Z.shiftl_mul_pow2 a n) by lia
  | |- context [Z.shiftr ?a ?n] => rewrite (Z.shiftr_div_pow2 a n) by lia
  end.
Ltac kb := repeat match goal with
  | H : context [Z.b2z (?a <? ?b)] |- _ => destruct (Z.ltb_spec a b); cbn [Z.b2z] in H
  | H : context [Z.b2z (?a =? ?b)] |- _ => destruct (Z.eqb_spec a b); cbn [Z.b2z] in H
  end.
Lemma zx16_lit : forall v, 0 <= v < 2^16 -> bv_unsigned (zx16 (Z_to_bv 64 v)) = v.
Proof. intros v H. unfold zx16. rewrite (unsigned_lit v) by lia. rewrite Z.mod_small by lia. apply unsigned_lit; lia. Qed.
Ltac kz := repeat match goal with
  | H : context [bv_unsigned (zx16 (Z_to_bv 64 ?v))] |- _ => rewrite (zx16_lit v) in H by lia
  | |- context [bv_unsigned (zx16 (Z_to_bv 64 ?v))] => rewrite (zx16_lit v) by lia
  end.
Ltac kw := repeat match goal with
  | H : context [bv_wrap 32 ?x] |- _ => rewrite (wrap32_small x) in H by (kn; lia)
  | H : context [bv_swrap 32 ?x] |- _ => rewrite (swrap32_small x) in H by (kn; lia)
  | |- context [bv_wrap 32 ?x] => rewrite (wrap32_small x) by (kn; lia)
  | |- context [bv_swrap 32 ?x] => rewrite (swrap32_small x) by (kn; lia)
  end.
Lemma lxor_lt1 : forall a b, 0 <= a -> 0 <= b -> (Z.lxor a b <? 1) = (a =? b).
Proof.
  intros a b Ha Hb. destruct (Z.eqb_spec a b) as [->|NE].
  - rewrite Z.lxor_nilpotent. reflexivity.
  - apply Z.ltb_ge. assert (0 <= Z.lxor a b) by (apply Z.lxor_nonneg; split; lia).
    destruct (Z.eq_dec (Z.lxor a b) 0) as [E|E]; [apply Z.lxor_eq in E; contradiction | lia].
Qed.
Ltac kl := repeat match goal with
  | H : context [Z.lxor ?a ?b <? 1] |- _ => rewrite (lxor_lt1 a b) in H by (kn; lia)
  end.
Ltac kx := repeat match goal with
  | H : context [Z.lxor ?a ?b] |- _ => is_Zlit a; is_Zlit b;
      let v := eval vm_compute in (Z.lxor a b) in change (Z.lxor a b) with v in H
  end.
Ltac dead ::= exfalso; solve [lia | kn; kb; lia | kz; kw; kn; kl; kb; kx; unfold BIT_MASK_TAB in *; lia].
(* [comment removed for export] *)
Ltac lds := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
  let a := cur_mem_addr in
  lazymatch a with Z_to_bv 64 ?E =>
  lazymatch goal with B : bytes_at usegs mm ?S0 (map (Z_to_bv 8) ?bs0) |- _ =>
    let RD := fresh "RDs" in
    pose proof (src_rd usegs mm S0 bs0 (E - S0) B ltac:(kw; kn; lia)) as RD;
    replace (S0 + (E - S0)) with E in RD by lia; zstep; clear RD
  end end end.
(* [comment removed for export] *)
Ltac ldm := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
  let a := cur_mem_addr in
  lazymatch goal with MI : mem_inv usegs mm |- _ =>
  match goal with N : nth_error _ _ = Some ?c |- _ =>
    let RD := fresh "RDm" in
    let E := fresh "E" in
    assert (E : a = Z_to_bv 64 (BIT_MASK_TAB + 4 * dc_nbBits c)) by (f_equal; kz; kn; lia);
    pose proof (mask_rd mm (dc_nbBits c) MI ltac:(lia)) as RD; rewrite <- E in RD; zstep; clear RD E
  end end end.
Lemma byte8_eq : forall a b, a mod 256 = b mod 256 -> Z_to_bv 8 a = Z_to_bv 8 b.
Proof. intros a b H. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. exact H. Qed.
Lemma le2_pair : forall s n, 0 <= s < 256 -> 0 <= n < 256 -> le2 (Z_to_bv 64 (s + 256 * n)) = [Z_to_bv 8 s; Z_to_bv 8 n].
Proof.
  intros s n Hs Hn. unfold le2. rewrite unsigned_lit by lia. cbn [Z_to_le_bytes]. f_equal; [|f_equal].
  - apply byte8_eq. rewrite (Z.mod_small s) by lia. symmetry. apply Z.mod_unique with n; lia.
  - f_equal. rewrite Z.shiftr_div_pow2 by lia. change (2^8) with 256. symmetry. apply Z.div_unique with s; lia.
Qed.
Lemma cell_rd_hi : forall m TB cells i c a, bytes_at usegs m TB (concat (map fse_cell_bytes cells)) ->
  nth_error cells (Z.to_nat i) = Some c -> 0 <= i -> 0 <= dc_symbol c < 256 -> 0 <= dc_nbBits c < 256 ->
  a = wa (TB + (4 * i + 2)) ->
  ov_read_bytes usegs m a 2 = Some (le2 (Z_to_bv 64 (dc_symbol c + 256 * dc_nbBits c))).
Proof.
  intros m TB cells i c a B N I S1 N1 ->. rewrite (cell_rd_off usegs m TB cells i c 2 2 B N I) by lia.
  rewrite le2_pair by lia. reflexivity.
Qed.
(* [comment removed for export] *)
Ltac ldc := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
  let a := cur_mem_addr in
  let RD := fresh "RDc" in
  lazymatch a with
  | Z_to_bv 64 (?T + Z.shiftl ?s 2 + 2) =>
      lazymatch goal with
      | N : nth_error _ (Z.to_nat s) = Some ?c, B : bytes_at usegs mm T _ |- _ =>
          first [ pose proof (cell_rd_hi mm T _ s c a B N ltac:(lia) ltac:(lia) ltac:(lia)
                                ltac:(unfold wa; f_equal; kn; lia)) as RD; zstep
                | pose proof (cell_rd_sym usegs mm T _ s c a B N ltac:(lia) ltac:(unfold wa; f_equal; kn; lia)) as RD; zstep ]
      end
  | Z_to_bv 64 (?T + Z.shiftl ?s 2 + 3) =>
      lazymatch goal with
      | N : nth_error _ (Z.to_nat s) = Some ?c, B : bytes_at usegs mm T _ |- _ =>
          pose proof (cell_rd_nb usegs mm T _ s c a B N ltac:(lia) ltac:(unfold wa; f_equal; kn; lia)) as RD; zstep
      end
  | Z_to_bv 64 (?T + Z.shiftl ?s 2) =>
      lazymatch goal with
      | N : nth_error _ (Z.to_nat s) = Some ?c, B : bytes_at usegs mm T _ |- _ =>
          pose proof (cell_rd_ns usegs mm T _ s c a B N ltac:(lia) ltac:(unfold wa; f_equal; kn; lia)) as RD; zstep
      end
  end; clear RD end.
Lemma zlen_tl1 : forall {A} (l : list A), (1 <= length l)%nat -> zlen (tl l) = zlen l - 1.
Proof. intros A l H. destruct l as [|x l]; cbn [length tl] in *; lia. Qed.
Lemma cw_lor : forall s n w M, M = 2^64 -> 0 <= s < 256 -> 0 <= n < 256 -> 0 <= w < 2^16 ->
  Z.lor (Z.shiftl (s + 256 * n) 16 mod M) w = w + 65536 * s + 16777216 * n.
Proof.
  intros s n w M -> Hs Hn Hw. rewrite Z.shiftl_mul_pow2 by lia. rewrite Z.mod_small by lia.
  rewrite lor_shift_add by lia. lia.
Qed.
Lemma sx32_lit2 : forall z, 0 <= z < 2^31 -> bv_unsigned (sx32 (Z_to_bv 64 z)) = z.
Proof. intros z H. unfold sx32. rewrite (unsigned_lit z) by lia. rewrite swrap32_small by lia. apply unsigned_lit; lia. Qed.
Lemma zx32_lit2 : forall z, 0 <= z < 2^32 -> bv_unsigned (zx32 (Z_to_bv 64 z)) = z.
Proof. intros z H. unfold zx32. rewrite (unsigned_lit z) by lia. rewrite Z.mod_small by lia. apply unsigned_lit; lia. Qed.
Lemma hi_nb : forall s n M, M = 2^64 -> 0 <= s < 256 -> 0 <= n < 256 -> Z.shiftr (Z.shiftl (s + 256 * n) 16 mod M) 24 = n.
Proof.
  intros s n M -> Hs Hn. rewrite Z.shiftl_mul_pow2 by lia. change (2^16) with 65536. rewrite Z.mod_small by lia.
  rewrite Z.shiftr_div_pow2 by lia. change (2^24) with 16777216. symmetry. apply Z.div_unique with (s * 65536); lia.
Qed.
Lemma w_lo : forall w s n, 0 <= w < 65536 -> 0 <= s < 256 -> 0 <= n < 256 -> Z.land (w + 65536 * s + 16777216 * n) 65535 = w.
Proof.
  intros w s n Hw Hs Hn. change 65535 with (Z.ones 16). rewrite Z.land_ones by lia. change (2^16) with 65536.
  symmetry. apply Z.mod_unique with (s + 256 * n); lia.
Qed.
Lemma w_hi : forall w s n, 0 <= w < 65536 -> 0 <= s < 256 -> 0 <= n < 256 -> Z.shiftr (w + 65536 * s + 16777216 * n) 16 = s + 256 * n.
Proof.
  intros w s n Hw Hs Hn. rewrite Z.shiftr_div_pow2 by lia. change (2^16) with 65536.
  symmetry. apply Z.div_unique with w; lia.
Qed.
Ltac znorm := repeat match goal with
  | |- context [bv_unsigned (zx16 (Z_to_bv 64 ?v))] => rewrite (zx16_lit v) by lia
  | |- context [Z.lor (Z.shiftl (?s + 256 * ?n) 16 mod ?M) ?w] => rewrite (cw_lor s n w M) by (reflexivity || lia)
  | |- context [Z.shiftr (Z.shiftl (?s + 256 * ?n) 16 mod ?M) 24] => rewrite (hi_nb s n M) by (reflexivity || lia)
  | |- context [Z.land (?w + 65536 * ?s + 16777216 * ?n) 65535] => rewrite (w_lo w s n) by lia
  | |- context [Z.shiftr (?w + 65536 * ?s + 16777216 * ?n) 16] => rewrite (w_hi w s n) by lia
  | |- context [bv_unsigned (sx32 (Z_to_bv 64 ?z))] => rewrite (sx32_lit2 z) by lia
  | |- context [bv_unsigned (zx32 (Z_to_bv 64 ?z))] => rewrite (zx32_lit2 z) by lia
  | |- context [bv_wrap 32 ?x] => rewrite (wrap32_small x) by (kn; lia)
  | |- context [bv_swrap 32 ?x] => rewrite (swrap32_small x) by (kn; lia)
  end.
Ltac zmods := repeat match goal with |- context [?x mod ?M] => rewrite (Z.mod_small x M) by lia end.
Ltac zeq := first [ reflexivity | f_equal; znorm; zmods; lia ].
(* [comment removed for export] *)
Ltac osh := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
  let a := cur_mem_addr in
  lazymatch goal with OUTA : u8arr usegs mm ?D (map (Z_to_bv 8) ?o ++ ?j), LJ : zlen ?j = ?dc - zlen ?o |- _ =>
    let SOK := fresh "SOK" in
    pose proof (u8arr_store_ok usegs mm D _ (zlen o) a OUTA
                  ltac:(rewrite length_app, length_map; lia) ltac:(unfold wa; f_equal; kn; lia)) as SOK;
    zstep;
    lazymatch goal with
    | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ (Z_to_bv 64 ?E) _) _) => replace E with (D + zlen o) by (kn; lia)
    | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ (wa ?E) _) _) => replace E with (D + zlen o) by (kn; lia)
    end;
    rewrite le1_lit;
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ [Z_to_bv 8 ?v]) _) =>
      try (match goal with N : nth_error _ _ = Some ?c |- _ =>
        replace (Z_to_bv 8 v) with (Z_to_bv 8 (dc_symbol c)) by (apply byte8_eq; kn; lia)
      end);
      let OUT2 := fresh "OUTA" in
      let LJ2 := fresh "LJ" in
      let LO2 := fresh "LO" in
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ [Z_to_bv 8 ?v2]) _) =>
        pose proof (out_sb usegs mm D o j v2 OUTA ltac:(lia)) as OUT2;
        assert (LO2 : zlen (o ++ [v2]) = zlen o + 1) by (rewrite length_app; cbn [length]; lia);
        assert (LJ2 : zlen (List.tl j) = dc - zlen (o ++ [v2])) by (rewrite zlen_tl1 by lia; lia)
      end;
      clear OUTA LJ; store_done; rename OUT2 into OUTA; rename LJ2 into LJ
    end
  end end.
Ltac wk := zstep; znorm; repeat (first [wk1; znorm | ldc; znorm | ldm; znorm | osh; znorm | lds; znorm]).
