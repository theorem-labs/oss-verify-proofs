From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Step MState.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import FseWalkKit FseRdKit2.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Ubsan Require Import UImg RF_huf_iface RF_huf_h_iface RF_huf_bdt_model RF_huf_fdw_tk.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma x2k_skipn_nth_cons : forall {X} (l : list X) k d, (k < length l)%nat -> skipn k l = nth k l d :: skipn (S k) l.
Proof.
  intros X l. induction l as [|a l IH]; intros k d L; [cbn in L; lia|].
  destruct k as [|k]; [reflexivity|]. cbn in L |- *. apply IH. lia.
Qed.

Lemma x2k_rw_cells_nth : forall segs m A cs k d, rw_cells segs m A cs -> (k < length cs)%nat ->
  rw_cells segs m (A + Z.of_nat (cells_size (firstn k cs))) [nth k cs d].
Proof.
  intros segs m A cs k d H L.
  rewrite <- (firstn_skipn k cs) in H.
  apply (proj1 (rw_cells_app' segs m A (firstn k cs) (skipn k cs))) in H. destruct H as [_ H].
  rewrite (x2k_skipn_nth_cons cs k d L) in H.
  apply (proj1 (rw_cells_app' segs m _ [nth k cs d] (skipn (S k) cs))) in H. exact (proj1 H).
Qed.

Lemma x2k_u8sub : forall m A l k n, u8arr usegs m A l -> 0 <= k -> 0 <= n -> k + n <= zlen l ->
  u8arr usegs m (A + k) (firstn (Z.to_nat n) (skipn (Z.to_nat k) l)).
Proof.
  intros m A l k n H K N KN.
  rewrite <- (firstn_skipn (Z.to_nat k) l) in H.
  apply (proj1 (u8arr_app usegs _ _ _ _)) in H. destruct H as [_ H].
  rewrite firstn_length_le in H by lia. rewrite Z2Nat.id in H by lia.
  rewrite <- (firstn_skipn (Z.to_nat n) (skipn (Z.to_nat k) l)) in H.
  apply (proj1 (u8arr_app usegs _ _ _ _)) in H. exact (proj1 H).
Qed.

Lemma x2k_sub_len : forall (l : list byte) k n, 0 <= k -> 0 <= n -> k + n <= zlen l ->
  length (firstn (Z.to_nat n) (skipn (Z.to_nat k) l)) = Z.to_nat n.
Proof. intros l k n K N KN. rewrite length_firstn, length_skipn. lia. Qed.

Lemma x2k_mtl_byte : forall mtl, 1 <= mtl <= 12 -> Z.land (bv_unsigned (zx32 (Z_to_bv 64 (mtl * 16777217)))) 255 = mtl.
Proof.
  intros mtl H.
  assert (mtl = 1 \/ mtl = 2 \/ mtl = 3 \/ mtl = 4 \/ mtl = 5 \/ mtl = 6 \/ mtl = 7 \/ mtl = 8 \/ mtl = 9 \/ mtl = 10 \/ mtl = 11 \/ mtl = 12) as C by lia.
  repeat destruct C as [C|C]; subst; vm_compute; reflexivity.
Qed.

Lemma x2k_mtl_byte' : forall mtl, 1 <= mtl <= 12 -> Z.land (mtl * 16777217) 255 = mtl.
Proof.
  intros mtl H.
  assert (mtl = 1 \/ mtl = 2 \/ mtl = 3 \/ mtl = 4 \/ mtl = 5 \/ mtl = 6 \/ mtl = 7 \/ mtl = 8 \/ mtl = 9 \/ mtl = 10 \/ mtl = 11 \/ mtl = 12) as C by lia.
  repeat destruct C as [C|C]; subst; vm_compute; reflexivity.
Qed.

Lemma x2k_zx32 : forall x, 0 <= x < 2^32 -> zx32 (Z_to_bv 64 x) = Z_to_bv 64 x.
Proof. intros x H. unfold zx32. rewrite unsigned_lit by lia. rewrite Z.mod_small by lia. reflexivity. Qed.

Lemma x2k_not : forall a, Z_to_bv 64 (18446744073709551615 - a) = Z_to_bv 64 (- a - 1).
Proof.
  intros a. apply Z_to_bv_eqm. replace (18446744073709551615 - a) with ((- a - 1) + 1 * 2^64) by lia.
  rewrite Z.mod_add by lia. reflexivity.
Qed.

Lemma x2k_hdr : forall mtl, 1 <= mtl <= 12 -> Z.land (mtl * 16777217) 18446744073692774400 = mtl * 16777216.
Proof.
  intros mtl H.
  assert (mtl = 1 \/ mtl = 2 \/ mtl = 3 \/ mtl = 4 \/ mtl = 5 \/ mtl = 6 \/ mtl = 7 \/ mtl = 8 \/ mtl = 9 \/ mtl = 10 \/ mtl = 11 \/ mtl = 12) as C by lia.
  repeat destruct C as [C|C]; subst; vm_compute; reflexivity.
Qed.

Lemma x2k_tsel : forall mtl tl, 1 <= mtl <= 12 -> 1 <= tl <= 12 ->
  Z.land (Z.b2z (tl <? 12)) (Z.b2z ((mtl + -12) mod 18446744073709551616 <? 1)) = Z.b2z ((tl <=? 11) && (11 <? mtl)).
Proof.
  intros mtl tl HM HT.
  assert (E : (tl <? 12) = (tl <=? 11)) by (destruct (Z.ltb_spec tl 12), (Z.leb_spec tl 11); auto; lia). rewrite E.
  assert (mtl = 1 \/ mtl = 2 \/ mtl = 3 \/ mtl = 4 \/ mtl = 5 \/ mtl = 6 \/ mtl = 7 \/ mtl = 8 \/ mtl = 9 \/ mtl = 10 \/ mtl = 11 \/ mtl = 12) as C by lia.
  repeat destruct C as [C|C]; subst; destruct (tl <=? 11); vm_compute; reflexivity.
Qed.

Ltac x2bf := repeat (match goal with H : context [Z.lxor ?a ?b] |- _ =>
  lazymatch goal with _ : 0 <= Z.lxor a b |- _ => fail | _ => assert (0 <= Z.lxor a b) by (apply Z.lxor_nonneg; lia) end end).

Ltac x2norm := repeat (first [ rewrite x2k_zx32 by lia | rewrite sx32_small by lia | rewrite unsigned_lit by lia
                             | rewrite swrap32_small by lia | rewrite zb_lxor_ones by lia | rewrite Z.add_0_r ]).

Ltac x2dec := lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
  tryif (match c with context [?v] => is_var v end) then fail else
  let b := eval vm_compute in c in change c with b; cbv iota end.

Ltac x2ref U := x2bf; rewrite ?Z.shiftl_mul_pow2 in U by lia; rewrite ?Z.shiftr_div_pow2 in U by lia;
  first [ lia | (Z.div_mod_to_equations; lia) ].

Ltac x2ck := lazymatch goal with |- evt _ _ (MS _ _ (if ?c then Z_to_bv 64 ?a else Z_to_bv 64 ?b) _ _ _ _) =>
  first [ let d := eval vm_compute in (a =? PHUF_RDT_X2 + 388) in lazymatch d with true =>
            let U := fresh "U" in if_cases U; zify_cond U; [ exfalso; x2ref U | ] end
        | let d := eval vm_compute in (b =? PHUF_RDT_X2 + 388) in lazymatch d with true =>
            let U := fresh "U" in if_cases U; zify_cond U; [ | exfalso; x2ref U ] end ] end.

Ltac x2at o := lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 ?z) _ _ _ _) =>
  let d := eval vm_compute in (z =? PHUF_RDT_X2 + o) in lazymatch d with true => idtac end end.

Ltac x2in := lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 ?z) _ _ _ _) =>
  let d := eval vm_compute in ((PHUF_RDT_X2 <=? z) && (z <? PHUF_RDT_X2 + 2096))%bool in
  lazymatch d with true => idtac end end.

Ltac x2lia := first [ let U := fresh "U" in if_cases U; zify_cond U; [ exfalso; lia | ]
                    | let U := fresh "U" in if_cases U; zify_cond U; [ | exfalso; lia ] ].

Ltac x2upto o := repeat (tryif x2at o then fail else first [ x2in; zstep | x2norm; first [ x2dec | x2ck | x2lia ] ]).
Ltac x2br := repeat (first [ x2in; zstep | x2norm; first [ x2dec | x2ck | x2lia ] ]).

Ltac x2eqz := first [ reflexivity | (f_equal; lia) | (apply Z_to_bv_eqm; Z.div_mod_to_equations; lia) ].
Ltac x2st := lazymatch goal with |- MS _ _ _ _ _ _ _ = MS _ _ _ _ _ _ _ =>
  f_equal; try (lazymatch goal with |- mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ = _ => f_equal end);
  x2eqz end.
Ltac x2pc o := lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 ?z) _ _ _ _) =>
  change (Z_to_bv 64 z) with (Z_to_bv 64 (PHUF_RDT_X2 + o)) end.
Ltac x2mk := lazymatch goal with |- evt _ _ (MS ?R _ _ _ _ _ _) =>
  lazymatch R with (TNode (TNode (TNode (TNode (TNode (TNode TEmpty (Some ?r31) TEmpty) (Some ?r15) TEmpty) (Some ?r7) (TNode TEmpty (Some ?r23) TEmpty)) (Some ?r3) (TNode (TNode TEmpty (Some ?r19) TEmpty) (Some ?r11) (TNode TEmpty (Some ?r27) TEmpty))) (Some ?r1) (TNode (TNode (TNode TEmpty (Some ?r17) TEmpty) (Some ?r9) (TNode TEmpty (Some ?r25) TEmpty)) (Some ?r5) (TNode (TNode TEmpty (Some ?r21) TEmpty) (Some ?r13) (TNode TEmpty (Some ?r29) TEmpty)))) None (TNode (TNode (TNode (TNode TEmpty (Some ?r16) TEmpty) (Some ?r8) (TNode TEmpty (Some ?r24) TEmpty)) (Some ?r4) (TNode (TNode TEmpty (Some ?r20) TEmpty) (Some ?r12) (TNode TEmpty (Some ?r28) TEmpty))) (Some ?r2) (TNode (TNode (TNode TEmpty (Some ?r18) TEmpty) (Some ?r10) (TNode TEmpty (Some ?r26) TEmpty)) (Some ?r6) (TNode (TNode TEmpty (Some ?r22) TEmpty) (Some ?r14) (TNode TEmpty (Some ?r30) TEmpty))))) => change R with (mkR r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 r28 r29 r30 r31) end end.

Ltac x2w32 RA A i v :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ (wa ?E) _) _) => replace E with (A + 4 * i) by lia
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ (Z_to_bv 64 ?E) _) _) => replace E with (A + 4 * i) by lia
  end;
  let RA2 := fresh "RA" in
  pose proof (u32arr_write usegs _ A _ i v RA ltac:(rewrite ?length_map; simpl_arr_sizes; lia)) as RA2;
  clear RA; store_done; rename RA2 into RA.

Ltac x2s32 RA A i v :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?M _) =>
    let SK := fresh "SOK" in
    pose proof (u32arr_store_ok usegs M A _ i (wa (A + 4 * i)) RA ltac:(rewrite ?length_map; simpl_arr_sizes; lia) eq_refl) as SK;
    zstep; x2w32 RA A i v; try clear SK end.
