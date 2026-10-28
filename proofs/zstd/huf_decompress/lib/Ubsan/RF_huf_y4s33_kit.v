From Stdlib Require Import ZArith NArith List Lia Bool Znumtheory.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount FseLemmas HufPure_FseDecomp HufPure_HufBits HufPure_HufX1 HufPure_HufX2.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk RunConst Image.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import STRW_tac FseWalkKit FseWalkMem FseRdKit FseRdKit2 HufWalkKit HufWalkKit2 HufWalkKit3.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Ubsan Require Import UImg RunDraw RF_huf_iface RF_huf_h_iface RF_huf_dec_iface RF_huf_x4s
  RF_huf_y4s_iface RF_huf_y4_kit_reload RF_huf_y4s31_kit.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".

Notation fmem := (word -> option byte).

Notation S3_ENTRY := 0x1c8d8 (only parsing).
Notation S3_L5H := 0x1c91c (only parsing).
Notation S3_L5C := 0x1ca0c (only parsing).
Notation S3_L5R := 0x1ca10 (only parsing).
Notation S3_L5J := 0x1ca18 (only parsing).
Notation S3_D5 := 0x1ca24 (only parsing).
Notation S3_L5X := 0x1cc08 (only parsing).
Notation S3_ELSE := 0x1cc24 (only parsing).
Notation S3_ELC := 0x1cffc (only parsing).
Notation S3_L4P := 0x1cd28 (only parsing).
Notation S3_L4H := 0x1cd50 (only parsing).
Notation S3_L4C := 0x1ce40 (only parsing).
Notation S3_L4J := 0x1ce48 (only parsing).
Notation S3_D4 := 0x1ce58 (only parsing).
Notation S3_L4X := 0x1cfdc (only parsing).
Notation S3_CL1 := 0x1d000 (only parsing).
Notation S3_CL2 := 0x1d018 (only parsing).
Notation S3_CL3 := 0x1d030 (only parsing).
Notation S3_CL4 := 0x1d034 (only parsing).
Notation S3_L2RP := 0x1d040 (only parsing).
Notation S3_L2RH := 0x1d064 (only parsing).
Notation S3_L2RC := 0x1d154 (only parsing).
Notation S3_L2RJ := 0x1d164 (only parsing).
Notation S3_L2RD := 0x1d16c (only parsing).
Notation S3_L2RX := 0x1d1c8 (only parsing).
Notation S3_L2T := 0x1d1d4 (only parsing).
Notation S3_L2H := 0x1d1dc (only parsing).
Notation S3_LAST := 0x1d234 (only parsing).
Notation S3_COLD := 0x1dcd8 (only parsing).
Notation S4_ENTRY := 0x1d2c0 (only parsing).
Notation S4_L5H := 0x1d2fc (only parsing).
Notation S4_L5C := 0x1d3d8 (only parsing).
Notation S4_L5J := 0x1d3e4 (only parsing).
Notation S4_D5 := 0x1d3f0 (only parsing).
Notation S4_L5X := 0x1d598 (only parsing).
Notation S4_ELSE := 0x1d5b4 (only parsing).
Notation S4_ELC := 0x1d924 (only parsing).
Notation S4_L4P := 0x1d6a0 (only parsing).
Notation S4_L4H := 0x1d6bc (only parsing).
Notation S4_L4C := 0x1d798 (only parsing).
Notation S4_L4J := 0x1d7a4 (only parsing).
Notation S4_D4 := 0x1d7b0 (only parsing).
Notation S4_L4X := 0x1d904 (only parsing).
Notation S4_CL1 := 0x1d928 (only parsing).
Notation S4_CL2 := 0x1d940 (only parsing).
Notation S4_CL3 := 0x1d954 (only parsing).
Notation S4_L2RP := 0x1d964 (only parsing).
Notation S4_L2RH := 0x1d988 (only parsing).
Notation S4_L2RC := 0x1da64 (only parsing).
Notation S4_L2RJ := 0x1da70 (only parsing).
Notation S4_L2RD := 0x1da7c (only parsing).
Notation S4_L2RX := 0x1dad8 (only parsing).
Notation S4_L2T := 0x1dae8 (only parsing).
Notation S4_L2H := 0x1daf0 (only parsing).
Notation S4_LAST := 0x1db4c (only parsing).
Notation S4_COLD := 0x1dcf4 (only parsing).
Notation YEND := 0x1dbe0 (only parsing).

Lemma k3_idx_bnd : forall tl x sh, 1 <= tl <= 12 -> sh = 64 - tl ->
  0 <= (x mod 2^64) ≫ sh < 2^tl.
Proof.
  intros tl x sh TL ->. rewrite Z.shiftr_div_pow2 by lia.
  assert (M : 0 <= x mod 2^64 < 2^64) by (apply Z.mod_pos_bound; lia).
  split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|].
  replace (2^(64 - tl) * 2^tl) with (2^64) by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
  lia.
Qed.

Lemma k3_nb_val : forall bc, 0 <= bc <= 64 -> bv_swrap 32 (bv_wrap 32 bc ≫ 3) = bc / 8.
Proof.
  intros bc B. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  replace (2 ^ Z.of_N 32) with 4294967296 by reflexivity.
  replace (4294967296 `div` 2) with 2147483648 by reflexivity.
  rewrite (Z.mod_small bc 4294967296) by lia. rewrite Z.shiftr_div_pow2 by lia.
  change (2 ^ 3) with 8.
  assert (0 <= bc / 8 <= 8) by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia).
  rewrite Z.mod_small by lia. lia.
Qed.

Lemma k3_lxor_lt1 : forall x y, 0 <= x -> 0 <= y -> (Z.lxor x y <? 1) = (x =? y).
Proof.
  intros x y X Y. destruct (Z.eqb_spec x y) as [->|NE].
  - rewrite Z.lxor_nilpotent. reflexivity.
  - apply Z.ltb_ge. assert (Z.lxor x y <> 0) by (intro H'; apply NE; apply Z.lxor_eq; exact H').
    assert (0 <= Z.lxor x y) by (apply Z.lxor_nonneg; tauto). lia.
Qed.

Lemma k3_swrap32_small : forall x, -2147483648 <= x < 2147483648 -> bv_swrap 32 x = x.
Proof.
  intros x B. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  replace (2 ^ Z.of_N 32) with 4294967296 by reflexivity.
  replace (4294967296 `div` 2) with 2147483648 by reflexivity.
  rewrite Z.mod_small by lia. lia.
Qed.

Lemma k3_zx32_lit : forall x, 0 <= x < 2^32 -> zx32 (Z_to_bv 64 x) = Z_to_bv 64 x.
Proof. intros x B. unfold zx32. rewrite unsigned_lit by lia. rewrite Z.mod_small by lia. reflexivity. Qed.

Lemma k3_shr32_mul : forall x, (x * 4294967296) ≫ 32 = x.
Proof. intros x. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 32) with 4294967296. apply Z.div_mul. lia. Qed.

Lemma k3_bytes_at_sub : forall segs m A l k len, bytes_at segs m A (map (Z_to_bv 8) l) -> 0 <= k -> 0 <= len -> k + len <= zlen l ->
  bytes_at segs m (A + k) (map (Z_to_bv 8) (firstn (Z.to_nat len) (skipn (Z.to_nat k) l))).
Proof.
  intros segs m A l k len H K0 L0 KL.
  rewrite <- (firstn_skipn (Z.to_nat k) l) in H. rewrite map_app in H.
  apply bytes_at_app in H. destruct H as [_ H]. rewrite length_map, length_firstn in H.
  replace (Z.of_nat (Init.Nat.min (Z.to_nat k) (length l))) with k in H by lia.
  rewrite <- (firstn_skipn (Z.to_nat len) (skipn (Z.to_nat k) l)) in H. rewrite map_app in H.
  apply bytes_at_app in H. tauto.
Qed.

Lemma k3_negdesc : forall tl mtl, 1 <= tl <= 12 -> 0 <= mtl <= 255 ->
  ((0 - (tl + 256 * mtl)) mod 18446744073709551616) mod 64 = 64 - tl.
Proof.
  intros tl mtl T M.
  rewrite <- (Znumtheory.Zmod_div_mod 64 18446744073709551616 (0 - (tl + 256 * mtl))) by (try lia; exists 288230376151711744; reflexivity).
  symmetry. apply Z.mod_unique with (q := -1 - 4 * mtl); lia.
Qed.

Lemma k3_negdesc_land : forall tl mtl, 1 <= tl <= 12 -> 0 <= mtl <= 255 ->
  Z.land ((0 - (tl + 256 * mtl)) mod 18446744073709551616) 63 = 64 - tl.
Proof.
  intros tl mtl T M. change 63 with (Z.ones 6). rewrite Z.land_ones by lia. change (2 ^ 6) with 64.
  apply k3_negdesc; lia.
Qed.

Lemma k3_swrap_range : forall x, -2^31 <= bv_swrap 32 x < 2^31.
Proof.
  intros x. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  replace (2 ^ Z.of_N 32) with 4294967296 by reflexivity.
  replace (4294967296 `div` 2) with 2147483648 by reflexivity.
  pose proof (Z.mod_pos_bound (x + 2147483648) 4294967296 ltac:(lia)). lia.
Qed.

Lemma k3_swrap_wrap : forall x, -2^31 <= x < 2^31 -> bv_swrap 32 (bv_wrap 32 x) = x.
Proof.
  intros x B. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  replace (2 ^ Z.of_N 32) with 4294967296 by reflexivity.
  replace (4294967296 `div` 2) with 2147483648 by reflexivity.
  rewrite Zplus_mod_idemp_l. rewrite Z.mod_small by lia. lia.
Qed.

(* [comment removed for export] *)
Ltac k3_ck U := exfalso; rewrite ?zb_lxor_ones in U by lia; rewrite ?byte_lit in U by lia;
  rewrite ?Z.shiftl_mul_pow2, ?Z.shiftr_div_pow2 in U by lia;
  rewrite ?Z.mod_small in U by lia; try (rewrite Z.div_small in U by lia); lia.

Ltac k3_cknull U := exfalso; rewrite ?k3_lxor_lt1 in U by lia;
  repeat match type of U with
  | context [?a =? ?b] => rewrite (proj2 (Z.eqb_neq a b)) in U by lia
  | context [?a <? ?b] => first [rewrite (proj2 (Z.ltb_lt a b)) in U by lia | rewrite (proj2 (Z.ltb_ge a b)) in U by lia]
  end; cbn in U; first [discriminate U | lia | apply U; reflexivity].

Ltac k3_st8 ARR i :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 ?w)) _) =>
    lazymatch w with
    | Z_to_bv 64 _ => idtac
    | _ => rewrite <- (Z_to_bv_lit_self w)
    end end;
  u8_store_same ARR i.

Ltac k3_gbuf DST dcap :=
  lazymatch goal with ARRx : u8arr usegs ?m DST (map (Z_to_bv 8) ?b) |- _ =>
    let b2 := fresh "buf" in let LB2 := fresh "LB" in let LB3 := fresh "LBm" in
    assert (LB2 : Z.of_nat (length b) = dcap) by (rewrite ?Zupd_length; lia);
    assert (LB3 : Z.of_nat (length (map (Z_to_bv 8) b)) = dcap) by (rewrite length_map; exact LB2);
    generalize dependent b; intros b2 ARRx LB2 LB3 end.

Ltac k3_x2facts DT cells cbs tl ECB :=
  repeat match goal with
  | ECx : ?cc = nth (Z.to_nat ?v) cells x2_default, SQx : 0 <= x2_seq ?cc < _,
    CEx : bytes_at usegs ?m (DT + 4) cbs |- _ =>
      lazymatch goal with
      | _ : ov_read_bytes usegs m (Z_to_bv 64 (DT + 4 + 4 * v)) 2 = Some _ |- _ => fail
      | _ => destruct (x2_cell_rd usegs m (DT + 4) cells (Z.to_nat (4 * 2^tl)) v cc ltac:(rewrite <- ECB; exact CEx)
                ltac:(lia) ltac:(lia) ltac:(lia) ECx SQx) as (? & ? & ? & ?)
      end
  end.

Ltac k3_newidx tl cells :=
  lazymatch goal with |- context [Z_to_bv 64 ((?x mod ?M) ≫ ?sh)] =>
    let v := fresh "v" in let EV := fresh "EV" in let VR := fresh "VR" in
    remember ((x mod M) ≫ sh) as v eqn:EV;
    assert (VR : 0 <= v < 2^tl) by (subst v; apply k3_idx_bnd; [lia| rewrite ?Z.mod_small by lia; reflexivity]);
    clear EV;
    let cc := fresh "cc" in let EC := fresh "EC" in
    remember (nth (Z.to_nat v) cells x2_default) as cc eqn:EC;
    let SQ := fresh "SQ" in let NB := fresh "NB" in let LN := fresh "LN" in
    lazymatch goal with TCKx : forall i, 0 <= i < 2^tl -> _ |- _ => destruct (TCKx v VR) as (SQ & NB & LN) end;
    rewrite <- EC in SQ, NB, LN
  end.

Ltac k3_outst DST dcap DT cells cbs tl ECB :=
  lazymatch goal with ARRx : u8arr usegs ?m DST (map (Z_to_bv 8) ?b) |- _ =>
    let a := cur_mem_addr in
    let E := lazymatch a with Z_to_bv 64 ?E => E end in
    u8_sok ARRx (E - DST); zstep; k3_st8 ARRx (E - DST); k3_gbuf DST dcap; k3_x2facts DT cells cbs tl ECB
  end.

Ltac k3_srcrd SS src :=
  lazymatch goal with SRCx : bytes_at usegs ?m SS (map (Z_to_bv 8) src) |- _ =>
    let a := cur_mem_addr in
    let E := lazymatch a with Z_to_bv 64 ?E => E end in
    pose proof (src_rd usegs m SS src (E - SS) SRCx ltac:(lia)) as ?
  end.

Ltac k3_norm DT cells cbs tl ECB :=
  repeat (rewrite k3_negdesc_land by lia); repeat (rewrite k3_negdesc by lia);
  repeat (rewrite k3_swrap_wrap by lia);
  try k3_newidx tl cells; rewrite ?Z.shiftl_mul_pow2 by lia; rewrite ?byte_lit by lia;
  repeat (rewrite k3_zx32_lit by lia); repeat (rewrite sx32_small by lia);
  repeat (rewrite k3_nb_val by lia); rewrite ?k3_shr32_mul;
  repeat (lazymatch goal with |- context [bv_swrap 32 ?x] => rewrite (k3_swrap32_small x) by lia end);
  repeat (lazymatch goal with |- context [?x mod 4294967296] => rewrite (Z.mod_small x 4294967296) by lia end);
  try k3_x2facts DT cells cbs tl ECB.

(* [comment removed for export] *)
Ltac k3_step DST dcap SS src DT cells cbs tl ECB :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) =>
      let U := fresh "U" in if_cases U; zify_cond U; try (k3_ck U); try (k3_cknull U)
  | |- evt ?segs _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) =>
      let fw := eval vm_compute in (fetch_word segs (Z_to_bv 64 pc)) in
      lazymatch fw with Some ?w =>
      let d := eval vm_compute in (decode_any w) in
      lazymatch d with
      | Some (Store _ ?rs _ _, _) =>
          let rz := eval vm_compute in (bv_unsigned rs) in
          lazymatch rz with 2%Z => zstep | _ => k3_outst DST dcap DT cells cbs tl ECB end
      | Some (Load _ _ _ _ _, _) => first [zstep | k3_srcrd SS src; zstep]
      | _ => lazymatch w with
             | 3221229683%bv => fail
             | _ => zstep
             end
      end end
  end;
  k3_norm DT cells cbs tl ECB.

(* [comment removed for export] *)
Ltac k3_at L :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) =>
      let b := eval vm_compute in (existsb (Z.eqb pc) L) in
      lazymatch b with true => idtac | false => fail end
  end.

Ltac k3_nrm :=
  rewrite ?Z.shiftl_mul_pow2 in * by lia;
  repeat (rewrite u_lxor_m1 by lia);
  repeat match goal with
  | |- context [?x mod ?M] => rewrite (Z.mod_small x M) by lia
  | H : context [?x mod ?M] |- _ => rewrite (Z.mod_small x M) in H by lia
  | |- context [bv_swrap 32 ?x] => rewrite (k3_swrap32_small x) by lia
  | H : context [bv_swrap 32 ?x] |- _ => rewrite (k3_swrap32_small x) in H by lia
  end.

Ltac k3_pg := lazymatch goal with
  | |- evt _ _ (MS ?R _ ?pc _ _ ?m _) => idtac "PRB pc" pc; idtac "PRB R" R
  | |- ?G => idtac "PRB goal" G
  end.
