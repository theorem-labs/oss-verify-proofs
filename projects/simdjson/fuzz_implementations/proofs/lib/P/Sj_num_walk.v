(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac Arr Bytes StoreFast.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Sj Require Import SjNumber.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.P Require Import Rnd Sj_num_kit.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Lemma bytes_read8_at : forall segs (m : mem) A bs k a,
  bytes_at segs m A bs -> (0 <= k)%Z -> (k + 8 <= Z.of_nat (length bs))%Z -> a = wa (A + k) ->
  ov_read_bytes segs m a 8 = Some (le8 (le_bytes_to_word (firstn 8 (skipn (Z.to_nat k) bs)))).
Proof.
  intros segs m A bs k a H Hk Hl ->.
  rewrite le8_le_bytes_to_word by (rewrite length_firstn, length_skipn; lia).
  apply bytes_at_read; [exact H | lia | lia].
Qed.

Lemma bytes_read1_at : forall segs (m : mem) A bs k a,
  bytes_at segs m A bs -> (0 <= k < Z.of_nat (length bs))%Z -> a = wa (A + k) ->
  ov_read_bytes segs m a 1 = Some [nth (Z.to_nat k) bs (Z_to_bv 8 0)].
Proof.
  intros segs m A bs k a H Hk ->.
  eapply (u8ro_read segs m A bs k); [exact H | | lia | reflexivity].
  apply nth_error_nth'. lia.
Qed.

Lemma bytes_read4_at : forall segs (m : mem) A bs k a,
  bytes_at segs m A bs -> (0 <= k)%Z -> (k + 4 <= Z.of_nat (length bs))%Z -> a = wa (A + k) ->
  ov_read_bytes segs m a 4 = Some (firstn 4 (skipn (Z.to_nat k) bs)).
Proof. intros segs m A bs k a H Hk Hl ->. apply bytes_at_read; [exact H | lia | lia]. Qed.

Lemma u8arr_read8_at : forall segs (m : mem) A bs k a,
  u8arr segs m A bs -> (0 <= k)%Z -> (k + 8 <= Z.of_nat (length bs))%Z -> a = wa (A + k) ->
  ov_read_bytes segs m a 8 = Some (le8 (le_bytes_to_word (firstn 8 (skipn (Z.to_nat k) bs)))).
Proof. intros segs m A bs k a [H _]. apply bytes_read8_at. exact H. Qed.

Lemma u8arr_read1_at : forall segs (m : mem) A bs k a,
  u8arr segs m A bs -> (0 <= k < Z.of_nat (length bs))%Z -> a = wa (A + k) ->
  ov_read_bytes segs m a 1 = Some [nth (Z.to_nat k) bs (Z_to_bv 8 0)].
Proof. intros segs m A bs k a [H _]. apply bytes_read1_at. exact H. Qed.

Ltac num_load_hook :=
  match goal with
  | |- context [ov_read_bytes ?segs ?m ?a ?n] =>
      let Ea := addr_expr a in
      match goal with
      | H : u8arr segs m ?A ?bs |- _ =>
          lazymatch n with
          | 8%nat => rewrite (u8arr_read8_at segs m A bs (Ea - A)%Z a H ltac:(lia) ltac:(lia) ltac:(unfold wa; f_equal; lia))
          | 1%nat => rewrite (u8arr_read1_at segs m A bs (Ea - A)%Z a H ltac:(lia) ltac:(unfold wa; f_equal; lia))
          end
      | H : bytes_at segs m ?A ?bs |- _ =>
          lazymatch n with
          | 4%nat => rewrite (bytes_read4_at segs m A bs (Ea - A)%Z a H ltac:(lia) ltac:(lia) ltac:(unfold wa; f_equal; lia))
          | 8%nat => rewrite (bytes_read8_at segs m A bs (Ea - A)%Z a H ltac:(lia) ltac:(lia) ltac:(unfold wa; f_equal; lia))
          | 1%nat => rewrite (bytes_read1_at segs m A bs (Ea - A)%Z a H ltac:(lia) ltac:(unfold wa; f_equal; lia))
          end
      end
  end;
  load_post.

Ltac num_solve_store0 :=
  match goal with
  | |- context [store_ok ?segs ?m ?a ?n] =>
    rewrite ?store_bytes_8', ?store_bytes_4', ?store_bytes_2', ?store_bytes_1';
    let E := addr_expr a in
    match goal with
    | H : rw_cells segs m ?A ?cs0 |- _ =>
        let k := addr_diff E A in addr_near k;
        let kn := eval vm_compute in (Z.to_nat k) in
        split_for_access H segs m A cs0 kn n;
        let cs := lazymatch type of H with rw_cells _ _ _ ?cs => cs end in
        let c := eval_cell_at cs kn in
        lazymatch c with Some ?c0 =>
          rewrite (rw_cells_store_ok_at segs m A cs kn c0 n a H) by (first [cells_cbv; reflexivity | reflexivity | addr_eq_tac]);
          cbv beta iota;
          match goal with
          | |- context [write_to_mem m a ?bs] =>
              replace (write_to_mem m a bs) with (write_to_mem m (wa (A + Z.of_nat kn)) bs) by (f_equal; addr_eq_tac)
          end
        end
    | HS : store_ok segs m ?a' n = true |- _ =>
        cbv delta [wa] in HS;
        first [ rewrite HS
              | replace (store_ok segs m a n) with true
                  by (rewrite <- HS; f_equal; word_eq_tac);
                try replace (write_to_mem m a) with (write_to_mem m a')
                  by (f_equal; word_eq_tac) ];
        cbv beta iota
    end
  end.

Ltac num_store_hook :=
  match goal with
  | |- context [store_ok ?segs ?m ?a ?n] =>
      rewrite ?store_bytes_8', ?store_bytes_4', ?store_bytes_2', ?store_bytes_1';
      let Ea := addr_expr a in
      match goal with
      | H : u8arr segs m ?A ?bs |- _ =>
          rewrite (u8arr_storeN_ok segs m A bs (Ea - A)%Z n a H ltac:(lia) ltac:(cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia)
                     ltac:(unfold wa; f_equal; lia));
          cbv beta iota
      end
  end.

Ltac num_bytes_len xs :=
  lazymatch xs with
  | le8 _ => constr:(8%nat) | le4 _ => constr:(4%nat) | le2 _ => constr:(2%nat) | le1 _ => constr:(1%nat)
  | Z_to_le_bytes ?n _ => constr:(n)
  | [_] => constr:(1%nat) | [_; _] => constr:(2%nat) | [_; _; _; _] => constr:(4%nat) | [_; _; _; _; _; _; _; _] => constr:(8%nat)
  end.
Ltac num_store_done :=
  lazymatch goal with
  | |- evt ?segs _ (MS _ _ _ _ _ (write_to_mem ?m ?a ?xs) _) =>
      let Ea := addr_expr a in
      let n := num_bytes_len xs in
      (match goal with
       | UA : u8arr segs m ?A ?bs |- _ =>
           let SOK := fresh "SOK" in
           assert (SOK : store_ok segs m a n = true)
             by (apply (u8arr_storeN_ok segs m A bs (Ea - A)%Z n a UA);
                 [lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | unfold wa; f_equal; lia]);
           let UA' := fresh "UA" in
           pose proof (u8arr_writeN segs m A bs (Ea - A)%Z xs UA ltac:(lia)
                         ltac:(rewrite ?length_le8, ?length_le4, ?length_le2, ?length_le1, ?length_Z_to_le_bytes; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; lia)) as UA';
           replace (wa (A + (Ea - A))) with (wa Ea) in UA' by (f_equal; lia);
           let LU := fresh "LU" in
           assert (LU : length (upd_bytes bs (Z.to_nat (Ea - A)) xs) = length bs)
             by (apply upd_bytes_length; rewrite ?length_le8, ?length_le4, ?length_le2, ?length_le1, ?length_Z_to_le_bytes; cbn [length]; lia);
           store_done;
           try clear UA; rename UA' into UA
       end)
  end.

Lemma num_signed_of_Z : forall z, (-2^63 <= z < 2^63)%Z -> bv_signed (Z_to_bv 64 z) = z.
Proof.
  intros z Hz. rewrite Z_to_bv_signed. apply bv_swrap_small. unfold bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 64 / 2)%Z with (2^63)%Z. lia.
Qed.
Ltac num_signed_lits_in H :=
  repeat match type of H with
  | context [bv_signed (Z_to_bv 64 ?z)] => rewrite (num_signed_of_Z z) in H by lia
  end.

Definition IsData (w : word) : Prop := True.
Ltac num_is_data_var v :=
  is_var v;
  first [ lazymatch type of v with bv 8 => idtac | byte => idtac end
        | lazymatch goal with M : IsData v |- _ => idtac end ].
Ltac num_abstract_loads :=
  repeat match goal with
  | |- context [nth ?k ?l (Z_to_bv 8 0)] => let b := fresh "b" in generalize (nth k l (Z_to_bv 8 0)); intro b
  | |- context [le_bytes_to_word (firstn 8 (skipn ?k ?l))] =>
      let w := fresh "w" in generalize (le_bytes_to_word (firstn 8 (skipn k l))); intro w;
      let M := fresh "DM" in assert (M : IsData w) by exact I
  | |- context [sext 64 (bv_extract 0 32 (le_bytes_to_word ?l))] =>
      let w := fresh "w" in generalize (sext 64 (bv_extract 0 32 (le_bytes_to_word l))); intro w;
      let M := fresh "DM" in assert (M : IsData w) by exact I
  | |- context [zext 64 (bv_extract 0 32 (le_bytes_to_word ?l))] =>
      let w := fresh "w" in generalize (zext 64 (bv_extract 0 32 (le_bytes_to_word l))); intro w;
      let M := fresh "DM" in assert (M : IsData w) by exact I
  end.
Ltac num_abstract_data :=
  repeat match goal with
  | |- context [Z_to_bv 64 (bv_swrap 32 ?t)] =>

      match t with
      | context [bv_unsigned ?v] => num_is_data_var v
      end;
      let z := fresh "z" in let Hz := fresh "Hz" in
      assert (Hz : (-2147483648 <= bv_swrap 32 t < 2147483648)%Z) by (rewrite bv_swrap32; apply swrap32_range);
      generalize Hz; generalize (bv_swrap 32 t); clear Hz; intros z Hz
  | |- context [Z_to_bv 64 ?t] =>
      match t with
      | context [bv_unsigned ?v] => num_is_data_var v
      end;
      let w := fresh "w" in generalize (Z_to_bv 64 t); intro w;
      let M := fresh "DM" in assert (M : IsData w) by exact I
  end.

Ltac nstep :=
  zstep; nnorm;
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ (wa (_ + Z.of_nat _)) (Z_to_le_bytes ?n ?z)) _) =>

      lazymatch n with
      | 8%nat => change (Z_to_le_bytes 8 z) with (le8 (Z_to_bv 64 z))
      | 4%nat => change (Z_to_le_bytes 4 z) with (le4 (Z_to_bv 64 z))
      | 2%nat => change (Z_to_le_bytes 2 z) with (le2 (Z_to_bv 64 z))
      | 1%nat => change (Z_to_le_bytes 1 z) with (le1 (Z_to_bv 64 z))
      end;
      mem_after_store
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ (wa (_ + Z.of_nat _)) (le1 ?v)) _) =>

      change (le1 v) with [Z_to_bv 8 (bv_unsigned v)]; mem_after_store
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ _) _) => num_store_done
  | |- _ => num_abstract_loads; num_abstract_data
  end.

Ltac num_drop_data H :=
  lazymatch type of H with
  | context [bv_unsigned ?x] => is_var x; clear H
  | context [Z.lor _ _] => clear H
  | context [Z.land _ _] => clear H
  | _ => idtac
  end.

Ltac num_is_data H :=
  lazymatch type of H with
  | context [bv_unsigned ?x] => num_is_data_var x
  | context [bv_signed ?x] => num_is_data_var x
  | context [Z.lor _ _] => idtac
  | context [Z.land _ _] => idtac
  end.

Ltac walk_fuel n K :=
  lazymatch n with
  | O => lazymatch goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => fail 100 "walk: out of fuel at" pc end
  | S ?n' =>
      lazymatch goal with
      | |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) => first [ K pc | (nstep; walk_fuel n' K) ]
      | |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) =>
          let H := fresh "KB" in
          if_cases H; zify_cond H; num_signed_lits_in H;
          tryif num_is_data H then (clear H; walk_fuel n' K) else first [ solve [exfalso; lia] | walk_fuel n' K ]
      end
  end.
Ltac walk K := walk_fuel 400%nat K.

Ltac walkn n K :=
  lazymatch n with
  | O => idtac
  | S ?n' =>
      lazymatch goal with
      | |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) => first [ K pc | (nstep; walkn n' K) ]
      | |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) =>
          let H := fresh "KB" in
          if_cases H; zify_cond H; num_signed_lits_in H;
          tryif num_is_data H then (clear H; walkn n' K) else first [ solve [exfalso; lia] | walkn n' K ]
      end
  end.

Ltac num_ret_pc :=
  lazymatch goal with
  | |- context [ret_pc (Z_to_bv 64 ?r)] =>
      replace (ret_pc (Z_to_bv 64 r)) with (Z_to_bv 64 r) by (symmetry; apply ret_pc_even; [lia| reflexivity])
  end.

Ltac num_call_memmove HM UA Dz Sz Nz :=
  lazymatch type of UA with
  | u8arr ?segs ?m ?Ub ?bsb =>
      let HM' := fresh "HM" in pose proof HM as HM'; hnf in HM';
      eapply evt_cut;
      [ eapply evt_eq;
        [| eapply HM' with (D := Dz) (S := Sz) (N := Nz) (U := Ub) (bs := bsb);
           [ exact UA | lia | lia | lia | lia | Z.div_mod_to_equations; lia
           | lazymatch goal with MI : mem_inv segs m |- _ => exact MI end ] ];
        num_st_eq
      | cbv beta;
        let ms' := fresh "ms'" in let P := fresh "P" in
        intros ms' P; unfold memmove_post_g in P;
        let m3 := fresh "m" in let bs3 := fresh "bs" in let MUc := fresh "MUc" in let WMc := fresh "WMc" in
        let MIc := fresh "MI" in let UA3 := fresh "UA" in let UL3 := fresh "LB" in
        destruct P as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m3 & bs3 & -> & MUc & WMc & MIc & UA3 & UL3);
        clear UA; transport_after_call segs m m3 MUc WMc;
        clear MUc WMc HM';
        repeat match goal with MI : mem_inv segs m |- _ => clear MI end;
        num_ret_pc; rename UA3 into UA ]
  end.

Ltac num_call_memset HS UA az bz Cz :=
  lazymatch type of UA with
  | u8arr ?segs ?m ?Ub ?bsb =>
      let b1 := fresh "b" in let mid := fresh "mid" in let b3 := fresh "b" in
      let L1 := fresh "L1" in let LM := fresh "LM" in let L3 := fresh "L3" in
      let U1 := fresh "U1" in let MID := fresh "MID" in let U3 := fresh "U3" in
      destruct (u8arr_range_split segs m Ub bsb (Z.to_nat az) (Z.to_nat bz) UA ltac:(lia) ltac:(lia))
        as (b1 & mid & b3 & L1 & LM & L3 & U1 & MID & U3);
      clear UA;
      replace (Ub + Z.of_nat (Z.to_nat az))%Z with (Ub + az)%Z in MID by lia;
      replace (Z.to_nat bz - Z.to_nat az)%nat with (Z.to_nat (bz - az)) in MID by lia;
      let HS' := fresh "HS" in pose proof HS as HS'; hnf in HS';
      eapply evt_cut;
      [ eapply evt_eq;
        [| eapply HS' with (D := (Ub + az)%Z) (C := Cz) (N := (bz - az)%Z) (junk := mid);
           [ exact MID | lazymatch goal with MI : mem_inv segs m |- _ => exact MI end | lia | lia | lia | lia ] ];
        num_st_eq
      | cbv beta;
        let ms' := fresh "ms'" in let P := fresh "P" in
        intros ms' P; unfold memsetZ_post_g in P;
        let m3 := fresh "m" in let MUc := fresh "MUc" in let WMc := fresh "WMc" in let MIc := fresh "MI" in let DSTc := fresh "DSTc" in
        destruct P as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m3 & -> & MUc & WMc & MIc & DSTc);
        transport_after_call segs m m3 MUc WMc;
        clear MUc WMc HS';
        repeat match goal with MI : mem_inv segs m |- _ => clear MI end;
        num_ret_pc;
        replace (Ub + az)%Z with (Ub + Z.of_nat (length b1))%Z in DSTc by lia;
        replace (Ub + Z.of_nat (Z.to_nat bz))%Z with (Ub + Z.of_nat (length b1) + Z.of_nat (Z.to_nat (bz - az)))%Z in U3 by lia;
        let bs' := fresh "bs" in let LJ := fresh "LJ" in let LB := fresh "LB" in
        destruct (u8arr_range_join segs m3 Ub b1 _ _ b3 U1 DSTc U3) as (bs' & LJ & UA);
        assert (LB : length bs' = length bsb) by lia;
        clear U1 U3 DSTc LJ ]
  end.

Ltac walkd_fuel n K :=
  lazymatch n with
  | O => idtac "walkd: out of fuel"
  | S ?n' =>
      lazymatch goal with
      | |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) => first [ K pc | (nstep; walkd_fuel n' K) | idtac "STUCK at" pc ]
      | |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) =>
          let H := fresh "KB" in
          if_cases H; zify_cond H; num_signed_lits_in H;
          tryif num_is_data H then (clear H; walkd_fuel n' K) else first [ solve [exfalso; lia] | walkd_fuel n' K ]
      end
  end.
Ltac walkd K := walkd_fuel 400%nat K.
