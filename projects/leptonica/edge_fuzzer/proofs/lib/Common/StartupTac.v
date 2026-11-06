(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common Require Export
  PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac StoreOk StreamSim MmapSim
  MemSplit StartupAux ZStores.
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
Ltac pin :=
  repeat match goal with
         | H : getr ?rs ?r = _ |- context [getr ?rs ?r] => rewrite !H
         end.

(* [comment removed for export] *)
Ltac unorm :=
  repeat match goal with
         | |- context [bv_unsigned (Z_to_bv 64 ?z)] =>
             lazymatch z with
             | context [Z_to_bv 64 _] => fail
             | _ => rewrite (u_Z2bv z) by lia
             end
         end.

(* [comment removed for export] *)
Ltac zlit :=
  repeat match goal with
         | |- context [Z_to_bv 64 ?z] =>
             lazymatch z with
             | Z0 => fail | Zpos _ => fail | Zneg _ => fail
             | _ => check_closed_term z; let z' := eval vm_compute in z in change z with z'
             end
         end.

(* [comment removed for export] *)
Ltac region_side :=
  unfold win_lo; rewrite ?stack_max_size_val, ?length_N_to_le_bytes, ?length_zeros, ?repeat_length;
  cbn [length Z.of_nat Pos.of_succ_nat Pos.succ Nat.add Nat.mul]; imm_norm; unorm; lia.

(* [comment removed for export] *)
Ltac addr_norm :=
  gres; pin; imm_norm; rewrite ?v_addi_0; unfold v_addi, v_add; unorm; zlit.

(* [comment removed for export] *)
Ltac vclose_fin :=
  first [ reflexivity | f_equal; lia | apply at_self | symmetry; apply at_self
        | apply Z_to_bv_u_eq; lia | apply Z_to_bv_u_eq_sym; lia | bveq ].
Ltac vclose :=
  gres; pin; imm_norm;
  first [ reflexivity
        | unfold v_addi, v_add; unorm; zlit; vclose_fin
        | rewrite ?v_addi_0, ?v_add_0_r, ?v_add_0_l; first [ reflexivity | vclose_fin ]
        | rewrite ?v_addi_0, ?v_add_0_r, ?v_add_0_l; unfold v_addi, v_add; unorm; zlit; vclose_fin ].

(* [comment removed for export] *)
Ltac sn F D := stepn F D; pin.
Ltac sv F D v := stepiv F D v vclose.

(* [comment removed for export] *)
Ltac blit :=
  repeat match goal with
         | |- context [Z_to_bv 8 (bv_unsigned (Z_to_bv 64 ?z))] =>
             lazymatch z with
             | Z0 => change (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 z))) with (Z_to_bv 8 0)
             | Zpos _ => let z' := eval vm_compute in (z mod 256)%Z in
                         change (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 z))) with (Z_to_bv 8 z')
             end
         end.

(* [comment removed for export] *)
Ltac push_store :=
  blit;
  first [ rewrite wbytes_cmem_win by region_side
        | rewrite wbytes_cmem_data by region_side
        | idtac ].

(* [comment removed for export] *)
Ltac stw F D aa vv oktac :=
  chain_step;
  [ reflexivity
  | lazymatch type of D with
    | decode_any _ = Some (Store SZ8 _ _ _, _) =>
        eapply step_sd_at with (a := aa) (v := vv);
        [ exact F | reflexivity | exact D | vclose | vclose | oktac ]
    | decode_any _ = Some (Store SZ4 _ _ _, _) =>
        eapply step_sw_at with (a := aa) (v := vv);
        [ exact F | reflexivity | exact D | vclose | vclose | oktac ]
    | decode_any _ = Some (Store SZ2 _ _ _, _) =>
        eapply step_sh_at with (a := aa) (v := vv);
        [ exact F | reflexivity | exact D | vclose | vclose | oktac ]
    | decode_any _ = Some (Store SZ1 _ _ _, _) =>
        eapply MmapSim.step_sb_at with (a := aa) (v := vv);
        [ exact F | reflexivity | exact D | vclose | vclose | reflexivity | oktac ]
    end
  | step_simpl; push_store ].

(* [comment removed for export] *)
Ltac ok_sub Hok :=
  store_ok_peel; eapply store_ok_sub; [ | exact Hok | | ];
  rewrite ?length_N_to_le_bytes, ?length_zeros; unorm; lia.

(* [comment removed for export] *)
Ltac ok_win HJ :=
  apply store_ok_cmem_win; [ repeat apply wfJ_wbytes; exact HJ | region_side | region_side ].

(* [comment removed for export] *)
Ltac ok_data :=
  apply store_ok_cmem_data;
  lazymatch goal with |- ?g => check_closed_term g; vm_compute; reflexivity end.

(* [comment removed for export] *)
Ltac ld_step F D bsv vv rdtac valtac :=
  chain_step;
  [ reflexivity
  | lazymatch type of D with
    | decode_any _ = Some (Load SZ8 _ _ _ _, _) => eapply step_ld with (bs := bsv) (v := vv)
    | decode_any _ = Some (Load SZ4 true _ _ _, _) => eapply step_lw with (bs := bsv) (v := vv)
    | decode_any _ = Some (Load SZ4 false _ _ _, _) => eapply step_lwu with (bs := bsv) (v := vv)
    | decode_any _ = Some (Load SZ2 true _ _ _, _) => eapply step_lh with (bs := bsv) (v := vv)
    | decode_any _ = Some (Load SZ2 false _ _ _, _) => eapply step_lhu with (bs := bsv) (v := vv)
    end;
    [ exact F | reflexivity | exact D | addr_norm; rdtac | valtac ]
  | step_simpl ]; vnorm; pin.

(* [comment removed for export] *)
Ltac lb_step F D bb rdtac :=
  chain_step;
  [ reflexivity
  | lazymatch type of D with
    | decode_any _ = Some (Load SZ1 false _ _ _, _) => eapply step_lbu with (b := bb)
    | decode_any _ = Some (Load SZ1 true _ _ _, _) => eapply step_lb with (b := bb)
    end;
    [ exact F | reflexivity | exact D | addr_norm; rdtac ]
  | step_simpl ]; vnorm; pin.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma rdn_wbytes_out_off : forall segs bs m (s k k' : Z) (n : nat),
  (2^33 <= s)%Z -> (s <= 2^63)%Z ->
  ((0 <=? k')%Z && (k' <=? 2^32)%Z && (0 <=? k)%Z && (k <=? 2^32)%Z && (Z.of_nat (length bs) <=? 2^32)%Z &&
   (Z.of_nat n <=? 2^32)%Z && ((k' + Z.of_nat n <=? k)%Z || (k + Z.of_nat (length bs) <=? k')%Z))%bool = true ->
  rdn segs (wbytes m (Z_to_bv 64 (s - k')) bs) (Z_to_bv 64 (s - k)) n = rdn segs m (Z_to_bv 64 (s - k)) n.
Proof.
  intros segs bs m s k k' n Hs1 Hs2 Hb.
  apply andb_prop in Hb as [Hb Hor]. apply andb_prop in Hb as [Hb H6]. apply andb_prop in Hb as [Hb H5]. apply andb_prop in Hb as [Hb H4].
  apply andb_prop in Hb as [Hb H3]. apply andb_prop in Hb as [H1 H2].
  apply Z.leb_le in H1. apply Z.leb_le in H2. apply Z.leb_le in H3. apply Z.leb_le in H4. apply Z.leb_le in H5. apply Z.leb_le in H6.
  assert (E1 : bv_unsigned (Z_to_bv 64 (s - k)) = (s - k)%Z) by (apply u_Z2bv; lia).
  assert (E2 : bv_unsigned (Z_to_bv 64 (s - k')) = (s - k')%Z) by (apply u_Z2bv; lia).
  apply rdn_wbytes_out; rewrite ?E1, ?E2; [| lia | lia].
  apply Bool.orb_prop in Hor as [H|H]; apply Z.leb_le in H; [left | right]; lia.
Qed.

Lemma rdn_wbytes_out_off0 : forall segs bs m (s k : Z) (n : nat),
  (2^33 <= s)%Z -> (s <= 2^63)%Z ->
  ((0 <=? k)%Z && (k <=? 2^32)%Z && (Z.of_nat (length bs) <=? 2^32)%Z && (Z.of_nat n <=? k)%Z && (Z.of_nat n <=? 2^32)%Z)%bool = true ->
  rdn segs (wbytes m (Z_to_bv 64 s) bs) (Z_to_bv 64 (s - k)) n = rdn segs m (Z_to_bv 64 (s - k)) n.
Proof.
  intros segs bs m s k n Hs1 Hs2 Hb.
  apply andb_prop in Hb as [Hb H5]. apply andb_prop in Hb as [Hb H4]. apply andb_prop in Hb as [Hb H3]. apply andb_prop in Hb as [H1 H2].
  apply Z.leb_le in H1. apply Z.leb_le in H2. apply Z.leb_le in H3. apply Z.leb_le in H4. apply Z.leb_le in H5.
  assert (E1 : bv_unsigned (Z_to_bv 64 (s - k)) = (s - k)%Z) by (apply u_Z2bv; lia).
  assert (E2 : bv_unsigned (Z_to_bv 64 s) = s) by (apply u_Z2bv; lia).
  apply rdn_wbytes_out; rewrite ?E1, ?E2; [left| |]; lia.
Qed.

Lemma rdn_wbytes_out_lit : forall segs bs m (za zb : Z) (n : nat),
  ((0 <=? zb)%Z && (zb <? 2^64)%Z && (zb + Z.of_nat (length bs) <=? 2^64)%Z && (0 <=? za)%Z && (za <? 2^64)%Z && (za + Z.of_nat n <=? 2^64)%Z &&
   ((za + Z.of_nat n <=? zb)%Z || (zb + Z.of_nat (length bs) <=? za)%Z))%bool = true ->
  rdn segs (wbytes m (Z_to_bv 64 zb) bs) (Z_to_bv 64 za) n = rdn segs m (Z_to_bv 64 za) n.
Proof.
  intros segs bs m za zb n Hb.
  apply andb_prop in Hb as [Hb Hor]. apply andb_prop in Hb as [Hb H6]. apply andb_prop in Hb as [Hb H5]. apply andb_prop in Hb as [Hb H4].
  apply andb_prop in Hb as [Hb H3]. apply andb_prop in Hb as [H1 H2].
  apply Z.leb_le in H1. apply Z.ltb_lt in H2. apply Z.leb_le in H3. apply Z.leb_le in H4. apply Z.ltb_lt in H5. apply Z.leb_le in H6.
  assert (E1 : bv_unsigned (Z_to_bv 64 za) = za) by (apply u_Z2bv; lia).
  assert (E2 : bv_unsigned (Z_to_bv 64 zb) = zb) by (apply u_Z2bv; lia).
  apply rdn_wbytes_out; rewrite ?E1, ?E2; [| lia | lia].
  apply Bool.orb_prop in Hor as [H|H]; apply Z.leb_le in H; [left | right]; lia.
Qed.

Ltac peel_zc z := lazymatch z with Z0 => idtac | Zpos _ => idtac | Zneg _ => idtac end.
(* [comment removed for export] *)
Ltac addr_lin :=
  repeat match goal with
  | |- context [Z_to_bv 64 (bv_unsigned ?s - ?a + ?b)%Z] =>
      peel_zc a; peel_zc b; let c := eval vm_compute in (a - b)%Z in
      lazymatch c with
      | Zneg _ => let c' := eval vm_compute in (b - a)%Z in replace (bv_unsigned s - a + b)%Z with (bv_unsigned s + c')%Z by lia
      | _ => replace (bv_unsigned s - a + b)%Z with (bv_unsigned s - c)%Z by lia
      end
  | |- context [Z_to_bv 64 (bv_unsigned ?s - ?a - ?b)%Z] =>
      peel_zc a; peel_zc b; let c := eval vm_compute in (a + b)%Z in replace (bv_unsigned s - a - b)%Z with (bv_unsigned s - c)%Z by lia
  | |- context [Z_to_bv 64 (bv_unsigned ?s + ?a - ?b)%Z] =>
      peel_zc a; peel_zc b; let c := eval vm_compute in (b - a)%Z in
      lazymatch c with
      | Zneg _ => let c' := eval vm_compute in (a - b)%Z in replace (bv_unsigned s + a - b)%Z with (bv_unsigned s + c')%Z by lia
      | _ => replace (bv_unsigned s + a - b)%Z with (bv_unsigned s - c)%Z by lia
      end
  | |- context [Z_to_bv 64 (bv_unsigned ?s + ?a + ?b)%Z] =>
      peel_zc a; peel_zc b; let c := eval vm_compute in (a + b)%Z in replace (bv_unsigned s + a + b)%Z with (bv_unsigned s + c)%Z by lia
  end.
Ltac peel_bool := cbn [length word_to_le_bytes Z_to_le_bytes zeros repeat app Datatypes.length Z.of_nat Pos.of_succ_nat Pos.succ Nat.add];
                  lazymatch goal with |- ?g => check_closed_term g end; vm_compute; reflexivity.
Ltac peel_generic :=
  repeat (lazymatch goal with
          | |- rdn _ (wbytes _ ?a _) ?b _ = _ =>
              tryif constr_eq a b then fail else
              first [ rewrite rdn_wbytes_out_lit by peel_bool
                    | rewrite rdn_wbytes_out by region_side ]
          end).
Ltac peel :=
  addr_lin;
  lazymatch goal with
  | |- rdn _ _ (Z_to_bv 64 (?s - _)%Z) _ = _ =>
      let L := fresh "PEEL_lo" in let H := fresh "PEEL_hi" in
      tryif (assert (L : (2^33 <= s)%Z) by lia; assert (H : (s <= 2^63)%Z) by lia) then
        (repeat (lazymatch goal with
                 | |- rdn _ (wbytes _ ?a _) ?b _ = _ =>
                     tryif constr_eq a b then fail else
                     first [ rewrite rdn_wbytes_out_off by (first [exact L | exact H | peel_bool])
                           | rewrite rdn_wbytes_out_off0 by (first [exact L | exact H | peel_bool])
                           | rewrite rdn_wbytes_out_lit by peel_bool
                           | rewrite rdn_wbytes_out by region_side ]
                 end); clear L H)
      else peel_generic
  | |- _ => peel_generic
  end.

(* [comment removed for export] *)
Ltac rd_img L := addr_norm; rewrite rdn_cmem_data by region_side; peel; exact L.

(* [comment removed for export] *)
Ltac rd_hit8 :=
  addr_norm; peel;
  lazymatch goal with |- rdn _ (wbytes _ ?a' _) ?a _ = _ =>
    first [ constr_eq a a' | replace a with a' by (first [f_equal; lia | bveq]) ] end;
  apply rdn_wbytes_hit8; unorm; lia.

(* [comment removed for export] *)
Ltac in_list := cbn [In]; repeat first [ left; reflexivity | right ].
Ltac solve_regs_agree :=
  repeat (apply regs_agree_upd; [ in_list | ]); apply regs_agree_refl.

(* [comment removed for export] *)
Ltac incl_list :=
  let r := fresh "r" in let Hr := fresh "Hr" in
  intros r Hr; cbn [In] in Hr;
  repeat (destruct Hr as [<-|Hr]; [in_list|]); destruct Hr.
Ltac regs_agree_weaken Hag :=
  eapply regs_agree_mono; [| exact Hag]; incl_list.

Ltac notin_list :=
  cbn [In]; intros HH; repeat (destruct HH as [HH|HH]; [apply bv_eq in HH; cbv in HH; discriminate HH|]); exact HH.

(* [comment removed for export] *)
Ltac carry Hag H r T :=
  pose proof (Hag r ltac:(notin_list)) as T;
  gres_loop_in T;          (* [comment removed for export] *)
  rewrite ?H in T.

(* [comment removed for export] *)
Ltac ra_chain :=
  first [ apply regs_agree_refl
        | apply regs_agree_upd; [ in_list | ]; ra_chain
        | match goal with
          | Hag : regs_agree _ _ ?r |- regs_agree _ _ ?r =>
              eapply regs_agree_trans; [ | regs_agree_weaken Hag ]; ra_chain
          end ].

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition bwd (segs : list Segment) (G : machine_state -> Prop) : Prop :=
  forall st st', msteps segs st st' -> G st' -> G st.

Lemma bwd_msteps : forall segs tgt, bwd segs (fun st => msteps segs st tgt).
Proof. intros segs tgt st st' H1 H2. eapply msteps_trans; eassumption. Qed.

(* [comment removed for export] *)
Ltac gsteps HG := eapply HG.
