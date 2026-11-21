(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: relocated for the zlib 1.4 build, ported to the model, comments removed. *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan Require Import
  PropExec CatExec CatSim SeqExec StoreOk Hoare StepTac.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1 Require Import
  SymEx2Expr SymEx2 SymEx2Tac MemRel SymAux DSLayout FillWinMem TreeMem BitsModel BitsModel2
  RomRead TreesRod BitsLib TrSmallModel.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import
  ZIface DeflateState Trees LmatchModel FillWinModel TreeModel SendModel TreesTab CompressModel.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.D6S Require Import Segs6 DS6 TreesRod6 Callee6 TreesApi6.
Import ListNotations.
Local Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec.FPState}.

End FXG.
Local Opaque length_code_a dist_code_a extra_lbits_a base_length_a extra_dbits_a base_dist_a
             static_ltree_fc static_ltree_dl static_dtree_fc static_dtree_dl bl_order_a extra_blbits_a.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec.FPState}.


Lemma pb_read4m : forall segs mem P n (t : arr) i a,
  cells segs mem P 4 2 n (arr_get t) -> 0 <= i < n -> a = P + 4 * i ->
  exists bs, rdn segs mem (zw a) 2 = Some bs /\ bytes_le_to_Z bs = pb t i.
Proof.
  intros segs mem P n t i a Hc Hi ->. unfold pb.
  apply (cell_read_at segs mem (P + 4 * i) 2 (arr_get t i)); [exact (Hc i Hi) | reflexivity].
Qed.
Lemma wb_read1m : forall segs mem P n (d : arr) i a,
  cells segs mem P 1 1 n (arr_get d) -> 0 <= i < n -> a = P + i ->
  exists bs, rdn segs mem (zw a) 1 = Some bs /\ bytes_le_to_Z bs = wb d i.
Proof.
  intros segs mem P n d i a Hc Hi ->. unfold wb.
  pose proof (Hc i Hi) as H. replace (P + 1 * i) with (P + i) in H by lia.
  apply (cell_read_at segs mem (P + i) 1 (arr_get d i)); [exact H | reflexivity].
Qed.

Lemma srl_eq : forall v value bv, 0 <= v < 2 ^ 16 -> v = wrap16 value -> 1 <= bv <= 16 ->
  (zaluw ALU_SRL v (szwrap 32 (16 - bv))) mod 2 ^ 16 = Z.shiftr (wrap16 value) (Buf_size - bv).
Proof.
  intros v value bv Hv -> Hbv. unfold zaluw. rewrite zw_srlw, u_zw. unfold Buf_size.
  rewrite (szwrap_small 32 (16 - bv)) by (change (2 ^ (32 - 1)) with 2147483648; lia).
  rewrite (Z.mod_small (16 - bv) 32) by lia.
  rewrite (Z.mod_small (wrap16 value) (2 ^ 32)) by (change (2 ^ 32) with 4294967296; change (2 ^ 16) with 65536 in Hv; lia).
  pose proof (Z.pow_pos_nonneg 2 (16 - bv) ltac:(lia) ltac:(lia)) as Hp.
  assert (Hq : 0 <= wrap16 value / 2 ^ (16 - bv) < 2 ^ 16).
  { split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|]. nia. }
  rewrite (szwrap_small 32) by (change (2 ^ (32 - 1)) with 2147483648; change (2 ^ 16) with 65536 in Hq; lia).
  rewrite Z.shiftr_div_pow2 by lia.
  rewrite (Z.mod_small _ (2 ^ 64)) by (change (2 ^ 64) with 18446744073709551616; change (2 ^ 16) with 65536 in Hq; lia).
  apply Z.mod_small. exact Hq.
Qed.

Lemma byte1_eq2 : forall e nb, e mod 2 ^ 16 = nb -> wrap8 ((e / 2 ^ 8) mod 2 ^ 8) = wrap8 (Z.shiftr (wrap16 nb) 8).
Proof.
  intros e nb E. rewrite <- (byte1_eq e nb E). f_equal.
  rewrite <- (Z.mod_small ((e mod 2 ^ 16) / 2 ^ 8) (2 ^ 8)).
  2:{ pose proof (Z.mod_pos_bound e (2 ^ 16) ltac:(lia)) as B.
      split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|]. change (2 ^ 8 * 2 ^ 8) with (2 ^ 16). lia. }
  rewrite <- !Z.shiftr_div_pow2 by lia. rewrite <- !Z.land_ones by lia.
  rewrite !Z.shiftr_land, <- !Z.land_assoc. f_equal.
Qed.

Lemma srl_eq' : forall v value bv, 0 <= v < 2 ^ 16 -> v = wrap16 value -> 1 <= bv <= 16 ->
  (zaluw ALU_SRL v (szwrap 32 (0 - bv + 16))) mod 2 ^ 16 = Z.shiftr (wrap16 value) (Buf_size - bv).
Proof. intros v value bv Hv Ev Hbv. replace (0 - bv + 16) with (16 - bv) by lia. apply srl_eq; assumption. Qed.

Lemma szwrap16_mod : forall x, 0 <= x < 2 ^ 16 -> (szwrap 16 x) mod 2 ^ 16 = x.
Proof. intros x Hx. rewrite (szwrap_eqm 16 x) by lia. apply Z.mod_small. exact Hx. Qed.

Lemma pb_mod16 : forall t i, (pb t i) mod 2 ^ 16 = (arr_get t i) mod 2 ^ 16.
Proof. intros. unfold pb. apply Z.mod_mod. lia. Qed.
Lemma pb_wrap16 : forall t i, pb t i = wrap16 (arr_get t i).
Proof. intros. unfold pb. rewrite wrap16_mod'. reflexivity. Qed.
Lemma pb_small : forall t i, 0 <= arr_get t i < 65536 -> pb t i = arr_get t i.
Proof. intros t i H. unfold pb. apply Z.mod_small. exact H. Qed.

Lemma land_255_wb : forall (A : arr) i, Z.land (arr_get A i) 255 = wb A i.
Proof. intros A i. unfold wb. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. reflexivity. Qed.

Lemma sym_dist_eq : forall s sx,
  sym_dist s sx = wb (ds_pending_buf s) (ds_lit_bufsize s + sx) + wb (ds_pending_buf s) (ds_lit_bufsize s + sx + 1) * 2 ^ 8.
Proof.
  intros s sx. unfold sym_dist, sym_d0, sym_d1, sym_buf_get. rewrite !land_255_wb.
  rewrite Z.shiftl_mul_pow2 by lia. rewrite <- Z.add_assoc. reflexivity.
Qed.

Lemma sym_lc_eq : forall s sx, PBB s -> 0 <= ds_lit_bufsize s + sx + 1 + 1 < arr_len (ds_pending_buf s) ->
  sym_lc s sx = wb (ds_pending_buf s) (ds_lit_bufsize s + sx + 1 + 1).
Proof.
  intros s sx HP Hi. unfold sym_lc, sym_buf_get.
  replace (ds_lit_bufsize s + (sx + 1 + 1)) with (ds_lit_bufsize s + sx + 1 + 1) by lia.
  symmetry. apply wb_get; [exact HP | exact Hi].
Qed.

Lemma sym_dist_range : forall s sx, 0 <= sym_dist s sx < 65536.
Proof.
  intros s sx. rewrite sym_dist_eq.
  pose proof (wb_range (ds_pending_buf s) (ds_lit_bufsize s + sx)).
  pose proof (wb_range (ds_pending_buf s) (ds_lit_bufsize s + sx + 1)). lia.
Qed.

Lemma lor_shl8 : forall a b, 0 <= a < 256 -> 0 <= b -> Z.lor (b * 2 ^ 8) a = a + b * 2 ^ 8.
Proof.
  intros a b Ha Hb. rewrite <- Z.shiftl_mul_pow2 by lia. rewrite Z.lor_comm.
  rewrite <- Z.lxor_lor.
  - rewrite <- Z.add_nocarry_lxor; [reflexivity|].
    apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.bits_0.
    destruct (Z_lt_le_dec n 8) as [C|C].
    + rewrite (Z.shiftl_spec_low b 8 n C). apply andb_false_r.
    + rewrite (Z.bits_above_log2 a n); [reflexivity | lia |].
      apply (Z.le_lt_trans _ (Z.log2 255)); [apply Z.log2_le_mono; lia | cbn; lia].
  - apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.bits_0.
    destruct (Z_lt_le_dec n 8) as [C|C].
    + rewrite (Z.shiftl_spec_low b 8 n C). apply andb_false_r.
    + rewrite (Z.bits_above_log2 a n); [reflexivity | lia |].
      apply (Z.le_lt_trans _ (Z.log2 255)); [apply Z.log2_le_mono; lia | cbn; lia].
Qed.

Lemma forallb_seq_spec : forall (P : Z -> bool) n,
  forallb P (map Z.of_nat (seq 0 n)) = true -> forall c, 0 <= c < Z.of_nat n -> P c = true.
Proof.
  intros P n H c Hc. rewrite forallb_forall in H. apply H. apply in_map_iff.
  exists (Z.to_nat c). split; [lia|]. apply in_seq. lia.
Qed.
Lemma extra_lbits_zero_iff : forall c, 0 <= c < 29 ->
  (arr_get extra_lbits_a c =? 0) = ((c <? 8) || (c =? 28)).
Proof.
  intros c Hc.
  pose proof (forallb_seq_spec (fun c => Bool.eqb (arr_get extra_lbits_a c =? 0) ((c <? 8) || (c =? 28))) 29
                ltac:(vm_compute; reflexivity) c Hc) as H.
  cbn beta in H. apply Bool.eqb_prop in H. exact H.
Qed.
Lemma extra_dbits_zero_iff : forall c, 0 <= c < 30 ->
  (arr_get extra_dbits_a c =? 0) = (c <? 4).
Proof.
  intros c Hc.
  pose proof (forallb_seq_spec (fun c => Bool.eqb (arr_get extra_dbits_a c =? 0) (c <? 4)) 30
                ltac:(vm_compute; reflexivity) c Hc) as H.
  cbn beta in H. apply Bool.eqb_prop in H. exact H.
Qed.
Lemma base_length_le : forall lc, 0 <= lc < 256 ->
  0 <= lc - arr_get base_length_a (arr_get length_code_a lc) < 256.
Proof.
  intros lc Hlc.
  pose proof (forallb_seq_spec
                (fun lc => (0 <=? lc - arr_get base_length_a (arr_get length_code_a lc))
                           && (lc - arr_get base_length_a (arr_get length_code_a lc) <? 256)) 256
                ltac:(vm_compute; reflexivity) lc Hlc) as H.
  cbn beta in H. apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. lia.
Qed.


End FXG.
Ltac tab_range :=
  lazymatch goal with
  | |- 0 <= wb _ _ < _ => apply wb_range
  | |- 0 <= pb _ _ < _ => apply pb_range
  | |- 0 <= arr_get length_code_a _ < _ => apply length_code_bound
  | |- 0 <= arr_get dist_code_a _ < _ => apply dist_code_bound
  | |- 0 <= arr_get extra_lbits_a _ < _ => apply extra_lbits_bound
  | |- 0 <= arr_get base_length_a _ < _ => apply base_length_bound
  | |- 0 <= arr_get extra_dbits_a _ < _ => apply extra_dbits_bound
  | |- 0 <= arr_get base_dist_a _ < _ => apply base_dist_bound
  end.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec.FPState}.


End FXG.
Ltac tab_bound :=
  lazymatch goal with
  | |- 0 <= arr_get ?tt ?i < _ =>
      first [ pose proof (length_code_bound i) | pose proof (dist_code_bound i)
            | pose proof (extra_lbits_bound i) | pose proof (base_length_bound i)
            | pose proof (extra_dbits_bound i) | pose proof (base_dist_bound i) ];
      lazymatch goal with H : 0 <= arr_get tt i < _ |- _ => lia end
  end.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec.FPState}.


End FXG.
Ltac cb_read :=
  lazymatch goal with
  | |- exists bs, rdn ?sg ?m (zw ?a) ?n = Some bs /\ bytes_le_to_Z bs = ?v =>
      lazymatch v with
      | pb ?tt ?i =>
          match goal with H : cells sg m ?P 4 2%nat ?len (arr_get tt) |- _ =>
            eapply (pb_read4m sg m P len tt i a H); [lia | lia] end
      | wb ?d ?i =>
          match goal with H : cells sg m ?P 1 1%nat ?len (arr_get d) |- _ =>
            eapply (wb_read1m sg m P len d i a H); [lia | lia] end
      | arr_get length_code_a ?i =>
          match goal with H : cells sg m ?P 1 1%nat _ (arr_get length_code_a) |- _ =>
            eapply (bytes_read_at sg m P _ (arr_get length_code_a) i a _ H); [lia | tab_bound | lia | reflexivity] end
      | arr_get dist_code_a ?i =>
          match goal with H : cells sg m ?P 1 1%nat _ (arr_get dist_code_a) |- _ =>
            eapply (bytes_read_at sg m P _ (arr_get dist_code_a) i a _ H); [lia | tab_bound | lia | reflexivity] end
      | arr_get ?tt ?i =>
          match goal with H : cells sg m ?P 4 4%nat _ (arr_get tt) |- _ =>
            eapply (u32_read_at sg m P _ (arr_get tt) i a _ H); [lia | tab_bound | lia | reflexivity] end
      end
  end.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec.FPState}.



Record CBH (F : franges) (mem0 mem : word -> option byte) (S : Z) (p : ds_ptrs) (PBL : Z)
       (ds : deflate_state) (ra : word) (sp : Z) (LT DT : Z) (lfc ldl dfc ddl : arr) : Prop := {
  cbh_ret : ret_ok ra;
  cbh_L : BRH F S p PBL;
  cbh_fr : call_frame F mem S (p_pending_buf p) PBL sp 48;
  cbh_br : BR6 F mem0 S p PBL mem ds;
  cbh_rod : trees_rod_clear6 mem;
  cbh_ok : compress_block_ok PBL ds lfc ldl dfc ddl;
  cbh_T : forall m s', BR6 F mem0 S p PBL m s' ->
    (forall t, tree_fc s' t = tree_fc ds t) -> (forall t, tree_dl s' t = tree_dl ds t) -> trees_rod_clear6 m ->
    cells s6_segs m LT 4 2 286 (arr_get lfc) /\ cells s6_segs m (LT + 2) 4 2 286 (arr_get ldl)
    /\ cells s6_segs m DT 4 2 30 (arr_get dfc) /\ cells s6_segs m (DT + 2) 4 2 30 (arr_get ddl);
  cbh_LT : 0 <= LT /\ LT + 1144 <= 2 ^ 63;
  cbh_DT : 0 <= DT /\ DT + 120 <= 2 ^ 63;
  cbh_sn : 0 <= ds_sym_next ds /\ ds_sym_next ds + 3 < 2 ^ 31;
  cbh_LB : 0 <= ds_lit_bufsize ds < 2 ^ 32;
  cbh_PBL : 0 < PBL }.

Section Walk.
Variables (F : franges) (mem0 mem : word -> option byte).
Variables (S : Z) (p : ds_ptrs) (PBL : Z) (ds : deflate_state) (ra : word) (sp : Z).
Variables (LT DT : Z) (lfc ldl dfc ddl : arr).
Local Abbreviation PB := (p_pending_buf p).
Local Abbreviation LB := (ds_lit_bufsize ds).
Local Abbreviation sn := (ds_sym_next ds).
Local Abbreviation SP := (sp - 48).
Local Abbreviation BRm := (BR6 F mem0 S p PBL).

Hypothesis HH : CBH F mem0 mem S p PBL ds ra sp LT DT lfc ldl dfc ddl.

Let Hret : ret_ok ra := cbh_ret _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HH.
Let HLb : BRH F S p PBL := cbh_L _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HH.
Let Hcf : call_frame F mem S PB PBL sp 48 := cbh_fr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HH.
Let HBR0 : BRm mem ds := cbh_br _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HH.
Let HRC0 : trees_rod_clear6 mem := cbh_rod _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HH.
Let Hok : compress_block_ok PBL ds lfc ldl dfc ddl := cbh_ok _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HH.
Let HT := cbh_T _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HH.
Let HLT : 0 <= LT /\ LT + 1144 <= 2 ^ 63 := cbh_LT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HH.
Let HDT : 0 <= DT /\ DT + 120 <= 2 ^ 63 := cbh_DT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HH.
Let Hsn : 0 <= sn /\ sn + 3 < 2 ^ 31 := cbh_sn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HH.
Let HLBr : 0 <= LB < 2 ^ 32 := cbh_LB _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HH.
Let HPBL : 0 < PBL := cbh_PBL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HH.
Let Hsp : 48 <= sp <= 2 ^ 63 := proj1 Hcf.


Definition PURE (s : deflate_state) : Prop :=
  PBB s /\ BINV PBL s
  /\ (forall t, tree_fc s t = tree_fc ds t) /\ (forall t, tree_dl s t = tree_dl ds t)
  /\ ds_lit_bufsize s = LB /\ ds_sym_next s = sn /\ arr_len (ds_pending_buf s) = PBL.

Definition GI : franges := [(S, 5968); (PB, PBL)].

Definition CI (m0 m : word -> option byte) (s : deflate_state) : Prop :=
  BRm m s /\ trees_rod_clear6 m /\ PURE s /\ agree_out GI m0 m.

Lemma PURE_send : forall s v l, PURE s -> 0 <= l <= 16 -> sb_room PBL s l -> PURE (send_bits s v l).
Proof.
  intros s v l (P1 & P2 & P3 & P4 & P5 & P6 & P7) Hl Hr. unfold PURE.
  split.
  { unfold PBB in *. unfold send_bits, put_short, put_byte. destruct (Buf_size - l <? ds_bi_valid s); dsred; [|exact P1].
    rewrite !arr_len_set. intros i Hi. rewrite !arr_get_set.
    destruct (_ && _); [apply wrap8_range|]. destruct (_ && _); [apply wrap8_range|]. apply P1. exact Hi. }
  split; [apply send_bits_BINV; assumption|].
  split; [intros t; rewrite sb_tree_fc; apply P3|]. split; [intros t; rewrite sb_tree_dl; apply P4|].
  pose proof (sb_pbl s v l) as E. rewrite send_bits_shape in E |- *. cbn [upd4] in E |- *. dsred. rewrite E. tauto.
Qed.

Definition KREGS (R : bvmap 5 word) : Prop :=
  getr R 10 = zw S /\ getr R 13 = zw (S + 5888) /\ getr R 11 = zw LT /\ getr R 12 = zw DT
  /\ getr R 15 = zw 16 /\ getr R 5 = zw 65535 /\ getr R 6 = zw 0x11ce0 /\ getr R 16 = zw (2 ^ 64 - 20)
  /\ getr R 17 = zw 257 /\ getr R 7 = zw 4 /\ getr R 2 = zw SP.
Definition KP : list (Z * expr) :=
  [(10, EVar 32); (13, EAdd (EVar 32) (ELit 5888)); (11, EVar 37); (12, EVar 38);
   (15, ELit 16); (5, ELit 65535); (6, ELit 0x11ce0); (16, ELit (2 ^ 64 - 20)); (17, ELit 257); (7, ELit 4);
   (2, EVar 44)].

Definition RBr (r : reg) (R : bvmap 5 word) (s : deflate_state) : Prop :=
  (bv_unsigned (getr R r)) mod 2 ^ 16 = ds_bi_buf s.

Definition CLOB : list reg := [5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31]%bv.
Definition CLOBI : list reg := [5; 6; 7; 8; 9; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 28; 29; 30; 31]%bv.


Definition cbF (A : arr) (f : nat) (x : Z) : Z :=
  match f with
  | 0%nat => wb A x
  | 1%nat => pb lfc x | 2%nat => pb ldl x | 3%nat => pb dfc x | 4%nat => pb ddl x
  | 5%nat => arr_get length_code_a x | 6%nat => arr_get dist_code_a x
  | 7%nat => arr_get extra_lbits_a x | 8%nat => arr_get base_length_a x
  | 9%nat => arr_get extra_dbits_a x | _ => arr_get base_dist_a x
  end.

Definition FBc : list (nat * Z) :=
  [(0%nat, 256); (1%nat, 65536); (2%nat, 65536); (3%nat, 65536); (4%nat, 65536);
   (5%nat, 29); (6%nat, 30); (7%nat, 6); (8%nat, 259); (9%nat, 14); (10%nat, 24577)].

Definition cbC : cfg :=
  CFG FBc [] [EVar 1%nat]
      [0x1c314; 0x1c35c; 0x1c3ec; 0x1c478; 0x1c514; 0x1c528; 0x1c5c0; 0x1c308; 0x1c660] [].

Definition VB : bounds :=
  [(32%nat, 2 ^ 63); (33%nat, 2 ^ 63); (34%nat, 2 ^ 63); (35%nat, 2 ^ 32); (36%nat, 17);
   (37%nat, 2 ^ 63); (38%nat, 2 ^ 63); (39%nat, 256); (40%nat, 32768); (41%nat, 2 ^ 31 - 3);
   (42%nat, 2 ^ 31); (43%nat, 30); (44%nat, 2 ^ 63); (45%nat, 2 ^ 64); (46%nat, 512); (47%nat, 65536);
   (48%nat, 2 ^ 64); (49%nat, 2 ^ 64); (50%nat, 2 ^ 64); (51%nat, 2 ^ 64); (52%nat, 2 ^ 64); (53%nat, 2 ^ 64)].



Local Ltac fr_weak Hfr :=
  let r := fresh "r" in let Hr := fresh "Hr" in
  intros r Hr; apply Hfr; eapply reg_in_sub; [| exact Hr]; reflexivity.

Local Ltac nf := cbn [cbF].

Local Ltac side_closer :=
  try solve [ assumption
            | nf; first [ assumption | lia
                        | repeat (rewrite (szwrap_small 32) by lia); repeat (rewrite (szwrap_small 64) by lia); lia ]
            | match goal with H : getr ?rs ?r = zw _ |- getr ?rs ?r = zw _ =>
                rewrite H; first [ f_equal; nf; lia
                                 | lazymatch goal with |- zw ?a = zw ?b =>
                                     lazymatch isZcst a with true => lazymatch isZcst b with true =>
                                       apply bv_eq; vm_compute; reflexivity end end end ] end
            | nf; cb_read
            | nf; symex_read_auto
            | nf; symex_store_auto
            | nf; symex_sok_auto
            | intros; nf; tab_range ].

Local Ltac run fuel dirs rds pins pv A :=
  let R := fresh "R" in let HR := fresh "HR" in let Hfr := fresh "Hfr" in let Hms := fresh "Hms" in
  let pinsv := eval vm_compute in pins in
  let vbv := eval vm_compute in VB in
  let rdv := eval vm_compute in rds in
  lazymatch goal with |- context [mkst ?regs ?pc ?m s6_rom] =>
    symex s6_segs cbC fuel dirs rdv pinsv vbv NoRegions pv NoVals (cbF A) F0' (mkst regs pc m s6_rom) R HR Hfr Hms
  end;
  match goal with
  | _ : regs_ok _ _ _ |- _ => idtac
  | |- _ => side_closer
  end.
Local Ltac run_dbg fuel dirs rds pins pv :=
  let pinsv := eval vm_compute in pins in
  let vbv := eval vm_compute in VB in
  let rdv := eval vm_compute in rds in
  lazymatch goal with |- context [mkst ?regs ?pc ?m s6_rom] =>
    symex_dbg s6_segs cbC fuel dirs rdv pinsv vbv NoRegions pv (mkst regs pc m s6_rom)
  end.

Local Ltac open_br HB HRC HP :=
  let P1 := fresh "Ppb" in let P2 := fresh "Pbinv" in let P3 := fresh "Pfc" in let P4 := fresh "Pdl" in
  let P5 := fresh "PLB" in let P6 := fresh "Psn" in let P7 := fresh "Plen" in
  pose proof HP as HP'; destruct HP' as (P1 & P2 & P3 & P4 & P5 & P6 & P7); unfold PBB in P1;
  let Hbv := fresh "Hbv" in let Hbb := fresh "Hbb" in let Hpd := fresh "Hpd" in
  pose proof P2 as HBI'; destruct HBI' as (Hbv & Hbb & Hpd);
  let HS' := fresh "HS'" in let HPB' := fresh "HPB'" in let HD := fresh "HD" in
  pose proof HLb as HL'; destruct HL' as (HS' & HPB' & HD & _); unfold dsl_SIZE in HS', HD;
  let MS := fresh "MS" in let MP := fresh "MP" in let Hsc := fresh "Hsc" in
  destruct (BR_out _ _ _ _ _ _ _ _ _ _ _ HB) as (Hsc & _ & _ & _ & _ & MS & MP & _); unfold mapped, dsl_SIZE in MS, MP;
  let Csn := fresh "Csn" in let Csb := fresh "Csb" in
  pose proof (dsl_sym_next _ _ _ _ _ _ _ _ Hsc) as Csn; pose proof (dsl_sym_buf _ _ _ _ _ _ _ _ Hsc) as Csb;
  dsred in Csn; dsred in Csb; try rewrite P6 in Csn; try rewrite P5 in Csb; clear Hsc;
  let C40 := fresh "C40" in let C16 := fresh "C16" in let C5936 := fresh "C5936" in let C5940 := fresh "C5940" in
  let Cpb := fresh "Cpb" in
  destruct (BR_cells _ _ _ _ _ _ _ _ _ _ _ HB) as (C40 & C16 & C5936 & C5940 & Cpb); dsred in C40; dsred in C5936; dsred in C5940; dsred in Cpb;
  let TL1 := fresh "TL1" in let TL2 := fresh "TL2" in let TD1 := fresh "TD1" in let TD2 := fresh "TD2" in
  destruct (HT _ _ HB P3 P4 HRC) as (TL1 & TL2 & TD1 & TD2);
  let Hsp' := fresh "Hsp'" in pose proof Hsp as Hsp';
  let HLT' := fresh "HLT'" in pose proof HLT as HLT';
  let HDT' := fresh "HDT'" in pose proof HDT as HDT';
  let RODS := fresh "RODS" in let RODP := fresh "RODP" in
  pose proof (proj1 (mapped_rod_apart R6 _ _ S 5968 trod_ok6 HRC MS ltac:(lia) ltac:(lia))) as RODS;
  pose proof (proj1 (mapped_rod_apart R6 _ _ (p_pending_buf p) PBL trod_ok6 HRC MP ltac:(lia) ltac:(lia))) as RODP;
  cbn [tr_lo tr_hi R6] in RODS, RODP;
  let Tlc := fresh "Tlc" in let Tdc := fresh "Tdc" in let Txl := fresh "Txl" in let Tbl := fresh "Tbl" in
  let Txd := fresh "Txd" in let Tbd := fresh "Tbd" in
  pose proof (length_code_cells R6 _ _ trod_ok6 HRC) as Tlc; pose proof (dist_code_cells R6 _ _ trod_ok6 HRC) as Tdc;
  pose proof (extra_lbits_cells R6 _ _ trod_ok6 HRC) as Txl; pose proof (base_length_cells R6 _ _ trod_ok6 HRC) as Tbl;
  pose proof (extra_dbits_cells R6 _ _ trod_ok6 HRC) as Txd; pose proof (base_dist_cells R6 _ _ trod_ok6 HRC) as Tbd;
  cbn [tr_length_code tr_dist_code tr_extra_lbits tr_base_length tr_extra_dbits tr_base_dist R6] in Tlc, Tdc, Txl, Tbl, Txd, Tbd.

Local Ltac wr_tower MS MP :=
  repeat (apply wr_ok_wbytes;
          [ | let x := fresh "x" in let Hx := fresh "Hx" in
              intros x Hx; rewrite ?length_Z_to_le_bytes in Hx; cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hx;
              first [ apply MS; lia | apply MP; lia ]
            | lia | rewrite ?length_Z_to_le_bytes; cbn; lia ]);
  apply wr_ok_refl.

Local Ltac ag_tower HAG :=
  repeat (apply agree_out_wbytes;
          [ | lia | rewrite ?length_Z_to_le_bytes; cbn; lia
            | rewrite ?length_Z_to_le_bytes; unfold GI;
              first [ apply sub_franges_here; cbn; lia | apply sub_franges_later; apply sub_franges_here; cbn; lia ] ]);
  exact HAG.

Local Ltac kregs HR Hfr :=
  unfold KREGS; repeat split;
  lazymatch goal with |- getr ?R ?r = _ =>
    first [ rewrite (Hfr r eq_refl); assumption
          | let A := fresh "A" in symex_reg HR r as A; rewrite A;
            first [ reflexivity | f_equal; lia
                  | lazymatch goal with |- zw ?a = zw ?b =>
                      lazymatch isZcst a with true => lazymatch isZcst b with true =>
                        apply bv_eq; vm_compute; reflexivity end end end ] ]
  end.

Local Ltac reg1 HR Hfr :=
  first [ fr_weak Hfr
        | lazymatch goal with |- getr ?R ?r = _ => rewrite (Hfr r eq_refl); assumption end
        | let A := fresh "A" in lazymatch goal with |- getr ?R ?r = _ => symex_reg HR r as A; rewrite A; nf;
            first [reflexivity | f_equal; lia | f_equal; f_equal; lia | f_equal; repeat (rewrite (szwrap_small 32) by lia); lia
                  | rewrite zw_u; assumption ] end
        | idtac ].
Local Ltac regs_of HR Hfr := repeat split; reg1 HR Hfr.

Local Ltac vcongr := first [ reflexivity | apply pb_mod16 | apply szwrap32_mod16 | rewrite szwrap32_mod16; reflexivity
                           | rewrite Z.mod_mod by lia; reflexivity
                           | rewrite szwrap32_mod16, wrap32_mod, mod_pow2_mod_pow2 by lia; reflexivity ].
Local Ltac vwrap := first [ reflexivity | apply pb_wrap16 | symmetry; apply wrap16_id; lia
                          | rewrite wrap16_mod'; reflexivity | rewrite wrap16_mod', szwrap32_mod16; reflexivity
                          | rewrite wrap16_mod', wrap32_mod, mod_pow2_mod_pow2 by lia; reflexivity ].
Local Ltac vrange := first [ apply pb_range | lia | apply Z.mod_pos_bound; lia ].
Local Ltac rbm := first [ assumption | apply szwrap16_mod; assumption | apply szwrap16_mod; lia ].

Local Ltac st_flush vnorm :=
  rewrite send_bits_flush_eq by (unfold Buf_size; lia); st_eq;
  [ vnorm; f_equal;
    [ f_equal; [lia | apply byte0_eq; unfold sb_nb; eapply nb_eqm2; [lia | rbm | vnorm; vcongr]]
    | lia
    | apply byte1_eq2; unfold sb_nb; eapply nb_eqm2; [lia | rbm | vnorm; vcongr] ]
  | lia
  | first [reflexivity | vnorm; apply srl_eq'; [vrange | vwrap | lia]]
  | first [reflexivity | vnorm; repeat (rewrite (szwrap_small 32) by lia); unfold Buf_size; lia] ].
Local Ltac rb_flush r HR vnorm :=
  unfold RBr; let A := fresh "A" in symex_reg HR r as A; rewrite A, u_zw, mod_pow2_mod_pow2 by lia;
  rewrite send_bits_flush_eq by (unfold Buf_size; lia); rewrite upd4_bi_buf;
  vnorm; apply srl_eq'; [vrange | vwrap | lia].
Local Ltac bv_flush r HR vnorm :=
  let A := fresh "A" in symex_reg HR r as A; rewrite A; f_equal;
  rewrite send_bits_flush_eq by (unfold Buf_size; lia); rewrite upd4_bi_valid;
  vnorm; repeat (rewrite (szwrap_small 32) by lia); unfold Buf_size; lia.
Local Ltac st_keep vnorm :=
  rewrite send_bits_keep_eq by (unfold Buf_size; lia); st_eq;
  [ reflexivity
  | reflexivity
  | first [reflexivity | vnorm; unfold sb_nb; eapply nb_eqm2; [lia | rbm | vnorm; vcongr]]
  | first [reflexivity | vnorm; repeat (rewrite (szwrap_small 32) by lia); lia] ].
Local Ltac rb_keep r HR vnorm :=
  unfold RBr; let A := fresh "A" in symex_reg HR r as A; rewrite A, u_zw, mod_pow2_mod_pow2 by lia;
  rewrite send_bits_keep_eq by (unfold Buf_size; lia); rewrite upd4_bi_buf;
  vnorm; unfold sb_nb; eapply nb_eqm2; [lia | rbm | vnorm; vcongr].
Local Ltac bv_keep r HR vnorm :=
  let A := fresh "A" in symex_reg HR r as A; rewrite A; f_equal;
  rewrite send_bits_keep_eq by (unfold Buf_size; lia); rewrite upd4_bi_valid;
  vnorm; repeat (rewrite (szwrap_small 32) by lia); lia.
Local Ltac pure_fin HP := first [exact HP | apply PURE_send; [exact HP | lia | unfold sb_room, Buf_size; intros; lia]].

Local Ltac site_fin Hms HR Hfr HB HRC HP HAG MS MP tst tregs :=
  lazymatch type of Hms with
  | msteps _ _ (mkst ?R _ ?M _) =>
      br_fwd HB M;
      lazymatch goal with
      | HB2 : BR _ _ _ _ _ _ _ _ _ M ?s1 |- _ =>
          exists R, M; split; [exact Hms|]; clear Hms;
          split; [ split; [eapply BR_eqst; [exact HB2|]; clear HB2; tst
                        | split; [ apply (trees_rod_clear_wr R6 _ _ HRC); wr_tower MS MP
                                 | split; [pure_fin HP | ag_tower HAG] ] ]
                 | tregs ]
      end
  end.


Lemma lit_site : forall regs m0 m s sx lc,
  CI m0 m s -> 0 <= lc < 256 -> 0 <= sx /\ sx + 3 < 2 ^ 31 ->
  sb_room PBL s (arr_get ldl lc) -> 0 <= arr_get ldl lc <= 15 ->
  KREGS regs -> getr regs 14 = zw sx -> getr regs 31 = zw lc ->
  let s2 := send_bits s (arr_get lfc lc) (arr_get ldl lc) in
  exists R m',
    msteps s6_segs (mkst regs (0x1c3ec : word) m s6_rom) (mkst R (0x1c308 : word) m' s6_rom)
    /\ CI m0 m' s2
    /\ (KREGS R /\ getr R 14 = zw sx /\ getr R 28 = zw (ds_bi_valid s2)
        /\ (forall r : reg, reg_in r CLOBI = false -> getr R r = getr regs r)).
Proof.
  intros regs m0 m s sx lc (HB & HRC & HP & HAG) Hlc Hsx Hroom Vdl HK P14 P31. cbv zeta.
  open_br HB HRC HP.
  destruct HK as (P10 & P13 & P11 & P12 & P15 & P5 & P6 & P16 & P17 & P7 & P2).
  assert (Edl : pb ldl lc = arr_get ldl lc) by (apply pb_small; lia).
  unfold sb_room, Buf_size in Hroom.
  destruct (Z.ltb_spec (16 - arr_get ldl lc) (ds_bi_valid s)) as [CF|CF];
    [specialize (Hroom ltac:(unfold Buf_size; lia))|].
  - run 80%nat [false]
        [RVal (EApp1 1 (EVar 39)); RVal (EApp1 2 (EVar 39)); RVal (EVar 36); RVal (EVar 47); RVal (EVar 34); RVal (EVar 33)]
        (KP ++ [(14, EVar 41); (31, EVar 39)])
        [S; PB; ds_pending s; LB; ds_bi_valid s; LT; DT; lc; 0; sx; sn; 0; SP; 0; 0; ds_bi_buf s] (ds_pending_buf s).
    site_fin Hms HR Hfr HB HRC HP HAG MS MP ltac:(st_flush nf)
      ltac:(split; [kregs HR Hfr|]; split; [reg1 HR Hfr|]; split; [bv_flush (28%bv : reg) HR nf | fr_weak Hfr]).
  - run 80%nat [true]
        [RVal (EApp1 1 (EVar 39)); RVal (EApp1 2 (EVar 39)); RVal (EVar 36); RVal (EVar 47)]
        (KP ++ [(14, EVar 41); (31, EVar 39)])
        [S; PB; ds_pending s; LB; ds_bi_valid s; LT; DT; lc; 0; sx; sn; 0; SP; 0; 0; ds_bi_buf s] (ds_pending_buf s).
    site_fin Hms HR Hfr HB HRC HP HAG MS MP ltac:(st_keep nf)
      ltac:(split; [kregs HR Hfr|]; split; [reg1 HR Hfr|]; split; [bv_keep (28%bv : reg) HR nf | fr_weak Hfr]).
Qed.



Lemma lt_blk : forall regs m0 m s sx,
  CI m0 m s -> 0 <= sx /\ sx + 3 < 2 ^ 31 ->
  KREGS regs -> getr regs 14 = zw sx -> getr regs 28 = zw (ds_bi_valid s) ->
  exists R,
    msteps s6_segs (mkst regs (0x1c308 : word) m s6_rom)
           (mkst R (if sx + 3 <? sn then (0x1c314 : word) else (0x1c660 : word)) m s6_rom)
    /\ KREGS R /\ getr R 14 = zw (sx + 3) /\ getr R 28 = zw (ds_bi_valid s)
    /\ (forall r : reg, reg_in r CLOBI = false -> getr R r = getr regs r).
Proof.
  intros regs m0 m s sx (HB & HRC & HP & HAG) Hsx HK P14 P28.
  open_br HB HRC HP.
  destruct HK as (P10 & P13 & P11 & P12 & P15 & P5 & P6 & P16 & P17 & P7 & P2).
  pose proof Hsn as Hsn'.
  destruct (Z.ltb_spec (sx + 3) sn) as [CL|CL].
  - run 20%nat [false] [RVal (EVar 42)] (KP ++ [(14, EVar 41); (28, EVar 36)])
        [S; PB; ds_pending s; LB; ds_bi_valid s; LT; DT; 0; 0; sx; sn; 0; SP; 0; 0; 0] (ds_pending_buf s).
    exists R. split; [exact Hms|]. split; [kregs HR Hfr|]. regs_of HR Hfr.
  - run 20%nat [true] [RVal (EVar 42)] (KP ++ [(14, EVar 41); (28, EVar 36)])
        [S; PB; ds_pending s; LB; ds_bi_valid s; LT; DT; 0; 0; sx; sn; 0; SP; 0; 0; 0] (ds_pending_buf s).
    exists R. split; [exact Hms|]. split; [kregs HR Hfr|]. regs_of HR Hfr.
Qed.


Lemma head_blk : forall regs m0 m s sx,
  CI m0 m s -> 0 <= sx -> LB + sx + 1 + 1 + 1 <= PBL -> sx + 3 < 2 ^ 31 ->
  KREGS regs -> getr regs 14 = zw sx ->
  let dist := sym_dist s sx in
  exists R,
    msteps s6_segs (mkst regs (0x1c314 : word) m s6_rom)
           (mkst R (if dist =? 0 then (0x1c3ec : word) else (0x1c35c : word)) m s6_rom)
    /\ KREGS R /\ getr R 14 = zw sx
    /\ getr R 31 = zw (sym_lc s sx) /\ getr R 28 = zw dist
    /\ (forall r : reg, reg_in r CLOBI = false -> getr R r = getr regs r).
Proof.
  intros regs m0 m s sx (HB & HRC & HP & HAG) Hsx Hroom Hsx3 HK P14. cbv zeta.
  open_br HB HRC HP.
  destruct HK as (P10 & P13 & P11 & P12 & P15 & P5 & P6 & P16 & P17 & P7 & P2).
  rewrite sym_dist_eq, PLB. rewrite sym_lc_eq by (first [exact Ppb | rewrite ?Plen, ?PLB; lia]). rewrite PLB.
  pose proof (wb_range (ds_pending_buf s) (LB + sx)) as W0.
  pose proof (wb_range (ds_pending_buf s) (LB + sx + 1)) as W1.
  destruct (Z.eqb_spec (wb (ds_pending_buf s) (LB + sx) + wb (ds_pending_buf s) (LB + sx + 1) * 2 ^ 8) 0) as [CD|CD].
  - run 40%nat [true]
        [RVal (EAdd (EVar 33) (EVar 35)); RVal (EApp1 0 (EAdd (EVar 35) (EVar 41)));
         RVal (EApp1 0 (EAdd (EAdd (EVar 35) (EVar 41)) (ELit 1))); RVal (EApp1 0 (EAdd (EAdd (EVar 35) (EVar 41)) (ELit 2)))]
        (KP ++ [(14, EVar 41)])
        [S; PB; ds_pending s; LB; ds_bi_valid s; LT; DT; 0; 0; sx; sn; 0; SP; 0; 0; 0] (ds_pending_buf s).
    all: try (nf; rewrite lor_shl8 by (first [apply wb_range | lia]); lia).
    exists R. split; [exact Hms|]. split; [kregs HR Hfr|].
    regs_of HR Hfr.
    let A := fresh "A" in symex_reg HR (28%bv : reg) as A; rewrite A; nf.
    rewrite lor_shl8 by (first [apply wb_range | lia]). reflexivity.
  - run 40%nat [false]
        [RVal (EAdd (EVar 33) (EVar 35)); RVal (EApp1 0 (EAdd (EVar 35) (EVar 41)));
         RVal (EApp1 0 (EAdd (EAdd (EVar 35) (EVar 41)) (ELit 1))); RVal (EApp1 0 (EAdd (EAdd (EVar 35) (EVar 41)) (ELit 2)))]
        (KP ++ [(14, EVar 41)])
        [S; PB; ds_pending s; LB; ds_bi_valid s; LT; DT; 0; 0; sx; sn; 0; SP; 0; 0; 0] (ds_pending_buf s).
    all: try (nf; rewrite lor_shl8 by (first [apply wb_range | lia]); lia).
    exists R. split; [exact Hms|]. split; [kregs HR Hfr|].
    regs_of HR Hfr.
    let A := fresh "A" in symex_reg HR (28%bv : reg) as A; rewrite A; nf.
    rewrite lor_shl8 by (first [apply wb_range | lia]). reflexivity.
Qed.

End Walk.
End FXG.
