(** [S_ENTRY] of reac_headamp_prop_parse_result (plain image, 0x1487c) from [S_WALK] and [S_EPI]
    (Prog/Seg/ParseCut.v): the code 0x1487c-0x14a24 and its exits.
      - the prologue (0x1487c-0x148c0): the 160-byte frame carved from the stack, the thirteen saves and fs0's;
        s0 = res, s2 = max, s3 = out;
      - res <> 0: res->n = res->keys = res->refusal = 0 (0x148c8-0x148d0);
      - props = NULL (0x148d8): -1 through the epilogue [S_EPI];
      - spa_pod_is_object_type (0x148dc-0x14908): -1 through [S_EPI];
      - the find setup and spa_pod_object_find_prop's loop (0x1490c-0x14970, an induction on its fuel): no params prop
        returns 0 through [S_EPI];
      - spa_pod_is_struct (0x14974-0x14990): not a Struct returns 0 through [S_EPI];
      - the walk setup (0x149fc-0x14a24), then [S_WALK] at the Struct's first child.
    The helpers on the pod words, the branch tests and the find loop are fuzz_role's
    (Prog/reac_role_prop_parse.v: pa_*, find_loop, pa_found, pa_entry) with headamp's registers. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Sem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Lib Require Import PropExec MState Mem Exec Frame Tac Cells Step Image FP.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Import Cursor Model Accessors Spa SpaBool Headamp.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Spec Require Import HeadBytes.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Prog Require Import reac_headamp_prop_parse_result_c ParseSites.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Prog.Seg Require Import ParseCut.
Import ListNotations.
Open Scope Z_scope.

(** * The model at the exits of the entry *)
Lemma pn_find_prop_step : forall bs size key res n,
  find_prop bs size key res (S n) =
  if prop_is_inside bs 8 size res then
    if u32_at bs res =? key then Some res
    else find_prop bs size key (res + round_up8 (16 + u32_at bs (res + 8))) n
  else None.
Proof. reflexivity. Qed.

Lemma pn_model_not_props : forall bs cap, is_object_type bs POD_OBJECT_PROPS = false ->
  parse_model bs cap = (-1, [], (0, 0, REFUSE_NONE)).
Proof. intros bs cap H. unfold parse_model, spa_view_of. rewrite H. reflexivity. Qed.

Lemma pn_model_no_params : forall bs cap, is_object_type bs POD_OBJECT_PROPS = true ->
  find_prop bs (u32_at bs 0) POD_PROP_PARAMS 16 (length bs) = None -> parse_model bs cap = (0, [], (0, 0, REFUSE_NONE)).
Proof. intros bs cap H E. unfold parse_model, spa_view_of. rewrite H, E. reflexivity. Qed.

(** The VPods arm: the fold over [walk_pairs] from the Struct's first child, the key slot open. *)
Lemma pn_model_found : forall bs cap r, is_object_type bs POD_OBJECT_PROPS = true ->
  find_prop bs (u32_at bs 0) POD_PROP_PARAMS 16 (length bs) = Some r ->
  parse_model bs cap =
  if is_struct_at bs (r + 8)
  then ha_result (ha_fold parse_cell cap (walk_pairs bs r (r + 16) (length bs) None) [] 0 REFUSE_NONE)
  else (0, [], (0, 0, REFUSE_NONE)).
Proof.
  intros bs cap r H E. unfold parse_model, spa_view_of. rewrite H, E.
  destruct (is_struct_at bs (r + 8)); reflexivity.
Qed.

(** * The words of the pod and the branch tests (fuzz_role's pa_ helpers) *)
Lemma pn_le_roundtrip : forall l : list byte, Z_to_le_bytes (length l) (bytes_le_to_Z l) = l.
Proof.
  induction l as [|b l IH]; [reflexivity|]. cbn [length Z_to_le_bytes bytes_le_to_Z].
  pose proof (byte_range b) as Hb. pose proof (le_bytes_nonneg l) as Hl.
  rewrite (lor_low_shiftl (bv_unsigned b) (bytes_le_to_Z l) Hb Hl). f_equal.
  - apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap.
    replace (bv_modulus 8) with 256 by reflexivity.
    rewrite Z_mod_plus_full. apply Z.mod_small. exact Hb.
  - replace (Z.shiftr (bv_unsigned b + bytes_le_to_Z l * 256) 8) with (bytes_le_to_Z l); [exact IH|].
    rewrite Z.shiftr_div_pow2 by lia. replace (2 ^ 8) with 256 by reflexivity.
    rewrite Z_div_plus_full by lia. rewrite Z.div_small by lia. lia.
Qed.

Lemma pn_u32 : forall bs o, 0 <= u32_at bs o < 2^32.
Proof. intros bs o. exact (rd32_range _). Qed.

Lemma pn_hm32 : bv_half_modulus 32 = 2^31.
Proof. reflexivity. Qed.

Lemma pn_sx32 : forall v, 0 <= v < 2^31 -> sx32 (Z_to_bv 64 v) = Z_to_bv 64 v.
Proof.
  intros v Hv. unfold sx32. rewrite unsigned_lit by lia. rewrite bv_swrap_small; [reflexivity|].
  rewrite pn_hm32. lia.
Qed.

Lemma pn_wsx : forall v, 0 <= v < 2^32 -> bv_wrap 32 (bv_unsigned (sx32 (Z_to_bv 64 v))) = v.
Proof.
  intros v Hv. unfold sx32. rewrite Z_to_bv_unsigned, unsigned_lit by lia.
  unfold bv_swrap, bv_wrap. rewrite pn_hm32.
  replace (bv_modulus 32) with (2^32) by reflexivity. replace (bv_modulus 64) with (2^64) by reflexivity.
  Z.div_mod_to_equations. lia.
Qed.

Lemma pn_srliw_sx : forall v, 0 <= v < 2^32 ->
  bv_swrap 32 (Z.shiftr (bv_wrap 32 (bv_unsigned (sx32 (Z_to_bv 64 v)))) 20) = v / 1048576.
Proof.
  intros v Hv. rewrite (pn_wsx v Hv). rewrite Z.shiftr_div_pow2 by lia. replace (2 ^ 20) with 1048576 by reflexivity.
  assert (0 <= v / 1048576 < 4096) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
  apply bv_swrap_small. rewrite pn_hm32. lia.
Qed.

Lemma pn_eqb_sx : forall v k, 0 <= v < 2^32 -> 0 <= k < 2^31 ->
  bv_eqb (sx32 (Z_to_bv 64 v)) (Z_to_bv 64 k) = (v =? k).
Proof.
  intros v k Hv Hk. unfold bv_eqb, sx32. rewrite !Z_to_bv_unsigned.
  unfold bv_swrap, bv_wrap. rewrite pn_hm32.
  replace (bv_modulus 32) with (2^32) by reflexivity. replace (bv_modulus 64) with (2^64) by reflexivity.
  rewrite (Z.mod_small v (2^64)), (Z.mod_small k (2^64)) by lia.
  apply eq_true_iff_eq. rewrite !Z.eqb_eq. split; intros E; Z.div_mod_to_equations; lia.
Qed.

Lemma pn_zx32 : forall z, 0 <= z < 2^32 -> zx32 (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof. intros z H. unfold zx32. rewrite unsigned_lit by lia. rewrite Z.mod_small by lia. reflexivity. Qed.

Lemma pn_land3 : forall x, Z.land x 3 = x mod 4.
Proof. intros x. change 3 with (Z.ones 2). rewrite Z.land_ones by lia. reflexivity. Qed.

Lemma pn_shr20 : forall v, Z.shiftr v 20 = v / 1048576.
Proof. intros v. rewrite Z.shiftr_div_pow2 by lia. reflexivity. Qed.

(** SPA_ROUND_UP_N(16 + v, 8) as the code computes it ((v + 15) | 7, then + 1). *)
Lemma pn_ru : forall v, Z.lor (v + 15) 7 = round_up8 (16 + v) - 1.
Proof. intros v. unfold round_up8. replace (16 + v - 1) with (v + 15) by lia. lia. Qed.

Lemma pn_ru_facts : forall v, 0 <= v -> 16 + v <= round_up8 (16 + v) <= 23 + v /\ round_up8 (16 + v) mod 8 = 0.
Proof.
  intros v Hv. rewrite round_up8_eq by lia. pose proof (pad8_bound (16 + v)). pose proof (pad8_eq (16 + v)) as E.
  split; [lia|]. rewrite E, Z.mul_comm. apply Z.mod_mul. lia.
Qed.

Lemma pn_obj_eq : forall bs, is_object_type bs POD_OBJECT_PROPS =
  (u32_at bs 0 <? 1048576) && (u32_at bs 4 =? 15) && (8 <=? u32_at bs 0) && (u32_at bs 8 =? 262146).
Proof. reflexivity. Qed.

Lemma pn_pin : forall bs size r, r mod 4 = 0 -> 8 <= r ->
  prop_is_inside bs 8 size r = (16 <=? size) && (r - 8 <=? size - 16) && (u32_at bs (r + 8) <=? 8 + size - (r + 16)).
Proof.
  intros bs size r H4 H8. unfold prop_is_inside, ptr_type_inside, ptrinside, ptr_remaining.
  rewrite (proj2 (Z.eqb_eq _ _) H4), (proj2 (Z.leb_le _ _) H8). reflexivity.
Qed.

Lemma pn_fp_in : forall bs size key r n, prop_is_inside bs 8 size r = true ->
  find_prop bs size key r (S n) =
  if u32_at bs r =? key then Some r else find_prop bs size key (r + round_up8 (16 + u32_at bs (r + 8))) n.
Proof. intros bs size key r n H. rewrite pn_find_prop_step, H. reflexivity. Qed.

Lemma pn_fp_out : forall bs size key r n, prop_is_inside bs 8 size r = false -> find_prop bs size key r (S n) = None.
Proof. intros bs size key r n H. rewrite pn_find_prop_step, H. reflexivity. Qed.

Lemma pn_is_struct : forall bs v, is_struct_at bs v = (u32_at bs v <? 1048576) && (u32_at bs (v + 4) =? 14).
Proof. reflexivity. Qed.

(** Branch tests: the condition of the pc's [if], decided on Z. *)
Ltac pn_lia := first [ lia | Z.div_mod_to_equations; lia ].
Ltac pn_cond_base :=
  first [ reflexivity
        | apply Z.ltb_lt; pn_lia | apply Z.ltb_ge; pn_lia
        | apply Z.leb_le; pn_lia | apply Z.leb_gt; pn_lia
        | apply Z.eqb_eq; pn_lia | apply Z.eqb_neq; pn_lia ].
Ltac pn_cond_rec :=
  lazymatch goal with
  | |- negb _ = true => apply (proj2 (Bool.negb_true_iff _)); pn_cond_rec
  | |- negb _ = false => apply (proj2 (Bool.negb_false_iff _)); pn_cond_rec
  | _ => pn_cond_base
  end.
Ltac pn_cond := unfold bv_eqb, bv_ltu, bv_lts, bv_leu; cbn [negb]; zsimp; rewrite ?pn_land3, ?pn_shr20; pn_cond_rec.
Ltac pn_go b :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => replace c with b; [cbv iota | symmetry; pn_cond]
  end.
Ltac pn_eq := first [ reflexivity | f_equal; lia | apply Z_to_bv_eqm; Z.div_mod_to_equations; lia ].

(** A fact kept out of sight of the store tactics. *)
Definition pn_hide (A : Prop) : Prop := A.
Lemma pn_hide_i : forall A : Prop, A -> pn_hide A.
Proof. intros A H. exact H. Qed.

(** * The entry of a call *)
Section PN.
Variable c : pctx.
Hypothesis HC : pc_ok c.
Hypothesis HW : S_WALK c.
Hypothesis HE : S_EPI c.
Variables (F : bvmap 5 word) (fc : bv 32).
Hypothesis HFC : frm0 fc.

Lemma pn_facts :
  8 <= Z.of_nat (length (c_bs c)) /\ u32_at (c_bs c) 0 = Z.of_nat (length (c_bs c)) - 8 /\
  0 < c_P c /\ c_P c mod 16 = 0 /\ c_P c + Z.of_nat (length (c_bs c)) <= c_lo c /\
  0 <= c_cap c <= 9 /\ 0 < c_O c /\ c_O c + 3 * (c_cap c + 1) <= c_lo c /\
  0 <= c_lo c /\ c_lo c + 528 <= bv_unsigned (c_sp c) /\ bv_unsigned (c_sp c) < 2^64 /\
  (c_R c = 0 \/ (c_R c mod 4 = 0 /\ bv_unsigned (c_sp c) <= c_R c /\ c_R c + 12 <= 2^64)).
Proof.
  pose proof HC as (HA & HSTK & HLO & _ & _).
  pose proof HA as (_ & HP0 & HP16 & HLEN & HS0 & HPL & HCAP & HO0 & _ & HOL & _ & HR & _).
  pose proof HSTK as (L0 & _ & _).
  pose proof (bv_unsigned_in_range 64 (c_sp c)) as Rsp. change (bv_modulus 64) with (2^64) in Rsp.
  unfold PARSE_STACK in HLO.
  assert (HRR : c_R c = 0 \/ (c_R c mod 4 = 0 /\ bv_unsigned (c_sp c) <= c_R c /\ c_R c + 12 <= 2^64)).
  { destruct HR as [HR | ((HR0 & HR12 & _) & HR4 & HRS)]; [left; exact HR | right; repeat split; lia]. }
  clear HR. repeat split; try lia; exact HRR.
Qed.

(** errno apart from the stack region, and from res. *)
Lemma pn_errno_facts :
  (c_E c + 4 <= c_lo c \/ bv_unsigned (c_sp c) <= c_E c) /\
  (c_R c = 0 \/ c_E c + 4 <= c_R c \/ c_R c + 12 <= c_E c).
Proof.
  pose proof HC as (HA & _).
  pose proof HA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HED & HRE & _).
  cbn [disjoint_from] in HED. unfold c_E.
  split; [lia|]. destruct HRE as [HRE | HRE]; [left; exact HRE|]. cbn [disjoint_from] in HRE. right. lia.
Qed.

(** The memory between the res stores and the find loop: the frame's temporary cells one block of 56 bytes, out
    empty, res (when not NULL) zero. *)
Definition pn_zeros : list byte := le4 (Z_to_bv 64 0) ++ le4 (Z_to_bv 64 0) ++ le4 (Z_to_bv 64 0).

Definition pn_inv (ja : list byte) (m : word -> option byte) : Prop :=
  PMem c (CB 56 ja :: saves c) [] m /\ (c_R c <> 0 -> bytes_at rsegs m (c_R c) pn_zeros).

(** The pod's bytes, in any memory the parse's writes allow. *)
Lemma pn_pod_at : forall ja m, pn_inv ja m -> bytes_at rsegs m (c_P c) (c_bs c).
Proof.
  intros ja m ((_ & _ & MU & _) & _). pose proof HC as (HA & _ & HLO & _).
  pose proof HA as (HB & _).
  pose proof pn_facts as (_ & _ & _ & _ & _ & HCAP & _).
  eapply (pod_kept (c_m c) m (c_lo c) _ (c_tp c) (c_P c) (c_O c) (c_cap c) (c_R c) (c_bs c) (c_ev c) (c_can c) 0
            (c_P c) (c_bs c) HA HLO); [lia | exact MU | lia | lia | exact HB].
Qed.

(** The 4 bytes at offset o of the pod. *)
Lemma pn_rd : forall ja m o, pn_inv ja m -> 0 <= o -> o + 4 <= Z.of_nat (length (c_bs c)) ->
  ov_read_bytes rsegs m (wa (c_P c + o)) 4%nat = Some (le4 (Z_to_bv 64 (u32_at (c_bs c) o))).
Proof.
  intros ja m o INV H0 H4. pose proof (pn_pod_at ja m INV) as B.
  replace (c_P c + o) with (c_P c + Z.of_nat (Z.to_nat o)) by lia.
  rewrite (bytes_at_ov_read rsegs m (c_P c) (c_bs c) (Z.to_nat o) 4 B ltac:(lia)).
  f_equal. unfold le4, u32_at, rd32.
  pose proof (rd32_range (skipn (Z.to_nat o) (c_bs c))) as R. unfold rd32 in R.
  rewrite unsigned_lit by lia.
  assert (L : length (firstn 4 (skipn (Z.to_nat o) (c_bs c))) = 4%nat)
    by (rewrite length_firstn, length_skipn; lia).
  pose proof (pn_le_roundtrip (firstn 4 (skipn (Z.to_nat o) (c_bs c)))) as E. rewrite L in E. symmetry. exact E.
Qed.

(** ** The invariant from the prologue's facts *)
Lemma pn_inv_mk : forall ja m,
  rw_cells rsegs m (bv_unsigned (c_sp c) + -160) (CB 56 ja :: saves c) ->
  stk rsegs m (c_lo c) (bv_unsigned (c_sp c) + -160) ->
  munch ((bv_unsigned (c_sp c) + -160, bv_unsigned (c_sp c)) ::
         (if c_R c =? 0 then [] else [(c_R c, c_R c + 12)])) (c_m c) m ->
  wmono rsegs (c_m c) m -> mem_inv rsegs m ->
  (c_R c <> 0 -> bytes_at rsegs m (c_R c) pn_zeros) ->
  pn_inv ja m.
Proof.
  intros ja m FR ST MU WM MI RZ. split; [|exact RZ].
  pose proof HC as (HA & _ & HLO & _ & _).
  pose proof HA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HEC & _).
  pose proof pn_facts as (_ & _ & _ & _ & _ & HCAP & HO0 & HOL & LO0 & HL & SP64 & _).
  pose proof pn_errno_facts as (HED & HRE).
  unfold PMem. split; [unfold c_spf; exact FR|].
  split; [unfold c_spf; exact ST|].
  split.
  { eapply munch_weaken; [|exact MU]. intros x Hx. unfold parse_writes, PARSE_STACK in Hx. revert Hx.
    destruct (c_R c =? 0); cbn [outside app]; intros Hx; repeat split; lia. }
  split; [apply bytes_at_nil; lia|].
  split.
  { exists (c_ev c). eapply rw_cells_transport; [exact HEC | exact MU | exact WM |].
    change (Z.of_nat (cells_size [C4 (c_ev c)])) with 4.
    destruct (Z.eqb_spec (c_R c) 0) as [E0|E0]; cbn [disjoint_from].
    - split; [lia | exact I].
    - split; [lia|]. split; [lia | exact I]. }
  split; [exact WM | exact MI].
Qed.

(** One 4-byte store inside res. *)
Lemma pn_st1 : forall m cs a b,
  bv_unsigned (c_sp c) <= c_R c -> c_R c <= a -> a + Z.of_nat (length b) <= c_R c + 12 -> c_R c + 12 <= 2^64 ->
  rw_cells rsegs m (bv_unsigned (c_sp c) + -160) cs -> Z.of_nat (cells_size cs) = 160 ->
  stk rsegs m (c_lo c) (bv_unsigned (c_sp c) + -160) ->
  munch [(bv_unsigned (c_sp c) + -160, bv_unsigned (c_sp c)); (c_R c, c_R c + 12)] (c_m c) m ->
  wmono rsegs (c_m c) m -> mem_inv rsegs m -> wr_at rsegs m (c_R c) 12 ->
  rw_cells rsegs (write_to_mem m (wa a) b) (bv_unsigned (c_sp c) + -160) cs /\
  stk rsegs (write_to_mem m (wa a) b) (c_lo c) (bv_unsigned (c_sp c) + -160) /\
  munch [(bv_unsigned (c_sp c) + -160, bv_unsigned (c_sp c)); (c_R c, c_R c + 12)] (c_m c)
    (write_to_mem m (wa a) b) /\
  wmono rsegs (c_m c) (write_to_mem m (wa a) b) /\ mem_inv rsegs (write_to_mem m (wa a) b) /\
  wr_at rsegs (write_to_mem m (wa a) b) (c_R c) 12.
Proof.
  intros m cs a b HSR H1 H2 H3 FR HCS ST MU WM MI WR.
  pose proof (rw_cells_bound rsegs m _ cs FR) as (B0 & B1).
  split; [apply rw_cells_frame; [exact FR | lia | lia | left; lia]|].
  split; [apply stk_write; [exact ST | lia | lia]|].
  split; [apply munch_write; [exact MU | lia | lia | cbn [inside]; right; left; lia]|].
  split; [apply wmono_write; exact WM|].
  split; [|apply wr_at_write; exact WR].
  apply mem_inv_store; [exact MI|].
  replace a with (c_R c + (a - c_R c)) by lia.
  apply (wr_at_store_ok rsegs m (c_R c) 12 (a - c_R c) (length b) WR); lia.
Qed.

(** The three stores of 0x148c8-0x148d0. *)
Definition pn_w3 (m : word -> option byte) (v1 v2 v3 : word) : word -> option byte :=
  write_to_mem (write_to_mem (write_to_mem m (wa (c_R c)) (le4 v1)) (wa (c_R c + 4)) (le4 v2))
    (wa (c_R c + 8)) (le4 v3).

Lemma pn_res3 : forall m cs v1 v2 v3,
  c_R c <> 0 ->
  rw_cells rsegs m (bv_unsigned (c_sp c) + -160) cs -> Z.of_nat (cells_size cs) = 160 ->
  stk rsegs m (c_lo c) (bv_unsigned (c_sp c) + -160) ->
  munch [(bv_unsigned (c_sp c) + -160, bv_unsigned (c_sp c))] (c_m c) m -> wmono rsegs (c_m c) m ->
  mem_inv rsegs m ->
  rw_cells rsegs (pn_w3 m v1 v2 v3) (bv_unsigned (c_sp c) + -160) cs /\
  stk rsegs (pn_w3 m v1 v2 v3) (c_lo c) (bv_unsigned (c_sp c) + -160) /\
  munch [(bv_unsigned (c_sp c) + -160, bv_unsigned (c_sp c)); (c_R c, c_R c + 12)] (c_m c) (pn_w3 m v1 v2 v3) /\
  wmono rsegs (c_m c) (pn_w3 m v1 v2 v3) /\ mem_inv rsegs (pn_w3 m v1 v2 v3) /\
  bytes_at rsegs (pn_w3 m v1 v2 v3) (c_R c) (le4 v1 ++ le4 v2 ++ le4 v3).
Proof.
  intros m cs v1 v2 v3 HR0 FR HCS ST MU WM MI.
  pose proof pn_facts as (_ & _ & _ & _ & _ & _ & _ & _ & LO0 & HL & HSP & HRR).
  destruct HRR as [HRR | (HR4 & HSR & HR12)]; [contradiction|].
  assert (WR : wr_at rsegs m (c_R c) 12).
  { pose proof HC as ((_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HR & _) & _).
    destruct HR as [HR | (W & _)]; [contradiction|]. exact (wr_at_transport rsegs (c_m c) m (c_R c) 12 W WM). }
  assert (MU0 : munch [(bv_unsigned (c_sp c) + -160, bv_unsigned (c_sp c)); (c_R c, c_R c + 12)] (c_m c) m).
  { eapply munch_weaken; [|exact MU]. intros x Hx. cbn [outside] in Hx |- *. tauto. }
  pose proof (length_le4 v1) as L1. pose proof (length_le4 v2) as L2. pose proof (length_le4 v3) as L3.
  destruct (pn_st1 m cs (c_R c) (le4 v1) HSR ltac:(lia) ltac:(lia) HR12 FR HCS ST MU0 WM MI WR)
    as (FR1 & ST1 & MU1 & WM1 & MI1 & WR1).
  destruct (pn_st1 _ cs (c_R c + 4) (le4 v2) HSR ltac:(lia) ltac:(lia) HR12 FR1 HCS ST1 MU1 WM1 MI1 WR1)
    as (FR2 & ST2 & MU2 & WM2 & MI2 & WR2).
  destruct (pn_st1 _ cs (c_R c + 8) (le4 v3) HSR ltac:(lia) ltac:(lia) HR12 FR2 HCS ST2 MU2 WM2 MI2 WR2)
    as (FR3 & ST3 & MU3 & WM3 & MI3 & _).
  unfold pn_w3.
  split; [exact FR3|]. split; [exact ST3|]. split; [exact MU3|]. split; [exact WM3|]. split; [exact MI3|].
  apply bytes_at_app. split.
  { apply bytes_at_write_other; [| lia | lia | lia].
    apply bytes_at_write_other; [| lia | lia | lia].
    apply bytes_at_write_same; lia. }
  rewrite L1. apply bytes_at_app. split.
  { apply bytes_at_write_other; [| lia | lia | lia].
    replace (c_R c + Z.of_nat 4) with (c_R c + 4) by lia.
    apply bytes_at_write_same; lia. }
  rewrite L2. replace (c_R c + Z.of_nat 4 + Z.of_nat 4) with (c_R c + 8) by lia.
  apply bytes_at_write_same; lia.
Qed.

Lemma pn_inv_res : forall ja m, c_R c <> 0 ->
  rw_cells rsegs m (bv_unsigned (c_sp c) + -160) (CB 56 ja :: saves c) ->
  stk rsegs m (c_lo c) (bv_unsigned (c_sp c) + -160) ->
  munch [(bv_unsigned (c_sp c) + -160, bv_unsigned (c_sp c))] (c_m c) m -> wmono rsegs (c_m c) m ->
  mem_inv rsegs m ->
  pn_inv ja (pn_w3 m (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0)).
Proof.
  intros ja m HR0 FR ST MU WM MI.
  destruct (pn_res3 m (CB 56 ja :: saves c) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) HR0 FR
              ltac:(reflexivity) ST MU WM MI) as (FR3 & ST3 & MU3 & WM3 & MI3 & BR).
  apply pn_inv_mk; [exact FR3 | exact ST3 | | exact WM3 | exact MI3 | intros _; exact BR].
  rewrite (proj2 (Z.eqb_neq _ _) HR0). exact MU3.
Qed.

(** ** The exits *)
(** 0x149b8 with s1 = rc: [S_EPI] for an answer with no cell and res (n, keys, refusal) = 0. *)
Lemma pn_exit : forall rc o ja m
    (x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
  o = (rc, [], (0, 0, REFUSE_NONE)) -> pn_inv ja m ->
  evt rsegs (PPost c o)
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned (c_sp c) + -160)) (c_gp c) (c_tp c) x5 x6 x7 x8 (Z_to_bv 64 rc)
             x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 0x149b8) fc None m (seg_rom rsegs)).
Proof.
  intros rc o ja m x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29
    x30 x31 Eo [PM RZ]. subst o.
  exact (HE (rc, [], (0, 0, REFUSE_NONE)) m F fc x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21
           x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 ja PM RZ HFC).
Qed.

(** 0x149b4: s1 = 0, then 0x149b8. *)
Lemma pn_149b4 : forall o ja m
    (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
  o = (0, [], (0, 0, REFUSE_NONE)) -> pn_inv ja m ->
  evt rsegs (PPost c o)
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned (c_sp c) + -160)) (c_gp c) (c_tp c) x5 x6 x7 x8 x9
             x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 0x149b4) fc None m (seg_rom rsegs)).
Proof.
  intros o ja m x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29
    x30 x31 Eo INV.
  zstep. eapply (pn_exit 0 o ja m); [exact Eo | exact INV].
Qed.

(** The munch of the parse across a store inside the frame. *)
Lemma pn_munch_frame : forall m m',
  munch (parse_writes (bv_unsigned (c_sp c)) (c_O c) (Z.of_nat (length (@nil Headamp.cell))) (c_E c) (c_R c))
    (c_m c) m ->
  munch [(bv_unsigned (c_sp c) + -160, bv_unsigned (c_sp c))] m m' ->
  munch (parse_writes (bv_unsigned (c_sp c)) (c_O c) (Z.of_nat (length (@nil Headamp.cell))) (c_E c) (c_R c))
    (c_m c) m'.
Proof.
  intros m m' H1 H2. eapply munch_trans; [exact H1|]. eapply munch_weaken; [|exact H2].
  intros x Hx. unfold parse_writes, PARSE_STACK in Hx. cbn [outside app] in Hx |- *.
  destruct Hx as [Hx _]. split; [lia | exact I].
Qed.

(** ** The walk: [S_WALK] at the Struct's first child, the key slot open, nothing folded *)
Lemma pn_walk_go : forall r ja jb m (F' : bvmap 5 word)
    (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
  x8 = Z_to_bv 64 (c_R c) -> x9 = Z_to_bv 64 0 -> x18 = Z_to_bv 64 (c_cap c) -> x19 = Z_to_bv 64 (c_O c) ->
  x20 = Z_to_bv 64 0 -> x21 = Z_to_bv 64 (c_P c + r + 16) -> x22 = Z_to_bv 64 0 -> x23 = Z_to_bv 64 0 ->
  x24 = Z_to_bv 64 LIT_PREFIX -> x25 = Z_to_bv 64 (c_P c + r + 8) -> x26 = Z_to_bv 64 (c_P c + (r + 16)) ->
  x27 = Z_to_bv 64 8 ->
  st_ok c r ->
  ha_result (ha_fold parse_cell (c_cap c) (walk_pairs (c_bs c) r (r + 16) (length (c_bs c)) None) [] 0 0) = RESM c ->
  PMem c (wframe c ja jb) [] m -> fp_ok F' fc ->
  evt rsegs (PPost c (RESM c))
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned (c_sp c) + -160)) (c_gp c) (c_tp c) x5 x6 x7 x8 x9 x10 x11 x12 x13 x14
             x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F' (Z_to_bv 64 0x14a28) fc None m (seg_rom rsegs)).
Proof.
  intros r ja jb m F' x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
    x29 x30 x31 E8 E9 E18 E19 E20 E21 E22 E23 E24 E25 E26 E27 HST HM PM FP.
  subst x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27.
  pose proof HST as (Hr1 & Hr8 & Hv20 & Hend).
  pose proof (pn_u32 (c_bs c) (r + 8)) as Rv.
  pose proof pn_facts as (_ & _ & _ & _ & _ & HCAP & _).
  refine (HW r (length (c_bs c)) (r + 16) None None [] 0 0 m F' fc x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17
            x28 x29 x30 x31 ja jb HST _ _ _ I _ _ _ _ HM PM FP).
  - lia.
  - pn_lia.
  - lia.
  - cbn [length Z.of_nat]. lia.
  - lia.
  - lia.
  - lia.
Qed.

(** 0x14974: the params prop at offset r was found (its value size in a4); spa_pod_is_struct, the walk setup
    0x149fc-0x14a24, then [S_WALK]. *)
Lemma pn_found : is_object_type (c_bs c) POD_OBJECT_PROPS = true ->
  forall r ja m
    (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
  x14 = Z_to_bv 64 (u32_at (c_bs c) (r + 8)) -> x25 = Z_to_bv 64 (c_P c + r) ->
  16 <= r -> r mod 8 = 0 -> r + 16 + u32_at (c_bs c) (r + 8) <= Z.of_nat (length (c_bs c)) ->
  find_prop (c_bs c) (u32_at (c_bs c) 0) POD_PROP_PARAMS 16 (length (c_bs c)) = Some r ->
  pn_inv ja m ->
  evt rsegs (PPost c (RESM c))
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned (c_sp c) + -160)) (c_gp c) (c_tp c) x5 x6 x7 (Z_to_bv 64 (c_R c))
             (Z_to_bv 64 0) x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (c_cap c)) (Z_to_bv 64 (c_O c))
             x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 0x14974) fc None m (seg_rom rsegs)).
Proof.
  intros HOBJ r ja m x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
    E14 E25 Hr1 Hr3 Hend HF INV.
  subst x14 x25.
  pose proof pn_facts as (L8 & HS & P0 & P16 & HPL & HCAP & O0 & HOL & LO0 & HL & SP64 & _).
  pose proof (pn_u32 (c_bs c) (r + 8)) as Rv. pose proof (pn_u32 (c_bs c) (r + 12)) as Rt.
  pose proof (pn_model_found (c_bs c) (c_cap c) r HOBJ HF) as EM.
  remember (u32_at (c_bs c) (r + 8)) as vs eqn:Evs.
  zstep. (* srli a4,a4,20 *)
  zstep. (* bnez a4 *)
  destruct (Z_lt_le_dec vs 1048576) as [V20|V20].
  2:{ pn_go true. eapply (pn_149b4 (RESM c)); [| exact INV]. unfold RESM. rewrite EM.
      replace (is_struct_at (c_bs c) (r + 8)) with false; [reflexivity|].
      rewrite pn_is_struct, <- Evs, (proj2 (Z.ltb_ge _ _) V20). reflexivity. }
  pn_go false.
  pose proof (pn_rd ja m (r + 12) INV ltac:(lia) ltac:(lia)) as RD.
  zstep. clear RD. (* lw a0,12(s9) *)
  zstep. (* li a1,14 *)
  zstep. rewrite (pn_eqb_sx (u32_at (c_bs c) (r + 12)) 14) by lia. (* bne a0,a1 *)
  destruct (Z.eq_dec (u32_at (c_bs c) (r + 12)) 14) as [T14|T14].
  2:{ pn_go true. eapply (pn_149b4 (RESM c)); [| exact INV]. unfold RESM. rewrite EM.
      replace (is_struct_at (c_bs c) (r + 8)) with false; [reflexivity|].
      rewrite pn_is_struct, <- Evs. replace (r + 8 + 4) with (r + 12) by lia.
      rewrite (proj2 (Z.ltb_lt _ _) V20), (proj2 (Z.eqb_neq _ _) T14). reflexivity. }
  pn_go false.
  assert (IS : is_struct_at (c_bs c) (r + 8) = true).
  { rewrite pn_is_struct, <- Evs. replace (r + 8 + 4) with (r + 12) by lia.
    rewrite (proj2 (Z.ltb_lt _ _) V20), (proj2 (Z.eqb_eq _ _) T14). reflexivity. }
  rewrite IS in EM.
  zstep. (* addi s9,s9,8 *)
  zstep. (* andi a0,s9,3 *)
  zstep. pn_go true. (* beqz a0 *)
  do 6 zstep. (* mv s6; mv s1; mv s4; mv s7; addi s5,s9,8; li s11,8 *)
  zstep. (* auipc a0 *)
  zstep. (* fmv.d.x fs0,zero *)
  zstep. (* addi s8,a0,-0x757 *)
  zstep. (* mv s10,s5 *)
  pose proof pn_errno_facts as (HED & _).
  destruct INV as ((FR & ST & MU & _ & (ev' & EV) & WM & MI) & _).
  unfold c_spf, saves in FR. unfold c_spf in ST.
  apply pn_hide_i in MU.
  pose proof (munch_refl [(bv_unsigned (c_sp c) + -160, bv_unsigned (c_sp c))] m) as MU2.
  zstep. (* sd s8,0x18(sp) *)
  eapply pn_walk_go.
  1-12: pn_eq.
  - unfold st_ok. subst vs. repeat split; lia.
  - unfold RESM. rewrite EM. reflexivity.
  - unfold PMem, wframe, saves, c_spf. split; [exact FR|].
    split; [exact ST|].
    split; [unfold pn_hide in MU; exact (pn_munch_frame _ _ MU MU2)|].
    split; [apply bytes_at_nil; lia|].
    split; [exists ev'; exact EV|].
    split; [exact WM | exact MI].
  - split; [|exact HFC]. rewrite freg_get_same by reflexivity. reflexivity.
Qed.

(** ** The find loop at 0x14938 (spa_pod_object_find_prop, iter.h:255-258, with spa_pod_prop_is_inside): the prop at
    offset r, n passes of fuel. a0 = P + 8 (the object body), a1 = S - 16, a2 = P + S - 8, a3 = SPA_PROP_params,
    s9 = P + r, s1 = 0. *)
Lemma pn_find : is_object_type (c_bs c) POD_OBJECT_PROPS = true -> 16 <= u32_at (c_bs c) 0 ->
  forall n r ja m
    (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
  x9 = Z_to_bv 64 0 -> x10 = Z_to_bv 64 (c_P c + 8) -> x11 = Z_to_bv 64 (u32_at (c_bs c) 0 - 16) ->
  x12 = Z_to_bv 64 (c_P c + u32_at (c_bs c) 0 - 8) -> x13 = Z_to_bv 64 0x80001 -> x25 = Z_to_bv 64 (c_P c + r) ->
  16 <= r -> r <= u32_at (c_bs c) 0 + 15 -> r mod 8 = 0 -> (Z.to_nat (8 + u32_at (c_bs c) 0 - r) < n)%nat ->
  find_prop (c_bs c) (u32_at (c_bs c) 0) POD_PROP_PARAMS r n =
    find_prop (c_bs c) (u32_at (c_bs c) 0) POD_PROP_PARAMS 16 (length (c_bs c)) ->
  pn_inv ja m ->
  evt rsegs (PPost c (RESM c))
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned (c_sp c) + -160)) (c_gp c) (c_tp c) x5 x6 x7 (Z_to_bv 64 (c_R c))
             x9 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (c_cap c)) (Z_to_bv 64 (c_O c))
             x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 0x14938) fc None m (seg_rom rsegs)).
Proof.
  intros HOBJ H16.
  pose proof pn_facts as (L8 & HS & P0 & P16 & HPL & HCAP & O0 & HOL & LO0 & HL & SP64 & _).
  pose proof (pn_u32 (c_bs c) 0) as R0.
  induction n as [|n IH]; intros r ja m x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x23 x24 x25 x26
    x27 x28 x29 x30 x31 E9 E10 E11 E12 E13 E25 Hr1 Hr2 Hr3 Hn HF INV; [lia|].
  subst x9 x10 x11 x12 x13 x25.
  assert (Hr4 : r mod 4 = 0) by pn_lia.
  zstep. pn_go false. (* bltu s9,a0 *)
  zstep. (* sub a4,s9,a0 *)
  zstep. (* bltu a1,a4 *)
  destruct (Z_lt_le_dec (u32_at (c_bs c) 0 - 16) (r - 8)) as [HB|HB].
  { pn_go true. eapply (pn_exit 0 (RESM c)); [| exact INV]. unfold RESM. apply pn_model_no_params; [exact HOBJ|].
    rewrite <- HF. apply pn_fp_out. rewrite pn_pin by lia.
    rewrite (proj2 (Z.leb_gt _ _) HB). destruct (16 <=? u32_at (c_bs c) 0); reflexivity. }
  pn_go false.
  pose proof (pn_u32 (c_bs c) (r + 8)) as Rv. pose proof (pn_u32 (c_bs c) r) as Rk.
  pose proof (pn_rd ja m (r + 8) INV ltac:(lia) ltac:(lia)) as RD.
  zstep. clear RD. rewrite (pn_zx32 (u32_at (c_bs c) (r + 8)) Rv). (* lwu a4,8(s9) *)
  remember (u32_at (c_bs c) (r + 8)) as vs eqn:Evs.
  zstep. (* sub a5,a2,s9 *)
  zstep. (* bltu a5,a4 *)
  destruct (Z_lt_le_dec (u32_at (c_bs c) 0 - 8 - r) vs) as [HV|HV].
  { pn_go true. eapply (pn_149b4 (RESM c)); [| exact INV]. unfold RESM. apply pn_model_no_params; [exact HOBJ|].
    rewrite <- HF. apply pn_fp_out. rewrite pn_pin by lia. rewrite <- Evs.
    assert (HV' : 8 + u32_at (c_bs c) 0 - (r + 16) < vs) by lia.
    rewrite (proj2 (Z.leb_gt _ _) HV'), andb_false_r. reflexivity. }
  pn_go false.
  assert (PI : prop_is_inside (c_bs c) 8 (u32_at (c_bs c) 0) r = true).
  { rewrite pn_pin by lia. rewrite <- Evs.
    assert (HV' : vs <= 8 + u32_at (c_bs c) 0 - (r + 16)) by lia.
    rewrite (proj2 (Z.leb_le _ _) H16), (proj2 (Z.leb_le _ _) HB), (proj2 (Z.leb_le _ _) HV'). reflexivity. }
  rewrite (pn_fp_in _ _ _ _ _ PI) in HF. rewrite <- Evs in HF.
  pose proof (pn_rd ja m r INV ltac:(lia) ltac:(lia)) as RD.
  zstep. clear RD. (* lw a5,0(s9) *)
  zstep. rewrite (pn_eqb_sx (u32_at (c_bs c) r) 524289) by lia. (* beq a5,a3 *)
  destruct (Z.eq_dec (u32_at (c_bs c) r) 524289) as [K|K].
  { pn_go true. subst vs.
    eapply (pn_found HOBJ r ja m); [reflexivity | reflexivity | exact Hr1 | exact Hr3 | lia | | exact INV].
    rewrite <- HF. rewrite (proj2 (Z.eqb_eq (u32_at (c_bs c) r) POD_PROP_PARAMS) K). reflexivity. }
  pn_go false.
  rewrite (proj2 (Z.eqb_neq (u32_at (c_bs c) r) POD_PROP_PARAMS) K) in HF.
  pose proof (pn_ru_facts vs ltac:(lia)) as (RU1 & RU2).
  zstep. (* addi a4,a4,15 *)
  zstep. rewrite (pn_ru vs). (* ori a4,a4,7 *)
  zstep. (* add a4,s9,a4 *)
  zstep. (* addi s9,a4,1 *)
  zstep. (* andi a4,s9,3 *)
  zstep. pn_go false. (* bnez a4 *)
  zstep. (* j 0x14938 *)
  eapply (IH (r + round_up8 (16 + vs)) ja m).
  1-6: pn_eq.
  1-4: pn_lia.
  - exact HF.
  - exact INV.
Qed.

(** ** 0x148dc: spa_pod_is_object_type, the find setup, then the find loop. *)
Lemma pn_obj : forall ja m
    (x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
  x9 = Z_to_bv 64 (-1) -> pn_inv ja m ->
  evt rsegs (PPost c (RESM c))
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned (c_sp c) + -160)) (c_gp c) (c_tp c) x5 x6 x7 (Z_to_bv 64 (c_R c)) x9
             (Z_to_bv 64 (c_P c)) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (c_cap c)) (Z_to_bv 64 (c_O c))
             x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 0x148dc) fc None m (seg_rom rsegs)).
Proof.
  intros ja m x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 E9 INV.
  subst x9.
  pose proof pn_facts as (L8 & HS & P0 & P16 & HPL & HCAP & O0 & HOL & LO0 & HL & SP64 & _).
  pose proof (pn_u32 (c_bs c) 0) as R0. pose proof (pn_u32 (c_bs c) 4) as R4. pose proof (pn_u32 (c_bs c) 8) as R8.
  pose proof (pn_rd ja m 0 INV ltac:(lia) ltac:(lia)) as RD. rewrite Z.add_0_r in RD.
  zstep. clear RD. (* lw a1,0(a0) *)
  zstep. rewrite (pn_srliw_sx (u32_at (c_bs c) 0)) by lia. (* srliw a2,a1,20 *)
  zstep. (* bnez a2 *)
  destruct (Z_lt_le_dec (u32_at (c_bs c) 0) 1048576) as [S20|S20].
  2:{ pn_go true. eapply (pn_exit (-1) (RESM c)); [| exact INV]. unfold RESM. apply pn_model_not_props.
      rewrite pn_obj_eq, (proj2 (Z.ltb_ge _ _) S20). reflexivity. }
  pn_go false. rewrite (pn_sx32 (u32_at (c_bs c) 0)) by lia.
  zstep. (* li a2,8 *)
  zstep. (* bltu a1,a2 *)
  destruct (Z_lt_le_dec (u32_at (c_bs c) 0) 8) as [S8|S8].
  { pn_go true. eapply (pn_exit (-1) (RESM c)); [| exact INV]. unfold RESM. apply pn_model_not_props.
    rewrite pn_obj_eq, (proj2 (Z.ltb_lt _ _) S20), (proj2 (Z.leb_gt _ _) S8).
    destruct (u32_at (c_bs c) 4 =? 15); reflexivity. }
  pn_go false.
  pose proof (pn_rd ja m 4 INV ltac:(lia) ltac:(lia)) as RD.
  zstep. clear RD. (* lw a2,4(a0) *)
  zstep. (* li a3,15 *)
  zstep. rewrite (pn_eqb_sx (u32_at (c_bs c) 4) 15) by lia. (* bne a2,a3 *)
  destruct (Z.eq_dec (u32_at (c_bs c) 4) 15) as [T15|T15].
  2:{ pn_go true. eapply (pn_exit (-1) (RESM c)); [| exact INV]. unfold RESM. apply pn_model_not_props.
      rewrite pn_obj_eq, (proj2 (Z.ltb_lt _ _) S20), (proj2 (Z.eqb_neq _ _) T15). reflexivity. }
  pn_go false.
  pose proof (pn_rd ja m 8 INV ltac:(lia) ltac:(lia)) as RD.
  zstep. clear RD. (* lw a2,8(a0) *)
  zstep. zstep. (* lui a3,0x40; addiw a3,a3,2 *)
  zstep. rewrite (pn_eqb_sx (u32_at (c_bs c) 8) 262146) by lia. (* bne a2,a3 *)
  destruct (Z.eq_dec (u32_at (c_bs c) 8) 262146) as [O2|O2].
  2:{ pn_go true. eapply (pn_exit (-1) (RESM c)); [| exact INV]. unfold RESM. apply pn_model_not_props.
      rewrite pn_obj_eq, (proj2 (Z.ltb_lt _ _) S20), (proj2 (Z.eqb_eq _ _) T15), (proj2 (Z.leb_le _ _) S8),
        (proj2 (Z.eqb_neq _ _) O2). reflexivity. }
  pn_go false.
  assert (HOBJ : is_object_type (c_bs c) POD_OBJECT_PROPS = true).
  { rewrite pn_obj_eq, (proj2 (Z.ltb_lt _ _) S20), (proj2 (Z.eqb_eq _ _) T15), (proj2 (Z.leb_le _ _) S8),
      (proj2 (Z.eqb_eq _ _) O2). reflexivity. }
  zstep. (* addi a0,a0,8 *)
  zstep. (* andi a2,a0,3 *)
  zstep. pn_go false. (* bnez a2 *)
  zstep. (* li a2,16 *)
  zstep. (* bltu a1,a2 *)
  destruct (Z_lt_le_dec (u32_at (c_bs c) 0) 16) as [S16|S16].
  { pn_go true. eapply (pn_149b4 (RESM c)); [| exact INV]. unfold RESM. apply pn_model_no_params; [exact HOBJ|].
    destruct (length (c_bs c)) as [|n0] eqn:EL; [lia|]. apply pn_fp_out.
    rewrite pn_pin by lia. rewrite (proj2 (Z.leb_gt _ _) S16). reflexivity. }
  pn_go false.
  do 6 zstep. (* addi a1,a1,-16; addi s9,a0,8; lui a3,0x80; add a2,a1,a0; addiw a3,a3,1; mv s1,zero *)
  eapply (pn_find HOBJ ltac:(lia) (length (c_bs c)) 16 ja m).
  1-6: pn_eq.
  1-4: pn_lia.
  - reflexivity.
  - exact INV.
Qed.

(** ** The prologue (0x1487c-0x148c0) and the res stores (0x148c4-0x148d0), on any memory m0 that the call has
    not changed outside the frame; then K at 0x148d4. *)
Lemma pn_pro : forall (Q : machine_state -> Prop) (t0 t1 t2 a0 a4 a5 a6 a7 t3 t4 t5 t6 : word) m0,
  (forall ja m (x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
     pn_inv ja m ->
     evt rsegs Q (MS (mkR x1 (Z_to_bv 64 (bv_unsigned (c_sp c) + -160)) (c_gp c) (c_tp c) x5 x6 x7
                          (Z_to_bv 64 (c_R c)) x9 a0 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (c_cap c))
                          (Z_to_bv 64 (c_O c)) x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                     F (Z_to_bv 64 0x148d4) fc None m (seg_rom rsegs))) ->
  stk rsegs m0 (c_lo c) (bv_unsigned (c_sp c)) -> mem_inv rsegs m0 ->
  munch [(bv_unsigned (c_sp c) + -160, bv_unsigned (c_sp c))] (c_m c) m0 -> wmono rsegs (c_m c) m0 ->
  evt rsegs Q (MS (mkR (c_ra c) (c_sp c) (c_gp c) (c_tp c) t0 t1 t2 (c_s0 c) (c_s1 c) a0 (Z_to_bv 64 (c_O c))
                       (Z_to_bv 64 (c_cap c)) (Z_to_bv 64 (c_R c)) a4 a5 a6 a7 (c_s2 c) (c_s3 c) (c_s4 c) (c_s5 c)
                       (c_s6 c) (c_s7 c) (c_s8 c) (c_s9 c) (c_s10 c) (c_s11 c) t3 t4 t5 t6)
                  F (Z_to_bv 64 0x1487c) fc None m0 (seg_rom rsegs)).
Proof.
  intros Q t0 t1 t2 a0 a4 a5 a6 a7 t3 t4 t5 t6 m0 K ST MI MU WM.
  pose proof pn_facts as (_ & _ & _ & _ & _ & _ & _ & _ & L0 & HL & HS & HRR).
  carve_frame 160%nat ST.
  do 15 zstep. (* addi sp; thirteen sd; fsd fs0 *)
  do 3 zstep. (* mv s0,a3; mv s2,a2; mv s3,a1 *)
  zstep. (* beqz a3 *)
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m1 end.
  lazymatch type of FR with rw_cells _ _ _ (CB 48 ?j :: C8 ?v :: ?rest) =>
    pose proof (rw_cells_merge rsegs m1 _ [] [CB 48 j; C8 v] rest FR) as FR2; clear FR end.
  cbn [app cells_size csize Nat.add] in FR2.
  lazymatch type of FR2 with rw_cells _ _ _ (CB _ ?jj :: _) => set (ja := jj) in FR2; clearbody ja end.
  destruct HRR as [HR0 | (HR4 & HSR & HR12)].
  - pn_go true. eapply K. apply pn_inv_mk; [exact FR2 | exact ST | | exact WM | exact MI | intros NR; contradiction].
    rewrite HR0. exact MU.
  - assert (HR0 : c_R c <> 0) by lia.
    pn_go false.
    assert (WR : wr_at rsegs m1 (c_R c) 12).
    { pose proof HC as ((_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HR & _) & _).
      destruct HR as [HR | (W & _)]; [contradiction|]. exact (wr_at_transport rsegs (c_m c) m1 (c_R c) 12 W WM). }
    pose proof (wr_at_store_ok rsegs m1 (c_R c) 12 0 4 WR ltac:(lia) ltac:(lia)) as HS0. rewrite Z.add_0_r in HS0.
    zstep. clear HS0. (* sw zero,0(s0) *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (wr_at_store_ok rsegs mm (c_R c) 12 4 4 (wr_at_write rsegs m1 (c_R c) 12 _ _ WR)
                    ltac:(lia) ltac:(lia)) as HS1 end.
    zstep. clear HS1. (* sw zero,4(s0) *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (wr_at_store_ok rsegs mm (c_R c) 12 8 4
                    (wr_at_write rsegs _ (c_R c) 12 _ _ (wr_at_write rsegs m1 (c_R c) 12 _ _ WR))
                    ltac:(lia) ltac:(lia)) as HS2 end.
    zstep. clear HS2. (* sw zero,8(s0) *)
    eapply K. eapply pn_inv_res; [exact HR0 | exact FR2 | exact ST | exact MU | exact WM | exact MI].
Qed.

(** ** The whole entry *)
Lemma pn_main : forall (null : bool) (t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 : word),
  evt rsegs (PPost c (parse_props (parse_arg null (c_bs c)) (c_cap c)))
    (MS (mkR (c_ra c) (c_sp c) (c_gp c) (c_tp c) t0 t1 t2 (c_s0 c) (c_s1 c)
             (Z_to_bv 64 (if null then 0 else c_P c)) (Z_to_bv 64 (c_O c)) (Z_to_bv 64 (c_cap c))
             (Z_to_bv 64 (c_R c)) a4 a5 a6 a7 (c_s2 c) (c_s3 c) (c_s4 c) (c_s5 c) (c_s6 c) (c_s7 c) (c_s8 c)
             (c_s9 c) (c_s10 c) (c_s11 c) t3 t4 t5 t6)
        F (Z_to_bv 64 HA_PARSE_RESULT) fc None (c_m c) (seg_rom rsegs)).
Proof.
  intros null t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6.
  pose proof HC as (_ & HSTK & _ & _ & HMI).
  pose proof pn_facts as (L8 & HS & P0 & P16 & HPL & HCAP & O0 & HOL & LO0 & HL & SP64 & _).
  unfold HA_PARSE_RESULT.
  destruct null; cbn [parse_arg parse_props].
  - eapply pn_pro; [| exact HSTK | exact HMI | apply munch_refl | apply wmono_refl].
    intros ja m x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 INV.
    zstep. (* li s1,-1 *)
    zstep. (* beqz a0 *)
    try pn_go true.
    eapply (pn_exit (-1)); [reflexivity | exact INV].
  - eapply pn_pro; [| exact HSTK | exact HMI | apply munch_refl | apply wmono_refl].
    intros ja m x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 INV.
    zstep. (* li s1,-1 *)
    zstep. pn_go false. (* beqz a0 *)
    eapply pn_obj; [pn_eq | exact INV].
Qed.

End PN.

(** [S_ENTRY] from the cuts it reaches. *)
Lemma pn_entry : forall c, pc_ok c -> S_WALK c -> S_EPI c -> S_ENTRY c.
Proof.
  intros c HC HW HE null F fc t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 HFC.
  apply pn_main; assumption.
Qed.
