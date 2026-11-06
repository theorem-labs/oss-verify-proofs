(** The walk of reac-pw/fuzz_headamp's LLVMFuzzerTestOneInput (plain) over segment M03 outside expect_of: from
    malloc(out)'s return (0x14080) through memset(out, 0xa5), res := 0x5a x 12, the parse, check_no_overrun,
    check_count, check_cells_valid and the corrupt test (0x140e8); expect_of (0x140f0 -> 0x14108) is taken from
    Cut.v's [expect_stmt]; then x->rc, check_object, check_cells, and for rc >= 0 check_keys and check_refusal
    (0x14108 -> 0x14148); then first's size (0x14148 -> 0x14164). Against headamp_check_contract
    (Prog/LLVMFuzzerTestOneInput_c.v), with the callee contracts and expect_stmt as Section hypotheses. Section Head
    fixes the contract's frame (sp, gp, tp, the entry memory m), the input inp (the record r = head_rec inp), the
    null flag nl, cap, pp, pod, out, lo, errno's first value and the SSP guard; QH is the contract's postcondition.
    Walked backwards: QH_done (0x14164), first_ok (0x14148), checks_ok (0x14108), corrupt_ok (0x140e8),
    after_parse (0x140c0), head_ok (0x14080). The four checks against x pass because on an uncorrupted record the
    parse's answer is expect_model (Pod/Headamp.v parse_props_build, Prog/HeadSites.v site_spine), which
    expect_stmt leaves in x; the other three pass from the parse contract's answer alone (parse_props_total). *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Sem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac FP.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib Require MemNorm.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Import Cursor Model Layout Spa Headamp.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Spec Require Import HeadBytes.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Prog Require Import memset_c reac_headamp_prop_parse_result_c
  check_no_overrun_c check_count_c check_cells_valid_c check_object_c check_cells_c check_keys_c check_refusal_c
  SlotInv LLVMFuzzerTestOneInput_c HeadSites.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Prog.HeadCheck Require Import Facts Cut.
Import ListNotations.
Open Scope Z_scope.

Ltac ret_even := rewrite ret_pc_even by (first [lia | reflexivity]).
(* lia over the frame constants; the disjunctive separation facts are kept as or_h (Facts.v) so that lia does not
   case-split them all: on a failure each or_h fact is tried, split, alone. *)
Ltac zl0 := unfold FRAME_LOCALS, MID_STACK, PARSE_STACK, OUT_LEN, head_len, NEAR_STACK, CHECK_CELLS_FRAME,
  CHECK_CELLS_VALID_FRAME in *; lia.
Ltac zl := first [ zl0 | match goal with H : or_h _ _ |- _ =>
                           let H' := fresh in pose proof H as H'; unfold or_h in H'; destruct H'; zl0 end ].
Ltac dj := cbn [disjoint_from]; repeat split; zl.

(** ** Arithmetic and byte facts *)
Lemma rc_cases : forall rc, -1 <= rc <= 9 ->
  rc = -1 \/ rc = 0 \/ rc = 1 \/ rc = 2 \/ rc = 3 \/ rc = 4 \/ rc = 5 \/ rc = 6 \/ rc = 7 \/ rc = 8 \/ rc = 9.
Proof. intros rc H. lia. Qed.

(** `addi a0,s7,-1; and s5,a0,s1`: the parse's props argument (null ? NULL : pod). *)
Lemma land_arg : forall nl pod, 0 <= nl <= 1 -> 0 <= pod < 2^64 ->
  Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 (nl + -1))) (bv_unsigned (Z_to_bv 64 pod)))
  = Z_to_bv 64 (if nl =? 1 then 0 else pod).
Proof.
  intros nl pod Hn Hp. rewrite (unsigned_lit pod) by lia.
  assert (C : nl = 0 \/ nl = 1) by lia. destruct C as [-> | ->]; cbn [Z.eqb].
  - change (bv_unsigned (Z_to_bv 64 (0 + -1))) with (Z.ones 64). rewrite Z.land_comm, Z.land_ones by lia.
    rewrite Z.mod_small by lia. reflexivity.
  - change (bv_unsigned (Z_to_bv 64 (1 + -1))) with 0. rewrite Z.land_0_l. reflexivity.
Qed.

(** res = sp + 0x150 is 4-aligned for a 16-aligned sp. *)
Lemma mod4_add336 : forall x, x mod 16 = 0 -> (x + 336) mod 4 = 0.
Proof.
  intros x H. apply (proj1 (Z.mod_divide x 16 ltac:(lia))) in H. destruct H as [k ->].
  replace (k * 16 + 336) with ((4 * k + 84) * 4) by ring. apply Z.mod_mul. lia.
Qed.

(** An address in a footprint lies in its first interval or in the rest. *)
Lemma not_outside_cons : forall a b W x, ~ outside ((a, b) :: W) x -> (a <= x < b) \/ ~ outside W x.
Proof.
  intros a b W x H. cbn [outside] in H.
  destruct (Z_le_gt_dec a x) as [H1|H1]; destruct (Z_lt_ge_dec x b) as [H2|H2];
    try (left; lia); right; intros H'; apply H; (split; [lia | exact H']).
Qed.

Lemma repeat_split : forall {A} (x : A) a b, repeat x (a + b) = repeat x a ++ repeat x b.
Proof. intros A x a b. induction a as [|a IH]; [reflexivity|]. cbn [repeat Nat.add app]. f_equal. exact IH. Qed.

(** The guard cell out[cap] after the parse: its three bytes are still 0xa5. *)
Lemma out_guard : forall m1 O cap o, 0 <= cap <= 9 -> answer_ok cap o ->
  bytes_at rsegs m1 O (out_after cap o) -> bytes_at rsegs m1 (O + 3 * cap) (repeat GUARD_BYTE 3).
Proof.
  intros m1 O cap o Hc HO HB. destruct (answer_cells_len cap o Hc HO) as [_ HL].
  unfold out_after, OUT_LEN in HB. rewrite length_ha_cells_bytes in HB.
  apply bytes_at_app in HB as [_ HB]. rewrite length_ha_cells_bytes in HB.
  replace (Z.to_nat (3 * (cap + 1)) - 3 * length (ans_cells o))%nat
    with ((Z.to_nat (3 * cap) - 3 * length (ans_cells o)) + 3)%nat in HB by lia.
  rewrite repeat_split in HB. apply bytes_at_app in HB as [_ HB]. rewrite repeat_length in HB.
  replace (O + Z.of_nat (3 * length (ans_cells o)) + Z.of_nat (Z.to_nat (3 * cap) - 3 * length (ans_cells o)))
    with (O + 3 * cap) in HB by lia.
  exact HB.
Qed.

Lemma out_cells : forall m1 O cap o,
  bytes_at rsegs m1 O (out_after cap o) -> bytes_at rsegs m1 O (ha_cells_bytes (ans_cells o)).
Proof. intros m1 O cap o HB. unfold out_after in HB. apply bytes_at_app in HB as [HB _]. exact HB. Qed.

(** out after memset(out, 0xa5, 3 (cap + 1)) and a parse that wrote out[0, 3n) with the cells. *)
Lemma out_after_parse : forall m2 m3 W O cap o,
  answer_ok cap o -> 0 <= cap <= 9 ->
  bytes_at rsegs m2 O (repeat GUARD_BYTE (Z.to_nat (OUT_LEN cap))) ->
  munch W m2 m3 -> bytes_at rsegs m3 O (ha_cells_bytes (ans_cells o)) ->
  disjoint_from W (O + 3 * Z.of_nat (length (ans_cells o))) (OUT_LEN cap - 3 * Z.of_nat (length (ans_cells o))) ->
  bytes_at rsegs m3 O (out_after cap o).
Proof.
  intros m2 m3 W O cap o HO Hc HB MU HC HD. destruct (answer_cells_len cap o Hc HO) as [_ HL].
  unfold out_after. apply bytes_at_app. split; [exact HC|]. rewrite length_ha_cells_bytes.
  unfold OUT_LEN in *.
  replace (Z.to_nat (3 * (cap + 1))) with (3 * length (ans_cells o) + (Z.to_nat (3 * (cap + 1)) - 3 * length (ans_cells o)))%nat
    in HB by lia.
  rewrite repeat_split in HB. apply bytes_at_app in HB as [_ HB]. rewrite repeat_length in HB.
  eapply bytes_at_transport; [exact HB | exact MU |]. rewrite repeat_length.
  replace (Z.of_nat (Z.to_nat (3 * (cap + 1)) - 3 * length (ans_cells o)))
    with (3 * (cap + 1) - 3 * Z.of_nat (length (ans_cells o))) by lia.
  replace (Z.of_nat (3 * length (ans_cells o))) with (3 * Z.of_nat (length (ans_cells o))) by lia. exact HD.
Qed.

(** x->rc's 4 bytes and x's tail after them make x_bytes. *)
Lemma x_join : forall m1 X o, bytes_at rsegs m1 X (le4 (Z_to_bv 64 (ans_rc o))) -> bytes_at rsegs m1 (X + 4) (x_tail o) ->
  bytes_at rsegs m1 X (x_bytes o).
Proof.
  intros m1 X o H1 H2. rewrite x_bytes_tail. apply bytes_at_app. split; [exact H1|].
  rewrite length_le4. exact H2.
Qed.

(** task_mem across a callee whose footprint is writable at the start. *)
Lemma tm_call : forall m1 m2 W, MemNorm.task_mem rsegs m1 -> munch W m1 m2 ->
  (forall x, ~ outside W x -> 0 <= x < 2^64 -> wview rsegs m1 (wa x) <> None) -> MemNorm.task_mem rsegs m2.
Proof.
  intros m1 m2 W TM MU H. apply (task_mem_munch rsegs W m1 m2 TM MU). intros x Hx.
  pose proof (bv_unsigned_in_range 64 x) as R. unfold bv_modulus in R. change (2 ^ Z.of_N 64) with (2^64) in R.
  specialize (H (bv_unsigned x) Hx R). unfold wa in H. rewrite Z_to_bv_lit_self in H. exact H.
Qed.

Lemma stk_wv : forall m1 lo hi x, stk rsegs m1 lo hi -> lo <= x < hi -> wview rsegs m1 (wa x) <> None.
Proof. intros m1 lo hi x (_ & _ & H) Hx. exact (proj1 (H x Hx)). Qed.

Lemma wr_wv : forall m1 a n x, wr_at rsegs m1 a n -> a <= x < a + n -> wview rsegs m1 (wa x) <> None.
Proof.
  intros m1 a n x (_ & _ & H) Hx. specialize (H (x - a) ltac:(lia)). replace (a + (x - a)) with x in H by lia.
  exact H.
Qed.

Section Head.
Variables (sp gp tp : word) (m : word -> option byte) (inp : list byte) (nl cap pp pod out lo : Z) (ev0 can : word).

Local Abbreviation SP := (bv_unsigned sp).
Local Abbreviation r := (head_rec inp).
Local Abbreviation o := (head_ans nl cap inp).
Local Abbreviation EA := (PARSE_ERRNO tp).
Local Abbreviation L := (OUT_LEN cap).
Local Abbreviation LEN := (head_len inp).
Local Abbreviation E0 := (expect_model (nl =? 1) cap r).

Hypothesis HNL : 0 <= nl <= 1.
Hypothesis HCAP : 0 <= cap <= 9.
Hypothesis HOUT : 0 < out.
Hypothesis HPOD : 0 < pod.
Hypothesis HPODA : pod mod 16 = 0.
Hypothesis HSEP1 : or_h (out + L <= pod) (pod + LEN <= out).
Hypothesis HSEP2 : or_h (out + L <= pp) (pp + POD_PROPS <= out).
Hypothesis HSEP3 : or_h (pod + LEN <= pp) (pp + POD_PROPS <= pod).
Hypothesis HOLO : out + L <= lo.
Hypothesis HPODLO : pod + LEN <= lo.
Hypothesis HPPLO : pp + POD_PROPS <= lo.
Hypothesis HLO : lo + MID_STACK <= SP.
Hypothesis HSPA : SP mod 16 = 0.
Hypothesis HSPT : SP + FRAME_LOCALS <= 2^64.
Hypothesis HLO0 : 0 <= lo.
Hypothesis HPP0 : 0 <= pp.
Hypothesis HROM : forall a, lo <= a < SP + FRAME_LOCALS -> seg_rom rsegs (wa a) = None.
Hypothesis HE0 : 0 <= EA /\ EA + 4 <= 2^64.
Hypothesis HED : disjoint_from [(lo, SP + FRAME_LOCALS); (pod, pod + LEN); (out, out + L); (pp, pp + POD_PROPS)] EA 4.
Hypothesis HGD1 : disjoint_from [(lo, SP + FRAME_LOCALS); (out, out + L); (EA, EA + 4)] PARSE_SSP_GOT 8.
Hypothesis HGD2 : disjoint_from [(lo, SP + FRAME_LOCALS); (out, out + L); (EA, EA + 4)] PARSE_SSP_GUARD 8.

Lemma lo_sp : lo + 528 <= SP.
Proof. unfold MID_STACK, PARSE_STACK in HLO. zl. Qed.

Lemma ea_facts : or_h (EA + 4 <= lo) (SP + FRAME_LOCALS <= EA) /\ or_h (EA + 4 <= pod) (pod + LEN <= EA) /\
  or_h (EA + 4 <= out) (out + L <= EA) /\ or_h (EA + 4 <= pp) (pp + POD_PROPS <= EA).
Proof. pose proof HED as H. cbn [disjoint_from] in H. destruct H as (A & B & C & D & _). unfold or_h. auto. Qed.

Lemma got_facts : or_h (PARSE_SSP_GOT + 8 <= lo) (SP + FRAME_LOCALS <= PARSE_SSP_GOT) /\
  or_h (PARSE_SSP_GOT + 8 <= out) (out + L <= PARSE_SSP_GOT) /\ or_h (PARSE_SSP_GOT + 8 <= EA) (EA + 4 <= PARSE_SSP_GOT).
Proof. pose proof HGD1 as H. cbn [disjoint_from] in H. destruct H as (A & B & C & _). unfold or_h. auto. Qed.

Lemma guard_facts : or_h (PARSE_SSP_GUARD + 8 <= lo) (SP + FRAME_LOCALS <= PARSE_SSP_GUARD) /\
  or_h (PARSE_SSP_GUARD + 8 <= out) (out + L <= PARSE_SSP_GUARD) /\
  or_h (PARSE_SSP_GUARD + 8 <= EA) (EA + 4 <= PARSE_SSP_GUARD).
Proof. pose proof HGD2 as H. cbn [disjoint_from] in H. destruct H as (A & B & C & _). unfold or_h. auto. Qed.

Lemma L_range : 3 <= L <= 30.
Proof. unfold OUT_LEN. zl. Qed.

Ltac facts := pose proof ea_facts as (FE1 & FE2 & FE3 & FE4); pose proof got_facts as (FG1 & FG2 & FG3);
  pose proof guard_facts as (FU1 & FU2 & FU3); pose proof lo_sp; pose proof L_range.

Lemma r_wf : pod_rec_wf r.
Proof. exact (pod_build_wf inp r (snd (pod_build inp)) (surjective_pairing _)). Qed.

Lemma len_bounds : 8 <= LEN <= 5440.
Proof. unfold head_len. destruct (buf_header r r_wf) as (_ & _ & _ & H). zl. Qed.

Lemma o_ok : answer_ok cap o /\ 0 <= ans_keys o <= 16384.
Proof. pose proof len_bounds. unfold head_ans. apply parse_answer; [zl | unfold head_len in *; zl]. Qed.

Lemma rc_range : -1 <= ans_rc o <= cap.
Proof.
  destruct o_ok as [HO _]. apply answer_ok_parts in HO as [[(E1 & _) | (E1 & _)] _]; zl.
Qed.

Lemma len_pp : Z.of_nat (length (pp_bytes r)) = POD_PROPS.
Proof. exact (length_pp_bytes r r_wf). Qed.

Lemma len_out_after : Z.of_nat (length (out_after cap o)) = L.
Proof.
  destruct o_ok as [HO _]. destruct (answer_cells_len cap o HCAP HO) as [_ HL].
  unfold out_after, OUT_LEN in *. rewrite length_app, repeat_length, length_ha_cells_bytes. zl.
Qed.

Lemma len_res : Z.of_nat (length (ans_res_bytes o)) = 12.
Proof. unfold ans_res_bytes. rewrite length_ha_res_bytes. reflexivity. Qed.

(** The footprint of the segment and the contract's postcondition. *)
Definition WH : list ivl := [(SP - MID_STACK, SP + FRAME_LOCALS); (out, out + L); (EA, EA + 4)].

Definition QH : machine_state -> Prop :=
  fun ms' => exists (ra' t0' t1' t2' s0' a1' a2' a3' a4' a5' a6' a7' s7' s9' s10' s11' t3' t4' t5' t6' : word)
                    (F' : bvmap 5 word) (fc' : bv 32) (m' : word -> option byte) (ev' : word),
    ms' = MS (mkR ra' sp gp tp t0' t1' t2' s0' (Z_to_bv 64 pod)
                  (Z_to_bv 64 (first_req (ans_rc o))) a1' a2' a3' a4' a5' a6' a7'
                  (Z_to_bv 64 cap) (Z_to_bv 64 out) (Z_to_bv 64 L)
                  (Z_to_bv 64 (if nl =? 1 then 0 else pod)) (Z_to_bv 64 (ans_rc o)) s7'
                  (Z_to_bv 64 (3 * Z.max (ans_rc o) 0)) s9' s10' s11' t3' t4' t5' t6')
             F' (Z_to_bv 64 HEAD_MALLOC4) fc' None m' (seg_rom rsegs) /\
    frm0 fc' /\
    bytes_at rsegs m' out (out_after cap o) /\
    bytes_at rsegs m' (SP + 0x58) (le8 (Z_to_bv 64 pp)) /\
    rw_cells rsegs m' EA [C4 ev'] /\
    munch WH m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (SP + FRAME_LOCALS).

(** The memory after the parse: changed only in WH; the out block holds the parse's cells over 0xa5; the frame cell
    sp + 0x58 = pp, res, errno a cell, the record in the pp block. *)
Definition MemB (m1 : word -> option byte) : Prop :=
  munch WH m m1 /\ wmono rsegs m m1 /\ mem_inv rsegs m1 /\ stk rsegs m1 lo (SP + FRAME_LOCALS) /\
  MemNorm.task_mem rsegs m1 /\
  bytes_at rsegs m1 out (out_after cap o) /\ bytes_at rsegs m1 (SP + 0x58) (le8 (Z_to_bv 64 pp)) /\
  (exists ev', rw_cells rsegs m1 EA [C4 ev']) /\ bytes_at rsegs m1 (SP + 0x150) (ans_res_bytes o) /\
  bytes_at rsegs m1 pp (pp_bytes r).

Lemma MemB_mi : forall m1, MemB m1 -> mem_inv rsegs m1.
Proof. intros m1 (_ & _ & MI & _). exact MI. Qed.

Lemma MemB_stk : forall m1, MemB m1 -> stk rsegs m1 lo SP.
Proof.
  intros m1 (_ & _ & _ & ST & _). pose proof lo_sp. unfold FRAME_LOCALS in *.
  exact (proj1 (stk_split rsegs m1 lo SP (SP + 0x1b0) ST ltac:(zl))).
Qed.

(** A callee whose footprint is the k bytes below sp (a check's frame). *)
Lemma MemB_below : forall m1 m2 k, MemB m1 -> munch [(SP - k, SP)] m1 m2 -> wmono rsegs m1 m2 -> mem_inv rsegs m2 ->
  stk rsegs m2 lo SP -> 0 <= k <= MID_STACK -> MemB m2.
Proof.
  intros m1 m2 k (MU & WM & MI & ST & TM & HO & H58 & (ev & HE) & HR & HPP) MU2 WM2 MI2 ST2 Hk. facts.
  pose proof len_out_after as LO. pose proof len_res as LR. pose proof len_pp as LP.
  unfold MID_STACK, PARSE_STACK, FRAME_LOCALS in *.
  split.
  { apply (munch_trans WH m m1 m2 MU). eapply munch_weaken; [|exact MU2].
    intros x Hx. unfold WH in Hx. cbn [outside] in Hx |- *. destruct Hx as (O1 & O2 & O3 & _).
    unfold MID_STACK, PARSE_STACK, FRAME_LOCALS in O1. split; [zl | exact I]. }
  split; [exact (wmono_trans rsegs m m1 m2 WM WM2)|].
  split; [exact MI2|].
  split.
  { destruct (stk_split rsegs m1 lo SP (SP + 0x1b0) ST ltac:(zl)) as [_ ST1].
    apply (stk_merge rsegs m2 lo SP); [exact ST2 | | zl].
    apply (stk_transport_disjoint rsegs _ m1 m2 _ _ ST1 MU2 WM2). dj. }
  split.
  { apply (tm_call m1 m2 _ TM MU2). intros x Hx Hr. cbn [outside] in Hx.
    apply (stk_wv m1 lo (SP + 0x1b0)); [exact ST | zl]. }
  split; [eapply bytes_at_transport; [exact HO | exact MU2 | rewrite LO; dj]|].
  split; [eapply bytes_at_transport; [exact H58 | exact MU2 | rewrite length_le8; dj]|].
  split; [exists ev; eapply rw_cells_transport; [exact HE | exact MU2 | exact WM2 | cbn [cells_size csize]; dj]|].
  split; [eapply bytes_at_transport; [exact HR | exact MU2 | rewrite LR; dj]|].
  eapply bytes_at_transport; [exact HPP | exact MU2 | rewrite LP; unfold POD_PROPS in *; dj].
Qed.

(** expect_of's writes: the soft-float stack, its temporaries and x. *)
Lemma MemB_expect : forall m1 m2, MemB m1 -> munch (EXPECT_W SP) m1 m2 -> wmono rsegs m1 m2 -> mem_inv rsegs m2 ->
  MemNorm.task_mem rsegs m2 -> stk rsegs m2 lo (SP + FRAME_LOCALS) -> MemB m2.
Proof.
  intros m1 m2 (MU & WM & MI & ST & TM & HO & H58 & (ev & HE) & HR & HPP) MU2 WM2 MI2 TM2 ST2. facts.
  pose proof len_out_after as LO. pose proof len_res as LR. pose proof len_pp as LP.
  unfold EXPECT_W, NEAR_STACK, MID_STACK, PARSE_STACK, FRAME_LOCALS in *.
  split.
  { apply (munch_trans WH m m1 m2 MU). eapply munch_weaken; [|exact MU2].
    intros x Hx. unfold WH in Hx. cbn [outside] in Hx |- *. destruct Hx as (O1 & O2 & O3 & _).
    unfold MID_STACK, PARSE_STACK, FRAME_LOCALS in O1. repeat split; try exact I; zl. }
  split; [exact (wmono_trans rsegs m m1 m2 WM WM2)|].
  split; [exact MI2|]. split; [exact ST2|]. split; [exact TM2|].
  split; [eapply bytes_at_transport; [exact HO | exact MU2 | rewrite LO; dj]|].
  split; [eapply bytes_at_transport; [exact H58 | exact MU2 | rewrite length_le8; dj]|].
  split; [exists ev; eapply rw_cells_transport; [exact HE | exact MU2 | exact WM2 | cbn [cells_size csize]; dj]|].
  split; [eapply bytes_at_transport; [exact HR | exact MU2 | rewrite LR; dj]|].
  eapply bytes_at_transport; [exact HPP | exact MU2 | rewrite LP; unfold POD_PROPS in *; dj].
Qed.

(** The store of x->rc (0x14108 `sw s0,0x90(sp)`). *)
Lemma MemB_xrc : forall m1 (v : word), MemB m1 ->
  store_ok rsegs m1 (wa (SP + 0x90)) 4 = true /\ MemB (write_to_mem m1 (wa (SP + 0x90)) (le4 v)).
Proof.
  intros m1 v (MU & WM & MI & ST & TM & HO & H58 & (ev & HE) & HR & HPP). facts.
  pose proof len_out_after as LO. pose proof len_res as LR. pose proof len_pp as LP.
  unfold MID_STACK, PARSE_STACK, FRAME_LOCALS in *.
  assert (HS : store_ok rsegs m1 (wa (SP + 0x90)) 4 = true) by exact (stk_store_ok rsegs m1 lo (SP + 0x1b0) (SP + 0x90) 4 ST ltac:(zl) ltac:(zl)).
  assert (HS' : store_ok rsegs m1 (wa (SP + 0x90)) (length (le4 v)) = true) by (rewrite length_le4; exact HS).
  split; [exact HS|].
  split; [apply munch_write; [exact MU | zl | rewrite length_le4; zl | unfold WH; cbn [inside]; rewrite length_le4; left; zl]|].
  split; [apply wmono_write; exact WM|].
  split; [apply mem_inv_store; [exact MI | exact HS']|].
  split; [apply stk_write; [exact ST | zl | rewrite length_le4; zl]|].
  split; [apply task_mem_write; [exact TM | exact HS']|].
  split; [apply bytes_at_write_other; [exact HO | zl | rewrite length_le4; zl | rewrite LO, length_le4; zl]|].
  split; [apply bytes_at_write_other; [exact H58 | zl | rewrite length_le4; zl | rewrite !length_le4, length_le8; zl]|].
  split; [exists ev; apply rw_cells_frame; [exact HE | zl | rewrite length_le4; zl | cbn [cells_size csize]; rewrite length_le4; zl]|].
  split; [apply bytes_at_write_other; [exact HR | zl | rewrite length_le4; zl | rewrite LR, length_le4; zl]|].
  apply bytes_at_write_other; [exact HPP | zl | rewrite length_le4; zl | rewrite LP, length_le4; unfold POD_PROPS in *; zl].
Qed.

(** ** 0x14164: the contract's postcondition *)
Lemma QH_done : forall (ra t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
                       (F : bvmap 5 word) (fc : bv 32) (m1 : word -> option byte),
  a0 = Z_to_bv 64 (first_req (ans_rc o)) -> s8 = Z_to_bv 64 (3 * Z.max (ans_rc o) 0) ->
  frm0 fc -> MemB m1 ->
  evt rsegs QH
    (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 pod) a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 cap) (Z_to_bv 64 out) (Z_to_bv 64 L) (Z_to_bv 64 (if nl =? 1 then 0 else pod))
             (Z_to_bv 64 (ans_rc o)) s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x14164) fc None m1 (seg_rom rsegs)).
Proof.
  intros ra t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1 -> -> HF
    (MU & WM & MI & ST & TM & HO & H58 & (ev & HE) & HR & HPP).
  apply evt_done. exists ra, t0, t1, t2, s0, a1, a2, a3, a4, a5, a6, a7, s7, s9, s10, s11, t3, t4, t5, t6, F, fc, m1, ev.
  split; [reflexivity|]. split; [exact HF|]. split; [exact HO|]. split; [exact H58|]. split; [exact HE|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI | exact ST].
Qed.

(** ** 0x14148 .. 0x14160: first's size s8 = 3 max(rc, 0), a0 = s8 + (s8 = 0) *)
Lemma first_ok : forall (ra t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
                        (F : bvmap 5 word) (fc : bv 32) (m1 : word -> option byte),
  frm0 fc -> MemB m1 ->
  evt rsegs QH
    (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 pod) a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 cap) (Z_to_bv 64 out) (Z_to_bv 64 L) (Z_to_bv 64 (if nl =? 1 then 0 else pod))
             (Z_to_bv 64 (ans_rc o)) s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x14148) fc None m1 (seg_rom rsegs)).
Proof.
  intros ra t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1 HF MB.
  pose proof (MemB_mi m1 MB) as MI. pose proof rc_range as Hrc.
  (* 0x14148 sgtz a0,s6; neg a0,a0; and s8,a0,s6; slli a0,s8,1; add s8,a0,s8; seqz a0,s8; add a0,s8,a0 *)
  step. step. step. step. step. step. step.
  eapply QH_done; [| | exact HF | exact MB];
    (revert Hrc; generalize (ans_rc o) as z; intros z Hz;
     destruct (rc_cases z ltac:(zl)) as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]];
     vm_compute; reflexivity).
Qed.

Hypothesis CKO : check_object_contract.
Hypothesis CKC : check_cells_contract.
Hypothesis CKK : check_keys_contract.
Hypothesis CKR : check_refusal_contract.

(** ** 0x14108 .. 0x14144: x->rc := s0, check_object, check_cells, and for rc >= 0 check_keys, check_refusal *)
Lemma checks_ok : o = E0 ->
  forall (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m1 : word -> option byte),
  frm0 fc -> MemB m1 -> bytes_at rsegs m1 (SP + 0x94) (x_tail E0) ->
  evt rsegs QH
    (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 (ans_rc E0)) (Z_to_bv 64 pod) a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 cap) (Z_to_bv 64 out) (Z_to_bv 64 L) (Z_to_bv 64 (if nl =? 1 then 0 else pod))
             (Z_to_bv 64 (ans_rc o)) s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x14108) fc None m1 (seg_rom rsegs)).
Proof.
  intros EO ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1 HF MB HX. pose proof lo_sp.
  destruct o_ok as [HO HK]. pose proof rc_range as Hrc.
  pose proof (answer_cells_len cap o HCAP HO) as [HL1 HL2].
  assert (LX : Z.of_nat (length (x_tail E0)) = 132).
  { pose proof (length_x_bytes E0) as LB. rewrite x_bytes_tail, length_app, length_le4 in LB.
    rewrite <- EO in LB |- *. specialize (LB HL1). zl. }
  (* 0x14108 sw s0,0x90(sp) *)
  destruct (MemB_xrc m1 (Z_to_bv 64 (ans_rc E0)) MB) as [HS MB2].
  step.
  match goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem m1 ?A ?BS) _) =>
    change A with (wa (SP + 0x90));
    change BS with (le4 (Z_to_bv 64 (ans_rc E0)))
  end.
  assert (HX2 : bytes_at rsegs (write_to_mem m1 (wa (SP + 0x90)) (le4 (Z_to_bv 64 (ans_rc E0)))) (SP + 0x90) (x_bytes E0)).
  { apply x_join.
    - apply bytes_at_write_same; rewrite ?length_le4; unfold FRAME_LOCALS in *; zl.
    - replace (SP + 0x90 + 4) with (SP + 0x94) by zl.
      apply bytes_at_write_other; [exact HX | zl | rewrite length_le4; unfold FRAME_LOCALS in *; zl | rewrite LX, length_le4; zl]. }
  revert MB2 HX2. generalize (write_to_mem m1 (wa (SP + 0x90)) (le4 (Z_to_bv 64 (ans_rc E0)))) as m2.
  intros m2 MB2 HX2. clear HS HX.
  pose proof MB2 as (_ & _ & MI2 & ST2 & _ & HO2 & _ & _ & HR2 & _).
  (* 0x1410c addi a1,sp,0x150; addi a2,sp,0x90; mv a0,s6; jal check_object *)
  step. step. step. step.
  destruct (site_object m2 (SP + 0x150) (SP + 0x90) cap o E0 HCAP HO EO HX2 HR2) as (R1 & HXR & R2 & IFF & HRZ).
  eapply evt_cut.
  { eapply CKO with (rc := ans_rc o) (xrc := ans_rc E0); [reflexivity | exact R1 | | exact R2 | exact IFF |].
    - rewrite unsigned_lit by (unfold FRAME_LOCALS in *; zl). exact HXR.
    - intros Hm1. rewrite unsigned_lit by (unfold FRAME_LOCALS in *; zl). exact (HRZ Hm1). }
  intros ms' (a0' & a2' & a3' & ->). ret_even.
  (* 0x1411c addi a2,sp,0x90; mv a0,s3; mv a1,s6; jal check_cells *)
  step. step. step. step.
  destruct (site_cells m2 out (SP + 0x90) lo cap o E0 HCAP HO EO HOLO HX2 (out_cells m2 out cap o HO2))
    as (R3 & HXR3 & HC3).
  eapply evt_cut.
  { eapply CKC with (lo := lo) (rc := ans_rc o) (cs := ans_cells o); [reflexivity | zl | | | | | | | exact MI2].
    - rewrite unsigned_lit by (unfold FRAME_LOCALS in *; zl). exact HXR3.
    - rewrite unsigned_lit by (unfold FRAME_LOCALS in *; zl). zl.
    - rewrite !unsigned_lit by (unfold FRAME_LOCALS in *; zl). exact HC3.
    - exact (MemB_stk m2 MB2).
    - unfold CHECK_CELLS_FRAME, MID_STACK, PARSE_STACK in *. zl.
    - intros a Ha. apply HROM. zl. }
  intros ms' (a0'' & a1'' & a2'' & a3'' & a4'' & m3 & E3 & MU3 & WM3 & MI3 & ST3). subst ms'. ret_even.
  pose proof (MemB_below m2 m3 CHECK_CELLS_FRAME MB2 MU3 WM3 MI3 ST3 ltac:(unfold CHECK_CELLS_FRAME, MID_STACK, PARSE_STACK; zl)) as MB3.
  assert (HX3 : bytes_at rsegs m3 (SP + 0x90) (x_bytes E0)).
  { eapply bytes_at_transport; [exact HX2 | exact MU3 |]. unfold CHECK_CELLS_FRAME. dj. }
  pose proof MB3 as (_ & _ & _ & _ & _ & _ & _ & _ & HR3 & _).
  (* 0x1412c bltz s6 *)
  step. rewrite lts_s by zl.
  destruct (Z.ltb_spec (ans_rc o) 0) as [Hn|Hn]; cbv beta iota.
  { eapply first_ok; [exact HF | exact MB3]. }
  (* 0x14130 addi a0,sp,0x150; addi a1,sp,0x90; jal check_keys *)
  step. step. step.
  destruct (site_keys m3 (SP + 0x150) (SP + 0x90) cap o E0 HCAP HO EO HX3 HR3) as (LK & K1 & K2).
  eapply evt_cut.
  { eapply CKK with (w := le4 (Z_to_bv 64 (ans_keys o))); [exact LK | |].
    - rewrite unsigned_lit by (unfold FRAME_LOCALS in *; zl). exact K1.
    - rewrite unsigned_lit by (unfold FRAME_LOCALS in *; zl). exact K2. }
  intros ms' (a0k & a1k & ->). ret_even.
  (* 0x1413c addi a0,sp,0x150; addi a1,sp,0x90; jal check_refusal *)
  step. step. step.
  destruct (site_refusal m3 (SP + 0x150) (SP + 0x90) cap o E0 HCAP HO EO HX3 HR3) as (LF & F1 & F2).
  eapply evt_cut.
  { eapply CKR with (w := le4 (Z_to_bv 64 (ans_rf o))); [exact LF | |].
    - rewrite unsigned_lit by (unfold FRAME_LOCALS in *; zl). exact F1.
    - rewrite unsigned_lit by (unfold FRAME_LOCALS in *; zl). exact F2. }
  intros ms' (a0f & a1f & ->). ret_even.
  eapply first_ok; [exact HF | exact MB3].
Qed.


Hypothesis EXP : expect_stmt.

(** ** 0x140e8 .. 0x140ec: `if (!pp->corrupt)`; expect_of (expect_stmt) and the checks against x, else first's size *)
Lemma corrupt_ok : forall (ra t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s9 s10 s11 t3 t4 t5 t6 : word)
                          (F : bvmap 5 word) (fc : bv 32) (m1 : word -> option byte),
  frm0 fc -> MemB m1 -> bytes_at rsegs m1 (SP + 0x50) (le8 (Z_to_bv 64 (pp + POD_LEN_OFF))) ->
  evt rsegs QH
    (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 pod) a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 cap) (Z_to_bv 64 out) (Z_to_bv 64 L) (Z_to_bv 64 (if nl =? 1 then 0 else pod))
             (Z_to_bv 64 (ans_rc o)) (Z_to_bv 64 nl) (Z_to_bv 64 (pp + 19732)) s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x140e8) fc None m1 (seg_rom rsegs)).
Proof.
  intros ra t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s9 s10 s11 t3 t4 t5 t6 F fc m1 HF MB H50. pose proof lo_sp.
  pose proof len_pp as LP.
  pose proof MB as (MU & WM & MI & ST & TM & HO & H58 & HE & HR & HPP).
  (* 0x140e8 lw a0,4(s8); bnez a0 *)
  assert (HRD : ov_read_bytes rsegs m1 (wa (pp + 19736)) 4 = Some (le4 (Z_to_bv 64 (Z.b2z (corrupt r))))).
  { apply (read_field rsegs m1 pp r 19736 _ HPP r_wf);
      [exact (pp_corrupt r r_wf) | zl | unfold PP_SIZE; zl | destruct (corrupt r); cbn; zl]. }
  revert HRD. destruct (corrupt r) eqn:EC; cbn [Z.b2z]; intros HRD.
  { step. clear HRD. rewrite sx32_small by zl. step. if_true. eapply first_ok; [exact HF | exact MB]. }
  step. clear HRD. rewrite sx32_small by zl. step. if_false.
  assert (EO : o = E0) by exact (site_spine inp r (snd (pod_build inp)) cap (nl =? 1) (surjective_pairing _) EC HCAP).
  (* 0x140f0 .. 0x14108: expect_of *)
  eapply EXP with (r := r) (nl := nl) (cap := cap) (pp := pp) (lo := lo).
  - exact r_wf.
  - exact HNL.
  - exact HCAP.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - exact H50.
  - exact H58.
  - exact HPP.
  - exact HPP0.
  - exact HPPLO.
  - exact ST.
  - unfold NEAR_STACK, MID_STACK, PARSE_STACK in *. zl.
  - exact HSPA.
  - exact HROM.
  - exact HF.
  - exact MI.
  - exact TM.
  - intros ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s7' s8' s9' s10' s11' t3' t4' t5' t6' F' fc' m5
      HF5 MU5 WM5 MI5 TM5 ST5 HX5.
    eapply checks_ok; [exact EO | exact HF5 | exact (MemB_expect m1 m5 MB MU5 WM5 MI5 TM5 ST5) | exact HX5].
Qed.

Hypothesis CKNO : check_no_overrun_contract.
Hypothesis CKCNT : check_count_contract.
Hypothesis CKCV : check_cells_valid_contract.

(** ** 0x140c0 .. 0x140e4: rc := a0; check_no_overrun(out + 3 cap), check_count(rc, cap, &res),
    check_cells_valid(out, rc) *)
Lemma after_parse : forall (ra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s5 s6 s9 s10 s11 t3 t4 t5 t6 : word)
                           (F : bvmap 5 word) (fc : bv 32) (m1 : word -> option byte),
  s5 = Z_to_bv 64 (if nl =? 1 then 0 else pod) ->
  frm0 fc -> MemB m1 -> bytes_at rsegs m1 (SP + 0x50) (le8 (Z_to_bv 64 (pp + POD_LEN_OFF))) ->
  evt rsegs QH
    (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 (3 * cap)) (Z_to_bv 64 pod) (Z_to_bv 64 (ans_rc o))
             a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 cap) (Z_to_bv 64 out) (Z_to_bv 64 L) s5 s6
             (Z_to_bv 64 nl) (Z_to_bv 64 (pp + 19732)) s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x140c0) fc None m1 (seg_rom rsegs)).
Proof.
  intros ra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s5 s6 s9 s10 s11 t3 t4 t5 t6 F fc m1 -> HF MB H50. pose proof lo_sp. pose proof L_range.
  destruct o_ok as [HO HK]. pose proof rc_range as Hrc.
  pose proof MB as (MU & WM & MI & ST & TM & HO1 & H58 & HE & HR & HPP).
  (* 0x140c0 mv s6,a0; add a0,s3,s0; jal check_no_overrun *)
  step. step. step.
  eapply evt_cut.
  { eapply CKNO.
    match goal with |- bytes_at _ _ ?A _ => replace A with (out + 3 * cap) end;
      [exact (out_guard m1 out cap o HCAP HO HO1) |].
    rewrite ?(unsigned_lit out) by zl. rewrite ?(unsigned_lit (3 * cap)) by zl. symmetry. apply unsigned_lit. zl. }
  intros ms' ->. ret_even.
  (* 0x140cc addi a2,sp,0x150; mv a0,s6; mv a1,s2; jal check_count *)
  step. step. step. step.
  destruct (site_count m1 (SP + 0x150) cap o HCAP HO HK HR) as (C1 & C2 & C3).
  eapply evt_cut.
  { eapply CKCNT with (rc := ans_rc o) (cap := cap) (keys := ans_keys o); [reflexivity | reflexivity | exact C1 | exact C2 |].
    rewrite unsigned_lit by (unfold FRAME_LOCALS in *; zl). exact C3. }
  intros ms' (a1' & ->). ret_even.
  (* 0x140dc mv a0,s3; mv a1,s6; jal check_cells_valid *)
  step. step. step.
  destruct (site_cells_valid m1 out lo cap o HCAP HO HOLO (out_cells m1 out cap o HO1)) as (V1 & V2).
  eapply evt_cut.
  { eapply CKCV with (lo := lo) (rc := ans_rc o) (cs := ans_cells o); [reflexivity | exact V1 | | | | | exact MI].
    - rewrite unsigned_lit by (unfold OUT_LEN in *; zl). exact V2.
    - exact (MemB_stk m1 MB).
    - unfold CHECK_CELLS_VALID_FRAME, MID_STACK, PARSE_STACK in *. zl.
    - intros a Ha. apply HROM. zl. }
  intros ms' (a0' & a1'' & a2' & a3' & a4' & a5' & m2 & E2 & MU2 & WM2 & MI2 & ST2). subst ms'. ret_even.
  pose proof (MemB_below m1 m2 CHECK_CELLS_VALID_FRAME MB MU2 WM2 MI2 ST2
                ltac:(unfold CHECK_CELLS_VALID_FRAME, MID_STACK, PARSE_STACK; zl)) as MB2.
  eapply corrupt_ok; [exact HF | exact MB2 |].
  eapply bytes_at_transport; [exact H50 | exact MU2 | rewrite length_le8; unfold CHECK_CELLS_VALID_FRAME; dj].
Qed.

(** ** The entry memory and the head before the parse *)
Variable junk : list byte.
Hypothesis HMI : mem_inv rsegs m.
Hypothesis HTM : MemNorm.task_mem rsegs m.
Hypothesis HST : stk rsegs m lo (SP + FRAME_LOCALS).
Hypothesis H50m : bytes_at rsegs m (SP + 0x50) (le8 (Z_to_bv 64 (pp + POD_LEN_OFF))).
Hypothesis H58m : bytes_at rsegs m (SP + 0x58) (le8 (Z_to_bv 64 pp)).
Hypothesis HPPm : bytes_at rsegs m pp (pp_bytes r).
Hypothesis HPODm : bytes_at rsegs m pod (buf r).
Hypothesis HOUTm : rw_cells rsegs m out [CB (Z.to_nat L) junk].
Hypothesis HERRm : rw_cells rsegs m EA [C4 ev0].
Hypothesis HGOTm : bytes_at rsegs m PARSE_SSP_GOT (le8 (Z_to_bv 64 PARSE_SSP_GUARD)).
Hypothesis HGUARDm : bytes_at rsegs m PARSE_SSP_GUARD (le8 can).

Lemma len_buf : Z.of_nat (length (buf r)) = LEN.
Proof. reflexivity. Qed.

(** The memory between memset(out) and the parse. *)
Definition MemH0 (m1 : word -> option byte) : Prop :=
  munch [(SP - MID_STACK, SP + FRAME_LOCALS); (out, out + L)] m m1 /\ wmono rsegs m m1 /\ mem_inv rsegs m1 /\
  stk rsegs m1 lo (SP + FRAME_LOCALS) /\ MemNorm.task_mem rsegs m1 /\
  bytes_at rsegs m1 out (repeat GUARD_BYTE (Z.to_nat L)) /\ wr_at rsegs m1 out L /\
  bytes_at rsegs m1 (SP + 0x50) (le8 (Z_to_bv 64 (pp + POD_LEN_OFF))) /\
  bytes_at rsegs m1 (SP + 0x58) (le8 (Z_to_bv 64 pp)) /\ bytes_at rsegs m1 pp (pp_bytes r) /\
  bytes_at rsegs m1 pod (buf r) /\ rw_cells rsegs m1 EA [C4 ev0] /\
  bytes_at rsegs m1 PARSE_SSP_GOT (le8 (Z_to_bv 64 PARSE_SSP_GUARD)) /\ bytes_at rsegs m1 PARSE_SSP_GUARD (le8 can).

Lemma MemH0_memset : forall m1, munch [(out, out + L)] m m1 -> wmono rsegs m m1 -> mem_inv rsegs m1 ->
  rw_cells rsegs m1 out [CB (Z.to_nat L) (repeat GUARD_BYTE (Z.to_nat L))] -> MemH0 m1.
Proof.
  intros m1 MU WM MI RW. facts. pose proof L_range as HL. pose proof len_pp as LP. pose proof len_bounds as LB.
  unfold MID_STACK, PARSE_STACK, FRAME_LOCALS in *.
  assert (HW0 : wr_at rsegs m out L).
  { destruct HOUTm as [_ W]. cbn [cells_size csize] in W. replace (Z.of_nat (Z.to_nat L + 0)) with L in W by zl. exact W. }
  split; [eapply munch_weaken; [|exact MU]; intros x Hx; cbn [outside] in *; tauto|].
  split; [exact WM|]. split; [exact MI|].
  split; [apply (stk_transport_disjoint rsegs _ m m1 _ _ HST MU WM); dj|].
  split; [apply (tm_call m m1 _ HTM MU); intros x Hx Hr; cbn [outside] in Hx; apply (wr_wv m out L x HW0); zl|].
  split; [exact (rw_cells_CB_bytes rsegs m1 out _ _ RW)|].
  split; [exact (wr_at_transport rsegs m m1 out L HW0 WM)|].
  split; [eapply bytes_at_transport; [exact H50m | exact MU | rewrite length_le8; dj]|].
  split; [eapply bytes_at_transport; [exact H58m | exact MU | rewrite length_le8; dj]|].
  split; [eapply bytes_at_transport; [exact HPPm | exact MU | rewrite LP; unfold POD_PROPS in *; dj]|].
  split; [eapply bytes_at_transport; [exact HPODm | exact MU | rewrite len_buf; dj]|].
  split; [eapply rw_cells_transport; [exact HERRm | exact MU | exact WM | cbn [cells_size csize]; dj]|].
  split; [eapply bytes_at_transport; [exact HGOTm | exact MU | rewrite length_le8; dj]|].
  eapply bytes_at_transport; [exact HGUARDm | exact MU | rewrite length_le8; dj].
Qed.

Lemma MemH0_store_ok : forall m1 a (n : nat), MemH0 m1 -> SP + 0x60 <= a -> a + Z.of_nat n <= SP + FRAME_LOCALS ->
  store_ok rsegs m1 (wa a) n = true.
Proof.
  intros m1 a n (_ & _ & _ & ST & _) H1 H2. unfold FRAME_LOCALS in *.
  exact (stk_store_ok rsegs m1 lo (SP + 0x1b0) a n ST ltac:(unfold MID_STACK, PARSE_STACK in *; zl) H2).
Qed.

Lemma MemH0_store : forall m1 a bs, MemH0 m1 -> store_ok rsegs m1 (wa a) (length bs) = true ->
  SP + 0x60 <= a -> a + Z.of_nat (length bs) <= SP + FRAME_LOCALS -> MemH0 (write_to_mem m1 (wa a) bs).
Proof.
  intros m1 a bs (MU & WM & MI & ST & TM & HO & HW & H50 & H58 & HPP & HPD & HE & HG1 & HG2) HS H1 H2. facts.
  pose proof L_range as HL. pose proof len_pp as LP. pose proof len_bounds as LB.
  unfold MID_STACK, PARSE_STACK, FRAME_LOCALS in *.
  split; [apply munch_write; [exact MU | zl | zl | cbn [inside]; left; zl]|].
  split; [apply wmono_write; exact WM|].
  split; [apply mem_inv_store; [exact MI | exact HS]|].
  split; [apply stk_write; [exact ST | zl | zl]|].
  split; [apply task_mem_write; [exact TM | exact HS]|].
  split; [apply bytes_at_write_other; [exact HO | zl | zl | rewrite repeat_length; zl]|].
  split; [apply wr_at_write; exact HW|].
  split; [apply bytes_at_write_other; [exact H50 | zl | zl | rewrite length_le8; zl]|].
  split; [apply bytes_at_write_other; [exact H58 | zl | zl | rewrite length_le8; zl]|].
  split; [apply bytes_at_write_other; [exact HPP | zl | zl | rewrite LP; unfold POD_PROPS in *; zl]|].
  split; [apply bytes_at_write_other; [exact HPD | zl | zl | rewrite len_buf; zl]|].
  split; [apply rw_cells_frame; [exact HE | zl | zl | cbn [cells_size csize]; zl]|].
  split; [apply bytes_at_write_other; [exact HG1 | zl | zl | rewrite length_le8; zl]|].
  apply bytes_at_write_other; [exact HG2 | zl | zl | rewrite length_le8; zl].
Qed.

(** The parse's premises at 0x140bc (Prog/HeadSites.v site_parse_args's form, res = sp + 0x150). *)
Lemma parse_args_here : forall m1, MemH0 m1 -> parse_args m1 lo SP tp pod out cap (SP + 0x150) (buf r) ev0 can.
Proof.
  intros m1 (MU & WM & MI & ST & TM & HO & HW & H50 & H58 & HPP & HPD & HE & HG1 & HG2). facts.
  pose proof L_range as HL. pose proof len_bounds as LB. destruct (buf_header r r_wf) as (_ & _ & HU & _).
  unfold MID_STACK, PARSE_STACK, FRAME_LOCALS, OUT_LEN, head_len in *.
  unfold parse_args.
  refine (conj HPD (conj HPOD (conj HPODA (conj _ (conj HU (conj HPODLO (conj HCAP (conj HOUT (conj HW
    (conj HOLO (conj _ (conj _ (conj HE (conj _ (conj _ (conj HG1 (conj HG2 (conj _ _)))))))))))))))))).
  - zl.
  - zl.
  - right. split; [exact (stk_wr_at rsegs m1 lo (SP + 0x1b0) (SP + 0x150) 12 ST ltac:(zl) ltac:(zl) ltac:(zl))|].
    split; [apply mod4_add336; exact HSPA | zl].
  - cbn [disjoint_from]. repeat split; zl.
  - right. cbn [disjoint_from]. repeat split; zl.
  - unfold parse_space. replace (SP + 0x150 =? 0) with false by (symmetry; apply Z.eqb_neq; zl).
    cbn [app disjoint_from]. repeat split; zl.
  - unfold parse_space. replace (SP + 0x150 =? 0) with false by (symmetry; apply Z.eqb_neq; zl).
    cbn [app disjoint_from]. repeat split; zl.
Qed.

(** The memory after the parse, from its post (n cells written, res at sp + 0x150). *)
Lemma MemB_parse : forall m1 m2 ev', MemH0 m1 ->
  munch (parse_writes SP out (Z.of_nat (length (ans_cells o))) EA (SP + 0x150)) m1 m2 ->
  bytes_at rsegs m2 out (ha_cells_bytes (ans_cells o)) -> bytes_at rsegs m2 (SP + 0x150) (ans_res_bytes o) ->
  rw_cells rsegs m2 EA [C4 ev'] -> wmono rsegs m1 m2 -> mem_inv rsegs m2 -> stk rsegs m2 lo SP ->
  MemB m2 /\ bytes_at rsegs m2 (SP + 0x50) (le8 (Z_to_bv 64 (pp + POD_LEN_OFF))).
Proof.
  intros m1 m2 ev' (MU & WM & MI & ST & TM & HO & HW & H50 & H58 & HPP & HPD & HE & HG1 & HG2) MU2 HC2 HR2 HE2 WM2 MI2 ST2. facts.
  destruct o_ok as [HOK _]. destruct (answer_cells_len cap o HCAP HOK) as [_ HLc].
  pose proof L_range as HL. pose proof len_pp as LP. pose proof len_res as LR.
  assert (HR0 : (SP + 0x150 =? 0) = false) by (apply Z.eqb_neq; unfold MID_STACK, PARSE_STACK in *; zl).
  unfold parse_writes in MU2. rewrite HR0 in MU2. cbn [app] in MU2.
  unfold MID_STACK, PARSE_STACK, FRAME_LOCALS in *.
  assert (HE0' : 0 <= PARSE_ERRNO tp /\ PARSE_ERRNO tp + 4 <= 2^64) by exact HE0.
  split; [split|].
  - apply (munch_trans WH m m1 m2); [eapply munch_weaken; [|exact MU]|eapply munch_weaken; [|exact MU2]];
      intros x Hx; unfold WH in Hx; cbn [outside] in Hx |- *; destruct Hx as (O1 & O2 & O3 & _);
      unfold MID_STACK, PARSE_STACK, FRAME_LOCALS in O1; repeat split; try exact I; zl.
  - split; [exact (wmono_trans rsegs m m1 m2 WM WM2)|].
    split; [exact MI2|].
    split.
    { destruct (stk_split rsegs m1 lo SP (SP + 0x1b0) ST ltac:(zl)) as [_ ST1].
      apply (stk_merge rsegs m2 lo SP); [exact ST2 | | zl].
      apply (stk_transport rsegs _ m1 m2 SP (SP + 0x1b0) ST1 MU2 WM2). intros x Hx.
      destruct (Z_lt_le_dec x (SP + 0x150)) as [X1|X1]; [left; cbn [outside]; repeat split; try exact I; zl|].
      destruct (Z_lt_le_dec x (SP + 0x15c)) as [X2|X2]; [right | left; cbn [outside]; repeat split; try exact I; zl].
      apply (bytes_at_some rsegs m2 (SP + 0x150) _ x HR2); rewrite LR; [intros a Ha; apply HROM | ]; zl. }
    split.
    { apply (tm_call m1 m2 _ TM MU2). intros x Hx Hr.
      destruct (not_outside_cons _ _ _ _ Hx) as [X1|Hx1]; [apply (stk_wv m1 lo (SP + 0x1b0)); [exact ST | zl]|].
      destruct (not_outside_cons _ _ _ _ Hx1) as [X2|Hx2]; [apply (wr_wv m1 out L x HW); zl|].
      destruct (not_outside_cons _ _ _ _ Hx2) as [X3|Hx3].
      { destruct HE as [_ HEW]. cbn [cells_size csize] in HEW. apply (wr_wv m1 _ _ x HEW). zl. }
      destruct (not_outside_cons _ _ _ _ Hx3) as [X4|Hx4]; [apply (stk_wv m1 lo (SP + 0x1b0)); [exact ST | zl]|].
      exfalso. apply Hx4. exact I. }
    split.
    { apply (out_after_parse m1 m2 _ out cap o HOK HCAP HO MU2 HC2). cbn [disjoint_from].
      unfold OUT_LEN in *. repeat split; zl. }
    split; [eapply bytes_at_transport; [exact H58 | exact MU2 | rewrite length_le8; cbn [disjoint_from]; repeat split; zl]|].
    split; [exists ev'; exact HE2|].
    split; [exact HR2|].
    eapply bytes_at_transport; [exact HPP | exact MU2 | rewrite LP; unfold POD_PROPS in *; cbn [disjoint_from]; repeat split; zl].
  - eapply bytes_at_transport; [exact H50 | exact MU2 | rewrite length_le8; cbn [disjoint_from]; repeat split; zl].
Qed.

Hypothesis MSET : memset_contract.
Hypothesis PARSE : reac_headamp_prop_parse_result_contract.

(** ** 0x14080 .. 0x140bc: out <> 0; memset(out, 0xa5, 3 cap + 3); res := 0x5a x 12; s5 := null ? 0 : pod;
    rc := reac_headamp_prop_parse_result(s5, out, cap, &res) *)
Lemma head_ok : forall (ra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s3 s5 s6 s9 s10 s11 t3 t4 t5 t6 : word)
                       (F : bvmap 5 word) (fc : bv 32),
  frm0 fc ->
  evt rsegs QH
    (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 (3 * cap)) (Z_to_bv 64 pod) (Z_to_bv 64 out) a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 cap) s3 (Z_to_bv 64 L) s5 s6 (Z_to_bv 64 nl) (Z_to_bv 64 (pp + 19732)) s9 s10 s11
             t3 t4 t5 t6)
        F (Z_to_bv 64 0x14080) fc None m (seg_rom rsegs)).
Proof.
  intros ra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s3 s5 s6 s9 s10 s11 t3 t4 t5 t6 F fc HF. pose proof lo_sp.
  pose proof L_range as HL. pose proof len_bounds as LB.
  assert (HSPL : SP < 2^64) by (unfold FRAME_LOCALS in *; zl).
  (* 0x14080 beqz a0 *)
  step. rewrite eqb_u by (unfold MID_STACK, PARSE_STACK in *; zl). rewrite (proj2 (Z.eqb_neq _ _)) by zl. cbv beta iota.
  (* 0x14084 mv s3,a0; addi a1,zero,0xa5; mv a2,s4; jal memset *)
  step. step. step. step.
  eapply evt_cut.
  { eapply MSET with (junk := junk); [| exact HMI].
    rewrite (unsigned_lit out) by (unfold MID_STACK, PARSE_STACK in *; zl).
    rewrite (unsigned_lit L) by zl. exact HOUTm. }
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 & -> & MU1 & WM1
              & MI1 & RW1).
  rewrite (unsigned_lit out) in MU1, RW1 by (unfold MID_STACK, PARSE_STACK in *; zl).
  rewrite (unsigned_lit L) in MU1, RW1 by zl. ret_even.
  assert (H1 : MemH0 m1) by (apply (MemH0_memset m1 MU1 WM1 MI1); exact RW1).
  clear MU1 WM1 RW1.
  (* 0x14094 auipc a0; ld a0,0x474(a0): the 0x5a word of .rodata 0x10508 *)
  step. step.
  (* 0x1409c sd a0,0x150(sp) *)
  assert (HS1 : store_ok rsegs m1 (wa (SP + 336)) 8 = true)
    by (apply (MemH0_store_ok m1 (SP + 336) 8 H1); unfold FRAME_LOCALS; zl).
  step.
  match goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem m1 ?A ?BS) _) =>
    change A with (wa (SP + 336));
    assert (H2 : MemH0 (write_to_mem m1 (wa (SP + 336)) BS))
      by (apply MemH0_store; [exact H1 | rewrite length_le8; exact HS1 | zl | rewrite length_le8; unfold FRAME_LOCALS; zl]);
    revert H2; generalize (write_to_mem m1 (wa (SP + 336)) BS) as m2; intros m2 H2
  end.
  clear HS1 MI1.
  (* 0x140a0 sw a0,0x158(sp) *)
  assert (HS2 : store_ok rsegs m2 (wa (SP + 344)) 4 = true)
    by (apply (MemH0_store_ok m2 (SP + 344) 4 H2); unfold FRAME_LOCALS; zl).
  step.
  match goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem m2 ?A ?BS) _) =>
    change A with (wa (SP + 344));
    assert (H3 : MemH0 (write_to_mem m2 (wa (SP + 344)) BS))
      by (apply MemH0_store; [exact H2 | rewrite length_le4; exact HS2 | zl | rewrite length_le4; unfold FRAME_LOCALS; zl]);
    revert H3; generalize (write_to_mem m2 (wa (SP + 344)) BS) as m3; intros m3 H3
  end.
  clear HS2 H2 H1.
  pose proof H3 as (_ & _ & MI3 & ST3 & _).
  (* 0x140a4 addi a0,s7,-1; and s5,a0,s1; addi a3,sp,0x150; mv a0,s5; mv a1,s3; mv a2,s2; jal parse_result *)
  step. step. step. step. step. step. step.
  eapply evt_cut.
  { eapply PARSE with (null := nl =? 1) (lo := lo) (P := pod) (O := out) (cap := cap) (R := SP + 0x150)
                      (bs := buf r) (ev := ev0) (can := can).
    - apply land_arg; [exact HNL | unfold MID_STACK, PARSE_STACK in *; zl].
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - exact (parse_args_here m3 H3).
    - unfold FRAME_LOCALS in *. exact (proj1 (stk_split rsegs m3 lo SP (SP + 0x1b0) ST3 ltac:(unfold MID_STACK, PARSE_STACK in *; zl))).
    - unfold MID_STACK in HLO. exact HLO.
    - intros a Ha. apply HROM. unfold FRAME_LOCALS. zl.
    - exact HF.
    - exact MI3. }
  intros ms' (t0'' & t1'' & t2'' & a1'' & a2'' & a3'' & a4'' & a5'' & a6'' & a7'' & t3'' & t4'' & t5'' & t6'' & F4 & fc4
              & m4 & ev' & E4 & HF4 & MU4 & HB4 & HR4 & HE4 & WM4 & MI4 & ST4).
  subst ms'. ret_even.
  assert (HRZ : SP + 0x150 <> 0) by (unfold MID_STACK, PARSE_STACK in *; zl).
  destruct (MemB_parse m3 m4 ev' H3 MU4 HB4 (HR4 HRZ) HE4 WM4 MI4 ST4) as [MB4 H504].
  eapply after_parse; [apply land_arg; [exact HNL | unfold MID_STACK, PARSE_STACK in *; zl] | exact HF4 | exact MB4 | exact H504].
Qed.

End Head.

(** ** headamp_check_contract from the callee contracts and expect_of's piece *)
Theorem head_holds :
  memset_contract -> reac_headamp_prop_parse_result_contract ->
  check_no_overrun_contract -> check_count_contract -> check_cells_valid_contract ->
  expect_stmt ->
  check_object_contract -> check_cells_contract -> check_keys_contract -> check_refusal_contract ->
  headamp_check_contract.
Proof.
  intros MSET PARSE CKNO CKCNT CKCV EXP CKO CKC CKK CKR. unfold headamp_check_contract.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    inp junk nl cap pp pod out lo ev can -> Hout Houta -> -> -> -> -> -> Hnl Hcap H50 H58 HPPB Hpod Hpoda HPODB
    HOUTC HROMO HSEP1 HSEP2 HSEP3 HOLO HPODLO HPPLO HST HLO HSPA HROM HERR HED HGOT HGUARD HGD1 HGD2 HF HMI HTM.
  pose proof HST as (HLO0 & HSPT & _).
  pose proof (bytes_at_bound rsegs m pp _ HPPB) as [HPP0 _].
  destruct (rw_cells_bound rsegs m _ _ HERR) as [HE1 HE2]. cbn [cells_size csize] in HE2.
  change (Z.of_nat (4 + 0)) with 4 in HE2.
  eapply head_ok with (sp := sp) (gp := gp) (tp := tp) (m := m) (inp := inp) (nl := nl) (cap := cap) (pp := pp)
    (pod := pod) (out := out) (lo := lo) (ev0 := ev) (can := can) (junk := junk).
  all: first [ eassumption | (split; lia) | (unfold FRAME_LOCALS in *; lia) ].
Qed.
