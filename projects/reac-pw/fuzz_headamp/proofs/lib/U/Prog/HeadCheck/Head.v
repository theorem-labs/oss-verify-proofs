(** The walk of reac-pw/fuzz_headamp's LLVMFuzzerTestOneInput (UBSan) over segment M03 outside expect_of: from
    malloc(out)'s return (0x14118) through memset(out, 0xa5), res := 0x5a x 12, the parse, the &out[cap] check
    (0x14160, not taken), check_no_overrun, check_count, check_cells_valid and the corrupt test (0x1418c); expect_of
    with the store of x->rc (0x14198 -> 0x14784) is taken from U/Prog/HeadCheck/Cut.v's [expect_stmt]; then
    check_object, check_cells, and for rc >= 0 check_keys and check_refusal (0x14784 -> 0x147c0); then first's size
    (0x147c0 -> 0x147dc). Against headamp_check_contract (U/Prog/LLVMFuzzerTestOneInput_c.v), with the callee
    contracts and expect_stmt as Section hypotheses: the plain walk (Prog/HeadCheck/Head.v) with the UBSan pcs,
    registers and cells (res at sp + 0x178, x at sp + 0xb8, the cells sp + 0x10 = 1 - null, sp + 0x68 =
    &pp->n_ent, sp + 0x70 = pp, sp + 0x78 = &pp->len) and the UBSan check contracts (4-aligned res and x). Section
    Head fixes the contract's frame (sp, gp, tp, the entry memory m), the input inp (the record r = head_rec inp),
    the null flag nl, cap, pp, pod, out, lo, errno's first value and the SSP guard; QH is the contract's
    postcondition. Walked backwards: QH_done (0x147dc), first_ok (0x147c0), checks_ok (0x14784), corrupt_ok
    (0x1418c), after_parse (0x1415c), head_ok (0x14118). The four checks against x pass because on an uncorrupted
    record the parse's answer is expect_model (Pod/Headamp.v parse_props_build, U/Prog/HeadSites.v site_spine), which
    expect_stmt leaves in x; the other three pass from the parse contract's answer alone (parse_props_total). *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Sem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac FP.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Lib Require ZBridge.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U Require MemNorm.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Import Cursor Model Layout Spa Headamp.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Spec Require Import HeadBytes.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.Prog Require Import memset_c reac_headamp_prop_parse_result_c
  check_no_overrun_c check_count_c check_cells_valid_c check_object_c check_cells_c check_keys_c check_refusal_c
  SlotInv LLVMFuzzerTestOneInput_c HeadSites.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Prog.HeadCheck Require Import Facts.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.Prog.HeadCheck Require Import Cut.
Import ListNotations.
Open Scope Z_scope.

Ltac ret_even := rewrite ret_pc_even by (first [lia | reflexivity]).
(* The section's separation facts are disjunctions; they stay folded as Facts.v's [or_h] so that lia does not split
   them all at once, and [zl] opens one of them when lia alone fails. *)
Ltac zl0 := unfold FRAME_LOCALS, MID_STACK, PARSE_STACK, OUT_LEN, head_len, NEAR_STACK, CHECK_CELLS_FRAME in *; lia.
Ltac zl := first [ zl0
                 | match goal with H : or_h _ _ |- _ =>
                     let H' := fresh "Hor" in pose proof H as H'; unfold or_h in H'; destruct H'; zl0 end ].
Ltac dj := cbn [disjoint_from]; repeat split; zl.

(** ** Arithmetic and byte facts *)
Lemma rc_cases : forall rc, -1 <= rc <= 9 ->
  rc = -1 \/ rc = 0 \/ rc = 1 \/ rc = 2 \/ rc = 3 \/ rc = 4 \/ rc = 5 \/ rc = 6 \/ rc = 7 \/ rc = 8 \/ rc = 9.
Proof. intros rc H. lia. Qed.

(** `neg a0,s8; and s5,a0,s1` with s8 = 1 - null: the parse's props argument (null ? NULL : pod). *)
Lemma neg_and_arg : forall nl pod, 0 <= nl <= 1 -> 0 <= pod < 2^64 ->
  Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 0) - bv_unsigned (Z_to_bv 64 (1 - nl)))))
                     (bv_unsigned (Z_to_bv 64 pod)))
  = Z_to_bv 64 (if nl =? 1 then 0 else pod).
Proof.
  intros nl pod Hn Hp. rewrite (unsigned_lit pod) by lia.
  assert (C : nl = 0 \/ nl = 1) by lia. destruct C as [-> | ->]; cbn [Z.eqb].
  - change (bv_unsigned (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 0) - bv_unsigned (Z_to_bv 64 (1 - 0)))))
      with (Z.ones 64). rewrite Z.land_comm, Z.land_ones by lia.
    rewrite Z.mod_small by lia. reflexivity.
  - change (bv_unsigned (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 0) - bv_unsigned (Z_to_bv 64 (1 - 1))))) with 0.
    rewrite Z.land_0_l. reflexivity.
Qed.

(** sp + k is 4-aligned for a 16-aligned sp and 4 | k. *)
Lemma mod4_add : forall x k, x mod 16 = 0 -> k mod 4 = 0 -> (x + k) mod 4 = 0.
Proof.
  intros x k H Hk. apply (proj1 (Z.mod_divide x 16 ltac:(lia))) in H. destruct H as [j ->].
  apply (proj1 (Z.mod_divide k 4 ltac:(lia))) in Hk. destruct Hk as [i ->].
  replace (j * 16 + i * 4) with ((4 * j + i) * 4) by ring. apply Z.mod_mul. lia.
Qed.

(** `not a1,s3; bltu a1,s0` at 0x1415c: the &out[cap] check (~out < 3 cap) is not taken while out + 3 cap < 2^64. *)
Lemma not_ltu_out : forall out k, 0 <= out -> 0 <= k -> out + k < 2^64 ->
  bv_ltu (Z_to_bv 64 (Z.lxor (bv_unsigned (Z_to_bv 64 out)) 18446744073709551615)) (Z_to_bv 64 k) = false.
Proof.
  intros out k H1 H2 H3. rewrite (unsigned_lit out) by lia. rewrite ZBridge.zb_lxor_ones by lia.
  rewrite ltu_u by lia. apply Z.ltb_ge. lia.
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

Lemma lo_sp : lo + 512 <= SP.
Proof. zl. Qed.

Lemma ea_facts : or_h (EA + 4 <= lo) (SP + FRAME_LOCALS <= EA) /\ or_h (EA + 4 <= pod) (pod + LEN <= EA) /\
  or_h (EA + 4 <= out) (out + L <= EA) /\ or_h (EA + 4 <= pp) (pp + POD_PROPS <= EA).
Proof. pose proof HED as H. cbn [disjoint_from] in H. destruct H as (A & B & C & D & _). unfold or_h. auto. Qed.

Lemma got_facts : or_h (PARSE_SSP_GOT + 8 <= lo) (SP + FRAME_LOCALS <= PARSE_SSP_GOT) /\
  or_h (PARSE_SSP_GOT + 8 <= out) (out + L <= PARSE_SSP_GOT) /\
  or_h (PARSE_SSP_GOT + 8 <= EA) (EA + 4 <= PARSE_SSP_GOT).
Proof. pose proof HGD1 as H. cbn [disjoint_from] in H. destruct H as (A & B & C & _). unfold or_h. auto. Qed.

Lemma guard_facts : or_h (PARSE_SSP_GUARD + 8 <= lo) (SP + FRAME_LOCALS <= PARSE_SSP_GUARD) /\
  or_h (PARSE_SSP_GUARD + 8 <= out) (out + L <= PARSE_SSP_GUARD) /\
  or_h (PARSE_SSP_GUARD + 8 <= EA) (EA + 4 <= PARSE_SSP_GUARD).
Proof. pose proof HGD2 as H. cbn [disjoint_from] in H. destruct H as (A & B & C & _). unfold or_h. auto. Qed.

Lemma L_range : 3 <= L <= 30.
Proof. zl. Qed.

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
    bytes_at rsegs m' (SP + 0x70) (le8 (Z_to_bv 64 pp)) /\
    rw_cells rsegs m' EA [C4 ev'] /\
    munch WH m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (SP + FRAME_LOCALS).

(** The memory after the parse: changed only in WH; the out block holds the parse's cells over 0xa5; the frame cells
    sp + 0x68 = &pp->n_ent, sp + 0x70 = pp, sp + 0x78 = &pp->len, res, errno a cell, the record in the pp block. *)
Definition MemB (m1 : word -> option byte) : Prop :=
  munch WH m m1 /\ wmono rsegs m m1 /\ mem_inv rsegs m1 /\ stk rsegs m1 lo (SP + FRAME_LOCALS) /\
  MemNorm.task_mem rsegs m1 /\
  bytes_at rsegs m1 out (out_after cap o) /\
  bytes_at rsegs m1 (SP + 0x68) (le8 (Z_to_bv 64 (pp + POD_NENT_OFF))) /\
  bytes_at rsegs m1 (SP + 0x70) (le8 (Z_to_bv 64 pp)) /\
  bytes_at rsegs m1 (SP + 0x78) (le8 (Z_to_bv 64 (pp + POD_LEN_OFF))) /\
  (exists ev', rw_cells rsegs m1 EA [C4 ev']) /\ bytes_at rsegs m1 (SP + 0x178) (ans_res_bytes o) /\
  bytes_at rsegs m1 pp (pp_bytes r).

Lemma MemB_mi : forall m1, MemB m1 -> mem_inv rsegs m1.
Proof. intros m1 (_ & _ & MI & _). exact MI. Qed.

Lemma MemB_stk : forall m1, MemB m1 -> stk rsegs m1 lo SP.
Proof.
  intros m1 (_ & _ & _ & ST & _). pose proof lo_sp. unfold FRAME_LOCALS in *.
  exact (proj1 (stk_split rsegs m1 lo SP (SP + 0x1d8) ST ltac:(zl))).
Qed.

(** A callee whose footprint is the k bytes below sp (a check's frame). *)
Lemma MemB_below : forall m1 m2 k, MemB m1 -> munch [(SP - k, SP)] m1 m2 -> wmono rsegs m1 m2 -> mem_inv rsegs m2 ->
  stk rsegs m2 lo SP -> 0 <= k <= MID_STACK -> MemB m2.
Proof.
  intros m1 m2 k (MU & WM & MI & ST & TM & HO & H68 & H70 & H78 & (ev & HE) & HR & HPP) MU2 WM2 MI2 ST2 Hk. facts.
  pose proof len_out_after as LO. pose proof len_res as LR. pose proof len_pp as LP.
  unfold MID_STACK, PARSE_STACK, FRAME_LOCALS in *.
  split.
  { apply (munch_trans WH m m1 m2 MU). eapply munch_weaken; [|exact MU2].
    intros x Hx. unfold WH in Hx. cbn [outside] in Hx |- *. destruct Hx as (O1 & O2 & O3 & _).
    unfold MID_STACK, PARSE_STACK, FRAME_LOCALS in O1. split; [zl | exact I]. }
  split; [exact (wmono_trans rsegs m m1 m2 WM WM2)|].
  split; [exact MI2|].
  split.
  { destruct (stk_split rsegs m1 lo SP (SP + 0x1d8) ST ltac:(zl)) as [_ ST1].
    apply (stk_merge rsegs m2 lo SP); [exact ST2 | | zl].
    apply (stk_transport_disjoint rsegs _ m1 m2 _ _ ST1 MU2 WM2). dj. }
  split.
  { apply (tm_call m1 m2 _ TM MU2). intros x Hx Hr. cbn [outside] in Hx.
    apply (stk_wv m1 lo (SP + 0x1d8)); [exact ST | zl]. }
  split; [eapply bytes_at_transport; [exact HO | exact MU2 | rewrite LO; dj]|].
  split; [eapply bytes_at_transport; [exact H68 | exact MU2 | rewrite length_le8; dj]|].
  split; [eapply bytes_at_transport; [exact H70 | exact MU2 | rewrite length_le8; dj]|].
  split; [eapply bytes_at_transport; [exact H78 | exact MU2 | rewrite length_le8; dj]|].
  split; [exists ev; eapply rw_cells_transport; [exact HE | exact MU2 | exact WM2 | cbn [cells_size csize]; dj]|].
  split; [eapply bytes_at_transport; [exact HR | exact MU2 | rewrite LR; dj]|].
  eapply bytes_at_transport; [exact HPP | exact MU2 | rewrite LP; unfold POD_PROPS in *; dj].
Qed.

(** expect_of's writes: the soft-float stack, its temporaries and x. *)
Lemma MemB_expect : forall m1 m2, MemB m1 -> munch (EXPECT_W SP) m1 m2 -> wmono rsegs m1 m2 -> mem_inv rsegs m2 ->
  MemNorm.task_mem rsegs m2 -> stk rsegs m2 lo (SP + FRAME_LOCALS) -> MemB m2.
Proof.
  intros m1 m2 (MU & WM & MI & ST & TM & HO & H68 & H70 & H78 & (ev & HE) & HR & HPP) MU2 WM2 MI2 TM2 ST2. facts.
  pose proof len_out_after as LO. pose proof len_res as LR. pose proof len_pp as LP.
  unfold EXPECT_W, NEAR_STACK, MID_STACK, PARSE_STACK, FRAME_LOCALS in *.
  split.
  { apply (munch_trans WH m m1 m2 MU). eapply munch_weaken; [|exact MU2].
    intros x Hx. unfold WH in Hx. cbn [outside] in Hx |- *. destruct Hx as (O1 & O2 & O3 & _).
    unfold MID_STACK, PARSE_STACK, FRAME_LOCALS in O1. repeat split; try exact I; zl. }
  split; [exact (wmono_trans rsegs m m1 m2 WM WM2)|].
  split; [exact MI2|]. split; [exact ST2|]. split; [exact TM2|].
  split; [eapply bytes_at_transport; [exact HO | exact MU2 | rewrite LO; dj]|].
  split; [eapply bytes_at_transport; [exact H68 | exact MU2 | rewrite length_le8; dj]|].
  split; [eapply bytes_at_transport; [exact H70 | exact MU2 | rewrite length_le8; dj]|].
  split; [eapply bytes_at_transport; [exact H78 | exact MU2 | rewrite length_le8; dj]|].
  split; [exists ev; eapply rw_cells_transport; [exact HE | exact MU2 | exact WM2 | cbn [cells_size csize]; dj]|].
  split; [eapply bytes_at_transport; [exact HR | exact MU2 | rewrite LR; dj]|].
  eapply bytes_at_transport; [exact HPP | exact MU2 | rewrite LP; unfold POD_PROPS in *; dj].
Qed.

(** ** 0x147dc: the contract's postcondition *)
Lemma QH_done : forall (ra t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
                       (F : bvmap 5 word) (fc : bv 32) (m1 : word -> option byte),
  a0 = Z_to_bv 64 (first_req (ans_rc o)) -> s8 = Z_to_bv 64 (3 * Z.max (ans_rc o) 0) ->
  frm0 fc -> MemB m1 ->
  evt rsegs QH
    (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 pod) a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 cap) (Z_to_bv 64 out) (Z_to_bv 64 L) (Z_to_bv 64 (if nl =? 1 then 0 else pod))
             (Z_to_bv 64 (ans_rc o)) s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x147dc) fc None m1 (seg_rom rsegs)).
Proof.
  intros ra t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1 -> -> HF
    (MU & WM & MI & ST & TM & HO & H68 & H70 & H78 & (ev & HE) & HR & HPP).
  apply evt_done. exists ra, t0, t1, t2, s0, a1, a2, a3, a4, a5, a6, a7, s7, s9, s10, s11, t3, t4, t5, t6, F, fc, m1, ev.
  split; [reflexivity|]. split; [exact HF|]. split; [exact HO|]. split; [exact H70|]. split; [exact HE|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI | exact ST].
Qed.

(** ** 0x147c0 .. 0x147d8: first's size s8 = 3 max(rc, 0), a0 = s8 + (s8 = 0) *)
Lemma first_ok : forall (ra t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
                        (F : bvmap 5 word) (fc : bv 32) (m1 : word -> option byte),
  frm0 fc -> MemB m1 ->
  evt rsegs QH
    (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 pod) a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 cap) (Z_to_bv 64 out) (Z_to_bv 64 L) (Z_to_bv 64 (if nl =? 1 then 0 else pod))
             (Z_to_bv 64 (ans_rc o)) s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x147c0) fc None m1 (seg_rom rsegs)).
Proof.
  intros ra t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1 HF MB.
  pose proof (MemB_mi m1 MB) as MI. pose proof rc_range as Hrc.
  (* 0x147c0 sgtz a0,s6; neg a0,a0; and s8,a0,s6; slli a0,s8,1; add s8,a0,s8; seqz a0,s8; add a0,s8,a0 *)
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

(** ** 0x14784 .. 0x147bc: check_object, check_cells, and for rc >= 0 check_keys, check_refusal *)
Lemma checks_ok : o = E0 ->
  forall (ra t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m2 : word -> option byte),
  frm0 fc -> MemB m2 -> bytes_at rsegs m2 (SP + 0xb8) (x_bytes E0) ->
  evt rsegs QH
    (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 pod) a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 cap) (Z_to_bv 64 out) (Z_to_bv 64 L) (Z_to_bv 64 (if nl =? 1 then 0 else pod))
             (Z_to_bv 64 (ans_rc o)) s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x14784) fc None m2 (seg_rom rsegs)).
Proof.
  intros EO ra t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m2 HF MB2 HX2. facts.
  destruct o_ok as [HO HK]. pose proof rc_range as Hrc.
  pose proof (answer_cells_len cap o HCAP HO) as [HL1 HL2].
  assert (HXA : (SP + 0xb8) mod 4 = 0) by (apply mod4_add; [exact HSPA | reflexivity]).
  assert (HRA : (SP + 0x178) mod 4 = 0) by (apply mod4_add; [exact HSPA | reflexivity]).
  pose proof MB2 as (_ & _ & MI2 & ST2 & _ & HO2 & _ & _ & _ & _ & HR2 & _).
  (* 0x14784 addi a1,sp,0x178; addi a2,sp,0xb8; mv a0,s6; jal check_object *)
  step. step. step. step.
  destruct (site_object m2 (SP + 0x178) (SP + 0xb8) cap o E0 HCAP HO EO HXA HRA HX2 HR2)
    as (R1 & HXA' & HXR & R2 & IFF & HRZ).
  eapply evt_cut.
  { eapply CKO with (rc := ans_rc o) (xrc := ans_rc E0); [reflexivity | exact R1 | | | exact R2 | exact IFF |].
    - rewrite unsigned_lit by zl. exact HXA.
    - rewrite unsigned_lit by zl. exact HXR.
    - intros Hm1. rewrite unsigned_lit by zl. exact (HRZ Hm1). }
  intros ms' (a0' & a2' & a3' & ->). ret_even.
  (* 0x14794 addi a2,sp,0xb8; mv a0,s3; mv a1,s6; jal check_cells *)
  step. step. step. step.
  destruct (site_cells m2 out (SP + 0xb8) lo cap o E0 HCAP HO EO HOLO HX2 (out_cells m2 out cap o HO2))
    as (R3 & HXR3 & HC3).
  eapply evt_cut.
  { eapply CKC with (lo := lo) (rc := ans_rc o) (cs := ans_cells o); [reflexivity | zl | | | | | | | | exact MI2].
    - rewrite unsigned_lit by zl. exact HXA.
    - rewrite unsigned_lit by zl. exact HXR3.
    - rewrite unsigned_lit by zl. zl.
    - rewrite !unsigned_lit by zl. exact HC3.
    - exact (MemB_stk m2 MB2).
    - zl.
    - intros a Ha. apply HROM. zl. }
  intros ms' (t0'' & t1'' & t2'' & a0'' & a1'' & a2'' & a3'' & a4'' & a5'' & a6'' & a7'' & m3 & E3 & MU3 & WM3 & MI3
              & ST3). subst ms'. ret_even.
  pose proof (MemB_below m2 m3 CHECK_CELLS_FRAME MB2 MU3 WM3 MI3 ST3 ltac:(zl)) as MB3.
  assert (HX3 : bytes_at rsegs m3 (SP + 0xb8) (x_bytes E0)).
  { eapply bytes_at_transport; [exact HX2 | exact MU3 |]. dj. }
  pose proof MB3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HR3 & _).
  (* 0x147a4 bltz s6 *)
  step. rewrite lts_s by zl.
  destruct (Z.ltb_spec (ans_rc o) 0) as [Hn|Hn]; cbv beta iota.
  { eapply first_ok; [exact HF | exact MB3]. }
  (* 0x147a8 addi a0,sp,0x178; addi a1,sp,0xb8; jal check_keys *)
  step. step. step.
  destruct (site_keys m3 (SP + 0x178) (SP + 0xb8) cap o E0 HCAP HO EO HX3 HR3) as (LK & K1 & K2).
  eapply evt_cut.
  { eapply CKK with (w := le4 (Z_to_bv 64 (ans_keys o))); [| | exact LK | |].
    - rewrite unsigned_lit by zl. exact HRA.
    - rewrite unsigned_lit by zl. exact HXA.
    - rewrite unsigned_lit by zl. exact K1.
    - rewrite unsigned_lit by zl. exact K2. }
  intros ms' (a0k & a1k & a2k & ->). ret_even.
  (* 0x147b4 addi a0,sp,0x178; addi a1,sp,0xb8; jal check_refusal *)
  step. step. step.
  destruct (site_refusal m3 (SP + 0x178) (SP + 0xb8) cap o E0 HCAP HO EO HX3 HR3) as (LF & F1 & F2).
  eapply evt_cut.
  { eapply CKR with (w := le4 (Z_to_bv 64 (ans_rf o))); [| | exact LF | |].
    - rewrite unsigned_lit by zl. exact HRA.
    - rewrite unsigned_lit by zl. exact HXA.
    - rewrite unsigned_lit by zl. exact F1.
    - rewrite unsigned_lit by zl. exact F2. }
  intros ms' (a0f & a1f & a2f & ->). ret_even.
  eapply first_ok; [exact HF | exact MB3].
Qed.

Hypothesis EXP : expect_stmt.

(** ** 0x1418c .. 0x14194: `if (!pp->corrupt)`; expect_of with x->rc (expect_stmt) and the checks against x, else
    first's size *)
Lemma corrupt_ok : forall (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s9 s10 s11 t3 t4 t5 t6 : word)
                          (F : bvmap 5 word) (fc : bv 32) (m1 : word -> option byte),
  frm0 fc -> MemB m1 ->
  evt rsegs QH
    (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 (3 * cap)) (Z_to_bv 64 pod) a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 cap) (Z_to_bv 64 out) (Z_to_bv 64 L) (Z_to_bv 64 (if nl =? 1 then 0 else pod))
             (Z_to_bv 64 (ans_rc o)) (Z_to_bv 64 (pp + POD_LEN_OFF)) (Z_to_bv 64 (1 - nl)) s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1418c) fc None m1 (seg_rom rsegs)).
Proof.
  intros ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s9 s10 s11 t3 t4 t5 t6 F fc m1 HF MB. facts.
  pose proof len_pp as LP.
  pose proof MB as (MU & WM & MI & ST & TM & HO & H68 & H70 & H78 & HE & HR & HPP).
  (* 0x1418c ld a0,0x68(sp); lw a0,4(a0); bnez a0 *)
  pose proof (read_le8 rsegs m1 (SP + 0x68) _ H68) as HR68. step. clear HR68.
  assert (HRD : ov_read_bytes rsegs m1 (wa (pp + POD_NENT_OFF + 4)) 4 = Some (le4 (Z_to_bv 64 (Z.b2z (corrupt r))))).
  { replace (pp + POD_NENT_OFF + 4) with (pp + 19736) by (unfold POD_NENT_OFF; lia).
    apply (read_field rsegs m1 pp r 19736 _ HPP r_wf);
      [exact (pp_corrupt r r_wf) | zl | unfold PP_SIZE; zl | destruct (corrupt r); cbn; zl]. }
  revert HRD. destruct (corrupt r) eqn:EC; cbn [Z.b2z]; intros HRD.
  { step. clear HRD. rewrite sx32_small by zl. step. if_true. eapply first_ok; [exact HF | exact MB]. }
  step. clear HRD. rewrite sx32_small by zl. step. if_false.
  assert (EO : o = E0) by exact (site_spine inp r (snd (pod_build inp)) cap (nl =? 1) (surjective_pairing _) EC HCAP).
  (* 0x14198 .. 0x14784: expect_of and x->rc *)
  eapply EXP with (r := r) (nl := nl) (cap := cap) (pp := pp) (lo := lo).
  - exact r_wf.
  - exact HNL.
  - exact HCAP.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - exact H68.
  - exact H70.
  - exact H78.
  - exact HPP.
  - exact HPP0.
  - exact HPPLO.
  - exact ST.
  - zl.
  - exact HSPA.
  - exact HROM.
  - exact HF.
  - exact MI.
  - exact TM.
  - intros ra' t0' t1' t2' s0' a0' a1' a2' a3' a4' a5' a6' a7' s7' s8' s9' s10' s11' t3' t4' t5' t6' F' fc' m5
      HF5 MU5 WM5 MI5 TM5 ST5 HX5.
    eapply checks_ok; [exact EO | exact HF5 | exact (MemB_expect m1 m5 MB MU5 WM5 MI5 TM5 ST5) | exact HX5].
Qed.

Hypothesis CKNO : check_no_overrun_contract.
Hypothesis CKCNT : check_count_contract.
Hypothesis CKCV : check_cells_valid_contract.

(** ** 0x1415c .. 0x14188: the &out[cap] check; rc := a0; check_no_overrun(out + 3 cap), check_count(rc, cap, &res),
    check_cells_valid(out, rc) *)
Lemma after_parse : forall (ra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s5 s6 s9 s10 s11 t3 t4 t5 t6 : word)
                           (F : bvmap 5 word) (fc : bv 32) (m1 : word -> option byte),
  s5 = Z_to_bv 64 (if nl =? 1 then 0 else pod) ->
  frm0 fc -> MemB m1 ->
  evt rsegs QH
    (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 (3 * cap)) (Z_to_bv 64 pod) (Z_to_bv 64 (ans_rc o))
             a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 cap) (Z_to_bv 64 out) (Z_to_bv 64 L) s5 s6
             (Z_to_bv 64 (pp + POD_LEN_OFF)) (Z_to_bv 64 (1 - nl)) s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1415c) fc None m1 (seg_rom rsegs)).
Proof.
  intros ra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s5 s6 s9 s10 s11 t3 t4 t5 t6 F fc m1 -> HF MB. facts.
  destruct o_ok as [HO HK]. pose proof rc_range as Hrc.
  pose proof MB as (MU & WM & MI & ST & TM & HO1 & H68 & H70 & H78 & HE & HR & HPP).
  assert (HRA : (SP + 0x178) mod 4 = 0) by (apply mod4_add; [exact HSPA | reflexivity]).
  (* 0x1415c not a1,s3; bltu a1,s0 (the &out[cap] check, not taken) *)
  step. step. rewrite not_ltu_out by zl. cbv beta iota.
  (* 0x14164 mv s6,a0; add a0,s3,s0; jal check_no_overrun *)
  step. step. step.
  eapply evt_cut.
  { eapply CKNO.
    match goal with |- bytes_at _ _ ?A _ => replace A with (out + 3 * cap) end;
      [exact (out_guard m1 out cap o HCAP HO HO1) |].
    rewrite ?(unsigned_lit out) by zl. rewrite ?(unsigned_lit (3 * cap)) by zl. symmetry. apply unsigned_lit. zl. }
  intros ms' ->. ret_even.
  (* 0x14170 addi a2,sp,0x178; mv a0,s6; mv a1,s2; jal check_count *)
  step. step. step. step.
  destruct (site_count m1 (SP + 0x178) cap o HCAP HO HK HRA HR) as (C1 & C2 & C3).
  eapply evt_cut.
  { eapply CKCNT with (rc := ans_rc o) (cap := cap) (keys := ans_keys o); [reflexivity | reflexivity | exact C1 | exact C2 |].
    rewrite unsigned_lit by zl. exact C3. }
  intros ms' (a1' & ->). ret_even.
  (* 0x14180 mv a0,s3; mv a1,s6; jal check_cells_valid *)
  step. step. step.
  destruct (site_cells_valid m1 out lo cap o HCAP HO HOLO (out_cells m1 out cap o HO1)) as (V1 & V2).
  eapply evt_cut.
  { eapply CKCV with (rc := ans_rc o) (cs := ans_cells o); [reflexivity | exact V1 |].
    rewrite unsigned_lit by zl. intros Hp. destruct (V2 Hp) as (V3 & V4 & V5 & _). split; [exact V3|]. split; [exact V4 | exact V5]. }
  intros ms' (t0' & a1'' & a2' & a3' & a4' & a5' & a6' & a7' & ->). ret_even.
  eapply corrupt_ok; [exact HF | exact MB].
Qed.

(** ** The entry memory and the head before the parse *)
Variable junk : list byte.
Hypothesis HMI : mem_inv rsegs m.
Hypothesis HTM : MemNorm.task_mem rsegs m.
Hypothesis HST : stk rsegs m lo (SP + FRAME_LOCALS).
Hypothesis H10m : bytes_at rsegs m (SP + 0x10) (le8 (Z_to_bv 64 (1 - nl))).
Hypothesis H68m : bytes_at rsegs m (SP + 0x68) (le8 (Z_to_bv 64 (pp + POD_NENT_OFF))).
Hypothesis H70m : bytes_at rsegs m (SP + 0x70) (le8 (Z_to_bv 64 pp)).
Hypothesis H78m : bytes_at rsegs m (SP + 0x78) (le8 (Z_to_bv 64 (pp + POD_LEN_OFF))).
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
  bytes_at rsegs m1 (SP + 0x10) (le8 (Z_to_bv 64 (1 - nl))) /\
  bytes_at rsegs m1 (SP + 0x68) (le8 (Z_to_bv 64 (pp + POD_NENT_OFF))) /\
  bytes_at rsegs m1 (SP + 0x70) (le8 (Z_to_bv 64 pp)) /\
  bytes_at rsegs m1 (SP + 0x78) (le8 (Z_to_bv 64 (pp + POD_LEN_OFF))) /\ bytes_at rsegs m1 pp (pp_bytes r) /\
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
  split; [eapply bytes_at_transport; [exact H10m | exact MU | rewrite length_le8; dj]|].
  split; [eapply bytes_at_transport; [exact H68m | exact MU | rewrite length_le8; dj]|].
  split; [eapply bytes_at_transport; [exact H70m | exact MU | rewrite length_le8; dj]|].
  split; [eapply bytes_at_transport; [exact H78m | exact MU | rewrite length_le8; dj]|].
  split; [eapply bytes_at_transport; [exact HPPm | exact MU | rewrite LP; unfold POD_PROPS in *; dj]|].
  split; [eapply bytes_at_transport; [exact HPODm | exact MU | rewrite len_buf; dj]|].
  split; [eapply rw_cells_transport; [exact HERRm | exact MU | exact WM | cbn [cells_size csize]; dj]|].
  split; [eapply bytes_at_transport; [exact HGOTm | exact MU | rewrite length_le8; dj]|].
  eapply bytes_at_transport; [exact HGUARDm | exact MU | rewrite length_le8; dj].
Qed.

Lemma MemH0_store_ok : forall m1 a (n : nat), MemH0 m1 -> SP + 0x80 <= a -> a + Z.of_nat n <= SP + FRAME_LOCALS ->
  store_ok rsegs m1 (wa a) n = true.
Proof.
  intros m1 a n (_ & _ & _ & ST & _) H1 H2. unfold FRAME_LOCALS in *.
  exact (stk_store_ok rsegs m1 lo (SP + 0x1d8) a n ST ltac:(zl) H2).
Qed.

Lemma MemH0_store : forall m1 a bs, MemH0 m1 -> store_ok rsegs m1 (wa a) (length bs) = true ->
  SP + 0x80 <= a -> a + Z.of_nat (length bs) <= SP + FRAME_LOCALS -> MemH0 (write_to_mem m1 (wa a) bs).
Proof.
  intros m1 a bs (MU & WM & MI & ST & TM & HO & HW & H10 & H68 & H70 & H78 & HPP & HPD & HE & HG1 & HG2) HS H1 H2.
  facts. pose proof L_range as HL. pose proof len_pp as LP. pose proof len_bounds as LB.
  unfold MID_STACK, PARSE_STACK, FRAME_LOCALS in *.
  split; [apply munch_write; [exact MU | zl | zl | cbn [inside]; left; zl]|].
  split; [apply wmono_write; exact WM|].
  split; [apply mem_inv_store; [exact MI | exact HS]|].
  split; [apply stk_write; [exact ST | zl | zl]|].
  split; [apply task_mem_write; [exact TM | exact HS]|].
  split; [apply bytes_at_write_other; [exact HO | zl | zl | rewrite repeat_length; zl]|].
  split; [apply wr_at_write; exact HW|].
  split; [apply bytes_at_write_other; [exact H10 | zl | zl | rewrite length_le8; zl]|].
  split; [apply bytes_at_write_other; [exact H68 | zl | zl | rewrite length_le8; zl]|].
  split; [apply bytes_at_write_other; [exact H70 | zl | zl | rewrite length_le8; zl]|].
  split; [apply bytes_at_write_other; [exact H78 | zl | zl | rewrite length_le8; zl]|].
  split; [apply bytes_at_write_other; [exact HPP | zl | zl | rewrite LP; unfold POD_PROPS in *; zl]|].
  split; [apply bytes_at_write_other; [exact HPD | zl | zl | rewrite len_buf; zl]|].
  split; [apply rw_cells_frame; [exact HE | zl | zl | cbn [cells_size csize]; zl]|].
  split; [apply bytes_at_write_other; [exact HG1 | zl | zl | rewrite length_le8; zl]|].
  apply bytes_at_write_other; [exact HG2 | zl | zl | rewrite length_le8; zl].
Qed.

(** The parse's premises at 0x14158 (U/Prog/HeadSites.v site_parse_args's form, res = sp + 0x178). *)
Lemma parse_args_here : forall m1, MemH0 m1 -> parse_args m1 lo SP tp pod out cap (SP + 0x178) (buf r) ev0 can.
Proof.
  intros m1 (MU & WM & MI & ST & TM & HO & HW & H10 & H68 & H70 & H78 & HPP & HPD & HE & HG1 & HG2). facts.
  pose proof L_range as HL. pose proof len_bounds as LB. destruct (buf_header r r_wf) as (_ & _ & HU & _).
  unfold MID_STACK, PARSE_STACK, FRAME_LOCALS, OUT_LEN, head_len in *.
  unfold parse_args.
  refine (conj HPD (conj HPOD (conj HPODA (conj _ (conj HU (conj HPODLO (conj HCAP (conj HOUT (conj HW
    (conj HOLO (conj _ (conj _ (conj HE (conj _ (conj _ (conj HG1 (conj HG2 (conj _ _)))))))))))))))))).
  - zl.
  - zl.
  - right. split; [exact (stk_wr_at rsegs m1 lo (SP + 0x1d8) (SP + 0x178) 12 ST ltac:(zl) ltac:(zl) ltac:(zl))|].
    split; [apply mod4_add; [exact HSPA | reflexivity] | zl].
  - cbn [disjoint_from]. repeat split; zl.
  - right. cbn [disjoint_from]. repeat split; zl.
  - unfold parse_space. replace (SP + 0x178 =? 0) with false by (symmetry; apply Z.eqb_neq; zl).
    cbn [app disjoint_from]. repeat split; zl.
  - unfold parse_space. replace (SP + 0x178 =? 0) with false by (symmetry; apply Z.eqb_neq; zl).
    cbn [app disjoint_from]. repeat split; zl.
Qed.

(** The memory after the parse, from its post (n cells written, res at sp + 0x178). *)
Lemma MemB_parse : forall m1 m2 ev', MemH0 m1 ->
  munch (parse_writes SP out (Z.of_nat (length (ans_cells o))) EA (SP + 0x178)) m1 m2 ->
  bytes_at rsegs m2 out (ha_cells_bytes (ans_cells o)) -> bytes_at rsegs m2 (SP + 0x178) (ans_res_bytes o) ->
  rw_cells rsegs m2 EA [C4 ev'] -> wmono rsegs m1 m2 -> mem_inv rsegs m2 -> stk rsegs m2 lo SP ->
  MemB m2.
Proof.
  intros m1 m2 ev' (MU & WM & MI & ST & TM & HO & HW & H10 & H68 & H70 & H78 & HPP & HPD & HE & HG1 & HG2)
    MU2 HC2 HR2 HE2 WM2 MI2 ST2. facts.
  destruct o_ok as [HOK _]. destruct (answer_cells_len cap o HCAP HOK) as [_ HLc].
  pose proof L_range as HL. pose proof len_pp as LP. pose proof len_res as LR.
  assert (HR0 : (SP + 0x178 =? 0) = false) by (apply Z.eqb_neq; zl).
  unfold parse_writes in MU2. rewrite HR0 in MU2. cbn [app] in MU2.
  unfold MID_STACK, PARSE_STACK, FRAME_LOCALS in *.
  assert (HE0' : 0 <= PARSE_ERRNO tp /\ PARSE_ERRNO tp + 4 <= 2^64) by exact HE0.
  split.
  - apply (munch_trans WH m m1 m2); [eapply munch_weaken; [|exact MU]|eapply munch_weaken; [|exact MU2]];
      intros x Hx; unfold WH in Hx; cbn [outside] in Hx |- *; destruct Hx as (O1 & O2 & O3 & _);
      unfold MID_STACK, PARSE_STACK, FRAME_LOCALS in O1; repeat split; try exact I; zl.
  - split; [exact (wmono_trans rsegs m m1 m2 WM WM2)|].
    split; [exact MI2|].
    split.
    { destruct (stk_split rsegs m1 lo SP (SP + 0x1d8) ST ltac:(zl)) as [_ ST1].
      apply (stk_merge rsegs m2 lo SP); [exact ST2 | | zl].
      apply (stk_transport rsegs _ m1 m2 SP (SP + 0x1d8) ST1 MU2 WM2). intros x Hx.
      destruct (Z_lt_le_dec x (SP + 0x178)) as [X1|X1]; [left; cbn [outside]; repeat split; try exact I; zl|].
      destruct (Z_lt_le_dec x (SP + 0x184)) as [X2|X2]; [right | left; cbn [outside]; repeat split; try exact I; zl].
      apply (bytes_at_some rsegs m2 (SP + 0x178) _ x HR2); rewrite LR; [intros a Ha; apply HROM | ]; zl. }
    split.
    { apply (tm_call m1 m2 _ TM MU2). intros x Hx Hr. cbn [outside] in Hx.
      destruct (Z_lt_le_dec x EA) as [Y1|Y1]; [|destruct (Z_lt_le_dec x (EA + 4)) as [Y2|Y2]].
      2: { destruct HE as [_ HEW]. cbn [cells_size csize] in HEW. apply (wr_wv m1 _ _ x HEW). zl. }
      all: destruct (Z_lt_le_dec x lo) as [X2|X2];
        [ apply (wr_wv m1 out L x HW); zl
        | destruct (Z_lt_le_dec x (SP + 0x1d8)) as [X3|X3];
          [ apply (stk_wv m1 lo (SP + 0x1d8)); [exact ST | zl] | exfalso; zl ] ]. }
    split.
    { apply (out_after_parse m1 m2 _ out cap o HOK HCAP HO MU2 HC2). cbn [disjoint_from].
      unfold OUT_LEN in *. repeat split; zl. }
    split; [eapply bytes_at_transport; [exact H68 | exact MU2 | rewrite length_le8; cbn [disjoint_from]; repeat split; zl]|].
    split; [eapply bytes_at_transport; [exact H70 | exact MU2 | rewrite length_le8; cbn [disjoint_from]; repeat split; zl]|].
    split; [eapply bytes_at_transport; [exact H78 | exact MU2 | rewrite length_le8; cbn [disjoint_from]; repeat split; zl]|].
    split; [exists ev'; exact HE2|].
    split; [exact HR2|].
    eapply bytes_at_transport; [exact HPP | exact MU2 | rewrite LP; unfold POD_PROPS in *; cbn [disjoint_from]; repeat split; zl].
Qed.

Hypothesis MSET : memset_contract.
Hypothesis PARSE : reac_headamp_prop_parse_result_contract.

(** ** 0x14118 .. 0x14158: out <> 0; memset(out, 0xa5, 3 cap + 3); res := 0x5a x 12; s8 := 1 - null;
    s5 := null ? 0 : pod; rc := reac_headamp_prop_parse_result(s5, out, cap, &res) *)
Lemma head_ok : forall (ra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s3 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6 : word)
                       (F : bvmap 5 word) (fc : bv 32),
  frm0 fc ->
  evt rsegs QH
    (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 (3 * cap)) (Z_to_bv 64 pod) (Z_to_bv 64 out) a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 cap) s3 (Z_to_bv 64 L) s5 s6 (Z_to_bv 64 (pp + POD_LEN_OFF)) s8 s9 s10 s11
             t3 t4 t5 t6)
        F (Z_to_bv 64 HEAD_CHECK) fc None m (seg_rom rsegs)).
Proof.
  intros ra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s3 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6 F fc HF. facts.
  pose proof L_range as HL. pose proof len_bounds as LB.
  assert (HSPL : SP < 2^64) by zl.
  unfold HEAD_CHECK.
  (* 0x14118 beqz a0 *)
  step. rewrite eqb_u by zl. rewrite (proj2 (Z.eqb_neq _ _)) by zl. cbv beta iota.
  (* 0x1411c mv s3,a0; addi a1,zero,0xa5; mv a2,s4; jal memset *)
  step. step. step. step.
  eapply evt_cut.
  { eapply MSET with (junk := junk); [| exact HMI].
    rewrite (unsigned_lit out) by zl.
    rewrite (unsigned_lit L) by zl. exact HOUTm. }
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 & -> & MU1 & WM1
              & MI1 & RW1).
  rewrite (unsigned_lit out) in MU1, RW1 by zl.
  rewrite (unsigned_lit L) in MU1, RW1 by zl. ret_even.
  assert (H1 : MemH0 m1) by (apply (MemH0_memset m1 MU1 WM1 MI1); exact RW1).
  clear MU1 WM1 RW1.
  (* 0x1412c auipc a0; ld a0,0x3ec(a0): the 0x5a word of .rodata 0x10518 *)
  step. step.
  (* 0x14134 sd a0,0x178(sp) *)
  assert (HS1 : store_ok rsegs m1 (wa (SP + 376)) 8 = true)
    by (apply (MemH0_store_ok m1 (SP + 376) 8 H1); zl).
  step.
  match goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem m1 ?A ?BS) _) =>
    change A with (wa (SP + 376));
    assert (H2 : MemH0 (write_to_mem m1 (wa (SP + 376)) BS))
      by (apply MemH0_store; [exact H1 | rewrite length_le8; exact HS1 | zl | rewrite length_le8; zl]);
    revert H2; generalize (write_to_mem m1 (wa (SP + 376)) BS) as m2; intros m2 H2
  end.
  clear HS1 MI1.
  (* 0x14138 sw a0,0x180(sp) *)
  assert (HS2 : store_ok rsegs m2 (wa (SP + 384)) 4 = true)
    by (apply (MemH0_store_ok m2 (SP + 384) 4 H2); zl).
  step.
  match goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem m2 ?A ?BS) _) =>
    change A with (wa (SP + 384));
    assert (H3 : MemH0 (write_to_mem m2 (wa (SP + 384)) BS))
      by (apply MemH0_store; [exact H2 | rewrite length_le4; exact HS2 | zl | rewrite length_le4; zl]);
    revert H3; generalize (write_to_mem m2 (wa (SP + 384)) BS) as m3; intros m3 H3
  end.
  clear HS2 H2 H1.
  pose proof H3 as (_ & _ & MI3 & ST3 & _ & _ & _ & H103 & _).
  (* 0x1413c ld s8,0x10(sp) *)
  pose proof (read_le8 rsegs m3 (SP + 0x10) _ H103) as HR10. step. clear HR10.
  (* 0x14140 neg a0,s8; and s5,a0,s1; addi a3,sp,0x178; mv a0,s5; mv a1,s3; mv a2,s2; jal parse_result *)
  step. step. step. step. step. step. step.
  eapply evt_cut.
  { eapply PARSE with (null := nl =? 1) (lo := lo) (P := pod) (O := out) (cap := cap) (R := SP + 0x178)
                      (bs := buf r) (ev := ev0) (can := can).
    - apply neg_and_arg; [exact HNL | zl].
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - exact (parse_args_here m3 H3).
    - unfold FRAME_LOCALS in *. exact (proj1 (stk_split rsegs m3 lo SP (SP + 0x1d8) ST3 ltac:(zl))).
    - unfold MID_STACK in HLO. exact HLO.
    - intros a Ha. apply HROM. zl.
    - exact HF.
    - exact MI3. }
  intros ms' (t0'' & t1'' & t2'' & a1'' & a2'' & a3'' & a4'' & a5'' & a6'' & a7'' & t3'' & t4'' & t5'' & t6'' & F4 & fc4
              & m4 & ev' & E4 & HF4 & MU4 & HB4 & HR4 & HE4 & WM4 & MI4 & ST4).
  subst ms'. ret_even.
  assert (HRZ : SP + 0x178 <> 0) by zl.
  pose proof (MemB_parse m3 m4 ev' H3 MU4 HB4 (HR4 HRZ) HE4 WM4 MI4 ST4) as MB4.
  eapply after_parse; [apply neg_and_arg; [exact HNL | zl] | exact HF4 | exact MB4].
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
    inp junk nl cap pp pod out lo ev can -> Hout Houta -> -> -> -> -> Hnl Hcap H10 H68 H70 H78 HPPB Hpod Hpoda
    HPODB HOUTC HROMO HSEP1 HSEP2 HSEP3 HOLO HPODLO HPPLO HST HLO HSPA HROM HERR HED HGOT HGUARD HGD1 HGD2 HF HMI HTM.
  pose proof HST as (HLO0 & HSPT & _).
  pose proof (bytes_at_bound rsegs m pp _ HPPB) as [HPP0 _].
  destruct (rw_cells_bound rsegs m _ _ HERR) as [HE1 HE2]. cbn [cells_size csize] in HE2.
  change (Z.of_nat (4 + 0)) with 4 in HE2.
  eapply head_ok with (sp := sp) (gp := gp) (tp := tp) (m := m) (inp := inp) (nl := nl) (cap := cap) (pp := pp)
    (pod := pod) (out := out) (lo := lo) (ev0 := ev) (can := can) (junk := junk).
  all: first [ eassumption | (unfold or_h; eassumption) | (split; lia) | (unfold FRAME_LOCALS in *; lia) ].
Qed.
