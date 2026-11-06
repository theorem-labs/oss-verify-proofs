(** The call sites of fuzz_headamp's own contracts in LLVMFuzzerTestOneInput (plain): for each callee contract, a
    closed lemma that gives its premises at the call from what the caller's walk holds there (the callee contracts
    before it and the harness's own memory), or the statement of what the caller's segment must show there. The main
    walk (Prog/LLVMFuzzerTestOneInput_c.v's headamp_check_contract / headamp_plain_contract) applies them; nothing of
    a binary is proved here.
    - [parse_answer]: the parse's answer on every pod of the harness (corrupted too) is answer_ok with keys <= 16384
      (Pod/Headamp.v parse_props_total, parse_props_keys).
    - [site_spine]: on an uncorrupted record, for either null flag, the parse's answer is expect_of's
      (parse_props_build): the four checks that compare with x (check_object, check_cells, check_keys, check_refusal).
    - [site_no_overrun] 0x140c8, [site_count] 0x140d8, [site_cells_valid] 0x140e4: from parse_props_total and the
      parse contract's post alone.
    - [site_object] 0x14118, [site_cells] 0x14128, [site_keys] 0x14138, [site_refusal] 0x14144: from site_spine, the
      parse's post and x = x_bytes (expect_model null cap r), which M03's walk shows for expect_of's code.
    - [site_plain] 0x141b0: from both parses' posts (the same answer) and memcpy(first, out, 3rc)'s post.
    - [parse_site_check] 0x140bc, [parse_site_plain] 0x141a0: every premise of the parse contract at each call,
      from the premises of the evt that holds the call (headamp_check_contract, headamp_plain_contract: generic in
      sp, lo and tp) and what the code before the call leaves (memset(out, 0xa5), and at 0x140bc the res fill):
      [site_parse_core] for the memory, Pod/Spa.v buf_header with Pod/Model.v pod_build_wf for the pod's header,
      [site_null_mask] for a0. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame FP.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Import Cursor Model Spa Headamp.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Spec Require Import HeadBytes.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Prog Require Import reac_headamp_prop_parse_result_c.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Prog Require Import SlotInv LLVMFuzzerTestOneInput_c.
Import ListNotations.
Open Scope Z_scope.

Lemma bytes_at_at : forall m a b bs, a = b -> bytes_at rsegs m a bs -> bytes_at rsegs m b bs.
Proof. intros m a b bs -> H. exact H. Qed.

(** ** The answer on every pod *)
Lemma parse_answer : forall null bs cap, 0 <= cap -> Z.of_nat (length bs) <= 16384 ->
  answer_ok cap (parse_props (parse_arg null bs) cap) /\ 0 <= ans_keys (parse_props (parse_arg null bs) cap) <= 16384.
Proof.
  intros null bs cap Hc Hl. split; [apply parse_props_total; exact Hc|].
  pose proof (parse_props_keys (parse_arg null bs) cap) as HK.
  unfold ans_keys. destruct (parse_props (parse_arg null bs) cap) as [[rc cells] [[n keys] rf]].
  cbn [fst snd]. destruct null; cbn in HK; lia.
Qed.

Lemma answer_cells_len : forall cap o, 0 <= cap <= 9 -> answer_ok cap o ->
  (length (ans_cells o) <= X_CELLS)%nat /\ Z.of_nat (length (ans_cells o)) <= cap.
Proof.
  intros cap o Hc HO. apply answer_ok_parts in HO as [[(E1 & E2 & _) | (E1 & E2 & _)] _].
  - rewrite E2. cbn [length]. split; lia.
  - unfold X_CELLS. split; lia.
Qed.

(** ** The spine: the parse answers what expect_of expects on an uncorrupted record *)
Lemma site_spine : forall inp r rest cap (null : bool), pod_build inp = (r, rest) -> corrupt r = false ->
  0 <= cap <= 9 -> parse_props (parse_arg null (buf r)) cap = expect_model null cap r.
Proof. intros inp r rest cap null H1 H2 H3. exact (parse_props_build inp r rest cap null H1 H2 H3). Qed.

(** ** 0x140c8 check_no_overrun(&out[cap]): the guard cell after memset(out, 0xa5) and the parse *)
Lemma site_no_overrun : forall m m' lo sp tp P O cap R bs ev can n,
  parse_args m lo sp tp P O cap R bs ev can -> lo + PARSE_STACK <= sp ->
  bytes_at rsegs m O (repeat GUARD_BYTE (Z.to_nat (3 * (cap + 1)))) -> 0 <= n <= cap ->
  munch (parse_writes sp O n (PARSE_ERRNO tp) R) m m' ->
  bytes_at rsegs m' (O + 3 * cap) (repeat GUARD_BYTE 3).
Proof.
  intros m m' lo sp tp P O cap R bs ev can n HA Hst HB Hn HM.
  destruct HA as (_ & _ & _ & _ & _ & _ & Hcap & _ & _ & HOlo & _ & HR & _ & HEd & _).
  assert (E : Z.to_nat (3 * (cap + 1)) = (Z.to_nat (3 * cap) + 3)%nat) by lia.
  rewrite E, repeat_app in HB. apply bytes_at_app in HB as [_ HB].
  rewrite repeat_length, Z2Nat.id in HB by lia.
  eapply bytes_at_transport; [exact HB | exact HM |].
  change (Z.of_nat (length (repeat GUARD_BYTE 3))) with 3.
  cbn [disjoint_from] in HEd. unfold parse_writes, PARSE_STACK in *.
  destruct (R =? 0) eqn:ER; cbn [app disjoint_from].
  - repeat split; lia.
  - apply Z.eqb_neq in ER. destruct HR as [HR | (_ & _ & HR)]; [contradiction|].
    repeat split; lia.
Qed.

(** ** 0x140d8 check_count(rc, cap, &res) *)
Lemma site_count : forall m R cap o, 0 <= cap <= 9 -> answer_ok cap o -> 0 <= ans_keys o <= 16384 ->
  bytes_at rsegs m R (ans_res_bytes o) ->
  -1 <= ans_rc o <= cap /\ cap < 2 ^ 31 /\
  (0 <= ans_rc o ->
     bytes_at rsegs m R (le4 (Z_to_bv 64 (ans_rc o)) ++ le4 (Z_to_bv 64 (ans_keys o))) /\
     ans_rc o <= ans_keys o < 2 ^ 31).
Proof.
  intros m R cap o Hc HO HK HB. apply answer_ok_parts in HO as [[(E1 & _ & _ & _ & _) | (E1 & _ & E3 & E4)] _].
  - split; [lia|]. split; [lia|]. intros H. exfalso. lia.
  - split; [lia|]. split; [lia|]. intros _. split; [|lia].
    unfold ans_res_bytes, ha_res_bytes in HB. rewrite E3, app_assoc in HB.
    apply bytes_at_app in HB as [HB _]. exact HB.
Qed.

(** ** 0x140e4 check_cells_valid(out, rc) *)
Lemma site_cells_valid : forall m O lo cap o, 0 <= cap <= 9 -> answer_ok cap o -> O + 3 * (cap + 1) <= lo ->
  bytes_at rsegs m O (ha_cells_bytes (ans_cells o)) ->
  - 2 ^ 31 <= ans_rc o < 2 ^ 31 /\
  (0 < ans_rc o ->
     bytes_at rsegs m O (ha_cells_bytes (ans_cells o)) /\ Z.of_nat (length (ans_cells o)) = ans_rc o /\
     Forall cell_valid (ans_cells o) /\ O + 3 * ans_rc o <= lo).
Proof.
  intros m O lo cap o Hc HO Hlo HB. apply answer_ok_parts in HO as [[(E1 & _) | (E1 & E2 & _)] HV].
  - split; [lia|]. intros H. exfalso. lia.
  - split; [lia|]. intros _. split; [exact HB|]. split; [lia|]. split; [exact HV | lia].
Qed.

(** ** 0x14118 check_object(rc, &res, &x) *)
Lemma site_object : forall m R X cap o e, 0 <= cap <= 9 -> answer_ok cap o -> o = e ->
  bytes_at rsegs m X (x_bytes e) -> bytes_at rsegs m R (ans_res_bytes o) ->
  - 2 ^ 31 <= ans_rc o < 2 ^ 31 /\
  bytes_at rsegs m X (le4 (Z_to_bv 64 (ans_rc e))) /\ - 2 ^ 31 <= ans_rc e < 2 ^ 31 /\
  (ans_rc o = -1 <-> ans_rc e = -1) /\
  (ans_rc o = -1 -> bytes_at rsegs m R (ha_res_bytes 0 0 0)).
Proof.
  intros m R X cap o e Hc HO <- HX HR.
  unfold x_bytes in HX. apply bytes_at_app in HX as [HX _].
  apply answer_ok_parts in HO as [[(E1 & _ & E3 & E4 & E5) | (E1 & _)] _].
  - split; [lia|]. split; [exact HX|]. split; [lia|]. split; [tauto|].
    intros _. unfold ans_res_bytes in HR. rewrite E3, E4, E5 in HR. exact HR.
  - split; [lia|]. split; [exact HX|]. split; [lia|]. split; [tauto|]. intros H. exfalso. lia.
Qed.

(** ** 0x14128 check_cells(out, rc, &x) (the bound rc <= 10 is the UBSan twin's) *)
Lemma site_cells : forall m O X lo cap o e, 0 <= cap <= 9 -> answer_ok cap o -> o = e -> O + 3 * (cap + 1) <= lo ->
  bytes_at rsegs m X (x_bytes e) -> bytes_at rsegs m O (ha_cells_bytes (ans_cells o)) ->
  - 2 ^ 31 <= ans_rc o <= 10 /\ bytes_at rsegs m X (le4 (Z_to_bv 64 (ans_rc o))) /\
  (0 < ans_rc o ->
     Z.of_nat (length (ans_cells o)) = ans_rc o /\ Forall cell_bytes_ok (ans_cells o) /\
     bytes_at rsegs m O (ha_cells_bytes (ans_cells o)) /\ O + 3 * ans_rc o <= lo /\
     bytes_at rsegs m (X + 4) (x_cells_bytes (ans_cells o))).
Proof.
  intros m O X lo cap o e Hc HO <- Hlo HX HB.
  unfold x_bytes in HX. apply bytes_at_app in HX as [HX0 HX1]. apply bytes_at_app in HX1 as [HX1 _].
  rewrite length_le4 in HX1. change (Z.of_nat 4) with 4 in HX1.
  apply answer_ok_parts in HO as [[(E1 & _) | (E1 & E2 & _)] HV].
  - split; [lia|]. split; [exact HX0|]. intros H. exfalso. lia.
  - split; [lia|]. split; [exact HX0|]. intros _.
    split; [lia|]. split; [revert HV; apply Forall_impl; exact cell_valid_bytes_ok|].
    split; [exact HB|]. split; [lia | exact HX1].
Qed.

(** The res and x words of keys and refusal. *)
Lemma res_words : forall m R o, bytes_at rsegs m R (ans_res_bytes o) ->
  bytes_at rsegs m (R + 4) (le4 (Z_to_bv 64 (ans_keys o))) /\ bytes_at rsegs m (R + 8) (le4 (Z_to_bv 64 (ans_rf o))).
Proof.
  intros m R o HR. unfold ans_res_bytes, ha_res_bytes in HR.
  rewrite !bytes_at_app in HR. destruct HR as (_ & HK & HF). rewrite !length_le4 in HK, HF.
  split; [exact HK|]. eapply bytes_at_at; [|exact HF]. cbn. lia.
Qed.

Lemma x_words : forall m X cap e, 0 <= cap <= 9 -> answer_ok cap e -> bytes_at rsegs m X (x_bytes e) ->
  bytes_at rsegs m (X + X_KEYS_OFF) (le4 (Z_to_bv 64 (ans_keys e))) /\
  bytes_at rsegs m (X + X_RF_OFF) (le4 (Z_to_bv 64 (ans_rf e))).
Proof.
  intros m X cap e Hc HO HX. destruct (answer_cells_len cap e Hc HO) as [HL _]. unfold X_CELLS in HL.
  unfold x_bytes in HX. rewrite !bytes_at_app in HX. destruct HX as (_ & _ & _ & HR).
  rewrite length_le4, length_x_cells_bytes, repeat_length in HR. unfold X_CELLS in HR.
  change (Z.of_nat 4) with 4 in HR.
  assert (E12 : Z.of_nat (12 * length (ans_cells e)) + Z.of_nat (12 * (10 - length (ans_cells e))) = 120).
  { rewrite <- Nat2Z.inj_add. replace (12 * length (ans_cells e) + 12 * (10 - length (ans_cells e)))%nat
      with 120%nat by lia. reflexivity. }
  assert (HR' : bytes_at rsegs m (X + 124) (ans_res_bytes e)) by (eapply bytes_at_at; [|exact HR]; lia).
  destruct (res_words m (X + 124) e HR') as [HK HF].
  split; [eapply bytes_at_at; [|exact HK] | eapply bytes_at_at; [|exact HF]]; unfold X_KEYS_OFF, X_RF_OFF; lia.
Qed.

(** ** 0x14138 check_keys(&res, &x), 0x14144 check_refusal(&res, &x) *)
Lemma site_keys : forall m R X cap o e, 0 <= cap <= 9 -> answer_ok cap o -> o = e ->
  bytes_at rsegs m X (x_bytes e) -> bytes_at rsegs m R (ans_res_bytes o) ->
  length (le4 (Z_to_bv 64 (ans_keys o))) = 4%nat /\
  bytes_at rsegs m (R + 4) (le4 (Z_to_bv 64 (ans_keys o))) /\
  bytes_at rsegs m (X + X_KEYS_OFF) (le4 (Z_to_bv 64 (ans_keys o))).
Proof.
  intros m R X cap o e Hc HO <- HX HR. split; [apply length_le4|].
  split; [exact (proj1 (res_words m R o HR)) | exact (proj1 (x_words m X cap o Hc HO HX))].
Qed.

Lemma site_refusal : forall m R X cap o e, 0 <= cap <= 9 -> answer_ok cap o -> o = e ->
  bytes_at rsegs m X (x_bytes e) -> bytes_at rsegs m R (ans_res_bytes o) ->
  length (le4 (Z_to_bv 64 (ans_rf o))) = 4%nat /\
  bytes_at rsegs m (R + 8) (le4 (Z_to_bv 64 (ans_rf o))) /\
  bytes_at rsegs m (X + X_RF_OFF) (le4 (Z_to_bv 64 (ans_rf o))).
Proof.
  intros m R X cap o e Hc HO <- HX HR. split; [apply length_le4|].
  split; [exact (proj2 (res_words m R o HR)) | exact (proj2 (x_words m X cap o Hc HO HX))].
Qed.

(** ** 0x141b0 check_plain(plain, rc, out, first): a0 = a1 because both parse contracts answer the same
    parse_props (parse_arg null bs) cap on the same bytes and cap; the bytes: *)
Lemma site_plain : forall m O Fst lo cap o, 0 <= cap <= 9 -> answer_ok cap o ->
  O + 3 * (cap + 1) <= lo -> Fst + 3 * Z.max 0 (ans_rc o) <= lo ->
  bytes_at rsegs m O (ha_cells_bytes (ans_cells o)) -> bytes_at rsegs m Fst (ha_cells_bytes (ans_cells o)) ->
  - 2 ^ 31 <= ans_rc o < 2 ^ 31 /\
  (0 < ans_rc o ->
     Z.of_nat (length (ha_cells_bytes (ans_cells o))) = 3 * ans_rc o /\
     bytes_at rsegs m O (ha_cells_bytes (ans_cells o)) /\ O + 3 * ans_rc o <= lo /\
     bytes_at rsegs m Fst (ha_cells_bytes (ans_cells o)) /\ Fst + 3 * ans_rc o <= lo).
Proof.
  intros m O Fst lo cap o Hc HO Hlo Hflo HB HF.
  apply answer_ok_parts in HO as [[(E1 & _) | (E1 & E2 & _)] _].
  - split; [lia|]. intros H. exfalso. lia.
  - split; [lia|]. intros Hp. rewrite length_ha_cells_bytes.
    split; [lia|]. split; [exact HB|]. split; [lia|]. split; [exact HF | lia].
Qed.

(** ** 0x140bc / 0x141a0: the parse contracts' premises at the two calls
    Both evts are generic in sp, lo and tp (lo + MID_STACK <= sp, sp 16-aligned). Each site lemma takes the premises
    of its evt that the call needs, verbatim, and what the code between the evt's start and the call leaves: m1, the
    memory at the call, differs from the evt's m only in out (memset(out, 0xa5, 3 cap + 3)) and, at 0x140bc, in the
    frame's locals (the res fill, 0x1409c-0x140a0); every writable byte stays writable; mem_inv holds of m1. It gives
    every premise of the parse contract there with null := nl =? 1, P = pod, bs = buf (head_rec inp) (so the
    answer is head_ans nl cap inp), O = out, R = sp + HARNESS_RES (0x140bc) or 0 (0x141a0). *)
Definition HARNESS_RES : Z := 0x150.

(** a0 at 0x140bc: 0x140a4 `addi a0,s7,-1`, 0x140a8 `and s5,a0,s1` (0x140b0 `mv a0,s5`), s7 = nl, s1 = pod. *)
Lemma site_null_mask : forall nl pod, 0 <= nl <= 1 -> 0 <= pod < 2 ^ 64 ->
  v_and (v_addi (Z_to_bv 64 nl) (-1)) (Z_to_bv 64 pod) = Z_to_bv 64 (if nl =? 1 then 0 else pod).
Proof.
  intros nl pod Hn Hp. unfold v_and, v_addi. rewrite !Z_to_bv_unsigned.
  rewrite (bv_wrap_small 64 pod) by (change (bv_modulus 64) with (2 ^ 64); lia).
  assert (E : nl = 0 \/ nl = 1) by lia. destruct E as [-> | ->].
  - replace (bv_wrap 64 (bv_wrap 64 0 + -1)) with (Z.ones 64) by reflexivity.
    rewrite Z.land_comm, Z.land_ones by lia. rewrite Z.mod_small by lia. reflexivity.
  - replace (bv_wrap 64 (bv_wrap 64 1 + -1)) with 0 by reflexivity. rewrite Z.land_0_l. reflexivity.
Qed.

(** The memory premises at either call, from the evt premises both evts share and m1; R is res: 0, or 12 bytes in
    the frame's locals, 4-aligned. *)
Lemma site_parse_core : forall (m m1 : word -> option byte) (sp tp : word) (inp junk : list byte)
    (cap pod out lo R : Z) (ev can : word) (fc : bv 32),
  0 <= cap <= 9 ->
  0 < pod -> pod mod 16 = 0 -> bytes_at rsegs m pod (buf (head_rec inp)) ->
  0 < out -> rw_cells rsegs m out [CB (Z.to_nat (OUT_LEN cap)) junk] ->
  (out + OUT_LEN cap <= pod \/ pod + head_len inp <= out) ->
  out + OUT_LEN cap <= lo -> pod + head_len inp <= lo ->
  stk rsegs m lo (bv_unsigned sp + FRAME_LOCALS) -> lo + MID_STACK <= bv_unsigned sp ->
  (forall a, lo <= a < bv_unsigned sp + FRAME_LOCALS -> seg_rom rsegs (wa a) = None) ->
  rw_cells rsegs m (PARSE_ERRNO tp) [C4 ev] ->
  disjoint_from [(lo, bv_unsigned sp + FRAME_LOCALS); (pod, pod + head_len inp); (out, out + OUT_LEN cap)]
    (PARSE_ERRNO tp) 4 ->
  bytes_at rsegs m PARSE_SSP_GOT (le8 (Z_to_bv 64 PARSE_SSP_GUARD)) ->
  bytes_at rsegs m PARSE_SSP_GUARD (le8 can) ->
  disjoint_from [(lo, bv_unsigned sp + FRAME_LOCALS); (out, out + OUT_LEN cap);
                 (PARSE_ERRNO tp, PARSE_ERRNO tp + 4)] PARSE_SSP_GOT 8 ->
  disjoint_from [(lo, bv_unsigned sp + FRAME_LOCALS); (out, out + OUT_LEN cap);
                 (PARSE_ERRNO tp, PARSE_ERRNO tp + 4)] PARSE_SSP_GUARD 8 ->
  frm0 fc ->
  (R = 0 \/ (bv_unsigned sp <= R /\ R + 12 <= bv_unsigned sp + FRAME_LOCALS /\ R mod 4 = 0)) ->
  munch [(out, out + OUT_LEN cap); (bv_unsigned sp, bv_unsigned sp + FRAME_LOCALS)] m m1 ->
  wmono rsegs m m1 -> mem_inv rsegs m1 ->
  parse_args m1 lo (bv_unsigned sp) tp pod out cap R (buf (head_rec inp)) ev can /\
  stk rsegs m1 lo (bv_unsigned sp) /\ lo + PARSE_STACK <= bv_unsigned sp /\
  (forall a, lo <= a < bv_unsigned sp -> seg_rom rsegs (wa a) = None) /\
  frm0 fc /\ mem_inv rsegs m1.
Proof.
  intros m m1 sp tp inp junk cap pod out lo R ev can fc Hcap Hp0 Hp16 HP Ho0 HO HOP HOlo HPlo Hstk Hroom Hrom
    HE HEd HG1 HG2 HG1d HG2d Hfrm HR HM HW Hinv.
  pose proof (pod_build_wf inp (head_rec inp) (snd (pod_build inp)) (surjective_pairing _)) as Hwf.
  destruct (buf_header (head_rec inp) Hwf) as (_ & _ & Htop & Hl).
  unfold parse_args. unfold MID_STACK in *. unfold head_len, OUT_LEN, FRAME_LOCALS, PARSE_STACK in *.
  set (bs := buf (head_rec inp)) in *.
  set (SP := bv_unsigned sp) in *.
  set (E := PARSE_ERRNO tp) in *.
  pose proof Hstk as (Sk0 & Sk1 & Sk).
  assert (HOw : wr_at rsegs m1 out (3 * (cap + 1))).
  { destruct HO as [_ HOw]. cbn [cells_size csize] in HOw. rewrite Nat.add_0_r, Z2Nat.id in HOw by lia.
    eapply wr_at_transport; [exact HOw | exact HW]. }
  assert (HP1 : bytes_at rsegs m1 pod bs).
  { eapply bytes_at_transport; [exact HP | exact HM |]. cbn [disjoint_from]. repeat split; lia. }
  assert (HE1 : rw_cells rsegs m1 E [C4 ev]).
  { eapply rw_cells_transport; [exact HE | exact HM | exact HW |].
    change (Z.of_nat (cells_size [C4 ev])) with 4. cbn [disjoint_from] in HEd |- *. repeat split; lia. }
  assert (HG1' : bytes_at rsegs m1 PARSE_SSP_GOT (le8 (Z_to_bv 64 PARSE_SSP_GUARD))).
  { eapply bytes_at_transport; [exact HG1 | exact HM |]. rewrite length_le8. change (Z.of_nat 8) with 8.
    cbn [disjoint_from] in HG1d |- *. repeat split; lia. }
  assert (HG2' : bytes_at rsegs m1 PARSE_SSP_GUARD (le8 can)).
  { eapply bytes_at_transport; [exact HG2 | exact HM |]. rewrite length_le8. change (Z.of_nat 8) with 8.
    cbn [disjoint_from] in HG2d |- *. repeat split; lia. }
  assert (HSP : forall X, disjoint_from [(lo, SP + 0x1b0); (out, out + 3 * (cap + 1)); (E, E + 4)] X 8 ->
                          disjoint_from (parse_space lo SP out cap E R) X 8).
  { intros X HX. unfold parse_space. cbn [disjoint_from] in HX.
    destruct (Z.eqb_spec R 0) as [HR0 | HR0]; cbn [app disjoint_from]; repeat split; lia. }
  assert (HRw : R = 0 \/ (wr_at rsegs m1 R 12 /\ R mod 4 = 0 /\ SP <= R)).
  { destruct HR as [HR | (HR1 & HR2 & HR3)]; [left; exact HR | right].
    split; [|split; [exact HR3 | exact HR1]].
    apply (wr_at_transport rsegs m m1 R 12); [|exact HW].
    split; [lia|]. split; [lia|]. intros i Hi. apply (proj1 (Sk (R + i) ltac:(lia))). }
  assert (HRE : R = 0 \/ disjoint_from [(E, E + 4)] R 12).
  { destruct HR as [HR | (HR1 & HR2 & HR3)]; [left; exact HR | right].
    cbn [disjoint_from] in HEd |- *. repeat split; lia. }
  assert (Hstk1 : stk rsegs m1 lo SP).
  { destruct (stk_split rsegs m lo SP (SP + 0x1b0) Hstk ltac:(lia)) as [Hs _].
    eapply stk_transport_disjoint; [exact Hs | exact HM | exact HW |]. cbn [disjoint_from]. repeat split; lia. }
  split; [|split; [exact Hstk1 | split; [lia | split; [intros a Ha; apply Hrom; lia | split; [exact Hfrm | exact Hinv]]]]].
  refine (conj HP1 (conj Hp0 (conj Hp16 (conj _ (conj Htop (conj HPlo (conj Hcap (conj Ho0 (conj HOw
    (conj HOlo (conj HOP (conj HRw (conj HE1 (conj _ (conj HRE (conj HG1' (conj HG2' (conj (HSP _ HG1d)
    (HSP _ HG2d))))))))))))))))))).
  - lia.
  - cbn [disjoint_from] in HEd |- *. repeat split; lia.
Qed.

(** 0x140bc `jal reac_headamp_prop_parse_result` (M03, headamp_check_contract): the parse contract's premises.
    a0 by site_null_mask from s7 and s1; a1 = s3 = out (0x14084 `mv s3,a0` with a0 = out, 0x140b4 `mv a1,s3`);
    a2 = s2 = cap (0x140b8 `mv a2,s2`); a3 = sp + 0x150 (0x140ac `addi a3,sp,0x150`). *)
Lemma parse_site_check :
  forall (sp tp s1 s7 : word) (m m1 : word -> option byte) (inp junk : list byte) (nl cap pp pod out lo : Z)
         (ev can : word) (fc : bv 32),
    0 < out -> s1 = Z_to_bv 64 pod -> s7 = Z_to_bv 64 nl -> 0 <= nl <= 1 -> 0 <= cap <= 9 ->
    0 < pod -> pod mod 16 = 0 -> bytes_at rsegs m pod (buf (head_rec inp)) ->
    rw_cells rsegs m out [CB (Z.to_nat (OUT_LEN cap)) junk] ->
    (out + OUT_LEN cap <= pod \/ pod + head_len inp <= out) ->
    out + OUT_LEN cap <= lo -> pod + head_len inp <= lo ->
    stk rsegs m lo (bv_unsigned sp + FRAME_LOCALS) -> lo + MID_STACK <= bv_unsigned sp -> bv_unsigned sp mod 16 = 0 ->
    (forall a, lo <= a < bv_unsigned sp + FRAME_LOCALS -> seg_rom rsegs (wa a) = None) ->
    rw_cells rsegs m (PARSE_ERRNO tp) [C4 ev] ->
    disjoint_from [(lo, bv_unsigned sp + FRAME_LOCALS); (pod, pod + head_len inp); (out, out + OUT_LEN cap);
                   (pp, pp + POD_PROPS)] (PARSE_ERRNO tp) 4 ->
    bytes_at rsegs m PARSE_SSP_GOT (le8 (Z_to_bv 64 PARSE_SSP_GUARD)) ->
    bytes_at rsegs m PARSE_SSP_GUARD (le8 can) ->
    disjoint_from [(lo, bv_unsigned sp + FRAME_LOCALS); (out, out + OUT_LEN cap);
                   (PARSE_ERRNO tp, PARSE_ERRNO tp + 4)] PARSE_SSP_GOT 8 ->
    disjoint_from [(lo, bv_unsigned sp + FRAME_LOCALS); (out, out + OUT_LEN cap);
                   (PARSE_ERRNO tp, PARSE_ERRNO tp + 4)] PARSE_SSP_GUARD 8 ->
    frm0 fc ->
    munch [(out, out + OUT_LEN cap); (bv_unsigned sp, bv_unsigned sp + FRAME_LOCALS)] m m1 ->
    wmono rsegs m m1 -> mem_inv rsegs m1 ->
    v_and (v_addi s7 (-1)) s1 = Z_to_bv 64 (if nl =? 1 then 0 else pod) /\
    v_addi sp HARNESS_RES = Z_to_bv 64 (bv_unsigned sp + HARNESS_RES) /\
    parse_args m1 lo (bv_unsigned sp) tp pod out cap (bv_unsigned sp + HARNESS_RES) (buf (head_rec inp)) ev can /\
    stk rsegs m1 lo (bv_unsigned sp) /\ lo + PARSE_STACK <= bv_unsigned sp /\
    (forall a, lo <= a < bv_unsigned sp -> seg_rom rsegs (wa a) = None) /\
    frm0 fc /\ mem_inv rsegs m1.
Proof.
  intros sp tp s1 s7 m m1 inp junk nl cap pp pod out lo ev can fc Ho0 -> -> Hnl Hcap Hp0 Hp16 HP HO HOP HOlo HPlo
    Hstk Hroom Hsp16 Hrom HE HEd HG1 HG2 HG1d HG2d Hfrm HM HW Hinv.
  split.
  { apply site_null_mask; [exact Hnl|]. pose proof Hstk as (_ & Hs1 & _).
    unfold head_len, MID_STACK, PARSE_STACK, FRAME_LOCALS in *. lia. }
  split; [reflexivity|].
  apply (site_parse_core m m1 sp tp inp junk cap pod out lo (bv_unsigned sp + HARNESS_RES) ev can fc); try assumption.
  - cbn [disjoint_from] in HEd |- *. tauto.
  - right. unfold FRAME_LOCALS, HARNESS_RES. split; [lia|]. split; [lia|].
    pose proof (Z.div_mod (bv_unsigned sp) 16 ltac:(lia)) as Hdm. rewrite Hsp16, Z.add_0_r in Hdm.
    rewrite Hdm. replace (16 * (bv_unsigned sp / 16) + 0x150) with ((4 * (bv_unsigned sp / 16) + 84) * 4) by lia.
    apply Z.mod_mul. lia.
Qed.

(** 0x141a0 `jal reac_headamp_prop_parse` (M04b, headamp_plain_contract; res = NULL): the parse contract's
    premises. a0 = s5 = Z_to_bv 64 (if nl =? 1 then 0 else pod), a1 = s3 = out, a2 = s2 = cap (0x14194-0x1419c,
    `mv`): the evt's premises on s5, s3 and s2. *)
Lemma parse_site_plain :
  forall (sp tp : word) (m m1 : word -> option byte) (inp junk : list byte) (nl cap pod out first lo : Z)
         (ev can : word) (fc : bv 32),
    0 <= cap <= 9 ->
    0 < pod -> pod mod 16 = 0 -> bytes_at rsegs m pod (buf (head_rec inp)) ->
    0 < out -> rw_cells rsegs m out [CB (Z.to_nat (OUT_LEN cap)) junk] ->
    (out + OUT_LEN cap <= pod \/ pod + head_len inp <= out) ->
    out + OUT_LEN cap <= lo -> pod + head_len inp <= lo ->
    stk rsegs m lo (bv_unsigned sp + FRAME_LOCALS) -> lo + MID_STACK <= bv_unsigned sp ->
    (forall a, lo <= a < bv_unsigned sp + FRAME_LOCALS -> seg_rom rsegs (wa a) = None) ->
    rw_cells rsegs m (PARSE_ERRNO tp) [C4 ev] ->
    disjoint_from [(lo, bv_unsigned sp + FRAME_LOCALS); (pod, pod + head_len inp); (out, out + OUT_LEN cap);
                   (first, first + 3 * Z.max (ans_rc (head_ans nl cap inp)) 0)] (PARSE_ERRNO tp) 4 ->
    bytes_at rsegs m PARSE_SSP_GOT (le8 (Z_to_bv 64 PARSE_SSP_GUARD)) ->
    bytes_at rsegs m PARSE_SSP_GUARD (le8 can) ->
    disjoint_from [(lo, bv_unsigned sp + FRAME_LOCALS); (out, out + OUT_LEN cap);
                   (PARSE_ERRNO tp, PARSE_ERRNO tp + 4)] PARSE_SSP_GOT 8 ->
    disjoint_from [(lo, bv_unsigned sp + FRAME_LOCALS); (out, out + OUT_LEN cap);
                   (PARSE_ERRNO tp, PARSE_ERRNO tp + 4)] PARSE_SSP_GUARD 8 ->
    frm0 fc ->
    munch [(out, out + OUT_LEN cap)] m m1 -> wmono rsegs m m1 -> mem_inv rsegs m1 ->
    parse_args m1 lo (bv_unsigned sp) tp pod out cap 0 (buf (head_rec inp)) ev can /\
    stk rsegs m1 lo (bv_unsigned sp) /\ lo + PARSE_STACK <= bv_unsigned sp /\
    (forall a, lo <= a < bv_unsigned sp -> seg_rom rsegs (wa a) = None) /\
    frm0 fc /\ mem_inv rsegs m1.
Proof.
  intros sp tp m m1 inp junk nl cap pod out first lo ev can fc Hcap Hp0 Hp16 HP Ho0 HO HOP HOlo HPlo Hstk Hroom
    Hrom HE HEd HG1 HG2 HG1d HG2d Hfrm HM HW Hinv.
  apply (site_parse_core m m1 sp tp inp junk cap pod out lo 0 ev can fc); try assumption.
  - cbn [disjoint_from] in HEd |- *. tauto.
  - left. reflexivity.
  - apply (munch_weaken [(out, out + OUT_LEN cap)]); [|exact HM]. intros x Hx. cbn [outside] in Hx |- *. tauto.
Qed.
