(** Satisfiability of the premises of the callee contracts (plain image): for each contract of Prog/*_c.v with
    a premise, its premises hold together at one concrete state of rate's real instance: the plain image's loaded
    segments (rsegs), main's own stack (entry sp W_S0 = 0x7ffffffef000, the slot's entry sp of the frame's start
    state, one page below the process entry sp 0x7fffffff0000 that lies in the start-up stack window [W_SP0_win]; the
    stack region [W_S0 - SLOT_STACK, W_S0) of FrameAPI; main's frame of 544 bytes, so main's sp at every call is
    W_S0 - 544), heap blocks below the frame's alloc_ceiling 0x7fffff7f0000 (role/pin SlotInvSat.v's W_ceil, the
    same start-up numbers), and the memory W_MEM: explicit bytes on the stack region, the pod block and the buf
    block, every other byte read from the image (None). Each lemma's conjunction is the contract's hypothesis list
    with `->` read as `/\` (generated from the contract text), at the witness its `let`s name; where main passes
    input-dependent values (r, hz, mask, buflen, the NULL flag, the pod bytes), the lemma holds for every such value:
    for the parse, [rate_prop_parse_contract_sat_all] holds for every pod of 8 .. 5440 bytes whose top size word is
    its length - 8, which [pod_top] shows of every record pod_build makes, corrupted or not, and
    [fit_prop_parse_all] applies the contract there for both values of the NULL flag ([rate_prop_parse_contract_sat]
    is its instance at the 8-byte pod).
    The contracts without a premise (reac_rate_bit, reac_rate_is_closed, reac_rate_best_drivable,
    reac_rate_cfg_decide) need no lemma.

    This file proves no program function. It adds no axiom and leaves no proof unfinished. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells FP.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib Require Import Img0 FrameAPI.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib Require MemNorm.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require YL0k.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Import Cursor Spa Model Nearest Rate RateCfg RateCsv.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Prog Require Import printf_facts_c snprintf_c.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Prog Require Import check_absent_c check_malformed_c
  reac_rate_refuse_code_c check_code_c check_list_c check_csv_c reac_rate_drivable_csv_c reac_rate_prop_parse_c.
Import ListNotations.
Open Scope Z_scope.

(** ** The instance *)
Definition W_SP0 : Z := 0x7fffffff0000.
Lemma W_SP0_win : sp_window_lo <= W_SP0 <= sp_window_hi.
Proof. unfold W_SP0, sp_window_lo, sp_window_hi. lia. Qed.
Definition W_S0 : Z := 0x7ffffffef000.
Definition W_LO : Z := W_S0 - SLOT_STACK.
Definition W_SP : Z := W_S0 - 544.
Definition W_POD : Z := 0x7fffff7e0000.
Definition W_BUF : Z := 0x7fffff7e0100.
Definition W_Q : Z := W_SP + 0x158.

Definition in_rng (lo n x : Z) : bool := (lo <=? x) && (x <? lo + n).

(** The stack region holds zeros, the pod block 8 zero bytes, the buf block the values bufc (0x5a past its end). *)
Definition W_MEM (bufc : list Z) (a : word) : option byte :=
  let x := bv_unsigned a in
  if in_rng W_LO SLOT_STACK x then Some (Z_to_bv 8 0)
  else if in_rng W_POD 8 x then Some (Z_to_bv 8 0)
  else if in_rng W_BUF 24 x then Some (Z_to_bv 8 (nth (Z.to_nat (x - W_BUF)) bufc 0x5a))
  else None.

Lemma bu64 : forall x, 0 <= x < 2 ^ 64 -> bv_unsigned (Z_to_bv 64 x) = x.
Proof. intros x Hx. apply wa_unsigned. exact Hx. Qed.

Lemma in_rng_t : forall lo n x, lo <= x < lo + n -> in_rng lo n x = true.
Proof. intros lo n x H. unfold in_rng. apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia. Qed.
Lemma in_rng_f : forall lo n x, ~ (lo <= x < lo + n) -> in_rng lo n x = false.
Proof.
  intros lo n x H. unfold in_rng. destruct (Z.leb_spec lo x); destruct (Z.ltb_spec x (lo + n)); cbn; auto; lia.
Qed.

Lemma W_MEM_stack : forall bufc x, W_LO <= x < W_S0 -> W_MEM bufc (wa x) = Some (Z_to_bv 8 0).
Proof.
  intros bufc x Hx. unfold W_MEM. rewrite wa_unsigned by (unfold W_LO, W_S0, SLOT_STACK in *; lia).
  rewrite in_rng_t by (unfold W_LO, W_S0, SLOT_STACK in *; lia). reflexivity.
Qed.

Lemma W_MEM_pod : forall bufc x, W_POD <= x < W_POD + 8 -> W_MEM bufc (wa x) = Some (Z_to_bv 8 0).
Proof.
  intros bufc x Hx. unfold W_MEM. rewrite wa_unsigned by (unfold W_POD in *; lia).
  rewrite in_rng_f by (unfold W_LO, W_S0, SLOT_STACK, W_POD in *; lia).
  rewrite in_rng_t by lia. reflexivity.
Qed.

Lemma W_MEM_buf : forall bufc x, W_BUF <= x < W_BUF + 24 ->
  W_MEM bufc (wa x) = Some (Z_to_bv 8 (nth (Z.to_nat (x - W_BUF)) bufc 0x5a)).
Proof.
  intros bufc x Hx. unfold W_MEM. rewrite wa_unsigned by (unfold W_BUF in *; lia).
  rewrite in_rng_f by (unfold W_LO, W_S0, SLOT_STACK, W_BUF in *; lia).
  rewrite in_rng_f by (unfold W_POD, W_BUF in *; lia).
  rewrite in_rng_t by lia. reflexivity.
Qed.

Lemma W_MEM_hi : forall bufc a b, W_MEM bufc a = Some b -> 0x60000 <= bv_unsigned a < W_S0.
Proof.
  intros bufc a b H. unfold W_MEM in H. unfold in_rng in H.
  destruct ((W_LO <=? bv_unsigned a) && (bv_unsigned a <? W_LO + SLOT_STACK)) eqn:E1.
  { apply andb_prop in E1 as [E1 E1']. apply Z.leb_le in E1. apply Z.ltb_lt in E1'.
    unfold W_LO, W_S0, SLOT_STACK in *. lia. }
  destruct ((W_POD <=? bv_unsigned a) && (bv_unsigned a <? W_POD + 8)) eqn:E2.
  { apply andb_prop in E2 as [E2 E2']. apply Z.leb_le in E2. apply Z.ltb_lt in E2'.
    unfold W_POD, W_S0 in *. lia. }
  destruct ((W_BUF <=? bv_unsigned a) && (bv_unsigned a <? W_BUF + 24)) eqn:E3; [|discriminate].
  apply andb_prop in E3 as [E3 E3']. apply Z.leb_le in E3. apply Z.ltb_lt in E3'. unfold W_BUF, W_S0 in *. lia.
Qed.

(** The image lies below 0x60000 (IMG_END = 0x50878). *)
Lemma W_top : forallb (fun s => Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? 0x60000) rsegs = true.
Proof. vm_compute. reflexivity. Qed.

Lemma W_rom_none : forall a, 0x60000 <= a < 2 ^ 64 -> seg_rom rsegs (wa a) = None.
Proof. intros a Ha. apply (YL0k.seg_rom_above rsegs 0x60000 (wa a) W_top). rewrite wa_unsigned; lia. Qed.

Lemma W_mem_inv : forall bufc, mem_inv rsegs (W_MEM bufc).
Proof.
  intros bufc a b H. apply W_MEM_hi in H. unfold ro_addr.
  rewrite (YL0k.find_segment_above rsegs 0x60000) by (exact W_top || lia). reflexivity.
Qed.

Lemma W_task : W_S0 < TASK_SIZE.
Proof. vm_compute. reflexivity. Qed.

Lemma W_task_mem : forall bufc, MemNorm.task_mem rsegs (W_MEM bufc).
Proof. intros bufc a b H. right. apply W_MEM_hi in H. pose proof W_task. lia. Qed.

Lemma W_stk : forall bufc lo hi, W_LO <= lo -> lo <= hi -> hi <= W_S0 -> stk rsegs (W_MEM bufc) lo hi.
Proof.
  intros bufc lo hi H1 H2 H3. unfold stk. split; [unfold W_LO, W_S0, SLOT_STACK in *; lia|].
  split; [unfold W_S0 in *; lia|]. intros a Ha.
  assert (W_MEM bufc (wa a) = Some (Z_to_bv 8 0)) as E by (apply W_MEM_stack; lia).
  split; [unfold wview; rewrite E; discriminate | exists (Z_to_bv 8 0); unfold mrd; rewrite E; reflexivity].
Qed.

Lemma W_stack_rom : forall a, W_LO <= a < W_S0 -> seg_rom rsegs (wa a) = None.
Proof. intros a Ha. apply W_rom_none. unfold W_LO, W_S0, SLOT_STACK in *. lia. Qed.

Lemma W_buf_bytes : forall bufc, (length bufc <= 24)%nat -> bytes_at rsegs (W_MEM bufc) W_BUF (csv_bytes bufc).
Proof.
  intros bufc Hl. unfold bytes_at. rewrite csv_bytes_length. split; [unfold W_BUF; lia|].
  split; [unfold W_BUF; lia|]. intros i Hi. unfold mrd.
  rewrite W_MEM_buf by lia. replace (Z.to_nat (W_BUF + Z.of_nat i - W_BUF)) with i by lia.
  unfold csv_bytes. rewrite nth_error_map. rewrite (nth_error_nth' bufc 0x5a) by exact Hi. reflexivity.
Qed.

Lemma W_buf_wr : forall bufc n, 0 <= n <= 24 -> wr_at rsegs (W_MEM bufc) W_BUF n.
Proof.
  intros bufc n Hn. unfold wr_at. split; [unfold W_BUF; lia|]. split; [unfold W_BUF; lia|].
  intros i Hi. unfold wview. rewrite W_MEM_buf by lia. discriminate.
Qed.

Lemma W_got_guard : forall bufc, bytes_at rsegs (W_MEM bufc) GOT_GUARD (le8 (Z_to_bv 64 GUARD)).
Proof.
  intros bufc. unfold bytes_at. assert (length (le8 (Z_to_bv 64 GUARD)) = 8%nat) as L by reflexivity.
  rewrite L. split; [unfold GOT_GUARD; lia|]. split; [unfold GOT_GUARD; lia|].
  intros i Hi. do 8 (destruct i as [|i]; [vm_compute; f_equal; apply bv_eq; reflexivity|]). lia.
Qed.

Lemma W_guard : forall bufc, bytes_at rsegs (W_MEM bufc) GUARD (le8 (Z_to_bv 64 0)).
Proof.
  intros bufc. unfold bytes_at. assert (length (le8 (Z_to_bv 64 0)) = 8%nat) as L by reflexivity.
  rewrite L. split; [unfold GUARD; lia|]. split; [unfold GUARD; lia|].
  intros i Hi. do 8 (destruct i as [|i]; [vm_compute; f_equal; apply bv_eq; reflexivity|]). lia.
Qed.

Lemma W_frm0 : frm0 (Z_to_bv 32 0).
Proof. unfold frm0. reflexivity. Qed.

Lemma W_SP_facts : W_LO + 6112 <= W_SP /\ W_SP < W_S0 /\ W_SP < 2 ^ 63 /\ 0x50878 <= W_LO /\ W_BUF + 24 <= W_LO /\
  W_POD + 8 <= W_LO /\ W_SP <= W_Q /\ W_Q + 4 <= W_S0 /\ W_Q mod 4 = 0 /\ W_POD mod 16 = 0.
Proof. unfold W_Q, W_LO, W_SP, W_S0, SLOT_STACK, W_BUF, W_POD. repeat split; (reflexivity || lia). Qed.

(** ** The lemmas, one per contract with a premise *)
Lemma check_absent_contract_sat :
  let a0 := Z_to_bv 64 0 in let a1 := Z_to_bv 64 0x5a5a5a5a in
    bv_unsigned a0 = 0 /\
    bv_unsigned a1 = 0x5a5a5a5a.
Proof.
  cbv zeta. split; reflexivity.
Qed.

Lemma check_malformed_contract_sat :
  let a0 := Z_to_bv 64 (-1) in let a1 := Z_to_bv 64 0x5a5a5a5a in
    bv_unsigned a0 = 2^64 - 1 /\
    bv_unsigned a1 = 0x5a5a5a5a.
Proof.
  cbv zeta. split; reflexivity.
Qed.

Lemma reac_rate_refuse_code_contract_sat :
  let m := W_MEM [] in
    mem_inv rsegs m.
Proof.
  cbv zeta. apply W_mem_inv.
Qed.

Lemma check_code_contract_sat :
  forall r, 0 <= r <= 4 ->
  let sp := Z_to_bv 64 W_SP in let a0 := Z_to_bv 64 (refuse_code_addr r) in let a1 := Z_to_bv 64 r in
  let m := W_MEM [] in let lo := W_LO in
    bv_unsigned a1 <= 4 /\
    a0 = Z_to_bv 64 (refuse_code_addr (bv_unsigned a1)) /\
    stk rsegs m lo (bv_unsigned sp) /\
    lo + CHECK_CODE_FRAME <= bv_unsigned sp /\
    (forall a, lo <= a < bv_unsigned sp -> seg_rom rsegs (wa a) = None) /\
    mem_inv rsegs m.
Proof.
  intros r Hr. cbv zeta. pose proof W_SP_facts as HW.
  assert (bv_unsigned (Z_to_bv 64 W_SP) = W_SP) as ES by (apply bu64; unfold W_SP, W_S0 in *; lia).
  rewrite bu64 by lia. rewrite ES.
  split; [lia|]. split; [reflexivity|].
  split; [apply W_stk; unfold W_LO, W_SP, W_S0, SLOT_STACK in *; lia|].
  split; [unfold CHECK_CODE_FRAME; unfold W_LO, W_SP, W_S0, SLOT_STACK in *; lia|].
  split; [intros a Ha; apply W_stack_rom; unfold W_LO, W_SP, W_S0, SLOT_STACK in *; lia|].
  apply W_mem_inv.
Qed.

Lemma check_list_contract_sat :
  forall a0 a3 : word,
  let sp := Z_to_bv 64 W_SP in let a1 := Z_to_bv 64 (rate_bit (bv_unsigned a0)) in
  let a2 := Z_to_bv 64 (rate_closed (bv_unsigned a0)) in let a4 := Z_to_bv 64 (rate_best (bv_unsigned a3)) in
  let m := W_MEM [] in let lo := W_LO in
    a1 = Z_to_bv 64 (rate_bit (bv_unsigned a0)) /\
    a2 = Z_to_bv 64 (rate_closed (bv_unsigned a0)) /\
    a4 = Z_to_bv 64 (rate_best (bv_unsigned a3)) /\
    stk rsegs m lo (bv_unsigned sp) /\
    lo + CHECK_LIST_FRAME <= bv_unsigned sp /\
    (forall a, lo <= a < bv_unsigned sp -> seg_rom rsegs (wa a) = None) /\
    mem_inv rsegs m.
Proof.
  intros a0 a3. cbv zeta. pose proof W_SP_facts as HW.
  assert (bv_unsigned (Z_to_bv 64 W_SP) = W_SP) as ES by (apply bu64; unfold W_SP, W_S0 in *; lia).
  rewrite ES.
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [apply W_stk; unfold W_LO, W_SP, W_S0, SLOT_STACK in *; lia|].
  split; [unfold CHECK_LIST_FRAME; unfold W_LO, W_SP, W_S0, SLOT_STACK in *; lia|].
  split; [intros a Ha; apply W_stack_rom; unfold W_LO, W_SP, W_S0, SLOT_STACK in *; lia|].
  apply W_mem_inv.
Qed.

Lemma check_csv_contract_sat :
  forall (a3 : word) (n : Z), 0 <= n <= 23 ->
  let bufc := if n =? 0 then [0x5a] else csv_cut (csv_list (bv_unsigned a3)) n ++ [0] in
  let sp := Z_to_bv 64 W_SP in let a0 := Z_to_bv 64 W_BUF in let a1 := Z_to_bv 64 n in
  let a2 := Z_to_bv 64 (Z.of_nat (length (csv_list (bv_unsigned a3)))) in
  let m := W_MEM bufc in let lo := W_LO in
  let S := bv_unsigned sp in let buf := bv_unsigned a0 in let n := bv_unsigned a1 in
  let L := csv_list (bv_unsigned a3) in
    bv_unsigned a2 = Z.of_nat (length L) /\
    n <= 23 /\
    (n = 0 -> bytes_at rsegs m buf [Z_to_bv 8 0x5a]) /\
    (0 < n -> bytes_at rsegs m buf (csv_bytes (csv_cut L n ++ [0]))) /\
    (buf + Z.max n 1 <= lo \/ S <= buf) /\
    stk rsegs m lo S /\
    lo + CHECK_CSV_FRAME <= S /\
    (forall a, lo <= a < S -> seg_rom rsegs (wa a) = None) /\
    mem_inv rsegs m.
Proof.
  intros a3 n Hn. cbv zeta. pose proof W_SP_facts as HW.
  assert (0 <= bv_unsigned a3) as H3 by (pose proof (bv_unsigned_in_range _ a3); lia).
  pose proof (csv_list_length (bv_unsigned a3) H3) as HL.
  assert (bv_unsigned (Z_to_bv 64 W_SP) = W_SP) as ES by (apply bu64; unfold W_SP, W_S0 in *; lia).
  assert (bv_unsigned (Z_to_bv 64 W_BUF) = W_BUF) as EB by (apply bu64; unfold W_BUF; lia).
  assert (bv_unsigned (Z_to_bv 64 n) = n) as EN by (apply bu64; lia).
  rewrite ES, EB, EN. rewrite bu64 by lia.
  split; [reflexivity|]. split; [lia|].
  split; [intros ->; exact (W_buf_bytes [0x5a] ltac:(cbn; lia))|].
  split; [intros Hp; replace (n =? 0) with false by (symmetry; apply Z.eqb_neq; lia);
          apply W_buf_bytes; rewrite length_app, csv_cut_length by lia; cbn [length]; lia|].
  split; [left; unfold W_LO, W_BUF, W_S0, SLOT_STACK in *; lia|].
  split; [apply W_stk; unfold W_LO, W_SP, W_S0, SLOT_STACK in *; lia|].
  split; [unfold CHECK_CSV_FRAME; unfold W_LO, W_SP, W_S0, SLOT_STACK in *; lia|].
  split; [intros a Ha; apply W_stack_rom; unfold W_LO, W_SP, W_S0, SLOT_STACK in *; lia|].
  apply W_mem_inv.
Qed.

Lemma reac_rate_drivable_csv_contract_sat :
  forall (a0 : word) (n : Z), 0 <= n <= 23 ->
  let bufc := repeat 0x5a (Z.to_nat n) in
  let sp := Z_to_bv 64 W_SP in let a1 := Z_to_bv 64 W_BUF in let a2 := Z_to_bv 64 n in
  let m := W_MEM bufc in let lo := W_LO in let fc := Z_to_bv 32 0 in let canary := Z_to_bv 64 0 in
  let junk := csv_bytes bufc in
  let S := bv_unsigned sp in let buf := bv_unsigned a1 in let n := bv_unsigned a2 in
  let L := csv_list (bv_unsigned a0) in
    n <= 23 /\
    (0 < n -> 0 < buf /\ rw_cells rsegs m buf [CB (Z.to_nat n) junk] /\ (buf + n <= lo \/ S <= buf)) /\
    stk rsegs m lo S /\
    lo + DCSV_K <= S /\
    IMG_END <= lo /\
    S < 2^63 /\
    frm0 fc /\
    mem_inv rsegs m /\
    MemNorm.task_mem rsegs m /\
    bytes_at rsegs m GOT_GUARD (le8 (Z_to_bv 64 GUARD)) /\
    bytes_at rsegs m GUARD (le8 canary).
Proof.
  intros a0 n Hn. cbv zeta. pose proof W_SP_facts as HW.
  assert (bv_unsigned (Z_to_bv 64 W_SP) = W_SP) as ES by (apply bu64; unfold W_SP, W_S0 in *; lia).
  assert (bv_unsigned (Z_to_bv 64 W_BUF) = W_BUF) as EB by (apply bu64; unfold W_BUF; lia).
  assert (bv_unsigned (Z_to_bv 64 n) = n) as EN by (apply bu64; lia).
  rewrite ES, EB, EN.
  split; [lia|].
  split.
  { intros Hp. split; [unfold W_BUF; lia|]. split; [|left; unfold W_LO, W_BUF, W_S0, SLOT_STACK in *; lia].
    unfold rw_cells, cells_at. cbn [cells_wf cell_wf cells_bytes cbytes cells_size csize].
    rewrite app_nil_r, Nat.add_0_r. split; [split; [split; [rewrite csv_bytes_length, repeat_length; reflexivity | exact I]|]|].
    - apply W_buf_bytes. rewrite repeat_length. lia.
    - apply W_buf_wr. lia. }
  split; [apply W_stk; unfold W_LO, W_SP, W_S0, SLOT_STACK in *; lia|].
  split; [unfold DCSV_K, DCSV_F, SNPRINTF_K; lia|].
  split; [unfold IMG_END; lia|]. split; [lia|]. split; [exact W_frm0|].
  split; [apply W_mem_inv|]. split; [apply W_task_mem|]. split; [apply W_got_guard|]. apply W_guard.
Qed.

Lemma rate_prop_parse_contract_sat :
  forall null : bool,
  let bs := repeat (Z_to_bv 8 0) 8 in let P := W_POD in let Q := W_Q in
  let sp := Z_to_bv 64 W_SP in let a0 := Z_to_bv 64 (if null then 0 else P) in let a1 := Z_to_bv 64 Q in
  let m := W_MEM [] in let lo := W_LO in let fc := Z_to_bv 32 0 in
    a0 = Z_to_bv 64 (if null then 0 else P) /\
    a1 = Z_to_bv 64 Q /\
    rate_args m lo (bv_unsigned sp) P Q bs /\
    stk rsegs m lo (bv_unsigned sp) /\
    lo + PARSE_FRAME <= bv_unsigned sp /\
    (forall a, lo <= a < bv_unsigned sp -> seg_rom rsegs (wa a) = None) /\
    frm0 fc /\
    mem_inv rsegs m.
Proof.
  intros null. cbv zeta. pose proof W_SP_facts as HW.
  assert (bv_unsigned (Z_to_bv 64 W_SP) = W_SP) as ES by (apply bu64; unfold W_SP, W_S0 in *; lia).
  rewrite ES.
  split; [reflexivity|]. split; [reflexivity|].
  split.
  { unfold rate_args. split.
    { unfold bytes_at. rewrite repeat_length. split; [unfold W_POD; lia|]. split; [unfold W_POD; lia|].
      intros i Hi. unfold mrd. rewrite W_MEM_pod by lia.
      do 8 (destruct i as [|i]; [reflexivity|]). lia. }
    split; [unfold W_POD; lia|]. split; [unfold W_POD; reflexivity|]. split; [rewrite repeat_length; lia|].
    split; [reflexivity|]. split; [rewrite repeat_length; lia|].
    split; [unfold wr_at; split; [unfold W_Q, W_SP, W_S0 in *; lia|]; split; [unfold W_Q, W_SP, W_S0 in *; lia|];
            intros i Hi; unfold wview; rewrite W_MEM_stack by (unfold W_LO, W_Q, W_SP, W_S0, SLOT_STACK in *; lia);
            discriminate|].
    split; [lia|]. lia. }
  split; [apply W_stk; unfold W_LO, W_SP, W_S0, SLOT_STACK in *; lia|].
  split; [unfold PARSE_FRAME; unfold W_LO, W_SP, W_S0, SLOT_STACK in *; lia|].
  split; [intros a Ha; apply W_stack_rom; unfold W_LO, W_SP, W_S0, SLOT_STACK in *; lia|].
  split; [exact W_frm0|]. apply W_mem_inv.
Qed.

(** The pod facts rate_args needs, on every record pod_build makes (corrupted or not): len >= 8, len <= 5440, and
    the top size word is len - 8 (Pod/Model.v pod_build_wf, pod_encode_len). *)
Lemma pod_top : forall inp r rest, pod_build inp = (r, rest) ->
  8 <= Z.of_nat (length (buf r)) <= 5440 /\ u32_at (buf r) 0 = Z.of_nat (length (buf r)) - 8.
Proof.
  intros inp r rest H. pose proof (pod_build_wf inp r rest H) as (Hs & Hp & He & Hl & Hlen & Hc).
  destruct r as [s ps co]. cbn [p_shape p_props p_corr] in *.
  assert (Hp' : Forall (fun kv => pval_wf (snd kv)) ps).
  { eapply Forall_impl; [|exact Hp]. intros kv [_ Hk]. exact Hk. }
  pose proof (pod_encode_len s ps co Hp' He Hl) as (L1 & L2 & _).
  unfold buf, pod_encode in *. cbv zeta in *. cbn [p_shape p_props p_corr] in *.
  set (b := body_bytes s ps) in *. rewrite length_app, length_le32 in L1, L2, Hc.
  assert (V : (Z.of_nat (length b) - 4) mod 2^32 = Z.of_nat (length b) - 4) by (apply Z.mod_small; lia).
  destruct co as [[off bs]|].
  - unfold corr_wf in Hc. destruct Hc as (Ho & Hob & Hbs). unfold overwrite.
    assert (F4 : firstn (Z.to_nat off) (le32 (Z.of_nat (length b) - 4)) = le32 (Z.of_nat (length b) - 4))
      by (apply firstn_all2; rewrite length_le32; lia).
    rewrite firstn_app, F4, length_le32. rewrite <- !app_assoc. rewrite u32_at_le32, V.
    rewrite !length_app, length_le32, length_firstn, length_skipn, length_app, length_le32. split; lia.
  - rewrite u32_at_le32, V. rewrite length_app, length_le32. split; lia.
Qed.

(** ** The parse's premises at every pod pod_build makes (copied verbatim from the contract review's section (E))

    [W_MEMP bs]: the stack region's zeros and the pod bytes bs at W_POD; every other byte reads the image. *)
Definition W_MEMP (bs : list byte) (a : word) : option byte :=
  let x := bv_unsigned a in
  if in_rng W_LO SLOT_STACK x then Some (Z_to_bv 8 0)
  else if in_rng W_POD (Z.of_nat (length bs)) x then nth_error bs (Z.to_nat (x - W_POD))
  else None.

Lemma W_MEMP_stack : forall bs x, W_LO <= x < W_S0 -> W_MEMP bs (wa x) = Some (Z_to_bv 8 0).
Proof.
  intros bs x Hx. unfold W_MEMP. rewrite wa_unsigned by (unfold W_LO, W_S0, SLOT_STACK in *; lia).
  rewrite in_rng_t by (unfold W_LO, W_S0, SLOT_STACK in *; lia). reflexivity.
Qed.

Lemma W_MEMP_hi : forall bs a b, Z.of_nat (length bs) <= 5440 -> W_MEMP bs a = Some b -> 0x60000 <= bv_unsigned a < W_S0.
Proof.
  intros bs a b Hl H. unfold W_MEMP, in_rng in H.
  destruct ((W_LO <=? bv_unsigned a) && (bv_unsigned a <? W_LO + SLOT_STACK)) eqn:E1.
  { apply andb_prop in E1 as [E1 E1']. apply Z.leb_le in E1. apply Z.ltb_lt in E1'.
    unfold W_LO, W_S0, SLOT_STACK in *. lia. }
  destruct ((W_POD <=? bv_unsigned a) && (bv_unsigned a <? W_POD + Z.of_nat (length bs))) eqn:E2; [|discriminate].
  apply andb_prop in E2 as [E2 E2']. apply Z.leb_le in E2. apply Z.ltb_lt in E2'. unfold W_POD, W_S0 in *. lia.
Qed.

Lemma W_MEMP_inv : forall bs, Z.of_nat (length bs) <= 5440 -> mem_inv rsegs (W_MEMP bs).
Proof.
  intros bs Hl a b H. apply (W_MEMP_hi bs a b Hl) in H. unfold ro_addr.
  rewrite (YL0k.find_segment_above rsegs 0x60000) by (exact W_top || lia). reflexivity.
Qed.

Lemma W_MEMP_stk : forall bs lo hi, W_LO <= lo -> lo <= hi -> hi <= W_S0 -> stk rsegs (W_MEMP bs) lo hi.
Proof.
  intros bs lo hi H1 H2 H3. unfold stk. split; [unfold W_LO, W_S0, SLOT_STACK in *; lia|].
  split; [unfold W_S0 in *; lia|]. intros a Ha.
  assert (W_MEMP bs (wa a) = Some (Z_to_bv 8 0)) as E by (apply W_MEMP_stack; lia).
  split; [unfold wview; rewrite E; discriminate | exists (Z_to_bv 8 0); unfold mrd; rewrite E; reflexivity].
Qed.

Lemma W_MEMP_pod : forall bs, Z.of_nat (length bs) <= 5440 -> bytes_at rsegs (W_MEMP bs) W_POD bs.
Proof.
  intros bs Hl. unfold bytes_at. split; [unfold W_POD; lia|]. split; [unfold W_POD; lia|].
  intros i Hi. unfold mrd. unfold W_MEMP. rewrite wa_unsigned by (unfold W_POD; lia).
  rewrite in_rng_f by (unfold W_LO, W_S0, SLOT_STACK, W_POD; lia).
  rewrite in_rng_t by lia. replace (Z.to_nat (W_POD + Z.of_nat i - W_POD)) with i by lia.
  destruct (nth_error bs i) eqn:E; [reflexivity|]. apply nth_error_None in E. lia.
Qed.

Lemma rate_prop_parse_contract_sat_all : forall (null : bool) (bs : list byte),
  8 <= Z.of_nat (length bs) <= 5440 -> u32_at bs 0 = Z.of_nat (length bs) - 8 ->
  let P := W_POD in let Q := W_Q in
  let sp := Z_to_bv 64 W_SP in let a0 := Z_to_bv 64 (if null then 0 else P) in let a1 := Z_to_bv 64 Q in
  let m := W_MEMP bs in let lo := W_LO in let fc := Z_to_bv 32 0 in
    a0 = Z_to_bv 64 (if null then 0 else P) /\
    a1 = Z_to_bv 64 Q /\
    rate_args m lo (bv_unsigned sp) P Q bs /\
    stk rsegs m lo (bv_unsigned sp) /\
    lo + PARSE_FRAME <= bv_unsigned sp /\
    (forall a, lo <= a < bv_unsigned sp -> seg_rom rsegs (wa a) = None) /\
    frm0 fc /\
    mem_inv rsegs m.
Proof.
  intros null bs Hl Hu. cbv zeta. pose proof W_SP_facts as HW.
  assert (bv_unsigned (Z_to_bv 64 W_SP) = W_SP) as ES by (apply bu64; unfold W_SP, W_S0 in *; lia).
  rewrite ES.
  split; [reflexivity|]. split; [reflexivity|].
  split.
  { unfold rate_args. split; [apply W_MEMP_pod; lia|].
    split; [unfold W_POD; lia|]. split; [unfold W_POD; reflexivity|]. split; [lia|]. split; [exact Hu|].
    split; [unfold W_POD, W_LO, W_S0, SLOT_STACK; lia|].
    split; [unfold wr_at; split; [unfold W_Q, W_SP, W_S0 in *; lia|]; split; [unfold W_Q, W_SP, W_S0 in *; lia|];
            intros i Hi; unfold wview; rewrite W_MEMP_stack by (unfold W_LO, W_Q, W_SP, W_S0, SLOT_STACK in *; lia);
            discriminate|].
    split; [lia|]. lia. }
  split; [apply W_MEMP_stk; unfold W_LO, W_SP, W_S0, SLOT_STACK in *; lia|].
  split; [unfold PARSE_FRAME; unfold W_LO, W_SP, W_S0, SLOT_STACK in *; lia|].
  split; [intros a Ha; apply W_stack_rom; unfold W_LO, W_SP, W_S0, SLOT_STACK in *; lia|].
  split; [exact W_frm0|]. apply W_MEMP_inv. lia.
Qed.

(** Every record pod_build makes (pod_top) meets the hypotheses, so the parse's premises hold at the real instance for
    every pod main can hand it, NULL flag or not; and the contract applies there. *)
Lemma fit_prop_parse_all : rate_prop_parse_contract -> forall inp r rest (null : bool), pod_build inp = (r, rest) ->
  forall ra gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F,
  exists P, evt rsegs P (MS (mkR ra (Z_to_bv 64 W_SP) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (if null then 0 else W_POD))
                              (Z_to_bv 64 W_Q) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                             F (Z_to_bv 64 REAC_RATE_PROP_PARSE) (Z_to_bv 32 0) None (W_MEMP (buf r)) (seg_rom rsegs)).
Proof.
  intros H inp r rest null Hb; intros. pose proof (pod_top inp r rest Hb) as (Hl & Hu).
  pose proof (rate_prop_parse_contract_sat_all null (buf r) Hl Hu) as HS. cbv zeta in HS.
  destruct HS as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8).
  eexists. exact (H ra _ gp tp t0 t1 t2 s0 s1 _ _ a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                    F _ _ null W_LO W_POD W_Q _ H1 H2 H3 H4 H5 H6 H7 H8).
Qed.
