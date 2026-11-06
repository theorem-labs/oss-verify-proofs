(* Case 2 of the op loop of LLVMFuzzerTestOneInput in the plain image (fuzz_transport.c:1175-1177
   `case 2: op_announce(&in); break;`, op_announce :1049-1063 inlined), 0x139a4-0x139e0 then 0x13b74-0x13de0.
   The model is the op =? 2 branch of TOps.v LLVMFuzzerTestOneInput_op_m: op_announce_m, which calls
   build_and_receive_m with the 34-byte announce body body3 the model builds.

   The machine (tr6/llvmf-plain.dis), n = fi_n c the cursor's count before the op byte:
     0x139a4 beqz s6 (n - 1 = 0) -> 0x13b74 s0 = sel = 0, j 0x13d0c                  (n = 1: no byte left)
     0x139a8 lbu s0 = sel = D[fi_off c + 1]
     0x139ac-0x139b0 beq s7, 2 -> 0x13d08 s3 = cursor + 2, then 0x13d0c               (n = 2: mac = nm = 0)
     0x139b4-0x139b8 bne s7, 3 -> 0x13cc0 s1 = nm = D[fi_off c + 3], s6 = n - 4, s3 = cursor + 4   (n >= 4)
     0x139bc-0x139c8 s6 = 0, s1 = nm = 0, s3 = cursor + 3, j 0x13ccc                  (n = 3)
     0x13ccc-0x13ce0 s2 = mac = D[fi_off c + 2] & 0xf, memset(sp + 0x50, 0, 0x22)    (body0 = 34 zeros)
     0x13ce4-0x13d04 mac < 10: 0x13d28; 12 < mac: 0x13d40 (no copy); else a0 = sp + 0x46 + mac, a1 = OTHER
                     (0x104c8), j 0x13d38                                             (body1 = upd body0 (mac - 10) OTHER)
     0x13d0c-0x13d24 memset(sp + 0x50, 0, 0x22), s6 = s1 = s2 = 0 (the n <= 2 paths), on to 0x13d28
     0x13d28-0x13d34 a0 = sp + 0x50 + mac, a1 = HOST (0x10480)                        (body1 = upd body0 mac HOST)
     0x13d38-0x13d3c a2 = 6, jal memcpy
     0x13d40-0x13d70 s2 = 0x39 again; name = nm mod 3 (q = nm * 171 >> 9, nm - q - 2 q); s4 = NAME[name] from
                     the .data.rel.ro table at 0x21408
     0x13d74-0x13d90 sb '1', '.', '3', '7' at sp + 0x5f .. sp + 0x62                  (body2 = upd body1 15 "1.37")
     0x13d94-0x13d98 jal strlen(NAME[name]); 0x13d9c-0x13da8 memcpy(sp + 0x68, NAME[name], len)
                                                                                      (body3 = upd body2 24 NAME[name])
     0x13dac-0x13dd4 a5 = cmd = (sel | 0xe0) & 0xe1, a0 = &SPEC_BCAST (0x1048c), a1 = &DESK (0x10486),
                     a2 = a3 = a4 = 0 (send = ack = retry = 0), a6 = sp + 0x50 (body3), a7 = 0x22 (len = 34)
     0x13dd8 jal build_and_receive (ra = 0x13ddc); 0x13ddc s1 = 7; 0x13de0 j 0x1428c (the latch)

   build_and_receive is an SR contract, so the case is two evt segments around the call: llvm_op2_pre_evt
   (0x139a4 to build_and_receive's entry; the joined blocks are the lemmas llvm_op2_t1 .. llvm_op2_t5) and
   llvm_op2_post_evt (0x13ddc to the latch), composed at the SR level in llvm_op2_sr through TSRGlue.v g_run and
   _sr.v llvm_sr_bar; llvm_op2_pass is the same case in the form of the loop's binder (_loopsr.v llvm_pass_sr).
*)
From Stdlib Require Import ZArith NArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YO0i YO0f YO0d YO05
  YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib Require Import Contract AllocSlots AllocRoom MemNorm.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Regs6ss.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TWorldLemmas TImg TWorldMem TNeed TCb TOps TOpsA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog Require Import memset_c memcpy_c strlen_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T Require Import TImgP WMem TContract receive_c TSRGlue
  build_and_receive_c LLVMFuzzerTestOneInput_lh LLVMFuzzerTestOneInput_fr LLVMFuzzerTestOneInput_disp
  LLVMFuzzerTestOneInput_sr LLVMFuzzerTestOneInput_op08.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T Require LLVMFuzzerTestOneInput_c.
Import ListNotations.
Open Scope Z_scope.

(* ---------------------------------------------------------------- model: op_announce_m body identity *)

(* The announce body the model builds (TOps.v op_announce_m :1055-1061), as its four stages:
   body0: the 34 zeros of the memset at :1055 (SPEC_ANN_MIN + 1 = 34).
   body1: body0 with HOST at mac for mac < 10, with OTHER at mac - 10 for 10 <= mac < 13, else body0 (:1056-1059).
   body2: body1 with "1.37" at SPEC_ANN_VERSION = 15 (:1060).
   body3: body2 with NAME[name] at SPEC_ANN_NAME = 24 (:1061, name = nm mod 3). *)
Definition op2_body0 : list byte := repeat (b8 0) 34.
Definition op2_body1 (mac : Z) : list byte :=
  if mac <? 10 then upd op2_body0 mac HOST
  else if mac <? 13 then upd op2_body0 (mac - 10) OTHER
  else op2_body0.
Definition op2_body2 (mac : Z) : list byte := upd (op2_body1 mac) 15 ANN_VERSION_137.
Definition op2_body3 (mac name : Z) : list byte :=
  upd (op2_body2 mac) 24 (nth (Z.to_nat name) op_announce_NAME []).

(* op_announce_m, unfolded with the three fuzz reads named (sel, m, nm) and the body stages above. *)
Lemma op2_announce_unfold :
  forall I B D a c c1 sel c2 mb c3 nm,
  fuzz_u8_m D c = (c1, sel) -> fuzz_u8_m D c1 = (c2, mb) -> fuzz_u8_m D c2 = (c3, nm) ->
  op_announce_m I B D a c =
    let body3 := op2_body3 (mb mod 16) (nm mod 3) in
    match build_and_receive_m I B a SPEC_BCAST DESK 0 0 0
            (if Z.land sel 1 =? 0 then SPEC_CMD_E0 else SPEC_CMD_E1) body3 with
    | Some (B1, _) => Some (B1, c3)
    | None => None
    end.
Proof.
  intros I B D a c c1 sel c2 mb c3 nm E1 E2 E3.
  unfold op_announce_m. rewrite E1. cbv beta iota zeta. rewrite E2. cbv beta iota zeta. rewrite E3. cbv beta iota zeta.
  unfold op2_body3, op2_body2, op2_body1, op2_body0, SPEC_ANN_MIN, SPEC_ANN_VERSION, SPEC_ANN_NAME.
  change (Z.to_nat (33 + 1)) with 34%nat. change (b8 0) with (Z_to_bv 8 0).
  reflexivity.
Qed.

(* body3's length is 34 at every mac, name. *)
Lemma op2_body0_length : length op2_body0 = 34%nat.
Proof. unfold op2_body0. apply repeat_length. Qed.

Lemma op2_name_length_le : forall k : nat, (length (nth k op_announce_NAME []) <= 8)%nat.
Proof.
  intros k. destruct (Nat.ltb_spec k 3) as [Hk|Hk].
  - destruct k as [|[|[|?]]]; try lia; cbn [nth op_announce_NAME length bs map]; lia.
  - rewrite nth_overflow by (cbn [length op_announce_NAME]; lia). cbn [length]. lia.
Qed.

Lemma op2_body1_length : forall mac, 0 <= mac -> length (op2_body1 mac) = 34%nat.
Proof.
  intros mac Hmac. unfold op2_body1.
  destruct (Z.ltb_spec mac 10) as [H10|H10];
    [|destruct (Z.ltb_spec mac 13) as [H13|H13]];
    try apply op2_body0_length.
  - apply length_upd; [exact Hmac|].
    rewrite op2_body0_length. unfold HOST, bs. cbn [length map]. lia.
  - apply length_upd; [lia|].
    rewrite op2_body0_length. unfold OTHER, bs. cbn [length map]. lia.
Qed.

Lemma op2_body2_length : forall mac, 0 <= mac -> length (op2_body2 mac) = 34%nat.
Proof.
  intros mac Hmac. unfold op2_body2.
  rewrite length_upd; [apply op2_body1_length; exact Hmac | lia |].
  rewrite op2_body1_length by exact Hmac.
  unfold ANN_VERSION_137, bs. cbn [length map]. lia.
Qed.

Lemma op2_body3_length : forall mac name, 0 <= mac ->
  length (op2_body3 mac name) = 34%nat.
Proof.
  intros mac name Hmac. unfold op2_body3.
  rewrite length_upd; [apply op2_body2_length; exact Hmac | lia |].
  rewrite op2_body2_length by exact Hmac.
  pose proof (op2_name_length_le (Z.to_nat name)) as HL. lia.
Qed.

(* ---- the compiler's remainder: (nm * 171) >> 9 = nm / 3 on a byte, as _disp.v's dis_div for /9 ---- *)

Lemma op2_div3 : forall n, 0 <= n < 256 -> n * 171 / 512 = n / 3.
Proof.
  intros n Hn.
  assert (Hr : 0 <= n mod 3 < 3) by (apply Z.mod_pos_bound; lia).
  pose proof (Z.div_mod n 3 ltac:(lia)) as E.
  assert (Hq : 0 <= n / 3 <= 85).
  { split; [apply Z.div_pos; lia|].
    assert (n / 3 < 86) by (apply Z.div_lt_upper_bound; lia). lia. }
  replace (n * 171) with (512 * (n / 3) + (n / 3 + 171 * (n mod 3))) by lia.
  rewrite Z.mul_comm, Z.div_add_l by lia.
  rewrite (Z.div_small (n / 3 + 171 * (n mod 3)) 512) by lia. lia.
Qed.

(* ---- the command byte: 0x13dac ori a0, s0, 0xe0; 0x13db0 andi a5, a0, 0xe1 is (sel & 1) ? 0xe1 : 0xe0
   (TOps.v op_announce_m :1062), for every byte sel, by computation ---- *)
Definition op2_cmd (sel : Z) : Z := if Z.land sel 1 =? 0 then SPEC_CMD_E0 else SPEC_CMD_E1.

Lemma op2_cmd_val : forall sel, 0 <= sel < 256 -> Z.land (Z.lor sel 224) 225 = op2_cmd sel.
Proof.
  intros sel Hs.
  assert (H : forallb (fun x => Z.land (Z.lor x 224) 225 =? op2_cmd x) (map Z.of_nat (seq 0 256)) = true)
    by (vm_compute; reflexivity).
  rewrite forallb_forall in H. apply Z.eqb_eq. apply H.
  apply in_map_iff. exists (Z.to_nat sel). split; [lia | apply in_seq; lia].
Qed.

(* ---- NAME[] (fuzz_transport.c:1051): the pointer table in .data.rel.ro at 0x21408 (0x13d4c auipc a1, 0xd and
   0x13d54 addi a1, a1, 0x6bc: 0x20d4c + 0x6bc) holds 0x10339, 0x10330, 0x10305 (the image's bytes at 0x21408,
   0x21410, 0x21418), the three strings in .rodata: "CNTRL|24", "MAINUNIT", "OTHER", each with its NUL. strlen
   reads 8-byte words, so each string is given with the image bytes after its NUL up to the next 8-byte boundary
   (strlen_c.v's slack): 6, 7 and 5 bytes. ---- *)
Definition op2_namep (j : Z) : Z := nth (Z.to_nat j) [0x10339; 0x10330; 0x10305] 0.
Definition op2_slack (j : Z) : list byte :=
  nth (Z.to_nat j) [bs [0x63; 0x6c; 0x69; 0x3a; 0x20; 0x63]; bs [0x43; 0x4e; 0x54; 0x52; 0x4c; 0x7c; 0x32];
                    bs [0x49; 0x4e; 0x46; 0x00; 0x63]] [].

Lemma op2_name_facts : forall m j, mem_inv rsegs m -> 0 <= j < 3 ->
  bytes_at rsegs m (op2_namep j) (nth (Z.to_nat j) op_announce_NAME [] ++ Z_to_bv 8 0 :: op2_slack j) /\
  ~ In (Z_to_bv 8 0) (nth (Z.to_nat j) op_announce_NAME []) /\
  (- (op2_namep j + Z.of_nat (length (nth (Z.to_nat j) op_announce_NAME [])) + 1)) mod 8
    <= Z.of_nat (length (op2_slack j)).
Proof.
  intros m j HI Hj. assert (Hc : j = 0 \/ j = 1 \/ j = 2) by lia.
  destruct Hc as [ -> | [ -> | -> ] ];
    (split; [apply ro_bytes_at; [exact HI | apply Z.leb_le; vm_compute; reflexivity
                                | apply Z.leb_le; vm_compute; reflexivity
                                | apply ro_bytes_b_sound; vm_compute; reflexivity]|]);
    (split; [|apply Z.leb_le; vm_compute; reflexivity]);
    vm_compute; intros H;
    repeat (destruct H as [H|H]; [apply (f_equal bv_unsigned) in H; vm_compute in H; discriminate H|]);
    exact H.
Qed.

(* the table's entry j, read through relro_img *)
Lemma op2_table_load : forall m j, relro_img m -> 0 <= j < 3 ->
  ov_read_bytes rsegs m (wa (0x21408 + 8 * j)) 8 = Some (le8 (Z_to_bv 64 (op2_namep j))).
Proof.
  intros m j HRO Hj.
  assert (HB : bytes_at rsegs m (0x21408 + 8 * j) (le8 (Z_to_bv 64 (op2_namep j)))).
  { split; [lia|]. split; [rewrite length_le8; lia|]. intros i Hi. rewrite length_le8 in Hi.
    replace (0x21408 + 8 * j + Z.of_nat i) with (RELRO_BASE + (64 + 8 * j + Z.of_nat i)) by (unfold RELRO_BASE; lia).
    rewrite HRO by (unfold RELRO_LEN; lia).
    assert (Hc : j = 0 \/ j = 1 \/ j = 2) by lia.
    destruct Hc as [ -> | [ -> | -> ] ];
      (do 8 (destruct i as [|i]; [vm_compute; f_equal; apply bv_eq; reflexivity|])); lia. }
  pose proof (bytes_at_read rsegs m _ _ 0 8 HB ltac:(lia) ltac:(rewrite length_le8; lia)) as R.
  rewrite Z.add_0_r in R. rewrite R. f_equal; try (cbn [skipn]; apply firstn_all2; rewrite length_le8; lia).
Qed.

Lemma op2_namep_range : forall j, 0 <= j < 3 -> 0x10305 <= op2_namep j <= 0x10339.
Proof. intros j Hj. assert (Hc : j = 0 \/ j = 1 \/ j = 2) by lia. destruct Hc as [ -> | [ -> | -> ] ]; vm_compute; split; discriminate. Qed.

Lemma op2_name_len : forall j, 0 <= j < 3 -> (5 <= length (nth (Z.to_nat j) op_announce_NAME []) <= 8)%nat.
Proof. intros j Hj. assert (Hc : j = 0 \/ j = 1 \/ j = 2) by lia. destruct Hc as [ -> | [ -> | -> ] ]; vm_compute; lia. Qed.

Lemma op2_swrap32_small : forall x, -2^31 <= x < 2^31 -> bv_swrap 32 x = x.
Proof.
  intros x Hx. apply bv_swrap_small.
  assert (E : bv_half_modulus 32 = 2 ^ 31) by reflexivity. rewrite E. lia.
Qed.

(* 0x13d44-0x13d60: q = (nm * 171) >> 9 (op2_div3), s1 = (nm - q) - 2 q in two subw: nm mod 3 *)
Lemma op2_mod3_val : forall nm, 0 <= nm < 256 ->
  bv_swrap 32 (bv_swrap 32 (nm - Z.shiftr (nm * 171) 9) mod 18446744073709551616 -
               Z.shiftl (Z.shiftr (nm * 171) 9) 1 mod 18446744073709551616) = nm mod 3.
Proof.
  intros nm Hn.
  rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 9) with 512. rewrite op2_div3 by exact Hn.
  rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 1) with 2.
  assert (Hq : 0 <= nm / 3 <= 85).
  { split; [apply Z.div_pos; lia|]. assert (nm / 3 < 86) by (apply Z.div_lt_upper_bound; lia). lia. }
  pose proof (Z.div_mod nm 3 ltac:(lia)) as E. pose proof (Z.mod_pos_bound nm 3 ltac:(lia)) as R.
  rewrite (op2_swrap32_small (nm - nm / 3)) by lia.
  rewrite (Z.mod_small (nm - nm / 3) 18446744073709551616) by lia.
  rewrite (Z.mod_small (nm / 3 * 2) 18446744073709551616) by lia.
  rewrite op2_swrap32_small by lia. lia.
Qed.

(* 0x13d64-0x13d6c: a0 = 0x21408 + ((name & 0xff) << 3) *)
Lemma op2_addr_val : forall j, 0 <= j < 3 ->
  136200 + Z.shiftl (Z.land (j mod 18446744073709551616) 255) 3 = 0x21408 + 8 * j.
Proof.
  intros j Hj. rewrite Z.mod_small by lia. change 255 with (Z.ones 8). rewrite Z.land_ones by lia.
  rewrite Z.mod_small by (change (2 ^ 8) with 256; lia).
  rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 3) with 8. lia.
Qed.

(* ---- frame surgery: the frame as any 224-byte cell list (op4_mem's form, re-stated here) ---- *)

Lemma op2_wr_at_app : forall m A n1 n2, 0 <= n1 -> 0 <= n2 ->
  wr_at rsegs m A (n1 + n2) <-> wr_at rsegs m A n1 /\ wr_at rsegs m (A + n1) n2.
Proof.
  intros m A n1 n2 H1 H2. unfold wr_at. split.
  - intros (Ha & Hb & Hw). split; (split; [lia|]); (split; [lia|]).
    + intros i Hi. apply Hw. lia.
    + intros i Hi. replace (A + n1 + i) with (A + (n1 + i)) by lia. apply Hw. lia.
  - intros [(Ha & Hb & Hw1) (Ha2 & Hb2 & Hw2)]. split; [lia|]. split; [lia|].
    intros i Hi. destruct (Z_lt_le_dec i n1) as [L|L]; [apply Hw1; lia|].
    replace (A + i) with (A + n1 + (i - n1)) by lia. apply Hw2. lia.
Qed.

Lemma op2_rw_app : forall m A cs1 cs2,
  rw_cells rsegs m A (cs1 ++ cs2) <->
  rw_cells rsegs m A cs1 /\ rw_cells rsegs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof.
  intros m A cs1 cs2. unfold rw_cells, cells_at.
  rewrite cells_wf_app, cells_bytes_app, cells_size_app, bytes_at_app, Nat2Z.inj_add.
  rewrite (op2_wr_at_app m A) by lia.
  split.
  - intros [[[W1 W2] [B1 B2]] [R1 R2]].
    assert (L1 : length (cells_bytes cs1) = cells_size cs1) by (apply cells_bytes_length; exact W1).
    rewrite L1 in B2. tauto.
  - intros [[[W1 B1] R1] [[W2 B2] R2]].
    assert (L1 : length (cells_bytes cs1) = cells_size cs1) by (apply cells_bytes_length; exact W1).
    rewrite L1. tauto.
Qed.

(* same bytes in other cells *)
Lemma op2_rw_rebytes : forall m A cs cs', rw_cells rsegs m A cs -> cells_wf cs' ->
  cells_bytes cs' = cells_bytes cs -> rw_cells rsegs m A cs'.
Proof.
  intros m A cs cs' [[W B] R] W' E. unfold rw_cells, cells_at.
  assert (S : cells_size cs' = cells_size cs).
  { rewrite <- (cells_bytes_length cs' W'), <- (cells_bytes_length cs W), E. reflexivity. }
  rewrite S, E. tauto.
Qed.

Lemma op2_rw_mid : forall m A pre mid mid' post, rw_cells rsegs m A (pre ++ mid ++ post) ->
  cells_wf mid' -> cells_bytes mid' = cells_bytes mid -> rw_cells rsegs m A (pre ++ mid' ++ post).
Proof.
  intros m A pre mid mid' post H W E. apply (op2_rw_rebytes m A _ _ H).
  - pose proof (proj1 (proj1 H)) as WH. rewrite !cells_wf_app in WH |- *. tauto.
  - rewrite !cells_bytes_app, E. reflexivity.
Qed.

Section OP2.
Context (data : Z) (D : list byte).

(* llvm_mem with the frame as any 224-byte cell list, carrying the reference memory m0 and its munch /
   wmono facts, the form the case's stores and calls keep. *)
Definition op2_mem (Sp lo : Z) (B : list byte) (m0 m : word -> option byte) (fr : list cell) : Prop :=
  munch (LLVM_FP Sp) m0 m /\ wmono rsegs m0 m /\
  bytes_at rsegs m data D /\
  Sp mod 16 = 0 /\ stk rsegs m lo Sp /\ lo + LLVM_LOOP_K <= Sp /\ Sp + LLVM_FRAME < 2 ^ 63 /\
  w_off_stack W_BASE_PLAIN (Z_to_bv 64 Sp) LLVM_LOOP_K /\ W_BASE_PLAIN + W_LEN <= lo /\
  off_world data (Z.of_nat (length D)) /\
  off_window (Z_to_bv 64 (Sp + LLVM_FRAME)) (LLVM_LOOP_K + LLVM_FRAME) data (Z.of_nat (length D)) /\
  mem_inv rsegs m /\ relro_img m /\ wmem rsegs m B /\ g_fail_next B <= 1 /\
  rw_cells rsegs m Sp fr /\ cells_size fr = 224%nat.

Lemma op2_of_llvm : forall (Sp lo : Z) (B : list byte) (m0 m : word -> option byte)
    (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (j10 j28 : list byte),
  llvm_mem data D Sp lo B m0 m ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 j10 j28 ->
  op2_mem Sp lo B m0 m
    ([C8 (Z_to_bv 64 (2 ^ 32 - 3)); C8 (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_s));
      CB 8 j10; C8 (Z_to_bv 64 0x610f); C8 (Z_to_bv 64 0xffff); CB 80 j28;
      C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
Proof.
  intros Sp lo B m0 m ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 j10 j28 H.
  unfold llvm_mem, llvm_frame_consts, llvm_saved in H. unfold op2_mem.
  destruct H as (HMU0 & HWMO0 & HD & HSP & HSTK & HLO & HSP2 & HWOS & HOWS & HOW & HOWIN & HMI & HRO & HWM & HFN & HJ1 & HJ2 & HRW).
  cbn [app] in HRW. repeat (split; [assumption|]). first [reflexivity | split; [exact HRW | reflexivity]].
Qed.

Lemma op2_to_llvm : forall (Sp lo : Z) (B : list byte) (m0 m : word -> option byte)
    (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (m10 m28 : list cell),
  op2_mem Sp lo B m0 m
    ([C8 (Z_to_bv 64 (2 ^ 32 - 3)); C8 (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_s))] ++ m10 ++
     [C8 (Z_to_bv 64 0x610f); C8 (Z_to_bv 64 0xffff)] ++ m28 ++
     [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]) ->
  cells_size m10 = 8%nat -> cells_size m28 = 80%nat ->
  llvm_mem data D Sp lo B m0 m ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (cells_bytes m10) (cells_bytes m28).
Proof.
  intros Sp lo B m0 m ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m10 m28 H S10 S28.
  unfold op2_mem in H. unfold llvm_mem, llvm_frame_consts, llvm_saved.
  destruct H as (HMU0 & HWMO0 & HD & HSP & HSTK & HLO & HSP2 & HWOS & HOWS & HOW & HOWIN & HMI & HRO & HWM & HFN & HRW & HSZ).
  pose proof (proj1 (proj1 HRW)) as WF. rewrite !cells_wf_app in WF.
  destruct WF as (_ & W10 & _ & W28 & _).
  repeat (split; [assumption|]).
  split; [rewrite cells_bytes_length by exact W10; exact S10|].
  split; [rewrite cells_bytes_length by exact W28; exact S28|].
  pose proof (rw_cells_merge rsegs m Sp
    ([C8 (Z_to_bv 64 (2 ^ 32 - 3)); C8 (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_s))] ++ m10 ++
     [C8 (Z_to_bv 64 0x610f); C8 (Z_to_bv 64 0xffff)]) m28
    [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]) as M1.
  rewrite <- !app_assoc in M1. specialize (M1 HRW). rewrite S28 in M1.
  cbn [app] in M1.
  pose proof (rw_cells_merge rsegs m Sp
    [C8 (Z_to_bv 64 (2 ^ 32 - 3)); C8 (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_s))] m10
    ([C8 (Z_to_bv 64 0x610f); C8 (Z_to_bv 64 0xffff)] ++
     CB 80 (cells_bytes m28) ::
     [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])) as M2.
  cbn [app] in M2. specialize (M2 M1). rewrite S10 in M2.
  cbn [app] in M2 |- *. exact M2.
Qed.

(* op2_mem is kept across any change that keeps the window and the world, with a new 224-byte frame.
   The new memory extends the munch and wmono from m0. *)
Lemma op2_mem_after : forall (Sp lo K : Z) (B B' : list byte) (m0 m m' : word -> option byte)
    (fr fr' : list cell),
  op2_mem Sp lo B m0 m fr ->
  0 <= K <= LLVM_LOOP_K ->
  munch [(Sp - K, Sp + LLVM_FRAME); (W_BASE_PLAIN, W_BASE_PLAIN + W_LEN)] m m' ->
  wmono rsegs m m' -> mem_inv rsegs m' -> stk rsegs m' lo Sp -> wmem rsegs m' B' -> g_fail_next B' <= 1 ->
  rw_cells rsegs m' Sp fr' -> cells_size fr' = 224%nat ->
  op2_mem Sp lo B' m0 m' fr'.
Proof.
  intros Sp lo K B B' m0 m m' fr fr' HM HK MU WMO MI ST WM HFN' HRW' HSZ'.
  unfold op2_mem in HM |- *.
  destruct HM as (HMU0 & HWMO0 & HD & HSP & HSTK & HLO & HSP2 & HWOS & HOWS & HOW & HOWIN & HMI & HRO & HWM & HFN & HRW & HSZ).
  unfold LLVM_LOOP_K, LLVM_FRAME in *.
  pose proof (bytes_at_bound rsegs m data D HD) as HDB.
  assert (HLO0 : 0 <= lo) by (unfold W_BASE_PLAIN, W_LEN in HOWS; lia).
  unfold off_window in HOWIN. rewrite unsigned_lit in HOWIN by lia. unfold off_world in HOW.
  split.
  { intros x Hx.
    assert (Hout : outside [(Sp - K, Sp + LLVM_FRAME); (W_BASE_PLAIN, W_BASE_PLAIN + W_LEN)] (bv_unsigned x)).
    { unfold LLVM_FP in Hx. cbn [outside] in Hx |- *.
      destruct Hx as (H1 & H2 & _). split.
      - intros [HA HB]. apply H1. split; unfold LLVM_LOOP_K in *; lia.
      - split; [exact H2 | exact I]. }
    rewrite (MU x Hout). exact (HMU0 x Hx). }
  split; [exact (wmono_trans rsegs m0 m m' HWMO0 WMO)|].
  split; [eapply bytes_at_transport; [exact HD | exact MU |];
          cbn [disjoint_from]; split; [lia | split; [lia | exact I]]|].
  split; [exact HSP|]. split; [exact ST|]. split; [exact HLO|]. split; [exact HSP2|].
  split; [exact HWOS|]. split; [exact HOWS|]. split; [exact HOW|].
  split; [unfold off_window; rewrite unsigned_lit by lia; exact HOWIN|].
  split; [exact MI|].
  split; [eapply relro_munch_hi; [exact HRO | exact MU | lia]|].
  split; [exact WM|]. split; [exact HFN'|]. split; [exact HRW'|]. exact HSZ'.
Qed.

(* A callee whose footprint is its stack window and the world: the frame is kept. *)
Lemma op2_mem_after_call : forall (Sp lo K : Z) (B B' : list byte) (m0 m m' : word -> option byte)
    (fr : list cell),
  op2_mem Sp lo B m0 m fr -> 0 <= K <= LLVM_LOOP_K ->
  munch [(Sp - K, Sp); (W_BASE_PLAIN, W_BASE_PLAIN + W_LEN)] m m' ->
  wmono rsegs m m' -> mem_inv rsegs m' -> stk rsegs m' lo Sp -> wmem rsegs m' B' -> g_fail_next B' <= 1 ->
  op2_mem Sp lo B' m0 m' fr.
Proof.
  intros Sp lo K B B' m0 m m' fr HM HK MU WMO MI ST WM HFN'.
  pose proof HM as HM1. unfold op2_mem in HM1.
  destruct HM1 as (_ & _ & _ & _ & _ & HLO & HSP2 & _ & HOWS & _ & _ & _ & _ & _ & _ & HRW & HSZ).
  unfold LLVM_LOOP_K in HLO.
  eapply (op2_mem_after Sp lo K B B' m0 m m' fr fr); [exact HM | exact HK | | exact WMO | exact MI | exact ST
    | exact WM | exact HFN' | | exact HSZ].
  - intros x Hx. apply MU. cbn [outside] in *. unfold LLVM_FRAME in Hx.
    destruct Hx as (H1 & H2 & _). split; [lia | split; [exact H2 | exact I]].
  - eapply rw_cells_transport; [exact HRW | exact MU | exact WMO |].
    rewrite HSZ. cbn [disjoint_from]. unfold W_BASE_PLAIN, W_LEN in *. split; [lia | split; [lia | exact I]].
Qed.


(* ---- splitting a CB cell at a symbolic offset, and merging after a sub-span write ---- *)

Lemma op2_firstn_skipn_app : forall (bs : list byte) (k q : nat), (k + q <= length bs)%nat ->
  bs = firstn k bs ++ firstn q (skipn k bs) ++ skipn (k + q) bs.
Proof.
  intros bs k q H.
  rewrite <- (firstn_skipn k bs) at 1. f_equal.
  rewrite <- (firstn_skipn q (skipn k bs)) at 1. f_equal.
  rewrite skipn_skipn. f_equal. lia.
Qed.

Lemma op2_upd_split : forall (bs v : list byte) (k : nat), (k + length v <= length bs)%nat ->
  upd bs (Z.of_nat k) v = firstn k bs ++ v ++ skipn (k + length v) bs.
Proof.
  intros bs v k H. unfold upd. rewrite Nat2Z.id. reflexivity.
Qed.

(* Split a CB cell at [k, k + q) into three CB cells with the same bytes. *)
Lemma op2_cell_split3 : forall m A n (bs : list byte) (k q : nat),
  (k + q <= n)%nat -> length bs = n ->
  rw_cells rsegs m A [CB n bs] ->
  rw_cells rsegs m A [CB k (firstn k bs); CB q (firstn q (skipn k bs));
                      CB (n - k - q) (skipn (k + q) bs)].
Proof.
  intros m A n bs k q Hkq Hl H.
  apply (op2_rw_rebytes m A [CB n bs]); [exact H | | ].
  - cbn [cells_wf cell_wf].
    split; [rewrite length_firstn; lia|].
    split; [rewrite length_firstn, length_skipn; lia|].
    split; [rewrite length_skipn; lia|]. exact I.
  - cbn [cells_bytes cbytes app]. rewrite !app_nil_r.
    symmetry. apply op2_firstn_skipn_app. lia.
Qed.

(* After a write of v (length q) into the middle cell: fold back as one CB cell with upd. *)
Lemma op2_cell_merge3 : forall m A n (bs v : list byte) (k q : nat),
  (k + q <= n)%nat -> length bs = n -> length v = q ->
  rw_cells rsegs m A [CB k (firstn k bs); CB q v; CB (n - k - q) (skipn (k + q) bs)] ->
  rw_cells rsegs m A [CB n (upd bs (Z.of_nat k) v)].
Proof.
  intros m A n bs v k q Hkq Hl Hv H.
  apply (op2_rw_rebytes m A [CB k (firstn k bs); CB q v; CB (n - k - q) (skipn (k + q) bs)]);
    [exact H | | ].
  - cbn [cells_wf cell_wf]. split; [|exact I].
    rewrite length_upd; [exact Hl | lia | rewrite Hv, Hl; lia].
  - cbn [cells_bytes cbytes app]. rewrite !app_nil_r.
    rewrite op2_upd_split by lia. rewrite Hv. reflexivity.
Qed.

(* If the three pieces reassemble to a known list bs' = firstn k bs ++ v ++ skipn (k + q) bs, that's upd. *)
Lemma op2_app_eq_upd : forall (bs v : list byte) (k : nat),
  (k + length v <= length bs)%nat ->
  firstn k bs ++ v ++ skipn (k + length v) bs = upd bs (Z.of_nat k) v.
Proof. intros. symmetry. apply op2_upd_split. exact H. Qed.

(* ---- the frame with op_announce's body[] as its own cell ----
   body[34] (fuzz_transport.c:1054 uint8_t body[SPEC_ANN_MIN + 1]) is at sp + 0x50 .. sp + 0x71: 0x13cd4 / 0x13d0c
   addi a0, sp, 0x50 with a2 = 0x22 for its memset, 0x13dbc addi a6, sp, 0x50 for build_and_receive. It lies in the
   loop's 80 scratch bytes at sp + 0x28 (_lh.v's CB 80 j28): 40 bytes before it and 6 after. *)
Definition op2_fr (j10 p40 b p6 : list byte) (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) : list cell :=
  [C8 (Z_to_bv 64 (2 ^ 32 - 3)); C8 (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_s)); CB 8 j10;
   C8 (Z_to_bv 64 0x610f); C8 (Z_to_bv 64 0xffff); CB 40 p40; CB 34 b; CB 6 p6;
   C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Lemma op2_mem_reframe : forall Sp lo B m0 m fr fr',
  op2_mem Sp lo B m0 m fr -> rw_cells rsegs m Sp fr' -> cells_size fr' = 224%nat -> op2_mem Sp lo B m0 m fr'.
Proof.
  intros Sp lo B m0 m fr fr' H HR HS. unfold op2_mem in *.
  destruct H as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & _ & _).
  repeat (split; [assumption|]). exact HS.
Qed.

Lemma op2_mem_rw : forall Sp lo B m0 m fr, op2_mem Sp lo B m0 m fr -> rw_cells rsegs m Sp fr.
Proof. intros Sp lo B m0 m fr H. unfold op2_mem in H. tauto. Qed.

(* the case entry's frame, with body[] split out of the scratch cell *)
Lemma op2_mem_of_llvm : forall Sp lo B m0 m ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 j10 j28,
  llvm_mem data D Sp lo B m0 m ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 j10 j28 ->
  op2_mem Sp lo B m0 m
    (op2_fr j10 (firstn 40 j28) (firstn 34 (skipn 40 j28)) (skipn 74 j28) ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11).
Proof.
  intros Sp lo B m0 m ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 j10 j28 H.
  pose proof H as HL. unfold llvm_mem in HL.
  destruct HL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJ1 & HJ2 & _).
  pose proof (op2_of_llvm Sp lo B m0 m ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 j10 j28 H) as H2.
  apply (op2_mem_reframe _ _ _ _ _ _ _ H2); [|reflexivity].
  pose proof (op2_mem_rw _ _ _ _ _ _ H2) as HRW.
  change (rw_cells rsegs m Sp
    ([C8 (Z_to_bv 64 (2 ^ 32 - 3)); C8 (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_s)); CB 8 j10;
      C8 (Z_to_bv 64 0x610f); C8 (Z_to_bv 64 0xffff)] ++ [CB 80 j28] ++
     [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])) in HRW.
  change (rw_cells rsegs m Sp
    ([C8 (Z_to_bv 64 (2 ^ 32 - 3)); C8 (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_s)); CB 8 j10;
      C8 (Z_to_bv 64 0x610f); C8 (Z_to_bv 64 0xffff)] ++
     [CB 40 (firstn 40 j28); CB 34 (firstn 34 (skipn 40 j28)); CB 6 (skipn 74 j28)] ++
     [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])).
  apply (op2_rw_mid m Sp _ [CB 80 j28] _ _ HRW).
  - cbn [cells_wf cell_wf]. rewrite length_firstn, length_firstn, length_skipn, length_skipn. lia.
  - cbn [cells_bytes cbytes]. rewrite !app_nil_r. symmetry. exact (op2_firstn_skipn_app j28 40 34 ltac:(lia)).
Qed.

(* body[]'s bytes *)
Lemma op2_body_cell : forall Sp lo B m0 m j10 p40 b p6 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11,
  op2_mem Sp lo B m0 m (op2_fr j10 p40 b p6 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
  rw_cells rsegs m (Sp + 80) [CB 34 b].
Proof.
  intros Sp lo B m0 m j10 p40 b p6 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 H.
  pose proof (op2_mem_rw _ _ _ _ _ _ H) as HRW.
  change (rw_cells rsegs m Sp
    ([C8 (Z_to_bv 64 (2 ^ 32 - 3)); C8 (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_s)); CB 8 j10;
      C8 (Z_to_bv 64 0x610f); C8 (Z_to_bv 64 0xffff); CB 40 p40] ++ [CB 34 b] ++
     [CB 6 p6; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]))
    in HRW.
  apply op2_rw_app in HRW as [_ HRW]. apply op2_rw_app in HRW as [HRW _].
  cbn [cells_size csize Nat.add] in HRW. exact HRW.
Qed.

Lemma op2_body_bytes : forall Sp lo B m0 m j10 p40 b p6 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11,
  op2_mem Sp lo B m0 m (op2_fr j10 p40 b p6 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
  bytes_at rsegs m (Sp + 80) b.
Proof.
  intros Sp lo B m0 m j10 p40 b p6 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 H.
  destruct (op2_body_cell Sp lo B m0 m j10 p40 b p6 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 H) as [[_ HB] _].
  cbn [cells_bytes cbytes] in HB. rewrite app_nil_r in HB. exact HB.
Qed.

(* n bytes at k of body[], as the destination cell a callee is given *)
Lemma op2_body_carve : forall Sp lo B m0 m j10 p40 b p6 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (k q : nat),
  op2_mem Sp lo B m0 m (op2_fr j10 p40 b p6 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
  length b = 34%nat -> (k + q <= 34)%nat ->
  rw_cells rsegs m (Sp + 80 + Z.of_nat k) [CB q (firstn q (skipn k b))].
Proof.
  intros Sp lo B m0 m j10 p40 b p6 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 k q H Hb Hkq.
  pose proof (op2_body_cell Sp lo B m0 m j10 p40 b p6 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 H) as HC.
  pose proof (op2_cell_split3 m (Sp + 80) 34 b k q Hkq Hb HC) as HS.
  change (rw_cells rsegs m (Sp + 80) ([CB k (firstn k b)] ++ [CB q (firstn q (skipn k b))] ++
                                       [CB (34 - k - q) (skipn (k + q) b)])) in HS.
  apply op2_rw_app in HS as [_ HS]. apply op2_rw_app in HS as [HS _].
  cbn [cells_size csize] in HS. rewrite Nat.add_0_r in HS. exact HS.
Qed.

(* op2_mem after a callee that writes the span [X, X + n) of the frame (memset / memcpy into body[]) *)
Lemma op2_mem_span : forall Sp lo B m0 m m' fr fr' X n,
  op2_mem Sp lo B m0 m fr -> Sp <= X -> 0 <= n -> X + n <= Sp + 224 ->
  munch [(X, X + n)] m m' -> wmono rsegs m m' -> mem_inv rsegs m' ->
  rw_cells rsegs m' Sp fr' -> cells_size fr' = 224%nat ->
  op2_mem Sp lo B m0 m' fr'.
Proof.
  intros Sp lo B m0 m m' fr fr' X n HM HX Hn HXn MU WMO MI HRW HS.
  pose proof HM as HM1. unfold op2_mem in HM1.
  destruct HM1 as (_ & _ & _ & _ & HSTK & HLO & HSP2 & _ & HOWS & _ & _ & _ & _ & HWM & HFN & _ & _).
  unfold LLVM_LOOP_K in HLO.
  apply (op2_mem_after Sp lo 0 B B m0 m m' fr fr'); try assumption.
  - unfold LLVM_LOOP_K; lia.
  - intros x Hx. apply MU. cbn [outside] in *. unfold LLVM_FRAME in Hx.
    destruct Hx as (H1 & H2 & _). split; [lia | exact I].
  - eapply stk_transport_disjoint; [exact HSTK | exact MU | exact WMO |].
    cbn [disjoint_from]. split; [lia | exact I].
  - eapply rw_cells_transport; [exact HWM | exact MU | exact WMO |].
    rewrite wm_size. cbn [disjoint_from]. split; [lia | exact I].
Qed.

(* op2_mem after a callee that writes v at k of body[] (the span [Sp + 80 + k, Sp + 80 + k + q)) *)
Lemma op2_body_put : forall Sp lo B m0 m m' j10 p40 b p6 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
    (k q : nat) (v : list byte),
  op2_mem Sp lo B m0 m (op2_fr j10 p40 b p6 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
  length b = 34%nat -> (k + q <= 34)%nat -> length v = q ->
  munch [(Sp + 80 + Z.of_nat k, Sp + 80 + Z.of_nat k + Z.of_nat q)] m m' -> wmono rsegs m m' ->
  mem_inv rsegs m' ->
  rw_cells rsegs m' (Sp + 80 + Z.of_nat k) [CB q v] ->
  op2_mem Sp lo B m0 m' (op2_fr j10 p40 (upd b (Z.of_nat k) v) p6 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11).
Proof.
  intros Sp lo B m0 m m' j10 p40 b p6 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 k q v H Hb Hkq Hv MU WMO MI HV.
  pose proof (op2_mem_rw _ _ _ _ _ _ H) as HRW.
  pose proof H as H1. unfold op2_mem in H1.
  destruct H1 as (_ & _ & _ & _ & _ & HLO & HSP2 & _ & HOWS & _ & _ & _ & _ & _ & _ & _ & _).
  change (rw_cells rsegs m Sp
    ([C8 (Z_to_bv 64 (2 ^ 32 - 3)); C8 (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_s)); CB 8 j10;
      C8 (Z_to_bv 64 0x610f); C8 (Z_to_bv 64 0xffff); CB 40 p40] ++ [CB 34 b] ++
     [CB 6 p6; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]))
    in HRW.
  apply op2_rw_app in HRW as [HPRE HRW]. apply op2_rw_app in HRW as [HB HPOST].
  cbn [cells_size csize Nat.add] in HPRE, HB, HPOST.
  change (Sp + Z.of_nat 80) with (Sp + 80) in HB, HPOST. change (Z.of_nat 34) with 34 in HPOST.
  pose proof (op2_cell_split3 m (Sp + 80) 34 b k q Hkq Hb HB) as HS.
  change (rw_cells rsegs m (Sp + 80) ([CB k (firstn k b)] ++ [CB q (firstn q (skipn k b))] ++
                                       [CB (34 - k - q) (skipn (k + q) b)])) in HS.
  apply op2_rw_app in HS as [HS1 HS]. apply op2_rw_app in HS as [_ HS3].
  cbn [cells_size csize] in HS1, HS3. rewrite !Nat.add_0_r in HS3.
  pose proof (rw_cells_bound rsegs m Sp _ HPRE) as BP. cbn [cells_size csize Nat.add] in BP.
  unfold LLVM_LOOP_K in HLO.
  assert (T : forall A cs, rw_cells rsegs m A cs ->
             A + Z.of_nat (cells_size cs) <= Sp + 80 + Z.of_nat k \/ Sp + 80 + Z.of_nat k + Z.of_nat q <= A ->
             rw_cells rsegs m' A cs).
  { intros A cs HA HD. eapply rw_cells_transport; [exact HA | exact MU | exact WMO |].
    cbn [disjoint_from]. split; [lia | exact I]. }
  apply T in HPRE; [| cbn [cells_size csize Nat.add]; lia].
  apply T in HS1; [| cbn [cells_size csize Nat.add]; lia].
  apply T in HS3; [| cbn [cells_size csize Nat.add]; lia].
  apply T in HPOST; [| cbn [cells_size csize Nat.add]; lia].
  assert (HMID : rw_cells rsegs m' (Sp + 80) [CB k (firstn k b); CB q v; CB (34 - k - q) (skipn (k + q) b)]).
  { change (rw_cells rsegs m' (Sp + 80) ([CB k (firstn k b)] ++ [CB q v] ++ [CB (34 - k - q) (skipn (k + q) b)])).
    apply op2_rw_app. split; [exact HS1|]. cbn [cells_size csize]. rewrite Nat.add_0_r.
    apply op2_rw_app. split; [exact HV|]. cbn [cells_size csize]. rewrite Nat.add_0_r.
    exact HS3. }
  apply (op2_cell_merge3 m' (Sp + 80) 34 b v k q Hkq Hb Hv) in HMID.
  apply (op2_mem_span Sp lo B m0 m m' _ _ (Sp + 80 + Z.of_nat k) (Z.of_nat q) H);
    [lia | lia | lia | exact MU | exact WMO | exact MI | | reflexivity].
  change (rw_cells rsegs m' Sp
    ([C8 (Z_to_bv 64 (2 ^ 32 - 3)); C8 (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_s)); CB 8 j10;
      C8 (Z_to_bv 64 0x610f); C8 (Z_to_bv 64 0xffff); CB 40 p40] ++ [CB 34 (upd b (Z.of_nat k) v)] ++
     [CB 6 p6; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])).
  apply op2_rw_app. split; [exact HPRE|]. cbn [cells_size csize Nat.add].
  apply op2_rw_app. split; [exact HMID|]. cbn [cells_size csize Nat.add].
  replace (Sp + 80 + 34) with (Sp + 114) by lia. exact HPOST.
Qed.

(* back to the loop's frame: the scratch cell is the three pieces again *)
Lemma op2_mem_to_llvm : forall Sp lo B m0 m j10 p40 b p6 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11,
  op2_mem Sp lo B m0 m (op2_fr j10 p40 b p6 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
  llvm_mem data D Sp lo B m0 m ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 j10 (p40 ++ b ++ p6).
Proof.
  intros Sp lo B m0 m j10 p40 b p6 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 H.
  pose proof (op2_to_llvm Sp lo B m0 m ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                [CB 8 j10] [CB 40 p40; CB 34 b; CB 6 p6] H eq_refl eq_refl) as R.
  cbn [cells_bytes cbytes] in R. rewrite !app_nil_r in R. exact R.
Qed.

(* body[] read back out of the loop's frame *)
Lemma op2_llvm_body : forall Sp lo B m0 m ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 j10 p40 b p6,
  llvm_mem data D Sp lo B m0 m ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 j10 (p40 ++ b ++ p6) ->
  length p40 = 40%nat -> length p6 = 6%nat ->
  bytes_at rsegs m (Sp + 80) b.
Proof.
  intros Sp lo B m0 m ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 j10 p40 b p6 H H40 H6.
  pose proof H as HL. unfold llvm_mem in HL.
  destruct HL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJ2 & _).
  rewrite !length_app in HJ2.
  pose proof (op2_body_bytes Sp lo B m0 m j10 _ _ _ ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                (op2_mem_of_llvm Sp lo B m0 m ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 j10 _ H)) as R.
  assert (Hb : length b = 34%nat) by lia.
  replace (firstn 34 (skipn 40 (p40 ++ b ++ p6))) with b in R; [exact R|].
  rewrite skipn_app, H40, (skipn_all2 p40) by lia. rewrite Nat.sub_diag. cbn [app skipn].
  change (skipn 0 (b ++ p6)) with (b ++ p6).
  rewrite firstn_app, Hb, Nat.sub_diag, firstn_O, app_nil_r, firstn_all2 by lia. reflexivity.
Qed.

(* ---- the state at build_and_receive's entry ----
   0x13dd8 jal build_and_receive (ra = 0x13ddc), entry 0x15be4 (build_and_receive_c.v): a0 = &SPEC_BCAST
   (0x13db4 auipc + 0x13dc0 addi: 0x1048c), a1 = &DESK (0x13db8 auipc + 0x13dc4 addi: 0x10486), a2 = send = 0,
   a3 = ack = 0, a4 = retry = 0 (0x13dcc-0x13dd4), a5 = cmd (0x13dac-0x13db0), a6 = body = sp + 0x50 (0x13dbc),
   a7 = len = 0x22 (0x13dc8); s3 / s6 the cursor after op_announce's three reads, s2 = 0x39 again (0x13d40), the
   other loop registers as at the case entry, gp and tp pinned (_lh.v). The frame holds body[] at sp + 0x50
   (j28 = p40 ++ body ++ p6). *)
Definition op2_call (m0 : word -> option byte) (gp tp : word) (Sp lo ops : Z) (c3 : fuzz_in) (Bw : list byte)
    (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (cmd : Z) (body : list byte)
    (F : bvmap 5 word) (fc : bv 32) (ms : machine_state) : Prop :=
  exists (t0 t1 t2 x8 x9 x20 x23 t3 t4 t5 t6 : word) (m : word -> option byte) (j10 p40 p6 : list byte),
    ms = MS (mkR (Z_to_bv 64 0x13ddc) (Z_to_bv 64 Sp) gp tp t0 t1 t2 x8 x9
                 (Z_to_bv 64 0x1048c) (Z_to_bv 64 0x10486) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0)
                 (Z_to_bv 64 cmd) (Z_to_bv 64 (Sp + 80)) (Z_to_bv 64 34)
                 (Z_to_bv 64 0x39) (Z_to_bv 64 (data + fi_off c3)) x20 (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_s))
                 (Z_to_bv 64 (fi_n c3)) x23 (Z_to_bv 64 1) (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_fail_next))
                 (Z_to_bv 64 (W_BASE_PLAIN + OFF_M)) (Z_to_bv 64 ops) t3 t4 t5 t6)
            F (Z_to_bv 64 build_and_receive_ENTRY) fc None m (seg_rom rsegs) /\
    0 <= ops < OPS_MAX /\ llvm_cursor D c3 /\ length p40 = 40%nat /\ length p6 = 6%nat /\
    llvm_mem data D Sp lo Bw m0 m ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 j10 (p40 ++ body ++ p6).

(* 0x13ddc addi s1, zero, 7 (the switch bound back); 0x13de0 j 0x1428c (the latch). *)
Lemma llvm_op2_post_evt : forall m0 m tp Sp lo ops c3 Bw ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc j10 j28
    x1 gp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x20 x23 x28 x29 x30 x31,
  llvm_mem data D Sp lo Bw m0 m ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 j10 j28 ->
  0 <= ops < OPS_MAX -> llvm_cursor D c3 ->
  evt rsegs (llvm_latch data D m0 gp tp Sp lo ops c3 Bw ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc)
    (MS (mkR x1 (Z_to_bv 64 Sp) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
             (Z_to_bv 64 0x39) (Z_to_bv 64 (data + fi_off c3)) x20 (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_s))
             (Z_to_bv 64 (fi_n c3)) x23 (Z_to_bv 64 1) (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_fail_next))
             (Z_to_bv 64 (W_BASE_PLAIN + OFF_M)) (Z_to_bv 64 ops) x28 x29 x30 x31)
        F (Z_to_bv 64 0x13ddc) fc None m (seg_rom rsegs)).
Proof.
  intros m0 m tp Sp lo ops c3 Bw ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc j10 j28
    x1 gp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x20 x23 x28 x29 x30 x31 HM HOPS HC.
  do 2 zstep.
  apply evt_done. unfold llvm_latch. do 22 eexists. split; [reflexivity|].
  split; [exact HOPS|]. split; [exact HC|]. exact HM.
Qed.

(* 0x13d40-0x13dd8, shared by every path: s2 = 0x39 again; name = nm % 3 by the multiply at 0x13d44-0x13d60;
   s4 = NAME[name] from the table at 0x21408 (0x13d64-0x13d70); "1.37" at body + 15 (0x13d74-0x13d90, sb at
   sp + 0x5f .. sp + 0x62); strlen(NAME[name]) (0x13d94-0x13d98); memcpy(body + 24, NAME[name], len)
   (0x13d9c-0x13da8); the arguments of build_and_receive (0x13dac-0x13dd4) and the call (0x13dd8). *)
Lemma llvm_op2_t5 : forall m0 tp Sp lo ops c3 Bw ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m
    j10 p40 b1 p6 sel nm x1 gp t0 t1 t2 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x23 t3 t4 t5 t6,
  memcpy_contract -> strlen_contract ->
  op2_mem Sp lo Bw m0 m (op2_fr j10 p40 b1 p6 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
  length p40 = 40%nat -> length b1 = 34%nat -> length p6 = 6%nat ->
  0 <= sel < 256 -> 0 <= nm < 256 -> 0 <= ops < OPS_MAX -> llvm_cursor D c3 ->
  evt rsegs (op2_call m0 gp tp Sp lo ops c3 Bw ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (op2_cmd sel)
               (upd (upd b1 15 ANN_VERSION_137) 24 (nth (Z.to_nat (nm mod 3)) op_announce_NAME [])) F fc)
    (MS (mkR x1 (Z_to_bv 64 Sp) gp tp t0 t1 t2 (Z_to_bv 64 sel) (Z_to_bv 64 nm) x10 x11 x12 x13 x14 x15 x16 x17
             x18 (Z_to_bv 64 (data + fi_off c3)) x20 (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_s))
             (Z_to_bv 64 (fi_n c3)) x23 (Z_to_bv 64 1) (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_fail_next))
             (Z_to_bv 64 (W_BASE_PLAIN + OFF_M)) (Z_to_bv 64 ops) t3 t4 t5 t6)
        F (Z_to_bv 64 0x13d40) fc None m (seg_rom rsegs)).
Proof.
  intros m0 tp Sp lo ops c3 Bw ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m
    j10 p40 b1 p6 sel nm x1 gp t0 t1 t2 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x23 t3 t4 t5 t6
    MCC STC HM H40 Hb1 H6 Hsel Hnm HOPS HC.
  pose proof HM as HM1. unfold op2_mem in HM1.
  destruct HM1 as (_ & _ & _ & HSP & _ & HLO & HSP2 & _ & HOWS & _ & _ & HMI & HRO & _ & _ & _ & _).
  assert (Hj : 0 <= nm mod 3 < 3) by (apply Z.mod_pos_bound; lia).
  pose proof (op2_table_load m (nm mod 3) HRO Hj) as HR.
  unfold LLVM_LOOP_K in HLO. unfold LLVM_FRAME in HSP2.
  pose proof wmem_end as HWE.
  assert (HSP0 : 0 <= Sp) by lia.
  do 12 zstep.
  rewrite (op2_mod3_val nm Hnm). rewrite (op2_addr_val (nm mod 3) Hj).
  (* 0x13d70 ld s4, 0(a0): NAME[name] *)
  zstep.
  (* 0x13d74-0x13d90: "1.37" into body[15 .. 18] *)
  pose proof (op2_body_carve Sp lo Bw m0 m j10 p40 b1 p6 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 15 4
                HM Hb1 ltac:(lia)) as HV.
  replace (Sp + 80 + Z.of_nat 15) with (Sp + 95) in HV by lia.
  pose proof (munch_refl [(Sp + 95, Sp + 99)] m) as MUv. pose proof (wmono_refl rsegs m) as WMv.
  clear HR HRO.
  do 8 zstep.
  lazymatch goal with H : rw_cells _ ?m2 (Sp + 95) _ |- evt _ _ (MS _ _ _ _ _ ?m2 _) =>
    assert (HV2 : rw_cells rsegs m2 (Sp + 95) [CB 4 ANN_VERSION_137]);
    [ apply (op2_rw_rebytes m2 (Sp + 95) _ _ H);
      [ cbn [cells_wf cell_wf]; split; [reflexivity | exact I]
      | apply bytes_eq_of_zs; vm_compute; reflexivity ]
    | clear H;
      assert (HM2 : op2_mem Sp lo Bw m0 m2
                      (op2_fr j10 p40 (upd b1 15 ANN_VERSION_137) p6 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11));
      [ apply (op2_body_put Sp lo Bw m0 m m2 j10 p40 b1 p6 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 15 4
                 ANN_VERSION_137 HM Hb1 ltac:(lia) eq_refl);
        [ replace (Sp + 80 + Z.of_nat 15) with (Sp + 95) by lia; replace (Sp + 95 + Z.of_nat 4) with (Sp + 99) by lia;
          exact MUv
        | exact WMv | assumption | replace (Sp + 80 + Z.of_nat 15) with (Sp + 95) by lia; exact HV2 ]
      | clear HV2 MUv WMv HM ] ] end.
  rename m2 into mA.
  set (b2 := upd b1 15 ANN_VERSION_137) in *.
  assert (Hb2 : length b2 = 34%nat).
  { unfold b2. rewrite length_upd; [exact Hb1 | lia | rewrite Hb1; unfold ANN_VERSION_137, bs; cbn; lia]. }
  (* 0x13d94 mv a0, s4; 0x13d98 jal strlen *)
  set (str := nth (Z.to_nat (nm mod 3)) op_announce_NAME []) in *.
  pose proof (op2_namep_range (nm mod 3) Hj) as HPR.
  pose proof (op2_name_len (nm mod 3) Hj) as HLS. fold str in HLS.
  destruct (op2_name_facts mA (nm mod 3) HMI Hj) as (HS & HN0 & HAL). fold str in HS, HN0, HAL.
  do 2 zstep.
  eapply evt_cut.
  { eapply STC with (str := str) (slack := op2_slack (nm mod 3)).
    - rewrite unsigned_lit by lia. exact HS.
    - exact HN0.
    - rewrite unsigned_lit by lia. exact HAL.
    - exact HMI. }
  intros ms' Hpost. unfold strlen_post in Hpost.
  destruct Hpost as (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & w3 & w4 & w5 & w6 & mB &
                     -> & MU3 & WMO3 & MI3 & HS3).
  rewrite unsigned_lit in HS3 by lia.
  assert (HM3 : op2_mem Sp lo Bw m0 mB (op2_fr j10 p40 b2 p6 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11)).
  { apply (op2_mem_span Sp lo Bw m0 mA mB _ _ Sp 0 HM2); [lia | lia | lia | | exact WMO3 | exact MI3 | | reflexivity].
    - intros x _. apply MU3. exact I.
    - eapply rw_cells_transport; [exact (op2_mem_rw _ _ _ _ _ _ HM2) | exact MU3 | exact WMO3 | exact I]. }
  clear HM2 MU3 WMO3 HMI HS.
  rewrite (ret_pc_even 0x13d9c) by (first [lia | reflexivity]).
  (* 0x13d9c mv a2, a0; 0x13da0 addi a0, sp, 0x68; 0x13da4 mv a1, s4; 0x13da8 jal memcpy: NAME[name] to body[24] *)
  pose proof (op2_body_carve Sp lo Bw m0 mB j10 p40 b2 p6 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 24 (length str)
                HM3 Hb2 ltac:(lia)) as HD.
  replace (Sp + 80 + Z.of_nat 24) with (Sp + 104) in HD by lia.
  pose proof (proj1 (proj1 (bytes_at_app rsegs mB _ str _) HS3)) as HSRC.
  do 4 zstep.
  eapply evt_cut.
  { eapply MCC with (src := str) (junk := firstn (length str) (skipn 24 b2)).
    - rewrite unsigned_lit by lia. exact HSRC.
    - rewrite unsigned_lit by lia. rewrite Nat2Z.id. reflexivity.
    - rewrite !unsigned_lit by lia. rewrite Nat2Z.id. exact HD.
    - rewrite !unsigned_lit by lia. left. lia.
    - exact MI3. }
  intros ms' Hpost. unfold memcpy_post in Hpost.
  destruct Hpost as (y0 & y1 & y2 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & q3 & q4 & q5 & q6 & mC &
                     -> & MU4 & WMO4 & MI4 & HD4 & _).
  rewrite !unsigned_lit in MU4, HD4 by lia. rewrite Nat2Z.id in HD4.
  assert (HM4 : op2_mem Sp lo Bw m0 mC (op2_fr j10 p40 (upd b2 24 str) p6 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11)).
  { apply (op2_body_put Sp lo Bw m0 mB mC j10 p40 b2 p6 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 24 (length str) str
             HM3 Hb2 ltac:(lia) eq_refl);
      [ replace (Sp + 80 + Z.of_nat 24) with (Sp + 104) by lia; exact MU4 | exact WMO4 | exact MI4
      | replace (Sp + 80 + Z.of_nat 24) with (Sp + 104) by lia; exact HD4 ]. }
  clear HM3 MU4 WMO4 HD4 HD HSRC HS3.
  rewrite (ret_pc_even 0x13dac) by (first [lia | reflexivity]).
  (* 0x13dac-0x13dd8: cmd, &SPEC_BCAST, &DESK, body, len, send = ack = retry = 0; jal build_and_receive *)
  do 12 zstep.
  rewrite (op2_cmd_val sel Hsel).
  apply evt_done. unfold op2_call.
  do 15 eexists. split; [reflexivity|].
  split; [exact HOPS|]. split; [exact HC|]. split; [exact H40|]. split; [exact H6|].
  exact (op2_mem_to_llvm Sp lo Bw m0 mC j10 p40 (upd b2 24 str) p6 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 HM4).
Qed.

(* 0x13d38 addi a2, zero, 6; 0x13d3c jal memcpy: the 6-byte MAC at macp (HOST or OTHER in .rodata) to body + k,
   then the shared tail at 0x13d40. Joined from 0x13d28 (mac < 10, HOST at mac) and 0x13cf4 (10 <= mac <= 12,
   OTHER at mac - 10). *)
Lemma llvm_op2_t4 : forall m0 tp Sp lo ops c3 Bw ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m
    j10 p40 p6 sel nm (k : nat) macp mac x1 gp t0 t1 t2 x12 x13 x14 x15 x16 x17 x18 x20 x23 t3 t4 t5 t6,
  memcpy_contract -> strlen_contract ->
  op2_mem Sp lo Bw m0 m (op2_fr j10 p40 op2_body0 p6 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
  length p40 = 40%nat -> length p6 = 6%nat -> (k + 6 <= 34)%nat ->
  ro_bytes_b rsegs macp mac = true -> length mac = 6%nat -> 0 <= macp < 0x20000 ->
  0 <= sel < 256 -> 0 <= nm < 256 -> 0 <= ops < OPS_MAX -> llvm_cursor D c3 ->
  evt rsegs (op2_call m0 gp tp Sp lo ops c3 Bw ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (op2_cmd sel)
               (upd (upd (upd op2_body0 (Z.of_nat k) mac) 15 ANN_VERSION_137) 24
                  (nth (Z.to_nat (nm mod 3)) op_announce_NAME [])) F fc)
    (MS (mkR x1 (Z_to_bv 64 Sp) gp tp t0 t1 t2 (Z_to_bv 64 sel) (Z_to_bv 64 nm)
             (Z_to_bv 64 (Sp + 80 + Z.of_nat k)) (Z_to_bv 64 macp) x12 x13 x14 x15 x16 x17
             x18 (Z_to_bv 64 (data + fi_off c3)) x20 (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_s))
             (Z_to_bv 64 (fi_n c3)) x23 (Z_to_bv 64 1) (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_fail_next))
             (Z_to_bv 64 (W_BASE_PLAIN + OFF_M)) (Z_to_bv 64 ops) t3 t4 t5 t6)
        F (Z_to_bv 64 0x13d38) fc None m (seg_rom rsegs)).
Proof.
  intros m0 tp Sp lo ops c3 Bw ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m
    j10 p40 p6 sel nm k macp mac x1 gp t0 t1 t2 x12 x13 x14 x15 x16 x17 x18 x20 x23 t3 t4 t5 t6
    MCC STC HM H40 H6 Hk Hro Hml Hmp Hsel Hnm HOPS HC.
  pose proof HM as HM1. unfold op2_mem in HM1.
  destruct HM1 as (_ & _ & _ & HSP & _ & HLO & HSP2 & _ & HOWS & _ & _ & HMI & _ & _ & _ & _ & _).
  unfold LLVM_LOOP_K in HLO. unfold LLVM_FRAME in HSP2. pose proof wmem_end as HWE.
  assert (HSRC : bytes_at rsegs m macp mac).
  { apply ro_bytes_at; [exact HMI | lia | rewrite Hml; lia | apply ro_bytes_b_sound; exact Hro]. }
  pose proof (op2_body_carve Sp lo Bw m0 m j10 p40 op2_body0 p6 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 k 6
                HM op2_body0_length Hk) as HD.
  do 2 zstep.
  eapply evt_cut.
  { eapply MCC with (src := mac) (junk := firstn 6 (skipn k op2_body0)).
    - rewrite unsigned_lit by lia. exact HSRC.
    - rewrite unsigned_lit by lia. rewrite Hml. reflexivity.
    - rewrite !unsigned_lit by lia. exact HD.
    - rewrite !unsigned_lit by lia. left. lia.
    - exact HMI. }
  intros ms' Hpost. unfold memcpy_post in Hpost.
  destruct Hpost as (y0 & y1 & y2 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & q3 & q4 & q5 & q6 & mC &
                     -> & MU4 & WMO4 & MI4 & HD4 & _).
  rewrite !unsigned_lit in MU4, HD4 by lia.
  assert (HM4 : op2_mem Sp lo Bw m0 mC
                  (op2_fr j10 p40 (upd op2_body0 (Z.of_nat k) mac) p6 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11)).
  { apply (op2_body_put Sp lo Bw m0 m mC j10 p40 op2_body0 p6 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 k 6 mac
             HM op2_body0_length Hk Hml); [exact MU4 | exact WMO4 | exact MI4 | exact HD4]. }
  rewrite (ret_pc_even 0x13d40) by (first [lia | reflexivity]).
  eapply llvm_op2_t5; [exact MCC | exact STC | exact HM4 | exact H40 | | exact H6 | exact Hsel | exact Hnm
                      | exact HOPS | exact HC].
  rewrite length_upd; [exact op2_body0_length | lia | rewrite Hml, op2_body0_length; lia].
Qed.

(* 0x13d28 addi a0, sp, 0x50; 0x13d2c add a0, a0, s2; 0x13d30-0x13d34 a1 = HOST (0x13d30 auipc a1, 0xffffc and
   addi a1, a1, 0x750: 0x10480), then 0x13d38: HOST at body + mac, for mac < 10. Joined from 0x13ce8 (mac < 10)
   and 0x13d24 (no mac byte: mac = 0). *)
Lemma llvm_op2_t3 : forall m0 tp Sp lo ops c3 Bw ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m
    j10 p40 p6 sel nm mac x1 gp t0 t1 t2 x10 x11 x12 x13 x14 x15 x16 x17 x20 x23 t3 t4 t5 t6,
  memcpy_contract -> strlen_contract ->
  op2_mem Sp lo Bw m0 m (op2_fr j10 p40 op2_body0 p6 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
  length p40 = 40%nat -> length p6 = 6%nat -> 0 <= mac < 10 ->
  0 <= sel < 256 -> 0 <= nm < 256 -> 0 <= ops < OPS_MAX -> llvm_cursor D c3 ->
  evt rsegs (op2_call m0 gp tp Sp lo ops c3 Bw ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (op2_cmd sel)
               (op2_body3 mac (nm mod 3)) F fc)
    (MS (mkR x1 (Z_to_bv 64 Sp) gp tp t0 t1 t2 (Z_to_bv 64 sel) (Z_to_bv 64 nm)
             x10 x11 x12 x13 x14 x15 x16 x17
             (Z_to_bv 64 mac) (Z_to_bv 64 (data + fi_off c3)) x20 (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_s))
             (Z_to_bv 64 (fi_n c3)) x23 (Z_to_bv 64 1) (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_fail_next))
             (Z_to_bv 64 (W_BASE_PLAIN + OFF_M)) (Z_to_bv 64 ops) t3 t4 t5 t6)
        F (Z_to_bv 64 0x13d28) fc None m (seg_rom rsegs)).
Proof.
  intros m0 tp Sp lo ops c3 Bw ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m
    j10 p40 p6 sel nm mac x1 gp t0 t1 t2 x10 x11 x12 x13 x14 x15 x16 x17 x20 x23 t3 t4 t5 t6
    MCC STC HM H40 H6 Hmac Hsel Hnm HOPS HC.
  pose proof HM as HM1. unfold op2_mem in HM1.
  destruct HM1 as (_ & _ & _ & HSP & _ & HLO & HSP2 & _ & HOWS & _ & _ & _ & _ & _ & _ & _ & _).
  unfold LLVM_LOOP_K in HLO. unfold LLVM_FRAME in HSP2. pose proof wmem_end as HWE.
  do 4 zstep.
  pose proof (llvm_op2_t4 m0 tp Sp lo ops c3 Bw ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m
                j10 p40 p6 sel nm (Z.to_nat mac) 0x10480 HOST) as T.
  rewrite Z2Nat.id in T by lia.
  unfold op2_body3, op2_body2, op2_body1. rewrite (proj2 (Z.ltb_lt mac 10) ltac:(lia)).
  eapply T; [exact MCC | exact STC | exact HM | exact H40 | exact H6 | lia | vm_compute; reflexivity
            | reflexivity | lia | exact Hsel | exact Hnm | exact HOPS | exact HC].
Qed.

(* op2_mem after memset(body, 0, 34) (0x13ce0 / 0x13d18): body[] is op_announce_m's body0 *)
Lemma op2_after_memset : forall Sp lo B m0 m m' j10 p40 b p6 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11,
  op2_mem Sp lo B m0 m (op2_fr j10 p40 b p6 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) -> length b = 34%nat ->
  munch [(Sp + 80, Sp + 80 + 34)] m m' -> wmono rsegs m m' -> mem_inv rsegs m' ->
  rw_cells rsegs m' (Sp + 80) [CB 34 (repeat (Z_to_bv 8 0) 34)] ->
  op2_mem Sp lo B m0 m' (op2_fr j10 p40 op2_body0 p6 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11).
Proof.
  intros Sp lo B m0 m m' j10 p40 b p6 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 H Hb MU WMO MI HC.
  pose proof (op2_body_put Sp lo B m0 m m' j10 p40 b p6 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 0 34
                (repeat (Z_to_bv 8 0) 34) H Hb ltac:(lia) (repeat_length _ _)) as R.
  replace (upd b (Z.of_nat 0) (repeat (Z_to_bv 8 0) 34)) with op2_body0 in R.
  - apply R; replace (Sp + 80 + Z.of_nat 0) with (Sp + 80) by lia; [| exact WMO | exact MI | exact HC].
    exact MU.
  - unfold op2_body0. rewrite (op2_upd_split b (repeat (Z_to_bv 8 0) 34) 0) by (rewrite repeat_length; lia).
    rewrite repeat_length. rewrite (skipn_all2 b) by (cbn; lia). cbn [firstn app]. rewrite app_nil_r.
    reflexivity.
Qed.

(* one byte of the input buffer, as the code's lbu reads it (op08's form) *)
Lemma op2_byte : forall m k, bytes_at rsegs m data D -> 0 <= k -> (Z.to_nat k < length D)%nat ->
  ov_read_bytes rsegs m (wa (data + k)) 1 = Some [nth (Z.to_nat k) D (b8 0)] /\
  0 <= bv_unsigned (nth (Z.to_nat k) D (b8 0)) < 256.
Proof.
  intros m k HD Hk Hl. split.
  - pose proof (bytes_at_read rsegs m data D k 1 HD Hk ltac:(lia)) as HR.
    rewrite disp_sub1 in HR by lia. exact HR.
  - pose proof (bv_unsigned_in_range 8 (nth (Z.to_nat k) D (b8 0))) as R. unfold bv_modulus in R.
    change (2 ^ Z.of_N 8) with 256 in R. lia.
Qed.

(* 0x13d0c-0x13d24, the paths with no mac byte (fi_n c = 1 from 0x13b74, fi_n c = 2 from 0x13d08):
   memset(body, 0, 0x22) (0x13d0c-0x13d18), then s6 = s1 = s2 = 0 (mac = nm = 0, the cursor's n 0) and 0x13d28. *)
Lemma llvm_op2_t2 : forall m0 tp Sp lo ops off3 Bw ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m
    j10 j28 sel x1 gp t0 t1 t2 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x22 x23 t3 t4 t5 t6,
  memset_contract -> memcpy_contract -> strlen_contract ->
  llvm_mem data D Sp lo Bw m0 m ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 j10 j28 ->
  0 <= sel < 256 -> 0 <= ops < OPS_MAX -> llvm_cursor D (FuzzIn off3 0) ->
  evt rsegs (op2_call m0 gp tp Sp lo ops (FuzzIn off3 0) Bw ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (op2_cmd sel)
               (op2_body3 0 0) F fc)
    (MS (mkR x1 (Z_to_bv 64 Sp) gp tp t0 t1 t2 (Z_to_bv 64 sel) x9 x10 x11 x12 x13 x14 x15 x16 x17
             x18 (Z_to_bv 64 (data + off3)) x20 (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_s))
             x22 x23 (Z_to_bv 64 1) (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_fail_next))
             (Z_to_bv 64 (W_BASE_PLAIN + OFF_M)) (Z_to_bv 64 ops) t3 t4 t5 t6)
        F (Z_to_bv 64 0x13d0c) fc None m (seg_rom rsegs)).
Proof.
  intros m0 tp Sp lo ops off3 Bw ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m
    j10 j28 sel x1 gp t0 t1 t2 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x22 x23 t3 t4 t5 t6
    MSC MCC STC HL Hsel HOPS HC.
  pose proof HL as HL1. unfold llvm_mem in HL1.
  destruct HL1 as (_ & _ & _ & HSP & _ & HLO & HSP2 & _ & HOWS & _ & _ & HMI & _ & _ & _ & _ & HJ2 & _).
  unfold LLVM_LOOP_K in HLO. unfold LLVM_FRAME in HSP2. pose proof wmem_end as HWE.
  pose proof (op2_mem_of_llvm Sp lo Bw m0 m ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 j10 j28 HL) as HM.
  assert (Hb0 : length (firstn 34 (skipn 40 j28)) = 34%nat) by (rewrite length_firstn, length_skipn; lia).
  pose proof (op2_body_carve Sp lo Bw m0 m j10 _ _ _ ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 0 34
                HM Hb0 ltac:(lia)) as HD.
  replace (Sp + 80 + Z.of_nat 0) with (Sp + 80) in HD by lia.
  do 4 zstep.
  eapply evt_cut.
  { eapply MSC with (junk := firstn 34 (skipn 0 (firstn 34 (skipn 40 j28)))).
    - rewrite !unsigned_lit by lia. exact HD.
    - exact HMI. }
  intros ms' Hpost. unfold memset_post in Hpost.
  destruct Hpost as (w0 & w1 & w2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m1 &
                     -> & MU1 & WMO1 & MI1 & CZ1).
  rewrite !unsigned_lit in MU1, CZ1 by lia.
  pose proof (op2_after_memset Sp lo Bw m0 m m1 j10 _ _ _ ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                HM Hb0 MU1 WMO1 MI1 CZ1) as HM1.
  rewrite (ret_pc_even 0x13d1c) by (first [lia | reflexivity]).
  do 3 zstep.
  eapply (llvm_op2_t3 m0 tp Sp lo ops (FuzzIn off3 0));
                      [exact MCC | exact STC | exact HM1 | rewrite length_firstn; lia
                      | rewrite length_skipn; lia | lia | exact Hsel | lia | exact HOPS | exact HC].
Qed.

(* 0x13ccc-0x13d04, the paths that read the mac byte (fi_n c >= 3): mac = D[c + 2] & 0xf (0x13ccc-0x13cd0),
   memset(body, 0, 0x22) (0x13cd4-0x13ce0), then mac < 10: HOST at mac (0x13ce8 to 0x13d28); 12 < mac: no copy
   (0x13cf0 to 0x13d40); else 0x13cf4-0x13d04: a0 = sp + 0x46 + mac = body + (mac - 10), a1 = OTHER
   (0x13cfc auipc a1, 0xffffc and addi a1, a1, 0x7cc: 0x104c8), j 0x13d38. *)
Lemma llvm_op2_t1 : forall m0 tp Sp lo ops c c3 Bw ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m
    j10 j28 sel nm x1 gp t0 t1 t2 x10 x11 x12 x13 x14 x15 x16 x17 x18 x23 t3 t4 t5 t6,
  memset_contract -> memcpy_contract -> strlen_contract ->
  llvm_mem data D Sp lo Bw m0 m ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 j10 j28 ->
  llvm_cursor D c -> 3 <= fi_n c ->
  0 <= sel < 256 -> 0 <= nm < 256 -> 0 <= ops < OPS_MAX -> llvm_cursor D c3 ->
  evt rsegs (op2_call m0 gp tp Sp lo ops c3 Bw ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (op2_cmd sel)
               (op2_body3 (at8 D (Z.to_nat (fi_off c + 2)) mod 16) (nm mod 3)) F fc)
    (MS (mkR x1 (Z_to_bv 64 Sp) gp tp t0 t1 t2 (Z_to_bv 64 sel) (Z_to_bv 64 nm) x10 x11 x12 x13 x14 x15 x16 x17
             x18 (Z_to_bv 64 (data + fi_off c3)) (Z_to_bv 64 (data + fi_off c)) (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_s))
             (Z_to_bv 64 (fi_n c3)) x23 (Z_to_bv 64 1) (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_fail_next))
             (Z_to_bv 64 (W_BASE_PLAIN + OFF_M)) (Z_to_bv 64 ops) t3 t4 t5 t6)
        F (Z_to_bv 64 0x13ccc) fc None m (seg_rom rsegs)).
Proof.
  intros m0 tp Sp lo ops c c3 Bw ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m
    j10 j28 sel nm x1 gp t0 t1 t2 x10 x11 x12 x13 x14 x15 x16 x17 x18 x23 t3 t4 t5 t6
    MSC MCC STC HL HCc Hn3 Hsel Hnm HOPS HC.
  pose proof HL as HL1. unfold llvm_mem in HL1.
  destruct HL1 as (_ & _ & HDa & HSP & _ & HLO & HSP2 & _ & HOWS & _ & _ & HMI & _ & _ & _ & _ & HJ2 & _).
  unfold LLVM_LOOP_K in HLO. unfold LLVM_FRAME in HSP2. pose proof wmem_end as HWE.
  unfold llvm_cursor, FUZZ_INPUT_MAX in HCc.
  pose proof (bytes_at_bound rsegs m data D HDa) as HDB.
  destruct (op2_byte m (fi_off c + 2) HDa ltac:(lia) ltac:(lia)) as [HR2 Hmb].
  pose proof (op2_mem_of_llvm Sp lo Bw m0 m ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 j10 j28 HL) as HM.
  assert (Hb0 : length (firstn 34 (skipn 40 j28)) = 34%nat) by (rewrite length_firstn, length_skipn; lia).
  pose proof (op2_body_carve Sp lo Bw m0 m j10 _ _ _ ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 0 34
                HM Hb0 ltac:(lia)) as HD.
  replace (Sp + 80 + Z.of_nat 0) with (Sp + 80) in HD by lia.
  clear HDa.
  do 6 zstep.
  eapply evt_cut.
  { eapply MSC with (junk := firstn 34 (skipn 0 (firstn 34 (skipn 40 j28)))).
    - rewrite !unsigned_lit by lia. exact HD.
    - exact HMI. }
  intros ms' Hpost. unfold memset_post in Hpost.
  destruct Hpost as (w0 & w1 & w2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m1 &
                     -> & MU1 & WMO1 & MI1 & CZ1).
  rewrite !unsigned_lit in MU1, CZ1 by lia.
  pose proof (op2_after_memset Sp lo Bw m0 m m1 j10 _ _ _ ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                HM Hb0 MU1 WMO1 MI1 CZ1) as HM1.
  assert (H40 : length (firstn 40 j28) = 40%nat) by (rewrite length_firstn; lia).
  assert (H6 : length (skipn 74 j28) = 6%nat) by (rewrite length_skipn; lia).
  rewrite (ret_pc_even 0x13ce4) by (first [lia | reflexivity]).
  do 2 zstep.
  set (mbv := bv_unsigned (nth (Z.to_nat (fi_off c + 2)) D (b8 0))) in *.
  assert (Hmac : Z.land mbv 15 = mbv mod 16)
    by (change 15 with (Z.ones 4); rewrite Z.land_ones by lia; reflexivity).
  rewrite Hmac. change (at8 D (Z.to_nat (fi_off c + 2))) with mbv.
  assert (HMR : 0 <= mbv mod 16 < 16) by (apply Z.mod_pos_bound; lia).
  set (mac := mbv mod 16) in *.
  if_cases K; zify_cond K.
  - (* mac < 10: 0x13d28 *)
    assert (Kc : mac < 10) by (rewrite ?Z.mod_small in K by lia; lia).
    eapply (llvm_op2_t3 m0 tp Sp lo ops c3);
      [exact MCC | exact STC | exact HM1 | exact H40 | exact H6 | lia | exact Hsel | exact Hnm | exact HOPS
      | exact HC].
  - assert (Kc : 10 <= mac) by (rewrite ?Z.mod_small in K by lia; lia).
    do 2 zstep.
    if_cases K2; zify_cond K2.
    + (* 12 < mac: no copy, 0x13d40 *)
      assert (K2c : 12 < mac) by (rewrite ?Z.mod_small in K2 by lia; lia).
      unfold op2_body3, op2_body2, op2_body1.
      rewrite (proj2 (Z.ltb_ge mac 10) ltac:(lia)), (proj2 (Z.ltb_ge mac 13) ltac:(lia)).
      eapply (llvm_op2_t5 m0 tp Sp lo ops c3);
        [exact MCC | exact STC | exact HM1 | exact H40 | exact op2_body0_length | exact H6 | exact Hsel
        | exact Hnm | exact HOPS | exact HC].
    + (* 10 <= mac <= 12: OTHER at mac - 10, 0x13cf4-0x13d04 *)
      assert (K2c : mac <= 12) by (rewrite ?Z.mod_small in K2 by lia; lia).
      do 5 zstep.
      pose proof (llvm_op2_t4 m0 tp Sp lo ops c3 Bw ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m1
                    j10 (firstn 40 j28) (skipn 74 j28) sel nm (Z.to_nat (mac - 10)) 0x104c8 OTHER) as T.
      rewrite Z2Nat.id in T by lia.
      replace (Sp + 70 + mac) with (Sp + 80 + (mac - 10)) by lia.
      unfold op2_body3, op2_body2, op2_body1.
      rewrite (proj2 (Z.ltb_ge mac 10) ltac:(lia)), (proj2 (Z.ltb_lt mac 13) ltac:(lia)).
      eapply T; [exact MCC | exact STC | exact HM1 | exact H40 | exact H6 | lia | vm_compute; reflexivity
                | reflexivity | lia | exact Hsel | exact Hnm | exact HOPS | exact HC].
Qed.

Lemma llvm_op2_pre_evt : forall m0 gp tp Sp lo ops c c1 c2 c3' c3 sel mb nm Bw
    ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ms,
  memset_contract -> memcpy_contract -> strlen_contract ->
  llvm_case data D m0 gp tp 2 Sp lo ops c c1 Bw ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ms ->
  fuzz_u8_m D c1 = (c2, sel) -> fuzz_u8_m D c2 = (c3', mb) -> fuzz_u8_m D c3' = (c3, nm) ->
  evt rsegs (op2_call m0 gp tp Sp lo ops c3 Bw ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (op2_cmd sel)
               (op2_body3 (mb mod 16) (nm mod 3)) F fc) ms.
Proof.
  intros m0 gp tp Sp lo ops c c1 c2 c3' c3 sel mb nm Bw ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ms
    MSC MCC STC H E1 E2 E3.
  destruct H as (rr & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & r8 &
                 t3 & t4 & t5 & t6 & m & j10 & j28 & -> & HOPS & HN & HC & HC1 & HM).
  pose proof HM as HM0. unfold llvm_mem in HM.
  destruct HM as (_ & _ & HD & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _).
  pose proof (bytes_at_bound rsegs m data D HD) as HDB.
  pose proof HC as HCc. unfold llvm_cursor, FUZZ_INPUT_MAX in HCc.
  assert (U1 : forall cc, fi_n cc <> 0 ->
            fuzz_u8_m D cc = (FuzzIn (fi_off cc + 1) (fi_n cc - 1), at8 D (Z.to_nat (fi_off cc)))).
  { intros cc Hcc. unfold fuzz_u8_m. destruct (Z.eqb_spec (fi_n cc) 0); [lia | reflexivity]. }
  assert (U0 : forall cc, fi_n cc = 0 -> fuzz_u8_m D cc = (cc, 0)).
  { intros cc Hcc. unfold fuzz_u8_m. rewrite Hcc. reflexivity. }
  rewrite (U1 c HN) in HC1. cbn [fst] in HC1. subst c1.
  unfold LLVM_CASE. cbn [Z.eqb Pos.eqb]. cbn [fi_off fi_n].
  (* ---- 0x139a4 beqz s6: the op byte was the cursor's last ---- *)
  zstep.
  if_cases K; zify_cond K.
  - assert (K1 : fi_n c = 1) by (rewrite ?Z.mod_small in K by lia; lia).
    rewrite U0 in E1 by (cbn; lia). injection E1 as <- <-.
    rewrite U0 in E2 by (cbn; lia). injection E2 as <- <-.
    rewrite U0 in E3 by (cbn; lia). injection E3 as <- <-.
    (* 0x13b74 mv s0, zero; 0x13b78 j 0x13d0c *)
    do 2 zstep.
    replace (fi_n c - 1) with 0 by lia.
    eapply (llvm_op2_t2 m0 tp Sp lo ops (fi_off c + 1));
      [exact MSC | exact MCC | exact STC | exact HM0 | lia | exact HOPS | unfold llvm_cursor, FUZZ_INPUT_MAX; cbn; lia].
  - assert (K2 : 2 <= fi_n c) by (rewrite ?Z.mod_small in K by lia; lia).
    rewrite U1 in E1 by (cbn; lia). cbn [fi_off fi_n] in E1. injection E1 as <- <-.
    destruct (op2_byte m (fi_off c + 1) HD ltac:(lia) ltac:(lia)) as [HR1 Hb1].
    (* 0x139a8 lbu s0, 1(s4); 0x139ac li a0, 2; 0x139b0 beq s7, a0 *)
    do 3 zstep.
    if_cases K3; zify_cond K3.
    + (* fi_n c = 2: 0x13d08 addi s3, s4, 2 *)
      assert (K4 : fi_n c = 2) by (rewrite ?Z.mod_small in K3 by lia; lia).
      rewrite U0 in E2 by (cbn; lia). injection E2 as <- <-.
      rewrite U0 in E3 by (cbn; lia). injection E3 as <- <-.
      zstep.
      try replace (fi_off c + 1 + 1) with (fi_off c + 2) by lia.
      replace (fi_n c - 1 - 1) with 0 by lia.
      replace (data + fi_off c + 2) with (data + (fi_off c + 2)) by lia.
      eapply (llvm_op2_t2 m0 tp Sp lo ops (fi_off c + 2));
        [exact MSC | exact MCC | exact STC | exact HM0 | exact Hb1 | exact HOPS
        | unfold llvm_cursor, FUZZ_INPUT_MAX; cbn; lia].
    + assert (K4 : 3 <= fi_n c) by (rewrite ?Z.mod_small in K3 by lia; lia).
      rewrite U1 in E2 by (cbn; lia). cbn [fi_off fi_n] in E2. injection E2 as <- <-.
      (* 0x139b4 li a0, 3; 0x139b8 bne s7, a0 *)
      do 2 zstep.
      if_cases K5; zify_cond K5.
      * (* fi_n c >= 4: 0x13cc0 lbu s1, 3(s4); 0x13cc4 addi s6, s7, -4; 0x13cc8 addi s3, s4, 4 *)
        assert (K6 : 4 <= fi_n c) by (rewrite ?Z.mod_small in K5 by lia; lia).
        rewrite U1 in E3 by (cbn; lia). cbn [fi_off fi_n] in E3. injection E3 as <- <-.
        destruct (op2_byte m (fi_off c + 3) HD ltac:(lia) ltac:(lia)) as [HR3 Hb3].
        do 3 zstep.
        try replace (fi_off c + 1 + 1 + 1) with (fi_off c + 3) by lia.
        try replace (fi_off c + 1 + 1) with (fi_off c + 2) by lia.
        try replace (fi_n c - 1 - 1 - 1 - 1) with (fi_n c - 4) by lia.
        try replace (fi_n c + -4) with (fi_n c - 4) by lia.
        try replace (data + fi_off c + 4) with (data + (fi_off c + 4)) by lia.
        eapply (llvm_op2_t1 m0 tp Sp lo ops c (FuzzIn (fi_off c + 4) (fi_n c - 4)));
          [exact MSC | exact MCC | exact STC | exact HM0 | exact HC | lia | exact Hb1 | exact Hb3 | exact HOPS
          | unfold llvm_cursor, FUZZ_INPUT_MAX; cbn; lia].
      * (* fi_n c = 3: 0x139bc mv s6, zero; mv s1, zero; addi s3, s4, 3; j 0x13ccc *)
        assert (K6 : fi_n c = 3) by (rewrite ?Z.mod_small in K5 by lia; lia).
        rewrite U0 in E3 by (cbn; lia). injection E3 as <- <-.
        do 4 zstep.
        try replace (fi_off c + 1 + 1 + 1) with (fi_off c + 3) by lia.
        try replace (fi_off c + 1 + 1) with (fi_off c + 2) by lia.
        try replace (fi_n c - 1 - 1 - 1) with 0 by lia.
        try replace (data + fi_off c + 3) with (data + (fi_off c + 3)) by lia.
        eapply (llvm_op2_t1 m0 tp Sp lo ops c (FuzzIn (fi_off c + 3) 0));
          [exact MSC | exact MCC | exact STC | exact HM0 | exact HC | lia | exact Hb1 | lia | exact HOPS
          | unfold llvm_cursor, FUZZ_INPUT_MAX; cbn; lia].
Qed.
End OP2.

(* ---------------------------------------------------------------- the SR level *)

Section OP2SR.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Context (data : Z) (D : list byte).

(* op_announce_m from the case's cursor c1, its three reads named *)
Lemma op2_announce_eq : forall c1 c2 sel c3' mb c3 nm Bw a,
  fuzz_u8_m D c1 = (c2, sel) -> fuzz_u8_m D c2 = (c3', mb) -> fuzz_u8_m D c3' = (c3, nm) ->
  op_announce_m timg_plain Bw D a c1 =
    match build_and_receive_m timg_plain Bw a SPEC_BCAST DESK 0 0 0 (op2_cmd sel)
            (op2_body3 (mb mod 16) (nm mod 3)) with
    | Some (B1, _) => Some (B1, c3)
    | None => None
    end.
Proof.
  intros c1 c2 sel c3' mb c3 nm Bw a E1 E2 E3.
  rewrite (op2_announce_unfold timg_plain Bw D a c1 c2 sel c3' mb c3 nm E1 E2 E3). reflexivity.
Qed.

(* Case 2 of the op loop (fuzz_transport.c:1175-1177 `case 2: op_announce(&in); break;`, TOps.v's op =? 2 branch)
   at the SR level: from the case's SR config (LLVM_CASE 2 = 0x139a4), the evt segment to build_and_receive's entry
   (llvm_op2_pre_evt, through TSRGlue.v g_run), the call (_sr.v llvm_sr_bar), the evt segment from its return to the
   latch (llvm_op2_post_evt, g_run again). The model premise: op_announce_m from the cursor c1 after the op byte is
   not None at every heap frame a the callee's malloc may return. The continuation gets the frame a, the world
   op_announce_m gives at it, and the latch with the cursor after op_announce's three reads. *)
Lemma llvm_op2_announce_sr : forall gp tp Sp lo ops c c1 Bw ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
    L0 A0 mem0 md0 b cfg (P : config -> Prop),
  h_binds B API ->
  (forall fx' : YK11.FPState, @build_and_receive_contract fx' rc B API) ->
  memset_contract -> memcpy_contract -> strlen_contract ->
  llvm_case_sr B API data D gp tp 2 Sp lo ops c c1 Bw ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L0 A0 mem0 md0 b cfg ->
  (forall a, h_addr_ok a -> op_announce_m timg_plain Bw D a c1 <> None) ->
  (forall a Bw' c' cfg', h_addr_ok a -> op_announce_m timg_plain Bw D a c1 = Some (Bw', c') ->
     llvm_latch_sr B API data D gp tp Sp lo ops c' Bw' ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L0 A0 mem0 md0 b
       cfg' ->
     SR rsegs cfg' P) ->
  SR rsegs cfg P.
Proof.
  intros gp tp Sp lo ops c c1 Bw ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L0 A0 mem0 md0 b cfg P
    HB HBAR MSC MCC STC HSR HMOD K.
  destruct (fuzz_u8_m D c1) as [c2 sel] eqn:E1.
  destruct (fuzz_u8_m D c2) as [c3' mb] eqn:E2.
  destruct (fuzz_u8_m D c3') as [c3 nm] eqn:E3.
  pose proof (fun a => op2_announce_eq c1 c2 sel c3' mb c3 nm Bw a E1 E2 E3) as EOP.
  set (body := op2_body3 (mb mod 16) (nm mod 3)) in *.
  pose proof HB as (SEGS & _ & _ & HGG & _ & AX & ERR & CTX & WORLD & RELRO).
  destruct HSR as (fx' & regs & mem & md & L & A & -> & Hfrm & FR & Hc1 & Hc2 & Hres & Hroom & Htp & HIN & HPe).
  pose proof HPe as HPe'.
  destruct HPe' as (rr & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & r8 & t3 & t4 & t5 & t6 & mm &
                    j10 & j28 & EMS & HOPS & HN & HC & HC1 & HM).
  pose proof (ms_mem_of _ _ _ _ _ _ _ _ _ _ _ _ _ _ EMS) as EM. subst mm.
  assert (Etp : YK11.getr regs 4 = tp).
  { change (YK11.getr regs 4) with (getr (Regs6ss.mkR_of regs) 4).
    apply (f_equal (fun ms => getr (ms_regs ms) 4)) in EMS. exact EMS. }
  rewrite Etp in Htp.
  pose proof HM as HM1. unfold llvm_mem in HM1.
  destruct HM1 as (_ & _ & HD & HSP & HSTK & HLO & HSP2 & HWOS & HOWS & HOW & HOWIN & _ & _ & _ & _ & _ & _ & _).
  unfold LLVM_LOOP_K in HLO. unfold LLVM_FRAME in HSP2. pose proof wmem_end as HWE.
  assert (HSmax : LLVM_SR_S Sp <= 2 ^ 64) by (unfold LLVM_SR_S, LLVM_FRAME; lia).
  assert (Hbl : length body = 34%nat) by (apply op2_body3_length; apply Z.mod_pos_bound; lia).
  (* ---- the case's evt segment, to build_and_receive's entry ---- *)
  eapply (g_run B API SEGS AX HGG WORLD LLVM_SR_K (LLVM_SR_S Sp) L0 A0 mem0 md0 fx' regs (Z_to_bv 64 (LLVM_CASE 2))
            mem md L A (op2_call data D (normalize rsegs mem) gp tp Sp lo ops c3 Bw ra s0 s1 s2 s3 s4 s5 s6 s7 s8
                          s9 s10 s11 (op2_cmd sel) body (@fp_regs fx') (@fp_csr fx')) P FR Hc1 HSmax).
  { exact (llvm_op2_pre_evt data D _ gp tp Sp lo ops c c1 c2 c3' c3 sel mb nm Bw
             ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ MSC MCC STC HPe E1 E2 E3). }
  { intros ms (u0 & u1 & u2 & u8 & u9 & u20 & u23 & u28 & u29 & u30 & u31 & mq & k10 & k40 & k6 &
               -> & _ & _ & _ & _ & HMq).
    do 5 eexists. exists (LLVM_FP Sp). split; [reflexivity|].
    unfold llvm_mem in HMq. destruct HMq as (MUq & WMq & _).
    split; [exact MUq|]. split; [exact WMq|].
    intros x _ NO. destruct (op08_fp Sp x NO) as [Hw|Hw]; [left; exact Hw | right; left; exact Hw]. }
  intros R F pc' fc m0' HQ regs' m' Hx Hrel FR'.
  destruct HQ as (u0 & u1 & u2 & u8 & u9 & u20 & u23 & u28 & u29 & u30 & u31 & mq & k10 & k40 & k6 &
                  EQ & HOPS' & HC3 & H40 & H6 & HMq).
  unfold MS in EQ. injection EQ; intros; subst R F pc' fc mq.
  (* the registers at the call *)
  assert (G1 : YK11.getr regs' 1 = Z_to_bv 64 0x13ddc) by (rewrite (sr_getr_eqv _ _ _ Hx); reflexivity).
  assert (G2 : YK11.getr regs' 2 = Z_to_bv 64 Sp) by (rewrite (sr_getr_eqv _ _ _ Hx); reflexivity).
  assert (G4 : YK11.getr regs' 4 = Z_to_bv 64 (ms_tp B)) by (rewrite (sr_getr_eqv _ _ _ Hx); exact Htp).
  assert (G10 : YK11.getr regs' 10 = Z_to_bv 64 0x1048c) by (rewrite (sr_getr_eqv _ _ _ Hx); reflexivity).
  assert (G11 : YK11.getr regs' 11 = Z_to_bv 64 0x10486) by (rewrite (sr_getr_eqv _ _ _ Hx); reflexivity).
  assert (G12 : YK11.getr regs' 12 = Z_to_bv 64 0) by (rewrite (sr_getr_eqv _ _ _ Hx); reflexivity).
  assert (G13 : YK11.getr regs' 13 = Z_to_bv 64 0) by (rewrite (sr_getr_eqv _ _ _ Hx); reflexivity).
  assert (G14 : YK11.getr regs' 14 = Z_to_bv 64 0) by (rewrite (sr_getr_eqv _ _ _ Hx); reflexivity).
  assert (G15 : YK11.getr regs' 15 = Z_to_bv 64 (op2_cmd sel)) by (rewrite (sr_getr_eqv _ _ _ Hx); reflexivity).
  assert (G16 : YK11.getr regs' 16 = Z_to_bv 64 (Sp + 80)) by (rewrite (sr_getr_eqv _ _ _ Hx); reflexivity).
  assert (G17 : YK11.getr regs' 17 = Z_to_bv 64 34) by (rewrite (sr_getr_eqv _ _ _ Hx); reflexivity).
  assert (Hro' : ro_agree rsegs m') by exact (ro_agree_of_mem_rel rsegs _ _ Hrel).
  assert (HM' : llvm_mem data D Sp lo Bw (normalize rsegs m') (normalize rsegs m')
                  ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 k10 (k40 ++ body ++ k6)).
  { apply (llvm_mem_ext data D Sp lo Bw (normalize rsegs mem) m0' (normalize rsegs m')); [|exact HMq].
    intros x. destruct Hrel as [E _]. symmetry. exact (E x). }
  assert (Hcmd : 0 <= op2_cmd sel < 2 ^ 8) by (unfold op2_cmd, SPEC_CMD_E0, SPEC_CMD_E1; destruct (_ =? 0); lia).
  (* ---- the call ---- *)
  apply (llvm_sr_bar B API data D Sp lo Bw (mkFP (@fp_regs fx') (@fp_csr fx')) regs' (normalize rsegs m') m' md L A
           L0 A0 mem0 md0 b ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 k10 (k40 ++ body ++ k6)
           0x1048c 0x10486 (Sp + 80) SPEC_BCAST DESK body 0 0 0 (op2_cmd sel) P HB HBAR FR' Hc2 Hfrm Hres Hroom
           G2 G4).
  { rewrite G1. reflexivity. }
  { exact HM'. }
  { exact HIN. }
  { (* bar_args *)
    split; [exact G10|].
    split; [apply (llvm_mac_img B m' 0x1048c SPEC_BCAST SEGS Hro'); [reflexivity | vm_compute; reflexivity]|].
    split; [exact G11|].
    split; [apply (llvm_mac_img B m' 0x10486 DESK SEGS Hro'); [reflexivity | vm_compute; reflexivity]|].
    split; [rewrite G12; reflexivity|]. split; [lia|].
    split; [rewrite G13; reflexivity|]. split; [lia|].
    split; [exact G14|]. split; [lia|].
    split; [exact G15|]. split; [exact Hcmd|].
    split; [exact G16|].
    split; [rewrite G17, Hbl; reflexivity|].
    split.
    { apply (llvm_blk_norm B m' (Sp + 80) body SEGS Hro').
      exact (op2_llvm_body data D Sp lo Bw _ _ ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 k10 k40 body k6 HM' H40 H6). }
    split.
    { right. split; [unfold off_world; lia|]. right. unfold spZ. rewrite G2, unsigned_lit by lia.
      rewrite Hbl. lia. }
    intros a Ha Hnone. apply (HMOD a Ha). rewrite EOP, Hnone. reflexivity. }
  (* ---- after the call: back to the latch ---- *)
  intros fx2 regs2 mem2 md2 L2 A2 a Bw' Ha HRM Hrp Hfrm2 FR2 Hres2 HM2.
  rewrite G1.
  assert (E2' : YK11.getr regs2 2 = Z_to_bv 64 Sp)
    by exact (op08_pres _ _ _ 2 Hx Hrp ltac:(unfold callee_saved; lia)).
  assert (E3' : YK11.getr regs2 3 = gp)
    by exact (op08_pres _ _ _ 3 Hx Hrp ltac:(unfold callee_saved; lia)).
  assert (E4 : YK11.getr regs2 4 = tp)
    by exact (op08_pres _ _ _ 4 Hx Hrp ltac:(unfold callee_saved; lia)).
  assert (E18 : YK11.getr regs2 18 = Z_to_bv 64 0x39)
    by exact (op08_pres _ _ _ 18 Hx Hrp ltac:(unfold callee_saved; lia)).
  assert (E19 : YK11.getr regs2 19 = Z_to_bv 64 (data + fi_off c3))
    by exact (op08_pres _ _ _ 19 Hx Hrp ltac:(unfold callee_saved; lia)).
  assert (E21 : YK11.getr regs2 21 = Z_to_bv 64 (W_BASE_PLAIN + OFF_g_s))
    by exact (op08_pres _ _ _ 21 Hx Hrp ltac:(unfold callee_saved; lia)).
  assert (E22 : YK11.getr regs2 22 = Z_to_bv 64 (fi_n c3))
    by exact (op08_pres _ _ _ 22 Hx Hrp ltac:(unfold callee_saved; lia)).
  assert (E24 : YK11.getr regs2 24 = Z_to_bv 64 1)
    by exact (op08_pres _ _ _ 24 Hx Hrp ltac:(unfold callee_saved; lia)).
  assert (E25 : YK11.getr regs2 25 = Z_to_bv 64 (W_BASE_PLAIN + OFF_g_fail_next))
    by exact (op08_pres _ _ _ 25 Hx Hrp ltac:(unfold callee_saved; lia)).
  assert (E26 : YK11.getr regs2 26 = Z_to_bv 64 (W_BASE_PLAIN + OFF_M))
    by exact (op08_pres _ _ _ 26 Hx Hrp ltac:(unfold callee_saved; lia)).
  assert (E27 : YK11.getr regs2 27 = Z_to_bv 64 ops)
    by exact (op08_pres _ _ _ 27 Hx Hrp ltac:(unfold callee_saved; lia)).
  eapply (g_run B API SEGS AX HGG WORLD LLVM_SR_K (LLVM_SR_S Sp) L0 A0 mem0 md0 fx2 regs2 (Z_to_bv 64 0x13ddc)
            mem2 md2 L2 A2
            (llvm_latch data D (normalize rsegs mem2) gp tp Sp lo ops c3 Bw' ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10
               s11 (@fp_regs fx2) (@fp_csr fx2)) P FR2 Hc1 HSmax).
  { rewrite op08_mkR_of_getr. rewrite E2', E3', E4, E18, E19, E21, E22, E24, E25, E26, E27.
    eapply (llvm_op2_post_evt data D); [exact HM2 | exact HOPS | exact HC3]. }
  { intros ms HQ.
    destruct HQ as (rq & v0 & v1 & v2 & v10 & v11 & v12 & v13 & v14 & v15 & v16 & v17 & v8 & v20 & v23 &
                    v28 & v29 & v30 & v31 & m'' & q10 & q28 & -> & _ & _ & HMq2).
    do 5 eexists. exists (LLVM_FP Sp). split; [reflexivity|].
    unfold llvm_mem in HMq2. destruct HMq2 as (MUq & WMq & _).
    split; [exact MUq|]. split; [exact WMq|].
    intros x _ NO. destruct (op08_fp Sp x NO) as [Hw|Hw]; [left; exact Hw | right; left; exact Hw]. }
  intros R3 F3 pc3 fc3 m0'' HQ regs3 m3 Hx3 Hrel3 FR3.
  pose proof HQ as HQ'.
  destruct HQ' as (rq & v0 & v1 & v2 & v10 & v11 & v12 & v13 & v14 & v15 & v16 & v17 & v8 & v20 & v23 &
                   v28 & v29 & v30 & v31 & m'' & q10 & q28 & EQ3 & _ & _ & _).
  unfold MS in EQ3. injection EQ3; intros; subst R3 F3 pc3 fc3 m0''.
  apply (K a Bw' c3 _ Ha); [rewrite EOP, HRM; reflexivity|].
  exists (mkFP (@fp_regs fx2) (@fp_csr fx2)), regs3, m3, md2, L2, A2.
  split; [reflexivity|].
  split; [exact Hfrm2|].
  split; [exact FR3|].
  split; [exact Hc1|]. split; [exact Hc2|].
  split; [exact Hres2|]. split; [exact Hroom|].
  split; [rewrite (sr_getr_eqv _ _ _ Hx3); exact Htp|].
  split; [exact HIN|].
  rewrite (op08_mkR_of _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hx3).
  eapply llvm_latch_ext; [|exact HQ].
  intros x. symmetry. exact (proj1 Hrel3 x).
Qed.

(* Case 2 in the form of the loop's binder (LLVMFuzzerTestOneInput_loopsr.v llvm_pass_sr; the statement of
   _op1.v llvm_op1_sr with 2 for 1, and the three libc contracts the walk calls): the model's op at aupd A k a,
   the address a build_and_receive's malloc returned, which the binder carries pass to pass with TOpsA.v
   loop_m_step_at. *)
Lemma llvm_op2_sr : forall gp tp Sp lo ops c c1 Bw (A : nat -> Z) (k : nat) L0 A0 mem0 md0 b
    ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 cfg (P : config -> Prop),
  h_binds B API -> memset_contract -> memcpy_contract -> strlen_contract ->
  (forall fx'' : YK11.FPState, @build_and_receive_contract fx'' rc B API) ->
  snd (fuzz_u8_m D c) mod 9 = 2 ->
  llvm_case_sr B API data D gp tp 2 Sp lo ops c c1 Bw
    ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L0 A0 mem0 md0 b cfg ->
  (forall a, h_addr_ok a -> exists Bres cout k1,
     LLVMFuzzerTestOneInput_op_m timg_plain Bw (aupd A k a) D c k = Some (Bres, (cout, k1))) ->
  (forall a Bres cout cfg', h_addr_ok a ->
     LLVMFuzzerTestOneInput_op_m timg_plain Bw (aupd A k a) D c k = Some (Bres, (cout, S k)) ->
     llvm_latch_sr B API data D gp tp Sp lo ops cout Bres
       ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L0 A0 mem0 md0 b cfg' ->
     SR rsegs cfg' P) ->
  SR rsegs cfg P.
Proof.
  intros gp tp Sp lo ops c c1 Bw A k L0 A0 mem0 md0 b ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 cfg P
    HB MSC MCC STC HBAR Hop HSR HMOD K.
  destruct (op08_case_facts B API data D gp tp 2 Sp lo ops c c1 Bw ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
              L0 A0 mem0 md0 b cfg HSR) as (HN & HC & HC1).
  destruct (fuzz_u8_m D c) as [cu opb] eqn:EU8.
  rewrite ?EU8 in HC1, Hop. cbn [fst snd] in HC1, Hop. subst cu.
  (* the model's op 2 at A k = a: op_announce_m from c1 at a (TOps.v :297-299) *)
  assert (EOP : forall a, LLVMFuzzerTestOneInput_op_m timg_plain Bw (aupd A k a) D c k =
            match op_announce_m timg_plain Bw D a c1 with
            | Some (B1, c2) => Some (B1, (c2, S k)) | None => None end).
  { intros a. unfold LLVMFuzzerTestOneInput_op_m. rewrite EU8. cbv beta iota zeta. rewrite Hop.
    cbn [Z.eqb Pos.eqb]. rewrite aupd_at. reflexivity. }
  apply (llvm_op2_announce_sr gp tp Sp lo ops c c1 Bw ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L0 A0 mem0 md0 b
           cfg P HB HBAR MSC MCC STC HSR).
  - intros a Ha Hnone. destruct (HMOD a Ha) as (Bres & cout & k1 & E).
    rewrite EOP, Hnone in E. discriminate E.
  - intros a Bw' c' cfg' Ha HAN HL. apply (K a Bw' c' cfg' Ha); [rewrite EOP, HAN; reflexivity | exact HL].
Qed.

End OP2SR.
