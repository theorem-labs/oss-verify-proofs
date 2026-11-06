(* Case 2 of the ubsan op loop of LLVMFuzzerTestOneInput, 0x13ab8 .. the jal of build_and_receive at 0x140c0
   (fuzz/fuzz_transport.c:1178-1180 `case 2: op_announce(&in); break;`, op_announce :1052-1066 inlined).

   The code reads up to three bytes (sel, m, nm) -- the short-input paths are 0x13dec, 0x13df0 and 0x13fc8, and
   nm % 3 is the multiply-high at 0x13fe4 -- zeroes the 34-byte body[] of :1057 in the loop's frame at sp + 0x60
   (memset), copies HOST at body + mac (mac < 10) or OTHER at body + mac - 10 (10 <= mac < 13), stores "1.37" at
   body + 15 with four sb, reads NAME[name] out of .data.rel.ro and copies its strlen bytes to body + 24, and
   calls build_and_receive(SPEC_BCAST, DESK, 0, 0, 0, sel & 1 ? SPEC_CMD_E1 : SPEC_CMD_E0, body, 34).
   Every UBSan check (the pointer tests against sp + 0x60 and against the cursor, all branching to the trap at
   0x14820) is refuted from the frame's bounds and 0 < data. The return at 0x140c4 sets s2 = 0x39 and s4 = 7 and
   jumps to the latch with the cursor op_announce_m leaves (s3 / s6).

   The loop's frame cell j60 (40 bytes at sp + 0x60) is carried as body ++ T with T the 6 bytes above body[];
   the walk keeps llvm_mem folded and touches memory only through the lemmas of
   U/Prog/T/LLVMFuzzerTestOneInput_op2_lem.v, so the kit's cell machinery never has to split the frame. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells
  Step Tac Bytes Image ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TWorldLemmas TImg TWorldMem
  TCb TOps.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog Require Import memcpy_c memset_c strlen_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog.T Require Import TImgU WMem TContract
  LLVMFuzzerTestOneInput_lh LLVMFuzzerTestOneInput_fr LLVMFuzzerTestOneInput_op2_lem.
Import ListNotations.
Open Scope Z_scope.

(* a branch whose condition the context decides (U/Prog/T/build_and_receive.v bar_br) *)
Ltac op2_br v := lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      replace c with v;
      [cbv iota | symmetry; unfold_cond; fold_lit_ux; rewrite ?unsigned_lit by lia; solve_cond_rec]
  end.
(* a UBSan check that branches to the trap at 0x14820 *)
Ltac op2_trap := step; op2_br false.

(* ---------------------------------------------------------------- the piece's goal and invariant *)

(* the postcondition of llvm_op_bar_stmt 2 LH_RET_BAR2, verbatim *)
Definition op2_goal (data : Z) (D : list byte) (regs0 : bvmap 5 word) (m0 : word -> option byte)
    (Sp lo ops : Z) (B : list byte) (c : fuzz_in) (F : bvmap 5 word) (fc : bv 32)
    : machine_state -> Prop :=
  fun ms' => exists (s0 s2 s3 s4 s5 s6 s7 : word) (dstp srcp bodyp : Z) (dst src body : list byte)
                    (send ack retry cmd : Z) (c2 : fuzz_in),
     llvm_at_bar data D regs0 m0 Sp lo ops B LH_RET_BAR2 s0 s2 s3 s4 s5 s6 s7 dstp srcp bodyp dst src body
       send ack retry cmd F fc ms' /\
     (forall I A k, LLVMFuzzerTestOneInput_op_m I B A D c k =
        match build_and_receive_m I B (A k) dst src send ack retry cmd body with
        | Some (B1, _) => Some (B1, (c2, S k))
        | None => None
        end) /\
     (forall m0' B' F' fc' ms'' (Q' : machine_state -> Prop), g_fail_next B' <= 1 ->
        llvm_ret data D regs0 m0' Sp lo ops B' LH_RET_BAR2 s0 s2 s3 s4 s5 s6 s7 F' fc' ms'' ->
        (forall ms3, llvm_latch data D regs0 m0' Sp lo ops c2 B' F' fc' ms3 -> evt rsegs Q' ms3) ->
        evt rsegs Q' ms'').

(* what the head of the case establishes about the model before it builds the body *)
Definition op2_eqm (B D : list byte) (c c3 : fuzz_in) (sel mac name : Z) : Prop :=
  forall I A k, LLVMFuzzerTestOneInput_op_m I B A D c k =
    match build_and_receive_m I B (A k) SPEC_BCAST DESK 0 0 0
            (if Z.land sel 1 =? 0 then SPEC_CMD_E0 else SPEC_CMD_E1) (op2_b3 mac name) with
    | Some (B1, _) => Some (B1, (c3, S k))
    | None => None
    end.

Definition op2_inv (D : list byte) (B : list byte) (ops : Z) (c c3 : fuzz_in) (sel mac name : Z) : Prop :=
  0 <= ops < OPS_MAX /\ 0 <= sel < 256 /\ 0 <= mac < 16 /\ 0 <= name < 3 /\
  llvm_cursor D c3 /\ op2_eqm B D c c3 sel mac name.

(* ---------------------------------------------------------------- the MACs and the name strings *)

Definition op2_BCASTP : Z := 0x1047c.
Definition op2_DESKP : Z := 0x10476.
Definition op2_HOSTP : Z := 0x10470.
Definition op2_OTHERP : Z := 0x10498.

(* NAME[k] (fuzz_transport.c:1054): the pointer .data.rel.ro holds at 0x21f78 + 8k, and the bytes after the
   string's NUL that strlen's word loads may touch. *)
Definition op2_namep (k : Z) : Z := if k =? 0 then 0x10339 else if k =? 1 then 0x10330 else 0x10305.
Definition op2_nameslack (k : Z) : list byte :=
  if k =? 0 then [b8 0x63; b8 0x6c; b8 0x69; b8 0x3a; b8 0x20; b8 0x63]
  else if k =? 1 then [b8 0x43; b8 0x4e; b8 0x54; b8 0x52; b8 0x4c; b8 0x7c; b8 0x32]
  else [b8 0x49; b8 0x4e; b8 0x46; b8 0x00; b8 0x63].

Lemma op2_namep_rng : forall k, 0x10000 < op2_namep k /\ op2_namep k + 32 <= 0x11000.
Proof.
  intros k. unfold op2_namep.
  destruct (k =? 0); [lia|]. destruct (k =? 1); lia.
Qed.

Lemma op2_bcast_at : forall m, mem_inv rsegs m -> lh_mac_at m op2_BCASTP SPEC_BCAST.
Proof.
  intros m MI. apply op2_mac_at;
    [ exact MI | vm_compute; reflexivity | reflexivity | unfold op2_BCASTP; lia | unfold op2_BCASTP; lia ].
Qed.

Lemma op2_desk_at : forall m, mem_inv rsegs m -> lh_mac_at m op2_DESKP DESK.
Proof.
  intros m MI. apply op2_mac_at;
    [ exact MI | vm_compute; reflexivity | reflexivity | unfold op2_DESKP; lia | unfold op2_DESKP; lia ].
Qed.

Lemma op2_host_at : forall m, mem_inv rsegs m -> bytes_at rsegs m op2_HOSTP HOST.
Proof.
  intros m MI. apply op2_img;
    [ exact MI | vm_compute; reflexivity | unfold op2_HOSTP; lia | vm_compute; discriminate ].
Qed.

Lemma op2_other_at : forall m, mem_inv rsegs m -> bytes_at rsegs m op2_OTHERP OTHER.
Proof.
  intros m MI. apply op2_img;
    [ exact MI | vm_compute; reflexivity | unfold op2_OTHERP; lia | vm_compute; discriminate ].
Qed.

Lemma op2_str_at : forall m k, mem_inv rsegs m -> 0 <= k < 3 ->
  bytes_at rsegs m (op2_namep k)
    (nth (Z.to_nat k) op_announce_NAME [] ++ Z_to_bv 8 0 :: op2_nameslack k).
Proof.
  intros m k MI Hk.
  assert (C : k = 0 \/ k = 1 \/ k = 2) by lia.
  destruct C as [E|[E|E]]; subst k; unfold op2_namep, op2_nameslack;
    cbn [Z.eqb Pos.eqb]; apply op2_img;
    solve [ exact MI | vm_compute; reflexivity | lia | (vm_compute; discriminate) ].
Qed.

Lemma op2_str_nonul : forall k, 0 <= k < 3 -> ~ In (Z_to_bv 8 0) (nth (Z.to_nat k) op_announce_NAME []).
Proof.
  intros k Hk.
  assert (C : k = 0 \/ k = 1 \/ k = 2) by lia.
  destruct C as [E|[E|E]]; subst k; apply op2_notin; vm_compute; reflexivity.
Qed.

Lemma op2_str_slack : forall k, 0 <= k < 3 ->
  (- (op2_namep k + Z.of_nat (length (nth (Z.to_nat k) op_announce_NAME [])) + 1)) mod 8
    <= Z.of_nat (length (op2_nameslack k)).
Proof.
  intros k Hk.
  assert (C : k = 0 \/ k = 1 \/ k = 2) by lia.
  destruct C as [E|[E|E]]; subst k; vm_compute; discriminate.
Qed.

Lemma op2_str_len : forall k, 0 <= k < 3 ->
  1 <= Z.of_nat (length (nth (Z.to_nat k) op_announce_NAME [])) <= 8.
Proof.
  intros k Hk.
  assert (C : k = 0 \/ k = 1 \/ k = 2) by lia.
  assert (L0 : length (nth 0 op_announce_NAME []) = 8%nat) by reflexivity.
  assert (L1 : length (nth 1 op_announce_NAME []) = 8%nat) by reflexivity.
  assert (L2 : length (nth 2 op_announce_NAME []) = 5%nat) by reflexivity.
  destruct C as [E|[E|E]]; subst k;
    [ change (Z.to_nat 0) with 0%nat; rewrite L0
    | change (Z.to_nat 1) with 1%nat; rewrite L1
    | change (Z.to_nat 2) with 2%nat; rewrite L2 ]; lia.
Qed.

(* an 8-byte pointer of .data.rel.ro, in the form the ld folds (Lib/Mem.v load_u64) *)
Lemma op2_relro_rd8 : forall m a v, relro_img m ->
  RELRO_BASE <= a -> a + 8 <= RELRO_BASE + RELRO_LEN ->
  image_bytes rsegs a 8 = Some (le8 (Z_to_bv 64 v)) ->
  ov_read_bytes rsegs m (Z_to_bv 64 a) 8 = Some (le8 (Z_to_bv 64 v)).
Proof.
  intros m a v RR H1 H2 HI.
  assert (HB : bytes_at rsegs m a (le8 (Z_to_bv 64 v))).
  { apply op2_relro_at;
      [ exact RR | exact H1 | rewrite length_le8; lia | rewrite length_le8; exact HI ]. }
  replace (Z_to_bv 64 a) with (wa (a + 0)) by (unfold wa; f_equal; lia).
  rewrite (bytes_at_read rsegs m a _ 0 8 HB ltac:(lia) ltac:(rewrite length_le8; lia)).
  reflexivity.
Qed.

(* the 8-byte pointer .data.rel.ro holds at NAME + 8 k *)
Lemma op2_namet_rd : forall m k a, relro_img m -> 0 <= k < 3 -> a = 0x21f78 + 8 * k ->
  ov_read_bytes rsegs m (Z_to_bv 64 a) 8 = Some (le8 (Z_to_bv 64 (op2_namep k))).
Proof.
  intros m k a RR Hk ->.
  assert (C : k = 0 \/ k = 1 \/ k = 2) by lia.
  destruct C as [E|[E|E]]; subst k; unfold op2_namep; cbn [Z.eqb Pos.eqb].
  - replace (0x21f78 + 8 * 0) with 0x21f78 by lia.
    apply op2_relro_rd8;
      [ exact RR | unfold RELRO_BASE; lia | unfold RELRO_BASE, RELRO_LEN; lia
      | vm_compute; f_equal; apply bytes_eq_of_zs; vm_compute; reflexivity ].
  - replace (0x21f78 + 8 * 1) with 0x21f80 by lia.
    apply op2_relro_rd8;
      [ exact RR | unfold RELRO_BASE; lia | unfold RELRO_BASE, RELRO_LEN; lia
      | vm_compute; f_equal; apply bytes_eq_of_zs; vm_compute; reflexivity ].
  - replace (0x21f78 + 8 * 2) with 0x21f88 by lia.
    apply op2_relro_rd8;
      [ exact RR | unfold RELRO_BASE; lia | unfold RELRO_BASE, RELRO_LEN; lia
      | vm_compute; f_equal; apply bytes_eq_of_zs; vm_compute; reflexivity ].
Qed.

(* ---------------------------------------------------------------- 0x14094: the call of build_and_receive *)

Lemma op2_bar : forall data D regs0 m0 Sp lo ops B c c3 sel mac name T
    (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s7 t3 t4 t5 t6 : word)
    (m : word -> option byte) (j10 jio : list byte) F fc,
  op2_inv D B ops c c3 sel mac name ->
  length T = 6%nat ->
  llvm_mem data D regs0 m0 Sp lo B m j10 jio (op2_b3 mac name ++ T) ->
  evt rsegs (op2_goal data D regs0 m0 Sp lo ops B c F fc)
    (MS (mkR ra (Z_to_bv 64 Sp) (reg_get regs0 3) (reg_get regs0 4) t0 t1 t2 (Z_to_bv 64 sel) (Z_to_bv 64 1)
           a0 a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 (data + fi_off c3)) s4 s5 (Z_to_bv 64 (fi_n c3)) s7
           (Z_to_bv 64 (W_BASE_UBSAN + OFF_M)) (Z_to_bv 64 (W_BASE_UBSAN + OFF_g_fail_next))
           (Z_to_bv 64 (W_BASE_UBSAN + OFF_g_s)) (Z_to_bv 64 ops) t3 t4 t5 t6)
        F (Z_to_bv 64 0x14094) fc None m (seg_rom rsegs)).
Proof.
  intros data D regs0 m0 Sp lo ops B c c3 sel mac name T
    ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s7 t3 t4 t5 t6 m j10 jio F fc INV LT HM.
  destruct INV as (HOPS & HSEL & HMAC & HNAME & HCUR & HEQ).
  pose proof (op2_mem_facts _ _ _ _ _ _ _ _ _ _ _ HM) as
    (HD0 & HDL & HLO & HSP2 & HWL & HSP16 & HJ1 & HJ2 & HJ3 & HMI & HRO & _ & _).
  unfold W_BASE_UBSAN, W_LEN in HWL.
  pose proof (op2_b3_len mac name HMAC HNAME) as LB3.
  (* 0x14094 ori a0,s0,0xe0; 0x14098 andi a5,a0,0xe1; 0x1409c .. 0x140bc the eight arguments; 0x140c0 jal *)
  do 12 zstep.
  apply evt_done. unfold op2_goal.
  exists (Z_to_bv 64 sel), s2, (Z_to_bv 64 (data + fi_off c3)), s4, s5, (Z_to_bv 64 (fi_n c3)), s7.
  exists op2_BCASTP, op2_DESKP, (Sp + 96).
  exists SPEC_BCAST, DESK, (op2_b3 mac name).
  exists 0, 0, 0, (if Z.land sel 1 =? 0 then SPEC_CMD_E0 else SPEC_CMD_E1), c3.
  assert (ECMD : Z.land (Z.lor sel 224) 225 = (if Z.land sel 1 =? 0 then SPEC_CMD_E0 else SPEC_CMD_E1))
    by (apply op2_cmd_val; lia).
  split; [| split; [exact HEQ |]].
  - unfold llvm_at_bar, LH_BAR, LH_RET_BAR2.
    exists t0, t1, t2, (Z_to_bv 64 0), (Z_to_bv 64 0), t3, t4, t5, t6, m, j10, jio, (op2_b3 mac name ++ T).
    split.
    { rewrite ECMD.
      replace (Z_to_bv 64 34) with (Z_to_bv 64 (Z.of_nat (length (op2_b3 mac name))))
        by (rewrite LB3; reflexivity).
      unfold op2_BCASTP, op2_DESKP. reflexivity. }
    split; [exact HOPS|].
    split; [exact (op2_bcast_at m HMI)|].
    split; [exact (op2_desk_at m HMI)|].
    split; [vm_compute; reflexivity|]. split; [lia|].
    split; [vm_compute; reflexivity|]. split; [lia|].
    split; [lia|].
    split; [destruct (Z.land sel 1 =? 0); unfold SPEC_CMD_E0, SPEC_CMD_E1; lia|].
    split.
    { pose proof (op2_mem_j60 _ _ _ _ _ _ _ _ _ _ _ HM) as HJ.
      apply bytes_at_app in HJ. destruct HJ as [HJ _]. exact HJ. }
    split; [right; split; [lia|]; unfold LH_FRAME; rewrite LB3; lia|].
    exact HM.
  - intros m0' B' F' fc' ms'' Q' HFN HRET HK.
    destruct HRET as (ra' & u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 &
                      m' & j10' & jio' & j60' & -> & HOPS' & HM').
    unfold LH_RET_BAR2.
    (* 0x140c4 addi s2,zero,0x39; 0x140c8 addi s4,zero,7; 0x140cc j 0x14574 *)
    do 3 step.
    apply HK. unfold llvm_latch, LH_LATCH.
    exists ra', u0, u1, u2, (Z_to_bv 64 sel), b0, b1, b2, b3, b4, b5, b6, b7, s5, s7, u3, u4, u5, u6.
    exists m', j10', jio', j60'.
    split; [reflexivity|]. split; [exact HOPS'|]. split; [exact HCUR|]. exact HM'.
Qed.

(* ---------------------------------------------------------------- 0x1407c: strlen and the name copy *)

Lemma op2_names : memcpy_contract -> strlen_contract ->
  forall data D regs0 m0 Sp lo ops B c c3 sel mac name np T
    (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s5 s7 t3 t4 t5 t6 : word)
    (m : word -> option byte) (j10 jio : list byte) F fc,
  op2_inv D B ops c c3 sel mac name ->
  length T = 6%nat ->
  np = op2_namep name ->
  llvm_mem data D regs0 m0 Sp lo B m j10 jio (op2_b2 mac ++ T) ->
  evt rsegs (op2_goal data D regs0 m0 Sp lo ops B c F fc)
    (MS (mkR ra (Z_to_bv 64 Sp) (reg_get regs0 3) (reg_get regs0 4) t0 t1 t2 (Z_to_bv 64 sel) (Z_to_bv 64 1)
           a0 a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 (data + fi_off c3)) (Z_to_bv 64 np)
           s5 (Z_to_bv 64 (fi_n c3)) s7
           (Z_to_bv 64 (W_BASE_UBSAN + OFF_M)) (Z_to_bv 64 (W_BASE_UBSAN + OFF_g_fail_next))
           (Z_to_bv 64 (W_BASE_UBSAN + OFF_g_s)) (Z_to_bv 64 ops) t3 t4 t5 t6)
        F (Z_to_bv 64 0x1407c) fc None m (seg_rom rsegs)).
Proof.
  intros MEMCPY STRLEN data D regs0 m0 Sp lo ops B c c3 sel mac name np T
    ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s5 s7 t3 t4 t5 t6 m j10 jio F fc INV LT ENP HM.
  subst np.
  pose proof INV as INV0. destruct INV0 as (HOPS & HSEL & HMAC & HNAME & HCUR & HEQ).
  pose proof (op2_mem_facts _ _ _ _ _ _ _ _ _ _ _ HM) as
    (HD0 & HDL & HLO & HSP2 & HWL & HSP16 & HJ1 & HJ2 & HJ3 & HMI & HRO & _ & _).
  unfold W_BASE_UBSAN, W_LEN in HWL.
  pose proof (op2_namep_rng name) as HNP.
  pose proof (op2_str_len name ltac:(lia)) as HSL.
  pose proof (op2_b2_len mac HMAC) as LB2.
  (* 0x1407c mv a0,s4; 0x14080 jal strlen *)
  do 2 step.
  eapply evt_cut.
  { eapply STRLEN with (str := nth (Z.to_nat name) op_announce_NAME []) (slack := op2_nameslack name).
    - rewrite (unsigned_lit (op2_namep name)) by lia. exact (op2_str_at m name HMI ltac:(lia)).
    - exact (op2_str_nonul name ltac:(lia)).
    - rewrite (unsigned_lit (op2_namep name)) by lia. exact (op2_str_slack name ltac:(lia)).
    - exact HMI. }
  intros ms1 PO1. unfold strlen_post in PO1. destruct_exs PO1.
  destruct PO1 as (E1 & MUs & WMs & MIs & SBs). subst ms1.
  rewrite (ret_pc_even 82052) by (first [lia | reflexivity]).
  rewrite (unsigned_lit (op2_namep name)) in SBs by lia.
  pose proof (op2_mem_same _ _ _ _ _ _ _ _ _ _ _ _ HM MUs WMs MIs) as HMb.
  clear HM MUs WMs.
  (* 0x14084 mv a2,a0; 0x14088 addi a0,sp,0x78; 0x1408c mv a1,s4; 0x14090 jal memcpy *)
  do 4 step.
  pose proof (op2_mem_cell _ _ _ _ _ _ _ _ _ _ _ 24
                (Z.of_nat (length (nth (Z.to_nat name) op_announce_NAME []))) (Sp + 120) HMb
                ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as DSTc.
  eapply evt_cut.
  { eapply MEMCPY with (src := nth (Z.to_nat name) op_announce_NAME [])
                       (junk := sub (op2_b2 mac ++ T) 24
                                  (Z.to_nat (Z.of_nat (length (nth (Z.to_nat name) op_announce_NAME []))))).
    - rewrite (unsigned_lit (op2_namep name)) by lia.
      apply bytes_at_app in SBs. destruct SBs as [SB1 _]. exact SB1.
    - rewrite (unsigned_lit (Z.of_nat (length (nth (Z.to_nat name) op_announce_NAME [])))) by lia.
      rewrite Nat2Z.id. reflexivity.
    - rewrite (unsigned_lit (Sp + 120)) by lia.
      rewrite (unsigned_lit (Z.of_nat (length (nth (Z.to_nat name) op_announce_NAME [])))) by lia.
      exact DSTc.
    - rewrite (unsigned_lit (op2_namep name)) by lia. rewrite (unsigned_lit (Sp + 120)) by lia.
      rewrite (unsigned_lit (Z.of_nat (length (nth (Z.to_nat name) op_announce_NAME [])))) by lia.
      left. lia.
    - exact MIs. }
  intros ms2 PO2. unfold memcpy_post in PO2. destruct_exs PO2.
  destruct PO2 as (E2 & MUc & WMc & MIc & DSTf & SRCf). subst ms2.
  rewrite (ret_pc_even 82068) by (first [lia | reflexivity]).
  rewrite (unsigned_lit (Sp + 120)) in MUc, DSTf by lia.
  rewrite (unsigned_lit (Z.of_nat (length (nth (Z.to_nat name) op_announce_NAME [])))) in MUc, DSTf by lia.
  pose proof (op2_mem_fill _ _ _ _ _ _ _ _ _ _ _ _ 24
                (Z.of_nat (length (nth (Z.to_nat name) op_announce_NAME [])))
                (nth (Z.to_nat name) op_announce_NAME []) (Sp + 120)
                HMb MUc WMc MIc DSTf ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as HMc.
  rewrite (op2_upd_app_l (op2_b2 mac) T (nth (Z.to_nat name) op_announce_NAME []) 24) in HMc by lia.
  eapply op2_bar; [exact INV | exact LT | unfold op2_b3; exact HMc].
Qed.

(* ---------------------------------------------------------------- 0x14030: "1.37" and NAME[name] *)

Lemma op2_tailC : memcpy_contract -> strlen_contract ->
  forall data D regs0 m0 Sp lo ops B c c3 sel mac name T
    (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s7 t3 t4 t5 t6 : word)
    (m : word -> option byte) (j10 jio : list byte) F fc,
  op2_inv D B ops c c3 sel mac name ->
  length T = 6%nat ->
  llvm_mem data D regs0 m0 Sp lo B m j10 jio (op2_b1 mac ++ T) ->
  evt rsegs (op2_goal data D regs0 m0 Sp lo ops B c F fc)
    (MS (mkR ra (Z_to_bv 64 Sp) (reg_get regs0 3) (reg_get regs0 4) t0 t1 t2 (Z_to_bv 64 sel) (Z_to_bv 64 1)
           a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 name) (Z_to_bv 64 (data + fi_off c3)) s4
           (Z_to_bv 64 (Sp + 96)) (Z_to_bv 64 (fi_n c3)) s7
           (Z_to_bv 64 (W_BASE_UBSAN + OFF_M)) (Z_to_bv 64 (W_BASE_UBSAN + OFF_g_fail_next))
           (Z_to_bv 64 (W_BASE_UBSAN + OFF_g_s)) (Z_to_bv 64 ops) t3 t4 t5 t6)
        F (Z_to_bv 64 0x14030) fc None m (seg_rom rsegs)).
Proof.
  intros MEMCPY STRLEN data D regs0 m0 Sp lo ops B c c3 sel mac name T
    ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s7 t3 t4 t5 t6 m j10 jio F fc INV LT HM.
  pose proof INV as INV0. destruct INV0 as (HOPS & HSEL & HMAC & HNAME & HCUR & HEQ).
  pose proof (op2_mem_facts _ _ _ _ _ _ _ _ _ _ _ HM) as
    (HD0 & HDL & HLO & HSP2 & HWL & HSP16 & HJ1 & HJ2 & HJ3 & HMI & HRO & _ & _).
  unfold W_BASE_UBSAN, W_LEN in HWL.
  pose proof (op2_b1_len mac HMAC) as LB1.
  pose proof (op2_b2_len mac HMAC) as LB2.
  assert (LL : length (op2_b1 mac ++ T) = 40%nat) by (rewrite app_length, LB1, LT; reflexivity).
  (* 0x14030 li a0,-0x10; 0x14034 bltu a0,s5 *)
  step. op2_trap.
  (* 0x14038 .. 0x14054: the four sb of "1.37" at body + 15 *)
  pose proof (op2_mem_store_ok _ _ _ _ _ _ _ _ _ _ _ 15 1%nat (Sp + 111) HM
                ltac:(lia) ltac:(cbn [Z.of_nat]; lia) ltac:(lia)) as HS1.
  step. step.
  pose proof (op2_mem_store _ _ _ _ _ _ _ _ _ _ _ 15 (le1 (Z_to_bv 64 49)) (Sp + 111) HM
                ltac:(lia) ltac:(rewrite length_le1; cbn [Z.of_nat]; lia) ltac:(lia)) as HM1.
  clear HS1 HM.
  pose proof (op2_mem_store_ok _ _ _ _ _ _ _ _ _ _ _ 16 1%nat (Sp + 112) HM1
                ltac:(lia) ltac:(cbn [Z.of_nat]; lia) ltac:(lia)) as HS2.
  step. step.
  pose proof (op2_mem_store _ _ _ _ _ _ _ _ _ _ _ 16 (le1 (Z_to_bv 64 46)) (Sp + 112) HM1
                ltac:(lia) ltac:(rewrite length_le1; cbn [Z.of_nat]; lia) ltac:(lia)) as HM2.
  clear HS2 HM1.
  pose proof (op2_mem_store_ok _ _ _ _ _ _ _ _ _ _ _ 17 1%nat (Sp + 113) HM2
                ltac:(lia) ltac:(cbn [Z.of_nat]; lia) ltac:(lia)) as HS3.
  step. step.
  pose proof (op2_mem_store _ _ _ _ _ _ _ _ _ _ _ 17 (le1 (Z_to_bv 64 51)) (Sp + 113) HM2
                ltac:(lia) ltac:(rewrite length_le1; cbn [Z.of_nat]; lia) ltac:(lia)) as HM3.
  clear HS3 HM2.
  pose proof (op2_mem_store_ok _ _ _ _ _ _ _ _ _ _ _ 18 1%nat (Sp + 114) HM3
                ltac:(lia) ltac:(cbn [Z.of_nat]; lia) ltac:(lia)) as HS4.
  step. step.
  pose proof (op2_mem_store _ _ _ _ _ _ _ _ _ _ _ 18 (le1 (Z_to_bv 64 55)) (Sp + 114) HM3
                ltac:(lia) ltac:(rewrite length_le1; cbn [Z.of_nat]; lia) ltac:(lia)) as HM4.
  clear HS4 HM3.
  rewrite (op2_v137 (op2_b1 mac) T LB1 LT) in HM4.
  (* 0x14058 li a0,-0x19; 0x1405c bltu a0,s5 *)
  step. op2_trap.
  pose proof (op2_mem_facts _ _ _ _ _ _ _ _ _ _ _ HM4) as
    (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HROb & _ & _).
  assert (CN : name = 0 \/ name = 1 \/ name = 2) by lia.
  (* 0x14060 slli s2,s2,3; 0x14064 auipc; 0x14068 addi: a0 = &NAME; 0x1406c not a1,a0; 0x14070 bltu a1,s2;
     0x14074 add a0,a0,s2; 0x14078 ld s4,0(a0) *)
  destruct CN as [EN|[EN|EN]]; subst name;
    [ pose proof (op2_namet_rd _ 0 0x21f78 HROb ltac:(lia) ltac:(lia)) as HRN
    | pose proof (op2_namet_rd _ 1 0x21f80 HROb ltac:(lia) ltac:(lia)) as HRN
    | pose proof (op2_namet_rd _ 2 0x21f88 HROb ltac:(lia) ltac:(lia)) as HRN ];
    unfold op2_namep in HRN; cbn [Z.eqb Pos.eqb] in HRN;
    do 4 step; op2_trap; do 2 step;
    (eapply op2_names;
      [ exact MEMCPY | exact STRLEN | exact INV | exact LT
      | unfold op2_namep; cbn [Z.eqb Pos.eqb]; reflexivity | exact HM4 ]).
Qed.

(* ---------------------------------------------------------------- 0x14014 and 0x140d0: the MAC copy *)

Lemma op2_fromC : memcpy_contract -> strlen_contract ->
  forall data D regs0 m0 Sp lo ops B c c3 sel mac name T
    (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 s7 t3 t4 t5 t6 : word)
    (m : word -> option byte) (j10 jio : list byte) F fc,
  op2_inv D B ops c c3 sel mac name ->
  s6 = Z_to_bv 64 (fi_n c3) ->
  mac < 10 ->
  length T = 6%nat ->
  llvm_mem data D regs0 m0 Sp lo B m j10 jio (op2_b0 ++ T) ->
  evt rsegs (op2_goal data D regs0 m0 Sp lo ops B c F fc)
    (MS (mkR ra (Z_to_bv 64 Sp) (reg_get regs0 3) (reg_get regs0 4) t0 t1 t2 (Z_to_bv 64 sel) (Z_to_bv 64 1)
           a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 name) (Z_to_bv 64 (data + fi_off c3)) (Z_to_bv 64 mac)
           (Z_to_bv 64 (Sp + 96)) s6 s7
           (Z_to_bv 64 (W_BASE_UBSAN + OFF_M)) (Z_to_bv 64 (W_BASE_UBSAN + OFF_g_fail_next))
           (Z_to_bv 64 (W_BASE_UBSAN + OFF_g_s)) (Z_to_bv 64 ops) t3 t4 t5 t6)
        F (Z_to_bv 64 0x14014) fc None m (seg_rom rsegs)).
Proof.
  intros MEMCPY STRLEN data D regs0 m0 Sp lo ops B c c3 sel mac name T
    ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 s7 t3 t4 t5 t6 m j10 jio F fc INV Es6 HM10 LT HM.
  subst s6.
  pose proof INV as INV0. destruct INV0 as (HOPS & HSEL & HMAC & HNAME & HCUR & HEQ).
  pose proof (op2_mem_facts _ _ _ _ _ _ _ _ _ _ _ HM) as
    (HD0 & HDL & HLO & HSP2 & HWL & HSP16 & HJ1 & HJ2 & HJ3 & HMI & HRO & _ & _).
  unfold W_BASE_UBSAN, W_LEN in HWL.
  assert (LH6 : length HOST = 6%nat) by reflexivity.
  pose proof op2_b0_len as LB0.
  pose proof (op2_mem_rd48 _ _ _ _ _ _ _ _ _ _ _ _ HM eq_refl) as HR48.
  (* 0x14014 ld a0,0x30(sp); 0x14018 bltu a0,s4 *)
  step. op2_trap.
  (* 0x1401c add a0,s5,s4; 0x14020 auipc a1; 0x14024 addi a1; 0x14028 li a2,6; 0x1402c jal memcpy *)
  do 5 step.
  pose proof (op2_mem_cell _ _ _ _ _ _ _ _ _ _ _ mac 6 (Sp + 96 + mac) HM
                ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as DSTc.
  eapply evt_cut.
  { eapply MEMCPY with (src := HOST) (junk := sub (op2_b0 ++ T) mac (Z.to_nat 6)).
    - rewrite (unsigned_lit 66672) by lia. exact (op2_host_at m HMI).
    - rewrite (unsigned_lit 6) by lia. reflexivity.
    - rewrite (unsigned_lit (Sp + 96 + mac)) by lia. rewrite (unsigned_lit 6) by lia. exact DSTc.
    - rewrite (unsigned_lit 66672) by lia. rewrite (unsigned_lit (Sp + 96 + mac)) by lia.
      rewrite (unsigned_lit 6) by lia. left. lia.
    - exact HMI. }
  intros ms2 PO2. unfold memcpy_post in PO2. destruct_exs PO2.
  destruct PO2 as (E2 & MUc & WMc & MIc & DSTf & SRCf). subst ms2.
  rewrite (ret_pc_even 81968) by (first [lia | reflexivity]).
  rewrite (unsigned_lit (Sp + 96 + mac)) in MUc, DSTf by lia.
  rewrite (unsigned_lit 6) in MUc, DSTf by lia.
  pose proof (op2_mem_fill _ _ _ _ _ _ _ _ _ _ _ _ mac 6 HOST (Sp + 96 + mac)
                HM MUc WMc MIc DSTf ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as HMc.
  rewrite (op2_upd_app_l op2_b0 T HOST mac) in HMc by lia.
  replace (upd op2_b0 mac HOST) with (op2_b1 mac) in HMc
    by (unfold op2_b1; destruct (Z.ltb_spec mac 10); [reflexivity | lia]).
  eapply op2_tailC; [exact MEMCPY | exact STRLEN | exact INV | exact LT | exact HMc].
Qed.

Lemma op2_fromD : memcpy_contract -> strlen_contract ->
  forall data D regs0 m0 Sp lo ops B c c3 sel mac name T
    (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s7 t3 t4 t5 t6 : word)
    (m : word -> option byte) (j10 jio : list byte) F fc,
  op2_inv D B ops c c3 sel mac name ->
  10 <= mac ->
  length T = 6%nat ->
  llvm_mem data D regs0 m0 Sp lo B m j10 jio (op2_b0 ++ T) ->
  evt rsegs (op2_goal data D regs0 m0 Sp lo ops B c F fc)
    (MS (mkR ra (Z_to_bv 64 Sp) (reg_get regs0 3) (reg_get regs0 4) t0 t1 t2 (Z_to_bv 64 sel) (Z_to_bv 64 1)
           a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 name) (Z_to_bv 64 (data + fi_off c3)) (Z_to_bv 64 mac)
           (Z_to_bv 64 (Sp + 96)) (Z_to_bv 64 (fi_n c3)) s7
           (Z_to_bv 64 (W_BASE_UBSAN + OFF_M)) (Z_to_bv 64 (W_BASE_UBSAN + OFF_g_fail_next))
           (Z_to_bv 64 (W_BASE_UBSAN + OFF_g_s)) (Z_to_bv 64 ops) t3 t4 t5 t6)
        F (Z_to_bv 64 0x140d0) fc None m (seg_rom rsegs)).
Proof.
  intros MEMCPY STRLEN data D regs0 m0 Sp lo ops B c c3 sel mac name T
    ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s7 t3 t4 t5 t6 m j10 jio F fc INV HM10 LT HM.
  pose proof INV as INV0. destruct INV0 as (HOPS & HSEL & HMAC & HNAME & HCUR & HEQ).
  pose proof (op2_mem_facts _ _ _ _ _ _ _ _ _ _ _ HM) as
    (HD0 & HDL & HLO & HSP2 & HWL & HSP16 & HJ1 & HJ2 & HJ3 & HMI & HRO & _ & _).
  unfold W_BASE_UBSAN, W_LEN in HWL.
  assert (LO6 : length OTHER = 6%nat) by reflexivity.
  pose proof op2_b0_len as LB0.
  (* 0x140d0 li a0,0xc; 0x140d4 bltu a0,s4 -> 0x14030 when 13 <= mac *)
  do 2 step.
  destruct (Z_le_gt_dec 13 mac) as [H13|H13].
  - op2_br true.
    replace (op2_b0 ++ T) with (op2_b1 mac ++ T) in HM
      by (unfold op2_b1; destruct (Z.ltb_spec mac 10); [lia|];
          destruct (Z.ltb_spec mac 13); [lia | reflexivity]).
    eapply op2_tailC; [exact MEMCPY | exact STRLEN | exact INV | exact LT | exact HM].
  - op2_br false.
    pose proof (op2_mem_rd48 _ _ _ _ _ _ _ _ _ _ _ _ HM eq_refl) as HR48.
    (* 0x140d8 ld a0,0x30(sp); 0x140dc bltu a0,s4 *)
    step. op2_trap.
    (* 0x140e0 add a0,s5,s4; 0x140e4 li a1,0xa; 0x140e8 beq a0,a1 *)
    step. step. op2_trap.
    (* 0x140ec li a1,0xa; 0x140f0 bltu a0,a1 *)
    step. op2_trap.
    (* 0x140f4 addi a0,a0,-0xa; 0x140f8 auipc a1; 0x140fc addi a1; 0x14100 j 0x14028;
       0x14028 li a2,6; 0x1402c jal memcpy *)
    do 6 step.
    pose proof (op2_mem_cell _ _ _ _ _ _ _ _ _ _ _ (mac - 10) 6 (Sp + 96 + mac + -10) HM
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as DSTc.
    eapply evt_cut.
    { eapply MEMCPY with (src := OTHER) (junk := sub (op2_b0 ++ T) (mac - 10) (Z.to_nat 6)).
      - rewrite (unsigned_lit 66712) by lia. exact (op2_other_at m HMI).
      - rewrite (unsigned_lit 6) by lia. reflexivity.
      - rewrite (unsigned_lit (Sp + 96 + mac + -10)) by lia. rewrite (unsigned_lit 6) by lia. exact DSTc.
      - rewrite (unsigned_lit 66712) by lia. rewrite (unsigned_lit (Sp + 96 + mac + -10)) by lia.
        rewrite (unsigned_lit 6) by lia. left. lia.
      - exact HMI. }
    intros ms2 PO2. unfold memcpy_post in PO2. destruct_exs PO2.
    destruct PO2 as (E2 & MUc & WMc & MIc & DSTf & SRCf). subst ms2.
    rewrite (ret_pc_even 81968) by (first [lia | reflexivity]).
    rewrite (unsigned_lit (Sp + 96 + mac + -10)) in MUc, DSTf by lia.
    rewrite (unsigned_lit 6) in MUc, DSTf by lia.
    pose proof (op2_mem_fill _ _ _ _ _ _ _ _ _ _ _ _ (mac - 10) 6 OTHER (Sp + 96 + mac + -10)
                  HM MUc WMc MIc DSTf ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as HMc.
    rewrite (op2_upd_app_l op2_b0 T OTHER (mac - 10)) in HMc by lia.
    replace (upd op2_b0 (mac - 10) OTHER) with (op2_b1 mac) in HMc
      by (unfold op2_b1; destruct (Z.ltb_spec mac 10); [lia|];
          destruct (Z.ltb_spec mac 13); [reflexivity | lia]).
    eapply op2_tailC; [exact MEMCPY | exact STRLEN | exact INV | exact LT | exact HMc].
Qed.

(* ---------------------------------------------------------------- the two memsets of body[] *)

Lemma op2_mset_eq : forall (a1 : word), a1 = Z_to_bv 64 0 ->
  repeat (Z_to_bv 8 (bv_unsigned a1 mod 256)) (Z.to_nat 34) = op2_b0.
Proof.
  intros a1 ->. unfold op2_b0.
  f_equal; try (apply bv_eq); vm_compute; reflexivity.
Qed.

(* 0x13ff4: mac = m & 15, the memset of body[], then the split on mac < 10 *)
Lemma op2_from_ff4 : memset_contract -> memcpy_contract -> strlen_contract ->
  forall data D regs0 m0 Sp lo ops B c c3 sel mb name
    (ra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s4 s5 s7 t3 t4 t5 t6 : word)
    (m : word -> option byte) (j10 jio j60 : list byte) F fc,
  op2_inv D B ops c c3 sel (mb mod 16) name ->
  0 <= mb < 256 ->
  llvm_mem data D regs0 m0 Sp lo B m j10 jio j60 ->
  evt rsegs (op2_goal data D regs0 m0 Sp lo ops B c F fc)
    (MS (mkR ra (Z_to_bv 64 Sp) (reg_get regs0 3) (reg_get regs0 4) t0 t1 t2 (Z_to_bv 64 sel) (Z_to_bv 64 1)
           (Z_to_bv 64 mb) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 name) (Z_to_bv 64 (data + fi_off c3)) s4
           s5 (Z_to_bv 64 (fi_n c3)) s7
           (Z_to_bv 64 (W_BASE_UBSAN + OFF_M)) (Z_to_bv 64 (W_BASE_UBSAN + OFF_g_fail_next))
           (Z_to_bv 64 (W_BASE_UBSAN + OFF_g_s)) (Z_to_bv 64 ops) t3 t4 t5 t6)
        F (Z_to_bv 64 0x13ff4) fc None m (seg_rom rsegs)).
Proof.
  intros MEMSET MEMCPY STRLEN data D regs0 m0 Sp lo ops B c c3 sel mb name
    ra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s4 s5 s7 t3 t4 t5 t6 m j10 jio j60 F fc INV HMB HM.
  pose proof INV as INV0. destruct INV0 as (HOPS & HSEL & HMAC & HNAME & HCUR & HEQ).
  pose proof (op2_mem_facts _ _ _ _ _ _ _ _ _ _ _ HM) as
    (HD0 & HDL & HLO & HSP2 & HWL & HSP16 & HJ1 & HJ2 & HJ3 & HMI & HRO & _ & _).
  unfold W_BASE_UBSAN, W_LEN in HWL.
  (* 0x13ff4 andi s4,a0,0xf; 0x13ff8 addi a0,sp,0x60; 0x13ffc li a2,0x22; 0x14000 mv a1,zero;
     0x14004 jal memset *)
  do 5 zstep.
  rewrite (op2_land15 mb ltac:(lia)).
  pose proof (op2_mem_cell _ _ _ _ _ _ _ _ _ _ _ 0 34 (Sp + 96) HM
                ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as DSTc.
  eapply evt_cut.
  { eapply MEMSET with (junk := sub j60 0 (Z.to_nat 34)).
    - rewrite (unsigned_lit (Sp + 96)) by lia. rewrite (unsigned_lit 34) by lia. exact DSTc.
    - exact HMI. }
  intros ms2 PO2. unfold memset_post in PO2. destruct_exs PO2.
  destruct PO2 as (E2 & MUc & WMc & MIc & DSTf). subst ms2.
  rewrite (ret_pc_even 81928) by (first [lia | reflexivity]).
  rewrite (unsigned_lit (Sp + 96)) in MUc, DSTf by lia.
  rewrite (unsigned_lit 34) in MUc, DSTf by lia.
  rewrite (op2_mset_eq (Z_to_bv 64 0) eq_refl) in DSTf.
  pose proof (op2_mem_fill _ _ _ _ _ _ _ _ _ _ _ _ 0 34 op2_b0 (Sp + 96)
                HM MUc WMc MIc DSTf ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as HMc.
  rewrite (op2_upd0 j60 op2_b0 34 op2_b0_len ltac:(lia)) in HMc.
  assert (LT : length (skipn 34 j60) = 6%nat) by (rewrite length_skipn, HJ3; reflexivity).
  (* 0x14008 addi s5,sp,0x60; 0x1400c li a0,9; 0x14010 bltu a0,s4 -> 0x140d0 when 10 <= mac *)
  do 3 step.
  destruct (Z_le_gt_dec 10 (mb mod 16)) as [H10|H10].
  - op2_br true. eapply op2_fromD; [exact MEMCPY | exact STRLEN | exact INV | lia | exact LT | exact HMc].
  - op2_br false.
    eapply op2_fromC;
      [exact MEMCPY | exact STRLEN | exact INV | reflexivity | lia | exact LT | exact HMc].
Qed.

(* 0x13df0: the short-input paths (mac = 0, name = 0, an empty cursor) *)
Lemma op2_from_df0 : memset_contract -> memcpy_contract -> strlen_contract ->
  forall data D regs0 m0 Sp lo ops B c c3 sel
    (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 t3 t4 t5 t6 : word)
    (m : word -> option byte) (j10 jio j60 : list byte) F fc,
  op2_inv D B ops c c3 sel 0 0 ->
  fi_n c3 = 0 ->
  llvm_mem data D regs0 m0 Sp lo B m j10 jio j60 ->
  evt rsegs (op2_goal data D regs0 m0 Sp lo ops B c F fc)
    (MS (mkR ra (Z_to_bv 64 Sp) (reg_get regs0 3) (reg_get regs0 4) t0 t1 t2 (Z_to_bv 64 sel) (Z_to_bv 64 1)
           a0 a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 (data + fi_off c3)) s4 s5 s6 s7
           (Z_to_bv 64 (W_BASE_UBSAN + OFF_M)) (Z_to_bv 64 (W_BASE_UBSAN + OFF_g_fail_next))
           (Z_to_bv 64 (W_BASE_UBSAN + OFF_g_s)) (Z_to_bv 64 ops) t3 t4 t5 t6)
        F (Z_to_bv 64 0x13df0) fc None m (seg_rom rsegs)).
Proof.
  intros MEMSET MEMCPY STRLEN data D regs0 m0 Sp lo ops B c c3 sel
    ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 t3 t4 t5 t6 m j10 jio j60 F fc INV HN3 HM.
  pose proof INV as INV0. destruct INV0 as (HOPS & HSEL & HMAC & HNAME & HCUR & HEQ).
  pose proof (op2_mem_facts _ _ _ _ _ _ _ _ _ _ _ HM) as
    (HD0 & HDL & HLO & HSP2 & HWL & HSP16 & HJ1 & HJ2 & HJ3 & HMI & HRO & _ & _).
  unfold W_BASE_UBSAN, W_LEN in HWL.
  (* 0x13df0 addi a0,sp,0x60; 0x13df4 li a2,0x22; 0x13df8 mv a1,zero; 0x13dfc jal memset *)
  do 4 step.
  pose proof (op2_mem_cell _ _ _ _ _ _ _ _ _ _ _ 0 34 (Sp + 96) HM
                ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as DSTc.
  eapply evt_cut.
  { eapply MEMSET with (junk := sub j60 0 (Z.to_nat 34)).
    - rewrite (unsigned_lit (Sp + 96)) by lia. rewrite (unsigned_lit 34) by lia. exact DSTc.
    - exact HMI. }
  intros ms2 PO2. unfold memset_post in PO2. destruct_exs PO2.
  destruct PO2 as (E2 & MUc & WMc & MIc & DSTf). subst ms2.
  rewrite (ret_pc_even 81408) by (first [lia | reflexivity]).
  rewrite (unsigned_lit (Sp + 96)) in MUc, DSTf by lia.
  rewrite (unsigned_lit 34) in MUc, DSTf by lia.
  rewrite (op2_mset_eq (Z_to_bv 64 0) eq_refl) in DSTf.
  pose proof (op2_mem_fill _ _ _ _ _ _ _ _ _ _ _ _ 0 34 op2_b0 (Sp + 96)
                HM MUc WMc MIc DSTf ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as HMc.
  rewrite (op2_upd0 j60 op2_b0 34 op2_b0_len ltac:(lia)) in HMc.
  assert (LT : length (skipn 34 j60) = 6%nat) by (rewrite length_skipn, HJ3; reflexivity).
  (* 0x13e00 mv s6,zero; 0x13e04 mv s2,zero; 0x13e08 mv s4,zero; 0x13e0c addi s5,sp,0x60; 0x13e10 j 0x14014 *)
  do 5 step.
  eapply op2_fromC;
    [exact MEMCPY | exact STRLEN | exact INV | (rewrite HN3; reflexivity) | lia | exact LT | exact HMc].
Qed.

(* ---------------------------------------------------------------- 0x13ab8: the head of the case *)

Lemma op2_head : memset_contract -> memcpy_contract -> strlen_contract ->
  forall data D regs0 m0 Sp lo ops c c1 B F fc ms,
  llvm_case data D regs0 2 m0 Sp lo ops c c1 B F fc ms ->
  evt rsegs (op2_goal data D regs0 m0 Sp lo ops B c F fc) ms.
Proof.
  intros MEMSET MEMCPY STRLEN data D regs0 m0 Sp lo ops c c1 B F fc ms HC.
  destruct HC as (ra & t0 & t1 & t2 & s0 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 &
                  m & j10 & jio & j60 & -> & HOPS & HN & HCUR & HC1 & HOP & HM).
  pose proof (op2_mem_facts _ _ _ _ _ _ _ _ _ _ _ HM) as
    (HD0 & HDL & HLO & HSP2 & HWL & HSP16 & HJ1 & HJ2 & HJ3 & HMI & HRO & _ & _).
  unfold W_BASE_UBSAN, W_LEN in HWL. unfold llvm_cursor in HCUR.
  assert (EU : fuzz_u8_m D c = (FuzzIn (fi_off c + 1) (fi_n c - 1), at8 D (Z.to_nat (fi_off c))))
    by (unfold fuzz_u8_m; destruct (Z.eqb_spec (fi_n c) 0); [contradiction | reflexivity]).
  assert (EF0 : fst (fuzz_u8_m D c) = c1) by (rewrite HC1; reflexivity).
  assert (EC1 : c1 = FuzzIn (fi_off c + 1) (fi_n c - 1)) by (rewrite HC1, EU; reflexivity).
  assert (Efo : fi_off c1 = fi_off c + 1) by (rewrite EC1; reflexivity).
  assert (Efn : fi_n c1 = fi_n c - 1) by (rewrite EC1; reflexivity).
  unfold LH_CASE. cbn [Z.eqb Pos.eqb].
  (* 0x13ab8 beqz s6, 0x13dec: no byte left for sel *)
  step.
  destruct (Z.eqb_spec (fi_n c1) 0) as [E1|E1].
  - (* fi_n c = 1: sel = 0, mac = 0, name = 0, the cursor stops after the op byte *)
    op2_br true.
    assert (EF : fuzz_u8_m D c1 = (c1, 0))
      by (unfold fuzz_u8_m; destruct (Z.eqb_spec (fi_n c1) 0); [reflexivity | lia]).
    assert (INV : op2_inv D B ops c c1 0 0 0).
    { split; [exact HOPS|]. split; [lia|]. split; [lia|]. split; [lia|].
      split; [unfold llvm_cursor; lia|].
      unfold op2_eqm. intros I A k. rewrite (op2_opm I B A D c k HOP). rewrite EF0.
      unfold op2_cmd, op2_body, op2_sel, op2_name, op2_mac, op2_c3, op2_cb, op2_ca.
      repeat (rewrite EF; cbn [fst snd]). reflexivity. }
    (* 0x13dec mv s0,zero *)
    step.
    eapply (op2_from_df0 MEMSET MEMCPY STRLEN data D regs0 m0 Sp lo ops B c c1 0);
      [ exact INV | lia | exact HM ].
  - (* at least one byte for sel *)
    op2_br false.
    assert (HI1 : (Z.to_nat (fi_off c + 1) < length D)%nat) by lia.
    pose proof (op2_mem_in _ _ _ _ _ _ _ _ _ _ _ (fi_off c + 1) (data + fi_off c + 1) HM
                  ltac:(lia) HI1 ltac:(lia)) as HRS.
    assert (EFa : fuzz_u8_m D c1 = (FuzzIn (fi_off c + 2) (fi_n c - 2), at8 D (Z.to_nat (fi_off c + 1))))
      by (unfold fuzz_u8_m; destruct (Z.eqb_spec (fi_n c1) 0); [lia|];
          rewrite Efo, Efn; f_equal; f_equal; lia).
    assert (HSELR : 0 <= at8 D (Z.to_nat (fi_off c + 1)) < 256) by (unfold at8, bz; apply op2_byte_rng).
    (* 0x13abc addi s3,s3,1; 0x13ac0 bgeu s1,s3; 0x13ac4 lbu s0,1(s5); 0x13ac8 addi s3,s5,2;
       0x13acc li a0,2; 0x13ad0 beq s7,a0 -> 0x13df0 *)
    step. op2_trap. do 4 zstep.
    change (bv_unsigned (nth (Z.to_nat (fi_off c + 1)) D (b8 0)))
      with (at8 D (Z.to_nat (fi_off c + 1))).
    destruct (Z.eqb_spec (fi_n c) 2) as [E2|E2].
    + (* exactly two bytes: m and nm are 0 *)
      op2_br true.
      assert (EFb : fuzz_u8_m D (FuzzIn (fi_off c + 2) 0) = (FuzzIn (fi_off c + 2) 0, 0))
        by reflexivity.
      assert (INV : op2_inv D B ops c (FuzzIn (fi_off c + 2) 0) (at8 D (Z.to_nat (fi_off c + 1))) 0 0).
      { split; [exact HOPS|]. split; [exact HSELR|]. split; [lia|]. split; [lia|].
        split; [unfold llvm_cursor; cbn [fi_off fi_n]; lia|].
        unfold op2_eqm. intros I A k. rewrite (op2_opm I B A D c k HOP). rewrite EF0.
        unfold op2_cmd, op2_body, op2_sel, op2_name, op2_mac, op2_c3, op2_cb, op2_ca.
        rewrite EFa. cbn [fst snd].
        replace (FuzzIn (fi_off c + 2) (fi_n c - 2)) with (FuzzIn (fi_off c + 2) 0) by (f_equal; lia).
        rewrite EFb. cbn [fst snd]. rewrite EFb. cbn [fst snd]. reflexivity. }
      replace (data + fi_off c + 2) with (data + fi_off (FuzzIn (fi_off c + 2) 0))
        by (cbn [fi_off]; lia).
      eapply (op2_from_df0 MEMSET MEMCPY STRLEN data D regs0 m0 Sp lo ops B c
                (FuzzIn (fi_off c + 2) 0) (at8 D (Z.to_nat (fi_off c + 1))));
        [ exact INV | reflexivity | exact HM ].
    + op2_br false.
      assert (HI2 : (Z.to_nat (fi_off c + 2) < length D)%nat) by lia.
      pose proof (op2_mem_in _ _ _ _ _ _ _ _ _ _ _ (fi_off c + 2) (data + fi_off c + 2) HM
                    ltac:(lia) HI2 ltac:(lia)) as HRM.
      assert (HMBR : 0 <= at8 D (Z.to_nat (fi_off c + 2)) < 256) by (unfold at8, bz; apply op2_byte_rng).
      (* 0x13ad4 addi s3,s3,1; 0x13ad8 bgeu s1,s3; 0x13adc lbu a0,2(s5); 0x13ae0 addi s3,s5,3;
         0x13ae4 li a1,3; 0x13ae8 bne s7,a1 -> 0x13fc8 *)
      step. op2_trap. do 4 zstep.
      change (bv_unsigned (nth (Z.to_nat (fi_off c + 2)) D (b8 0)))
        with (at8 D (Z.to_nat (fi_off c + 2))).
      destruct (Z.eqb_spec (fi_n c) 3) as [E3|E3].
      * (* exactly three bytes: nm is 0, so name = 0 *)
        op2_br false.
        assert (EFb : fuzz_u8_m D (FuzzIn (fi_off c + 2) (fi_n c - 2))
                    = (FuzzIn (fi_off c + 3) 0, at8 D (Z.to_nat (fi_off c + 2))))
          by (unfold fuzz_u8_m; cbn [fi_n fi_off];
              destruct (Z.eqb_spec (fi_n c - 2) 0); [lia|]; f_equal; f_equal; lia).
        assert (EFc : fuzz_u8_m D (FuzzIn (fi_off c + 3) 0) = (FuzzIn (fi_off c + 3) 0, 0))
          by (unfold fuzz_u8_m; cbn [fi_n fi_off]; reflexivity).
        assert (INV : op2_inv D B ops c (FuzzIn (fi_off c + 3) 0)
                        (at8 D (Z.to_nat (fi_off c + 1))) (at8 D (Z.to_nat (fi_off c + 2)) mod 16) 0).
        { split; [exact HOPS|]. split; [exact HSELR|]. split; [lia|]. split; [lia|].
          split; [unfold llvm_cursor; cbn [fi_off fi_n]; lia|].
          unfold op2_eqm. intros I A k. rewrite (op2_opm I B A D c k HOP). rewrite EF0.
          unfold op2_cmd, op2_body, op2_sel, op2_name, op2_mac, op2_c3, op2_cb, op2_ca.
          rewrite EFa. cbn [fst snd]. rewrite EFb. cbn [fst snd]. rewrite EFc. cbn [fst snd].
          reflexivity. }
        (* 0x13aec mv s6,zero; 0x13af0 mv s2,zero; 0x13af4 j 0x13ff4 *)
        do 3 step.
        replace (data + fi_off c + 3) with (data + fi_off (FuzzIn (fi_off c + 3) 0))
          by (cbn [fi_off]; lia).
        eapply (op2_from_ff4 MEMSET MEMCPY STRLEN data D regs0 m0 Sp lo ops B c
                  (FuzzIn (fi_off c + 3) 0) (at8 D (Z.to_nat (fi_off c + 1)))
                  (at8 D (Z.to_nat (fi_off c + 2))) 0);
          [ exact INV | exact HMBR | exact HM ].
      * (* four bytes or more: nm is read and reduced mod 3 by the multiply at 0x13fe4 *)
        op2_br true.
        assert (HI3 : (Z.to_nat (fi_off c + 3) < length D)%nat) by lia.
        pose proof (op2_mem_in _ _ _ _ _ _ _ _ _ _ _ (fi_off c + 3) (data + fi_off c + 3) HM
                      ltac:(lia) HI3 ltac:(lia)) as HRN.
        assert (HNMR : 0 <= at8 D (Z.to_nat (fi_off c + 3)) < 256) by (unfold at8, bz; apply op2_byte_rng).
        assert (EFb : fuzz_u8_m D (FuzzIn (fi_off c + 2) (fi_n c - 2))
                    = (FuzzIn (fi_off c + 3) (fi_n c - 3), at8 D (Z.to_nat (fi_off c + 2))))
          by (unfold fuzz_u8_m; cbn [fi_n fi_off];
              destruct (Z.eqb_spec (fi_n c - 2) 0); [lia|]; f_equal; f_equal; lia).
        assert (EFc : fuzz_u8_m D (FuzzIn (fi_off c + 3) (fi_n c - 3))
                    = (FuzzIn (fi_off c + 4) (fi_n c - 4), at8 D (Z.to_nat (fi_off c + 3))))
          by (unfold fuzz_u8_m; cbn [fi_n fi_off];
              destruct (Z.eqb_spec (fi_n c - 3) 0); [lia|]; f_equal; f_equal; lia).
        assert (INV : op2_inv D B ops c (FuzzIn (fi_off c + 4) (fi_n c - 4))
                        (at8 D (Z.to_nat (fi_off c + 1))) (at8 D (Z.to_nat (fi_off c + 2)) mod 16)
                        (at8 D (Z.to_nat (fi_off c + 3)) mod 3)).
        { split; [exact HOPS|]. split; [exact HSELR|]. split; [lia|]. split; [lia|].
          split; [unfold llvm_cursor; cbn [fi_off fi_n]; lia|].
          unfold op2_eqm. intros I A k. rewrite (op2_opm I B A D c k HOP). rewrite EF0.
          unfold op2_cmd, op2_body, op2_sel, op2_name, op2_mac, op2_c3, op2_cb, op2_ca.
          rewrite EFa. cbn [fst snd]. rewrite EFb. cbn [fst snd]. rewrite EFc. cbn [fst snd].
          reflexivity. }
        (* 0x13fc8 addi s3,s3,1; 0x13fcc bgeu s1,s3; 0x13fd0 lbu a1,3(s5); 0x13fd4 auipc a2;
           0x13fd8 ld a2,0x3dc(a2); 0x13fdc addi s6,s7,-4; 0x13fe0 addi s3,s5,4 *)
        step. op2_trap. do 5 zstep.
        change (bv_unsigned (nth (Z.to_nat (fi_off c + 3)) D (b8 0)))
          with (at8 D (Z.to_nat (fi_off c + 3))).
        (* 0x13fe4 mulhu a2,a1,a2: the quotient of nm by 3 *)
        zstep.
        rewrite (op2_div3 (at8 D (Z.to_nat (fi_off c + 3))) HNMR).
        (* 0x13fe8 slli a3,a2,1; 0x13fec sub a1,a1,a2; 0x13ff0 sub s2,a1,a3 *)
        zstep. rewrite Z.shiftl_mul_pow2 by lia.
        zstep. zstep.
        replace (at8 D (Z.to_nat (fi_off c + 3)) - at8 D (Z.to_nat (fi_off c + 3)) / 3
                 - at8 D (Z.to_nat (fi_off c + 3)) / 3 * 2)
          with (at8 D (Z.to_nat (fi_off c + 3)) mod 3) by (Z.div_mod_to_equations; lia).
        replace (data + fi_off c + 4) with (data + fi_off (FuzzIn (fi_off c + 4) (fi_n c - 4)))
          by (cbn [fi_off]; lia).
        replace (fi_n c + -4) with (fi_n (FuzzIn (fi_off c + 4) (fi_n c - 4))) by (cbn [fi_n]; lia).
        eapply (op2_from_ff4 MEMSET MEMCPY STRLEN data D regs0 m0 Sp lo ops B c
                  (FuzzIn (fi_off c + 4) (fi_n c - 4)) (at8 D (Z.to_nat (fi_off c + 1)))
                  (at8 D (Z.to_nat (fi_off c + 2))) (at8 D (Z.to_nat (fi_off c + 3)) mod 3));
          [ exact INV | exact HMBR | exact HM ].
Qed.

(* ---------------------------------------------------------------- the piece *)

Theorem llvm_op2_holds : memset_contract -> memcpy_contract -> strlen_contract ->
  llvm_op_bar_stmt 2 LH_RET_BAR2.
Proof.
  intros MEMSET MEMCPY STRLEN.
  unfold llvm_op_bar_stmt. intros data D regs0 m0 Sp lo ops c c1 B F fc ms HC.
  exact (op2_head MEMSET MEMCPY STRLEN data D regs0 m0 Sp lo ops c c1 B F fc ms HC).
Qed.
