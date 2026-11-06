(* reac_frame_is_reac_cg: the ASan contract of reac_frame_is_reac (fuzz_wire.asan-ubsan 0x8183c), in the leaf form
   of the shared kit lib/B/Prog/LeafCgKit.v (SRr world walk), and its translation from the footprint contract
   (lib/B/Prog/reac_frame_is_reac_F_nosh.v), PROVED here over the kit's generic translation; no walk of the function.

   The C (libreac src/reac.c reac_frame_is_reac (frame, len)): 0 when frame is NULL or len < 14; else 1 when
   frame[12] = 0x88 and frame[13] = 0x19, and 0 otherwise (is_reac_result, lib/B/Prog/reac_frame_is_reac_c.v).
   The code (image B; offsets from the entry 0x8183c, 43 words to 0x818e8; byte for byte the function of decode's
   image B at 0x8144c, except the pc-relative words +0x20, +0x24, +0x9c and +0xa8, which reach the GOT word of the
   same runtime cell and the same error-path entry at image B's addresses: 0x98878 -> 0xa07f8, and 0x57e5c):
     +0x0   `addi sp, sp, -16`, +0x4 `sd ra, 8(sp)`: the frame [sp - 16, sp) (REAC_FRAME_IS_REAC_FRAME);
            +0x80 `ld ra, 8(sp)`, +0x84 `addi sp, sp, 16`, +0x88 `ret`;
     +0xc   `beqz a0` and +0x14 `bltu a1, a3` (a3 = 14, +0x10) go to +0x7c with a2 = 0 (+0x8): the result 0;
     +0x1c  `bgeu a0, a1` (a1 = -12, +0x18) and +0x50 `bltu a1, a0` (a1 = -14, +0x4c) go to `unimp` at +0x8c
            (0x818c8): image B's UBSan checks that a0 + 12 and a0 + 13 do not wrap. The premise
            `addressable m (a0 + 12) 2` (a0 + 14 <= APPMEM_END) refutes both;
     +0x20 / +0x24 `auipc a1, 0x17` / `ld a1, 28(a1)` read the GOT word GOT_CELL_K = 0x98878, which holds
            CELL_K = 0xa07f8; +0x28 `ld a2, 0(a1)` reads the 8 bytes at CELL_K (the shadow base ASAN_K);
     +0x2c..+0x38 load the shadow byte k of a0 + 12 (signed: `lb`), at ((a0 + 12) >> 3) + ASAN_K; when k <> 0,
            +0x3c goes to +0x90, where +0x94 `blt a4, a3` (signed; a4 = (a0 + 12) mod 8) goes back to +0x40, else
            +0x9c `jal` 0x57e5c is the error path (1-byte load); +0x40 `lbu a1, 0(a1)` loads the byte at a0 + 12,
            +0x44 / +0x48 compare it with 0x88 (136) and go to +0x78 (a2 = 0) when it differs;
     +0x54..+0x64 the same check for a0 + 13 (its error path +0xa0..+0xa8, `jal` 0x57e5c at +0xa8); +0x68
            `lbu a0, 0(a0)` loads the byte at a0 + 13; +0x6c / +0x70 `addi a0, a0, -25` / `seqz a2, a0`: a2 = 1
            when it is 0x19 (25), else 0; +0x74 `j` +0x7c;
     +0x7c  `mv a0, a2`: the result.
   Its only calls are the two `jal` of the error path, which the shadow premise keeps unreached, so the statement has
   no callee premise. The shadow premise `addressable m (a0 + 12) 2` makes both checks pass (k = 0, or
   (a mod 8) < k, k signed), so the error path is not reached; no premise says that the error path is not called. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B Require Import Img0 AsanCells.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog Require Import AsanKA reac_frame_is_reac_c.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Lib Require Import ExecF.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YK11.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog Require Import reac_frame_is_reac_F_c reac_frame_is_reac_F_nosh LeafCgKit.
From Stdlib Require Import Lia.
Open Scope Z_scope.

Section LeafCg.
Context {fx : YK11.FPState}.
Variable world : Type.                                                (* YA0n.v Record world *)
Variable w_H : world -> word -> bool.                                 (* YA0n.v field w_H *)
Variable SRr : world -> config -> (world -> config -> Prop) -> Prop.    (* YA0n.v SRr *)
Variable alayout : Type.                                              (* YG0f.v *)
Variable astate : Type.                                               (* YG00.v *)
Variable AR : alayout -> astate -> world -> (word -> option byte) -> Model -> Prop.  (* YG0n.v AR *)
Variable aview : (word -> bool) -> (word -> option byte) -> Z -> option Z.          (* YG0n.v aview *)
Variable same_but_materialized : Model -> Model -> Prop.              (* YK04.v *)
Variable ly_stk_lo ly_stk_hi : alayout -> Z.                          (* YG0f.v *)
Variable ret_ok : word -> Prop.                                       (* YK0s.v *)
Variable as_gp as_tp : Z.                                             (* asyms B *)
Variable aowned : alayout -> astate -> Z -> Prop.                     (* YG0n.v aowned *)
(* The kit's definitions and facts at these names (LeafCgKit.v; argument order = the kit's Section order). *)
Let ecall_pre := @LeafCgKit.ecall_pre world w_H alayout astate AR ly_stk_lo ly_stk_hi ret_ok as_gp as_tp.
Let RNG_W := @LeafCgKit.RNG_W world w_H.
Let dleaf_post := @LeafCgKit.dleaf_post fx world w_H alayout astate AR aview same_but_materialized.
Let dleaf_post_fx := @LeafCgKit.dleaf_post_fx fx world w_H alayout astate AR aview same_but_materialized.
Let bridge_evtF_stmt := @LeafCgKit.bridge_evtF_stmt world w_H SRr same_but_materialized.
Let SRr_ret_stmt := @LeafCgKit.SRr_ret_stmt world SRr.
Let AR_frame_stmt := @LeafCgKit.AR_frame_stmt world w_H alayout astate AR aview aowned.
Let AR_stack_stmt := @LeafCgKit.AR_stack_stmt world alayout astate AR ly_stk_lo ly_stk_hi aowned.
Let AR_sbm_stmt := @LeafCgKit.AR_sbm_stmt world alayout astate AR same_but_materialized.
Let aview_ext_stmt := @LeafCgKit.aview_ext_stmt aview.
Let aview_some_stmt := @LeafCgKit.aview_some_stmt aview.
Let ret_ok_stmt := @LeafCgKit.ret_ok_stmt ret_ok.
Let leaf_cg_of_evtF_stmt := @LeafCgKit.leaf_cg_of_evtF_stmt fx world w_H SRr alayout astate AR aview
  same_but_materialized ly_stk_lo ly_stk_hi ret_ok as_gp as_tp aowned.
Let leaf_cg_of_evtF_fx_stmt := @LeafCgKit.leaf_cg_of_evtF_fx_stmt fx world w_H SRr alayout astate AR aview
  same_but_materialized ly_stk_lo ly_stk_hi ret_ok as_gp as_tp aowned.

Definition wire_reac_frame_is_reac_cg : Prop :=
  forall ly S (W : world) regs mem md (bs : list byte) (lo : Z),
    ecall_pre ly S W regs mem md ->
    let RNG := RNG_W W in let m := mem in let F := fp_regs in let fc := fp_csr in
    let ra := YK11.getr regs (Z_to_bv 5 1) in let sp := YK11.getr regs (Z_to_bv 5 2) in let gp := YK11.getr regs (Z_to_bv 5 3) in let tp := YK11.getr regs (Z_to_bv 5 4) in let t0 := YK11.getr regs (Z_to_bv 5 5) in let t1 := YK11.getr regs (Z_to_bv 5 6) in let t2 := YK11.getr regs (Z_to_bv 5 7) in let s0 := YK11.getr regs (Z_to_bv 5 8) in let s1 := YK11.getr regs (Z_to_bv 5 9) in let a0 := YK11.getr regs (Z_to_bv 5 10) in let a1 := YK11.getr regs (Z_to_bv 5 11) in let a2 := YK11.getr regs (Z_to_bv 5 12) in let a3 := YK11.getr regs (Z_to_bv 5 13) in let a4 := YK11.getr regs (Z_to_bv 5 14) in let a5 := YK11.getr regs (Z_to_bv 5 15) in let a6 := YK11.getr regs (Z_to_bv 5 16) in let a7 := YK11.getr regs (Z_to_bv 5 17) in let s2 := YK11.getr regs (Z_to_bv 5 18) in let s3 := YK11.getr regs (Z_to_bv 5 19) in let s4 := YK11.getr regs (Z_to_bv 5 20) in let s5 := YK11.getr regs (Z_to_bv 5 21) in let s6 := YK11.getr regs (Z_to_bv 5 22) in let s7 := YK11.getr regs (Z_to_bv 5 23) in let s8 := YK11.getr regs (Z_to_bv 5 24) in let s9 := YK11.getr regs (Z_to_bv 5 25) in let s10 := YK11.getr regs (Z_to_bv 5 26) in let s11 := YK11.getr regs (Z_to_bv 5 27) in let t3 := YK11.getr regs (Z_to_bv 5 28) in let t4 := YK11.getr regs (Z_to_bv 5 29) in let t5 := YK11.getr regs (Z_to_bv 5 30) in let t6 := YK11.getr regs (Z_to_bv 5 31) in
    stk rsegs m lo (bv_unsigned sp) ->
    lo + REAC_FRAME_IS_REAC_FRAME <= bv_unsigned sp ->
    (bv_unsigned a0 <> 0 -> 14 <= bv_unsigned a1 ->
    (14 <= length bs)%nat /\ bytes_at rsegs m (bv_unsigned a0) bs /\
    off_stk sp REAC_FRAME_IS_REAC_FRAME (bv_unsigned a0) 14 /\
    app_mem (bv_unsigned sp - REAC_FRAME_IS_REAC_FRAME) /\ app_mem (bv_unsigned sp - 1) /\
    asan_cells m /\ off_stk sp REAC_FRAME_IS_REAC_FRAME GOT_CELL_K 8 /\
    off_stk sp REAC_FRAME_IS_REAC_FRAME CELL_K 8 /\
    addressable m (bv_unsigned a0 + 12) 2) ->
    ExecF.rng RNG (bv_unsigned sp - REAC_FRAME_IS_REAC_FRAME) REAC_FRAME_IS_REAC_FRAME ->
    (bv_unsigned a0 <> 0 -> 14 <= bv_unsigned a1 ->
    ExecF.rng RNG GOT_CELL_K 8 /\ ExecF.rng RNG CELL_K 8 /\
    ExecF.rng RNG (bv_unsigned a0 + 12) 2 /\
    ExecF.rng RNG ((bv_unsigned a0 + 12) / 8 + ASAN_K)
    ((bv_unsigned a0 + 12 + 2 - 1) / 8 - (bv_unsigned a0 + 12) / 8 + 1)) ->
    SRr W (cfg_at REAC_FRAME_IS_REAC regs mem md)
      (dleaf_post ly S W regs mem md (Some (is_reac_result (bv_unsigned a0) (bv_unsigned a1) bs)) [] (fun _ => True)).

Definition wire_reac_frame_is_reac_cg_of_F_stmt : Prop := reac_frame_is_reac_contract_F_nosh -> wire_reac_frame_is_reac_cg.

(* The proof applies the kit's generic translation (HGLUE) to the footprint walk. The run is the footprint contract's
   (reac_frame_is_reac_F_nosh.v: reac_frame_is_reac_F_c.v without its shadow_rw premise) at RNG := RNG_W W and the
   call state's registers; the post shape is the footprint contract's (MS (mkR ...) with munch / wmono / stk): the
   window is its munch range, the window's bytes come from its stk (as mrd), and the callee-saved registers are
   the mkR fields read back. *)
Hypothesis HGLUE : leaf_cg_of_evtF_stmt.

Lemma wire_reac_frame_is_reac_cg_of_F : wire_reac_frame_is_reac_cg_of_F_stmt.
Proof.
  intros HF. unfold wire_reac_frame_is_reac_cg.
  intros ly S W regs mem md bs lo HPRE. cbv zeta.
  intros ST HLO HB RFR RX.
  destruct (HF (RNG_W W)
    (YK11.getr regs (Z_to_bv 5 1)) (YK11.getr regs (Z_to_bv 5 2)) (YK11.getr regs (Z_to_bv 5 3)) (YK11.getr regs (Z_to_bv 5 4))
    (YK11.getr regs (Z_to_bv 5 5)) (YK11.getr regs (Z_to_bv 5 6)) (YK11.getr regs (Z_to_bv 5 7)) (YK11.getr regs (Z_to_bv 5 8))
    (YK11.getr regs (Z_to_bv 5 9)) (YK11.getr regs (Z_to_bv 5 10)) (YK11.getr regs (Z_to_bv 5 11)) (YK11.getr regs (Z_to_bv 5 12))
    (YK11.getr regs (Z_to_bv 5 13)) (YK11.getr regs (Z_to_bv 5 14)) (YK11.getr regs (Z_to_bv 5 15)) (YK11.getr regs (Z_to_bv 5 16))
    (YK11.getr regs (Z_to_bv 5 17)) (YK11.getr regs (Z_to_bv 5 18)) (YK11.getr regs (Z_to_bv 5 19)) (YK11.getr regs (Z_to_bv 5 20))
    (YK11.getr regs (Z_to_bv 5 21)) (YK11.getr regs (Z_to_bv 5 22)) (YK11.getr regs (Z_to_bv 5 23)) (YK11.getr regs (Z_to_bv 5 24))
    (YK11.getr regs (Z_to_bv 5 25)) (YK11.getr regs (Z_to_bv 5 26)) (YK11.getr regs (Z_to_bv 5 27)) (YK11.getr regs (Z_to_bv 5 28))
    (YK11.getr regs (Z_to_bv 5 29)) (YK11.getr regs (Z_to_bv 5 30)) (YK11.getr regs (Z_to_bv 5 31))
    fp_regs fp_csr mem bs lo ST HLO HB RFR RX) as (msf & STEPS & POST).
  eapply (HGLUE ly S W regs mem md REAC_FRAME_IS_REAC REAC_FRAME_IS_REAC_FRAME (fun ms' : machine_state => ms' = msf)).
  - exact HPRE.
  - unfold REAC_FRAME_IS_REAC_FRAME, LeafCgKit.ESTACK. lia.
  - intros x Hx. unfold LeafCgKit.in_wr in Hx. inversion Hx.
  - unfold ExecF.evtF. exists msf. split; [exact STEPS | reflexivity].
  - intros ms' Hms'. subst ms'.
    destruct POST as (a1' & a2' & a3' & a4' & m' & EQ & MU & WM & STK).
    subst msf.
    eexists _, m'.
    split; [reflexivity|].
    split; [exact MU|].
    split.
    + intros x [Hx|Hx]; [|unfold LeafCgKit.in_wr in Hx; inversion Hx].
      unfold LeafCgKit.spZ in Hx.
      destruct STK as (STKLO & STKHI & STKB).
      destruct (STKB x ltac:(lia)) as (HWX & bx & HBX).
      exists bx. exact HBX.
    + split.
      * intros r Hr. unfold LeafCgKit.acallee_saved in Hr.
        assert (Hr' : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/
                      r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
        repeat (destruct Hr' as [->|Hr']; [reflexivity|]). subst r. reflexivity.
      * split; [intros r Hr; injection Hr as <-; reflexivity|].
        exact I.
Qed.

End LeafCg.

(* The statement the walk will prove: the footprint contract reac_frame_is_reac_contract_F_nosh
   (lib/B/Prog/reac_frame_is_reac_F_nosh.v; decode's walk of it is reac_frame_is_reac_holds_F_nosh). A caller's
   premise is the leaf statement at this unit's model, `forall fx, @WireCg.wire_leaf_at rc B
   (@wire_reac_frame_is_reac_cg) fx`, which follows from it by wire_reac_frame_is_reac_cg_of_F and the kit's generic
   translation. It has no callee premise: under its premises the function makes no call (above). *)
Definition wire_reac_frame_is_reac_holds_stmt : Prop := reac_frame_is_reac_contract_F_nosh.
