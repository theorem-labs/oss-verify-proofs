(* Modified by Theorem Labs, 2026-10: copied from the released projects/libreac/fuzz_decode/proofs/lib/A/Prog/reac_frame_is_reac_cg.v (commit 48907dc7e8ca) for reac-repacer/fuzz_wire's image A (fuzz_wire.asan). Changed: the module paths (libreac.fuzz_decode -> reac_repacer.fuzz_wire); the prefix dec_ -> wire_ of the two Definitions and the Lemma; the header comment, rewritten for this image with the offsets of every number (the entry, the frame and the model are this unit's lib/A/Prog/reac_frame_is_reac_c.v, the footprint contracts its reac_frame_is_reac_F_c.v and reac_frame_is_reac_F_nosh.v, copied from decode's); the comments of the Section Variables, which name the file and the name instead of a line number; the comment before HGLUE, which names the footprint walk as decode's file. Added: wire_reac_frame_is_reac_holds_stmt, the statement the footprint walk proves (reac_frame_is_reac_contract_F_nosh, the type of decode's reac_frame_is_reac_holds_F_nosh). *)
(* reac_frame_is_reac_cg: wire image A's reac_frame_is_reac, its footprint contract (reac_frame_is_reac_F_nosh.v:
   reac_frame_is_reac_F_c.v without its shadow_rw premise) translated to cgif_file's leaf form (SRr world walk), as a
   STATEMENT (a Definition of a Prop), with the translation proved. The premises of the target are
   reac_frame_is_reac_F_nosh.v's premises VERBATIM, read at the call state (registers from regs, memory mem, footprint
   RNG_W W).
   The cgif side (names, verbatim copies, the facts a proof may assume, the generic translation lemma) is the shared
   kit lib/A/Prog/LeafCgKit.v; this file only re-declares the kit's Section Variables and names its definitions.
   wire_reac_frame_is_reac_cg_of_F is proved in this file's Section over the kit's leaf_cg_of_evtF_stmt (HGLUE, proved
   in LeafCgGlue.v).

   The C (libreac src/reac.c reac_frame_is_reac (frame, len)): 0 when frame is NULL or len < 14, else 1 exactly when
   frame[12] = 0x88 and frame[13] = 0x19 (is_reac_result, lib/A/Prog/reac_frame_is_reac_c.v).
   The code (fuzz_wire.asan, entry 0x817bc; offsets from the entry; the same 38 instruction words as decode image A's
   reac_frame_is_reac except the immediates of the pc-relative data address at +0x18 / +0x1c (its high and low part)
   and of the two `jal` at +0x88, +0x94):
     +0x0   `addi sp, sp, -16`, +0x4 `sd ra, 8(sp)`; +0x70 `ld ra, 8(sp)`, +0x74 `addi sp, sp, 16`, +0x78 `ret`:
            the frame is 16 bytes, and the only store is ra's, at sp - 8;
     +0x8   `li a2, 0`; +0xc `beqz a0, +0x6c`; +0x10 `li a3, 14`, +0x14 `bltu a1, a3, +0x6c`: frame = 0 or len < 14
            returns 0 (+0x6c `mv a0, a2`) with no access but the frame's ra store and load;
     +0x18  `auipc a1, 0x17`, +0x1c `ld a1, 20(a1)`: the 8 bytes at 0x987e8 (GOT_CELL_K of this image); their value
            0xa0778 is the address of the cell (CELL_K) whose 8 bytes +0x20 `ld a2, 0(a1)` reads: the shadow offset
            (ASAN_K) of the instrumented checks;
     +0x24  `addi a1, a0, 12`; +0x28..+0x30 load the shadow byte of a0 + 12 at ((a0 + 12) >> 3) + K; +0x34 `bnez`
            goes to +0x7c, which continues at +0x38 when ((a0 + 12) mod 8) < the shadow byte (+0x7c `andi`,
            +0x80 `blt`) and else takes the error path (+0x88 `jal`, a report of a 1-byte load);
     +0x38  `lbu a1, 0(a1)` (frame[12]); +0x3c `li a3, 136` (0x88); +0x40 `bne` to +0x68 (`li a2, 0`);
     +0x44  `addi a0, a0, 13`; +0x48..+0x50 load the shadow byte of a0 + 13; +0x54 `bnez` goes to +0x8c, which
            continues at +0x58 (+0x8c `andi`, +0x90 `blt`) and else takes the error path (+0x94 `jal`);
     +0x58  `lbu a0, 0(a0)` (frame[13]); +0x5c `addi a0, a0, -25` (0x19); +0x60 `seqz a2, a0`; +0x64 `j +0x6c`.
   It calls nothing except on the error path, so the statement has no call return address; the ra it loads at +0x70
   is the one it stored at +0x4. The premise `addressable m (a0 + 12) 2` (both bytes usable in the shadow map)
   refutes both error-path branches. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A Require Import Img0 AsanCells.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog Require Import AsanKA reac_frame_is_reac_c.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Lib Require Import ExecF.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YK11.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Lib Require Import ExecF MState Frame.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog Require Import reac_frame_is_reac_F_c reac_frame_is_reac_F_nosh LeafCgKit.
From Stdlib Require Import Lia.
Open Scope Z_scope.

Section LeafCg.
Context {fx : YK11.FPState}.
Variable world : Type.                                                (* YA0n.v Record world *)
Variable w_H : world -> word -> bool.                                 (* YA0n.v field w_H *)
Variable SRr : world -> config -> (world -> config -> Prop) -> Prop.    (* YA0n.v SRr *)
Variable alayout : Type.                                              (* YG0f.v Record alayout *)
Variable astate : Type.                                               (* YG00.v Record astate *)
Variable AR : alayout -> astate -> world -> (word -> option byte) -> Model -> Prop.  (* YG0n.v AR *)
Variable aview : (word -> bool) -> (word -> option byte) -> Z -> option Z.          (* YG0n.v aview *)
Variable same_but_materialized : Model -> Model -> Prop.              (* YK04.v same_but_materialized *)
Variable ly_stk_lo ly_stk_hi : alayout -> Z.                          (* YG0f.v alayout fields ly_stk_lo, ly_stk_hi *)
Variable ret_ok : word -> Prop.                                       (* YK0s.v ret_ok *)
Variable as_gp as_tp : Z.                                             (* YG0f.v asyms fields as_gp, as_tp *)
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
    (bv_unsigned a0 <> 0 -> 14 <= bv_unsigned a1 -> ExecF.rng RNG GOT_CELL_K 8) ->
    (bv_unsigned a0 <> 0 -> 14 <= bv_unsigned a1 -> ExecF.rng RNG CELL_K 8) ->
    (bv_unsigned a0 <> 0 -> 14 <= bv_unsigned a1 -> ExecF.rng RNG (bv_unsigned a0 + 12) 2) ->
    (bv_unsigned a0 <> 0 -> 14 <= bv_unsigned a1 ->
    ExecF.rng RNG (shadow_addr (bv_unsigned a0 + 12))
    (shadow_addr (bv_unsigned a0 + 12 + 2 - 1) - shadow_addr (bv_unsigned a0 + 12) + 1)) ->
    SRr W (cfg_at REAC_FRAME_IS_REAC regs mem md)
      (dleaf_post ly S W regs mem md (Some (is_reac_result (bv_unsigned a0) (bv_unsigned a1) bs)) [] (fun _ => True)).

Definition wire_reac_frame_is_reac_cg_of_F_stmt : Prop := reac_frame_is_reac_contract_F_nosh -> wire_reac_frame_is_reac_cg.

(* The proof applies the kit's generic translation (HGLUE) to the footprint walk. The run is the footprint contract's
   (reac_frame_is_reac_F_nosh.v: reac_frame_is_reac_F_c.v without its shadow_rw premise) at RNG := RNG_W W and the call state's registers; the post shape is the footprint proof's post
   (decode's reac_frame_is_reac_F.v, the footprint walk: MS (mkR ...) with munch / wmono / stk): the window is its munch range, the window's bytes come
   from its stk (as mrd), and the callee-saved registers are the mkR fields read back. *)
Hypothesis HGLUE : leaf_cg_of_evtF_stmt.

Lemma wire_reac_frame_is_reac_cg_of_F : wire_reac_frame_is_reac_cg_of_F_stmt.
Proof.
  intros HF. unfold wire_reac_frame_is_reac_cg.
  intros ly S W regs mem md bs lo HPRE. cbv zeta.
  intros ST HLO HB RFR RGOT RCELL RBUF RSH.
  destruct (HF (RNG_W W)
    (YK11.getr regs (Z_to_bv 5 1)) (YK11.getr regs (Z_to_bv 5 2)) (YK11.getr regs (Z_to_bv 5 3)) (YK11.getr regs (Z_to_bv 5 4))
    (YK11.getr regs (Z_to_bv 5 5)) (YK11.getr regs (Z_to_bv 5 6)) (YK11.getr regs (Z_to_bv 5 7)) (YK11.getr regs (Z_to_bv 5 8))
    (YK11.getr regs (Z_to_bv 5 9)) (YK11.getr regs (Z_to_bv 5 10)) (YK11.getr regs (Z_to_bv 5 11)) (YK11.getr regs (Z_to_bv 5 12))
    (YK11.getr regs (Z_to_bv 5 13)) (YK11.getr regs (Z_to_bv 5 14)) (YK11.getr regs (Z_to_bv 5 15)) (YK11.getr regs (Z_to_bv 5 16))
    (YK11.getr regs (Z_to_bv 5 17)) (YK11.getr regs (Z_to_bv 5 18)) (YK11.getr regs (Z_to_bv 5 19)) (YK11.getr regs (Z_to_bv 5 20))
    (YK11.getr regs (Z_to_bv 5 21)) (YK11.getr regs (Z_to_bv 5 22)) (YK11.getr regs (Z_to_bv 5 23)) (YK11.getr regs (Z_to_bv 5 24))
    (YK11.getr regs (Z_to_bv 5 25)) (YK11.getr regs (Z_to_bv 5 26)) (YK11.getr regs (Z_to_bv 5 27)) (YK11.getr regs (Z_to_bv 5 28))
    (YK11.getr regs (Z_to_bv 5 29)) (YK11.getr regs (Z_to_bv 5 30)) (YK11.getr regs (Z_to_bv 5 31))
    fp_regs fp_csr mem bs lo ST HLO HB RFR RGOT RCELL RBUF RSH) as (msf & STEPS & POST).
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

(* The statement the walk will prove: the footprint contract without its shadow_rw premise
   (reac_frame_is_reac_F_nosh.v), the type of decode's walk theorem reac_frame_is_reac_holds_F_nosh. With HGLUE
   (LeafCgGlue.v), wire_reac_frame_is_reac_cg_of_F turns it into wire_reac_frame_is_reac_cg, as decode's close does
   for this leaf. *)
Definition wire_reac_frame_is_reac_holds_stmt : Prop := reac_frame_is_reac_contract_F_nosh.
