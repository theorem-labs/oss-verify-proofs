(* reac_frame_counter_cg: decode image A's reac_frame_counter, its footprint contract (reac_frame_counter_F_nosh.v: reac_frame_counter_F_c.v without its shadow_rw premise) translated to cgif_file's leaf form
   (SRr world walk), as a STATEMENT (a Definition of a Prop; no proof here). Port of fuzz_decode to the released
   cgif_file_fuzzer structure (the port recipe, sec. 3). The premises of the
   target are reac_frame_counter_F_nosh.v's premises VERBATIM (= reac_frame_counter_F_c.v's without `shadow_rw m`), read at the call state (registers from regs, memory mem, footprint RNG_W W).
   The cgif side (names, verbatim copies, the facts a proof may assume, the generic translation lemma) is the shared
   kit lib/A/Prog/LeafCgKit.v; this file only re-declares the kit's Section Variables and names its definitions.
   A proof of `dec_reac_frame_counter_cg_of_F_stmt` goes in this file's Section, taking the kit's `_stmt` facts as Section
   Hypotheses, and applies LeafCgKit's leaf_cg_of_evtF_stmt (proof: LeafCgGlue.v). *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A Require Import Img0 AsanCells.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require Import AsanKA reac_frame_counter_c.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require Import ExecF.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YK11.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require Import ExecF MState Frame.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require Import reac_frame_counter_F_c reac_frame_counter_F_nosh LeafCgKit.
From Stdlib Require Import Lia.
Open Scope Z_scope.

Section LeafCg.
Context {fx : YK11.FPState}.
Variable world : Type.                                                (* YA0n.v:17 *)
Variable w_H : world -> word -> bool.                                 (* YA0n.v:18 *)
Variable SRr : world -> config -> (world -> config -> Prop) -> Prop.    (* YA0n.v:34 *)
Variable alayout : Type.                                              (* YG0f.v:42 *)
Variable astate : Type.                                               (* YG00.v:153 *)
Variable AR : alayout -> astate -> world -> (word -> option byte) -> Model -> Prop.  (* YG0n.v:489 *)
Variable aview : (word -> bool) -> (word -> option byte) -> Z -> option Z.          (* YG0n.v:17 *)
Variable same_but_materialized : Model -> Model -> Prop.              (* YK04.v:538 *)
Variable ly_stk_lo ly_stk_hi : alayout -> Z.                          (* YG0f.v *)
Variable ret_ok : word -> Prop.                                       (* YK0s.v:192 *)
Variable as_gp as_tp : Z.                                             (* asyms B *)
Variable aowned : alayout -> astate -> Z -> Prop.                     (* YG0n.v:235 *)
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

Definition dec_reac_frame_counter_cg : Prop :=
  forall ly S (W : world) regs mem md (bs : list byte) (lo : Z),
    ecall_pre ly S W regs mem md ->
    let RNG := RNG_W W in let m := mem in let F := fp_regs in let fc := fp_csr in
    let ra := YK11.getr regs (Z_to_bv 5 1) in let sp := YK11.getr regs (Z_to_bv 5 2) in let gp := YK11.getr regs (Z_to_bv 5 3) in let tp := YK11.getr regs (Z_to_bv 5 4) in let t0 := YK11.getr regs (Z_to_bv 5 5) in let t1 := YK11.getr regs (Z_to_bv 5 6) in let t2 := YK11.getr regs (Z_to_bv 5 7) in let s0 := YK11.getr regs (Z_to_bv 5 8) in let s1 := YK11.getr regs (Z_to_bv 5 9) in let a0 := YK11.getr regs (Z_to_bv 5 10) in let a1 := YK11.getr regs (Z_to_bv 5 11) in let a2 := YK11.getr regs (Z_to_bv 5 12) in let a3 := YK11.getr regs (Z_to_bv 5 13) in let a4 := YK11.getr regs (Z_to_bv 5 14) in let a5 := YK11.getr regs (Z_to_bv 5 15) in let a6 := YK11.getr regs (Z_to_bv 5 16) in let a7 := YK11.getr regs (Z_to_bv 5 17) in let s2 := YK11.getr regs (Z_to_bv 5 18) in let s3 := YK11.getr regs (Z_to_bv 5 19) in let s4 := YK11.getr regs (Z_to_bv 5 20) in let s5 := YK11.getr regs (Z_to_bv 5 21) in let s6 := YK11.getr regs (Z_to_bv 5 22) in let s7 := YK11.getr regs (Z_to_bv 5 23) in let s8 := YK11.getr regs (Z_to_bv 5 24) in let s9 := YK11.getr regs (Z_to_bv 5 25) in let s10 := YK11.getr regs (Z_to_bv 5 26) in let s11 := YK11.getr regs (Z_to_bv 5 27) in let t3 := YK11.getr regs (Z_to_bv 5 28) in let t4 := YK11.getr regs (Z_to_bv 5 29) in let t5 := YK11.getr regs (Z_to_bv 5 30) in let t6 := YK11.getr regs (Z_to_bv 5 31) in
    (16 <= length bs)%nat ->
    bytes_at rsegs m (bv_unsigned a0) bs ->
    stk rsegs m lo (bv_unsigned sp) ->
    lo + REAC_FRAME_COUNTER_FRAME <= bv_unsigned sp ->
    off_stk sp REAC_FRAME_COUNTER_FRAME (bv_unsigned a0) 16 ->
    app_mem (bv_unsigned sp - REAC_FRAME_COUNTER_FRAME) -> app_mem (bv_unsigned sp - 1) ->
    asan_cells m -> off_stk sp REAC_FRAME_COUNTER_FRAME GOT_CELL_K 8 ->
    off_stk sp REAC_FRAME_COUNTER_FRAME CELL_K 8 ->
    addressable m (bv_unsigned a0 + 14) 2 ->
    ExecF.rng RNG (bv_unsigned sp - REAC_FRAME_COUNTER_FRAME) REAC_FRAME_COUNTER_FRAME ->
    ExecF.rng RNG GOT_CELL_K 8 ->
    ExecF.rng RNG CELL_K 8 ->
    ExecF.rng RNG (bv_unsigned a0 + 14) 2 ->
    ExecF.rng RNG (shadow_addr (bv_unsigned a0 + 14))
    (shadow_addr (bv_unsigned a0 + 14 + 2 - 1) - shadow_addr (bv_unsigned a0 + 14) + 1) ->
    SRr W (cfg_at REAC_FRAME_COUNTER regs mem md)
      (dleaf_post ly S W regs mem md (Some (counter_result bs)) [] (fun _ => True)).

Definition dec_reac_frame_counter_cg_of_F_stmt : Prop := reac_frame_counter_contract_F_nosh -> dec_reac_frame_counter_cg.

(* The proof applies the kit's generic translation (HGLUE) to the footprint walk. The run is the footprint contract's
   (reac_frame_counter_F_nosh.v: reac_frame_counter_F_c.v without its shadow_rw premise) at RNG := RNG_W W and the call state's registers; the post shape is the footprint proof's post
   (reac_frame_counter_F.v: MS (mkR ...) with munch / wmono / stk): the window is its munch range, the window's bytes come
   from its stk (as mrd), and the callee-saved registers are the mkR fields read back. *)
Hypothesis HGLUE : leaf_cg_of_evtF_stmt.

Lemma dec_reac_frame_counter_cg_of_F : dec_reac_frame_counter_cg_of_F_stmt.
Proof.
  intros HF. unfold dec_reac_frame_counter_cg.
  intros ly S W regs mem md bs lo HPRE. cbv zeta.
  intros LEN BA ST HLO D0 APS1 APS2 CELLS DG DS ADR RFR RGOT RCELL RBUF RSH.
  destruct (HF (RNG_W W)
    (YK11.getr regs (Z_to_bv 5 1)) (YK11.getr regs (Z_to_bv 5 2)) (YK11.getr regs (Z_to_bv 5 3)) (YK11.getr regs (Z_to_bv 5 4))
    (YK11.getr regs (Z_to_bv 5 5)) (YK11.getr regs (Z_to_bv 5 6)) (YK11.getr regs (Z_to_bv 5 7)) (YK11.getr regs (Z_to_bv 5 8))
    (YK11.getr regs (Z_to_bv 5 9)) (YK11.getr regs (Z_to_bv 5 10)) (YK11.getr regs (Z_to_bv 5 11)) (YK11.getr regs (Z_to_bv 5 12))
    (YK11.getr regs (Z_to_bv 5 13)) (YK11.getr regs (Z_to_bv 5 14)) (YK11.getr regs (Z_to_bv 5 15)) (YK11.getr regs (Z_to_bv 5 16))
    (YK11.getr regs (Z_to_bv 5 17)) (YK11.getr regs (Z_to_bv 5 18)) (YK11.getr regs (Z_to_bv 5 19)) (YK11.getr regs (Z_to_bv 5 20))
    (YK11.getr regs (Z_to_bv 5 21)) (YK11.getr regs (Z_to_bv 5 22)) (YK11.getr regs (Z_to_bv 5 23)) (YK11.getr regs (Z_to_bv 5 24))
    (YK11.getr regs (Z_to_bv 5 25)) (YK11.getr regs (Z_to_bv 5 26)) (YK11.getr regs (Z_to_bv 5 27)) (YK11.getr regs (Z_to_bv 5 28))
    (YK11.getr regs (Z_to_bv 5 29)) (YK11.getr regs (Z_to_bv 5 30)) (YK11.getr regs (Z_to_bv 5 31))
    fp_regs fp_csr mem bs lo LEN BA ST HLO D0 APS1 APS2 CELLS DG DS ADR RFR RGOT RCELL RBUF RSH) as (msf & STEPS & POST).
  eapply (HGLUE ly S W regs mem md REAC_FRAME_COUNTER REAC_FRAME_COUNTER_FRAME (fun ms' : machine_state => ms' = msf)).
  - exact HPRE.
  - unfold REAC_FRAME_COUNTER_FRAME, LeafCgKit.ESTACK. lia.
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
