(* check_braid_cg: decode image A's check_braid, its footprint contract (check_braid_F_c.v) translated to cgif_file's leaf form
   (SRr world walk), as a STATEMENT (a Definition of a Prop; no proof here). Port of fuzz_decode to the released
   cgif_file_fuzzer structure (the port recipe, sec. 3). The premises of the
   target are check_braid_F_c.v's premises VERBATIM, read at the call state (registers from regs, memory mem, footprint RNG_W W).
   The cgif side (names, verbatim copies, the facts a proof may assume, the generic translation lemma) is the shared
   kit lib/A/Prog/LeafCgKit.v; this file only re-declares the kit's Section Variables and names its definitions.
   A proof of `dec_check_braid_cg_of_F_stmt` goes in this file's Section, taking the kit's `_stmt` facts as Section
   Hypotheses, and applies LeafCgKit's leaf_cg_of_evtF_stmt (proof: LeafCgGlue.v). *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require Import PropExec MState Mem Exec Frame ExecF.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A Require Import Img0 AsanCells.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require Import AsanKA check_braid_c.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YK11.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require Import ExecF MState Frame.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require Import check_braid_F_c LeafCgKit.
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

Definition dec_check_braid_cg : Prop :=
  forall ly S (W : world) regs mem md (audio pcm nch ns lo : Z),
    ecall_pre ly S W regs mem md ->
    YK11.getr regs (Z_to_bv 5 10) = Z_to_bv 64 audio -> YK11.getr regs (Z_to_bv 5 11) = Z_to_bv 64 pcm ->
    YK11.getr regs (Z_to_bv 5 12) = Z_to_bv 64 nch -> YK11.getr regs (Z_to_bv 5 13) = Z_to_bv 64 ns ->
    let RNG := RNG_W W in let m := mem in let F := fp_regs in let fc := fp_csr in
    let ra := YK11.getr regs (Z_to_bv 5 1) in let sp := YK11.getr regs (Z_to_bv 5 2) in let gp := YK11.getr regs (Z_to_bv 5 3) in let tp := YK11.getr regs (Z_to_bv 5 4) in let t0 := YK11.getr regs (Z_to_bv 5 5) in let t1 := YK11.getr regs (Z_to_bv 5 6) in let t2 := YK11.getr regs (Z_to_bv 5 7) in let s0 := YK11.getr regs (Z_to_bv 5 8) in let s1 := YK11.getr regs (Z_to_bv 5 9) in let a0 := YK11.getr regs (Z_to_bv 5 10) in let a1 := YK11.getr regs (Z_to_bv 5 11) in let a2 := YK11.getr regs (Z_to_bv 5 12) in let a3 := YK11.getr regs (Z_to_bv 5 13) in let a4 := YK11.getr regs (Z_to_bv 5 14) in let a5 := YK11.getr regs (Z_to_bv 5 15) in let a6 := YK11.getr regs (Z_to_bv 5 16) in let a7 := YK11.getr regs (Z_to_bv 5 17) in let s2 := YK11.getr regs (Z_to_bv 5 18) in let s3 := YK11.getr regs (Z_to_bv 5 19) in let s4 := YK11.getr regs (Z_to_bv 5 20) in let s5 := YK11.getr regs (Z_to_bv 5 21) in let s6 := YK11.getr regs (Z_to_bv 5 22) in let s7 := YK11.getr regs (Z_to_bv 5 23) in let s8 := YK11.getr regs (Z_to_bv 5 24) in let s9 := YK11.getr regs (Z_to_bv 5 25) in let s10 := YK11.getr regs (Z_to_bv 5 26) in let s11 := YK11.getr regs (Z_to_bv 5 27) in let t3 := YK11.getr regs (Z_to_bv 5 28) in let t4 := YK11.getr regs (Z_to_bv 5 29) in let t5 := YK11.getr regs (Z_to_bv 5 30) in let t6 := YK11.getr regs (Z_to_bv 5 31) in
    1 <= nch <= 127 ->
    1 <= ns <= 127 ->
    0 <= audio < 2^63 ->
    0 <= pcm < 2^63 ->
    braid_map m audio pcm nch ns ->
    stk rsegs m lo (bv_unsigned sp) ->
    lo + CHECK_BRAID_FRAME <= bv_unsigned sp ->
    audio + 3 * nch * ns + 3 * (nch mod 2) <= bv_unsigned sp - CHECK_BRAID_FRAME \/ bv_unsigned sp <= audio ->
    pcm + 3 * nch * ns <= bv_unsigned sp - CHECK_BRAID_FRAME \/ bv_unsigned sp <= pcm ->
    asan_cells m ->
    app_mem (bv_unsigned sp - CHECK_BRAID_FRAME) -> app_mem (bv_unsigned sp - 1) ->
    off_stk sp CHECK_BRAID_FRAME GOT_CELL_K (MIDEND + 8 - GOT_CELL_K) ->
    addressable m audio (3 * nch * ns + 3 * (nch mod 2)) ->
    addressable m pcm (3 * nch * ns) ->
    ExecF.rng RNG (bv_unsigned sp - CHECK_BRAID_FRAME) CHECK_BRAID_FRAME ->
    ExecF.rng RNG GOT_CELL_K 8 ->
    ExecF.rng RNG CELL_K 8 ->
    ExecF.rng RNG pcm (3 * nch * ns) ->
    ExecF.rng RNG audio (3 * nch * ns + 3 * (nch mod 2)) ->
    ExecF.rng RNG (shad pcm) (shad (pcm + 3 * nch * ns - 1) - shad pcm + 1) ->
    ExecF.rng RNG (shad audio) (shad (audio + (3 * nch * ns + 3 * (nch mod 2)) - 1) - shad audio + 1) ->
    SRr W (cfg_at CHECK_BRAID regs mem md)
      (dleaf_post ly S W regs mem md (None) [] (fun _ => True)).

Definition dec_check_braid_cg_of_F_stmt : Prop := check_braid_contract_F -> dec_check_braid_cg.

Hypothesis HGLUE : leaf_cg_of_evtF_stmt.

(* Proof outline of the brief (leaf-proofs-brief.md, steps 1-3): the run is check_braid_contract_F at RNG := RNG_W W,
   read at the call state; LeafCgKit's leaf_cg_of_evtF_stmt turns it into the cgif leaf form. The post destruct
   follows check_braid_F.v's check_braid_holds_F post: the 15 caller-saved results and m', then munch / wmono / stk. *)
Lemma dec_check_braid_cg_of_F : dec_check_braid_cg_of_F_stmt.
Proof.
  (* no unfold: it would zeta-reduce the statement's lets; intros head-reduces dec_check_braid_cg and keeps them as
     local definitions named as in check_braid_contract_F *)
  intros HF ly S W regs mem md audio pcm nch ns lo HPRE H10 H11 H12 H13
    RNG m F fc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    HN HS HA HP BR STK HLO DA DP CELLS APW1 APW2 DC AAD APD RFR RGC RCK RPC RAU RSPC RSAU.
  (* the run: check_braid_contract_F, its premises in order, at the call state's registers *)
  pose proof (HF RNG ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    audio pcm nch ns lo HN HS HA HP BR STK HLO DA DP CELLS APW1 APW2 DC AAD APD RFR RGC RCK RPC RAU RSPC RSAU)
    as RUN.
  rewrite <- H10, <- H11, <- H12, <- H13 in RUN.
  refine (HGLUE ly S W regs mem md CHECK_BRAID CHECK_BRAID_FRAME _ [] None (fun _ => True) HPRE _ _ RUN _).
  - (* the window bound *)
    unfold CHECK_BRAID_FRAME, ESTACK. lia.
  - (* WR is empty *)
    intros x Hx. unfold in_wr in Hx. inversion Hx.
  - (* the post *)
    intros ms' (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m'
                & -> & MU & _ & STK').
    eexists _, m'. split; [reflexivity|].
    split; [exact MU|].
    split.
    + intros x [Hx | Hx]; [| unfold in_wr in Hx; inversion Hx].
      change (spZ regs) with (bv_unsigned sp) in Hx.
      destruct STK' as (_ & _ & STKx).
      destruct (STKx x ltac:(lia)) as (_ & b & Hb).
      exists b. exact Hb.
    + split.
      * intros r Hr. unfold acallee_saved in Hr.
        destruct Hr as [-> | [-> | [-> | [-> | [-> | Hr]]]]]; [reflexivity .. |].
        assert (E : r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27)
          by lia.
        destruct E as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]; reflexivity.
      * split; [intros r Hr; discriminate Hr | exact I].
Qed.

End LeafCg.
