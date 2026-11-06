(* reac_frame_inspect_cg: decode image B's reac_frame_inspect, its footprint contract (reac_frame_inspect_F_nosh.v: reac_frame_inspect_F_c.v without its shadow_rw premise) translated to cgif_file's leaf form
   (SRr world walk), as a STATEMENT (a Definition of a Prop; no proof here). Port of fuzz_decode to the released
   cgif_file_fuzzer structure (the port recipe, sec. 3). The premises of the
   target are reac_frame_inspect_F_nosh.v's premises VERBATIM (= reac_frame_inspect_F_c.v's without `shadow_rw m`), read at the call state (registers from regs, memory mem, footprint RNG_W W).
   The cgif side (names, verbatim copies, the facts a proof may assume, the generic translation lemma) is the shared
   kit lib/B/Prog/LeafCgKit.v; this file only re-declares the kit's Section Variables and names its definitions.
   A proof of `dec_reac_frame_inspect_cg_of_F_stmt` goes in this file's Section, taking the kit's `_stmt` facts as Section
   Hypotheses, and applies LeafCgKit's leaf_cg_of_evtF_stmt (proof: LeafCgGlue.v). *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require Import Img0 AsanCells.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog Require Import AsanKA reac_frame_inspect_c.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require Import ExecF.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YK11.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require Import ExecF MState Frame.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog Require Import reac_frame_inspect_F_c reac_frame_inspect_F_nosh LeafCgKit.
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

Definition dec_reac_frame_inspect_cg : Prop :=
  forall ly S (W : world) regs mem md (bs : list byte) (lo : Z),
    ecall_pre ly S W regs mem md ->
    let RNG := RNG_W W in let m := mem in let F := fp_regs in let fc := fp_csr in
    let ra := YK11.getr regs (Z_to_bv 5 1) in let sp := YK11.getr regs (Z_to_bv 5 2) in let gp := YK11.getr regs (Z_to_bv 5 3) in let tp := YK11.getr regs (Z_to_bv 5 4) in let t0 := YK11.getr regs (Z_to_bv 5 5) in let t1 := YK11.getr regs (Z_to_bv 5 6) in let t2 := YK11.getr regs (Z_to_bv 5 7) in let s0 := YK11.getr regs (Z_to_bv 5 8) in let s1 := YK11.getr regs (Z_to_bv 5 9) in let a0 := YK11.getr regs (Z_to_bv 5 10) in let a1 := YK11.getr regs (Z_to_bv 5 11) in let a2 := YK11.getr regs (Z_to_bv 5 12) in let a3 := YK11.getr regs (Z_to_bv 5 13) in let a4 := YK11.getr regs (Z_to_bv 5 14) in let a5 := YK11.getr regs (Z_to_bv 5 15) in let a6 := YK11.getr regs (Z_to_bv 5 16) in let a7 := YK11.getr regs (Z_to_bv 5 17) in let s2 := YK11.getr regs (Z_to_bv 5 18) in let s3 := YK11.getr regs (Z_to_bv 5 19) in let s4 := YK11.getr regs (Z_to_bv 5 20) in let s5 := YK11.getr regs (Z_to_bv 5 21) in let s6 := YK11.getr regs (Z_to_bv 5 22) in let s7 := YK11.getr regs (Z_to_bv 5 23) in let s8 := YK11.getr regs (Z_to_bv 5 24) in let s9 := YK11.getr regs (Z_to_bv 5 25) in let s10 := YK11.getr regs (Z_to_bv 5 26) in let s11 := YK11.getr regs (Z_to_bv 5 27) in let t3 := YK11.getr regs (Z_to_bv 5 28) in let t4 := YK11.getr regs (Z_to_bv 5 29) in let t5 := YK11.getr regs (Z_to_bv 5 30) in let t6 := YK11.getr regs (Z_to_bv 5 31) in
    stk rsegs m lo (bv_unsigned sp) ->
    lo + REAC_FRAME_INSPECT_FRAME <= bv_unsigned sp ->
    (bv_unsigned a1 = 1492 ->
    length bs = 1492%nat /\ bytes_at rsegs m (bv_unsigned a0) bs /\ bv_unsigned a0 <> 0 /\
    off_stk sp REAC_FRAME_INSPECT_FRAME (bv_unsigned a0) 1492 /\
    app_mem (bv_unsigned sp - REAC_FRAME_INSPECT_FRAME) /\ app_mem (bv_unsigned sp - 1) /\
    asan_cells m /\ off_stk sp REAC_FRAME_INSPECT_FRAME GOT_CELL_K 8 /\
    off_stk sp REAC_FRAME_INSPECT_FRAME CELL_K 8 /\
    addressable m (bv_unsigned a0) 1492) ->
    ExecF.rng RNG (bv_unsigned sp - REAC_FRAME_INSPECT_FRAME) REAC_FRAME_INSPECT_FRAME ->
    (bv_unsigned a1 = 1492 ->
    ExecF.rng RNG GOT_CELL_K 8 /\ ExecF.rng RNG CELL_K 8 /\
    ExecF.rng RNG (bv_unsigned a0 + 12) 4 /\ ExecF.rng RNG (bv_unsigned a0 + 1490) 2 /\
    ExecF.rng RNG ((bv_unsigned a0 + 12) / 8 + ASAN_K)
    ((bv_unsigned a0 + 15) / 8 - (bv_unsigned a0 + 12) / 8 + 1) /\
    ExecF.rng RNG ((bv_unsigned a0 + 1490) / 8 + ASAN_K)
    ((bv_unsigned a0 + 1491) / 8 - (bv_unsigned a0 + 1490) / 8 + 1)) ->
    SRr W (cfg_at REAC_FRAME_INSPECT regs mem md)
      (dleaf_post ly S W regs mem md (Some (inspect_result (bv_unsigned a1) bs)) [] (fun _ => True)).

Definition dec_reac_frame_inspect_cg_of_F_stmt : Prop := reac_frame_inspect_contract_F_nosh -> dec_reac_frame_inspect_cg.

Hypothesis HGLUE : leaf_cg_of_evtF_stmt.
Lemma dec_reac_frame_inspect_cg_of_F : dec_reac_frame_inspect_cg_of_F_stmt.
Proof.
  intros HF ly S W regs mem md bs lo Hpre RNG m F fc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 Hstk Hlo Hbuf Hfr Hacc.
  (* The footprint run at the call state (premises in order); HGLUE's P is equality with its end state msf. *)
  destruct (HF RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
              F fc m bs lo Hstk Hlo Hbuf Hfr Hacc) as (msf & Hsteps & Hpost).
  cbv beta in Hpost.
  apply (HGLUE ly S W regs mem md REAC_FRAME_INSPECT REAC_FRAME_INSPECT_FRAME (fun ms' => ms' = msf) []
           (Some (inspect_result (bv_unsigned a1) bs)) (fun _ => True)).
  - exact Hpre.
  - unfold REAC_FRAME_INSPECT_FRAME, LeafCgKit.ESTACK. lia.
  - intros x Hx. unfold LeafCgKit.in_wr in Hx. apply Exists_nil in Hx. destruct Hx.
  - exists msf. split; [exact Hsteps | exact eq_refl].
  - intros ms' Hms'. subst ms'.
    destruct Hpost as (a1' & a2' & a3' & a4' & m' & Hmsf & Hmunch & Hwmono & Hstk').
    exists (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (inspect_result (bv_unsigned a1) bs)) a1' a2' a3' a4'
              a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6), m'.
    split; [exact Hmsf |].
    split; [exact Hmunch |].
    split.
    { intros x [Hx | Hx].
      - destruct Hstk' as (Hlo' & Hhi' & Hall').
        change (LeafCgKit.spZ regs) with (bv_unsigned sp) in Hx.
        destruct (Hall' x ltac:(lia)) as (Hwv & b & Hb).
        exists b. exact Hb.
      - unfold LeafCgKit.in_wr in Hx. apply Exists_nil in Hx. destruct Hx. }
    split.
    { intros r Hr. unfold LeafCgKit.acallee_saved in Hr.
      assert (Hr' : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/
                    r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
      destruct Hr' as [E | [E | [E | [E | [E | [E | [E | [E | [E | [E | [E | [E | [E | [E | E]]]]]]]]]]]]]];
        subst r; reflexivity. }
    split.
    { intros r Hr. injection Hr as Hr. subst r. reflexivity. }
    exact I.
Qed.

End LeafCg.
