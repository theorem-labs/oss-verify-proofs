(* rp_ds_accept_cg: image B's rp_ds_accept, its footprint contract (rp_ds_accept_F_c.v) translated to cgif_file's leaf
   form (SRr world walk). The premises of the target are rp_ds_accept_F_c.v's premises VERBATIM, read at the call
   state (registers from regs, memory mem, footprint RNG_W W). The cgif side (names, verbatim copies, the facts a proof
   may assume, the generic translation lemma) is the shared kit lib/B/Prog/LeafCgKit.v; this file only re-declares the
   kit's Section Variables and names its definitions. wire_rp_ds_accept_cg_of_F is proved in this file's Section over
   the kit's leaf_cg_of_evtF_stmt (HGLUE, proved in LeafCgGlue.v). The caller is check_downstream, which takes this
   contract through lib/B/Prog/WireCg.v wire_leaf_at (no write list, so no aowned).
   wire_rp_ds_accept_holds_stmt is the statement its walk will prove: on image B rp_ds_accept TAIL-JUMPS to
   is_tagged_reac (`j 0x8103c` at 0x81014, ra and sp as at entry), so the footprint chain ends in is_tagged_reac's
   footprint contract (lib/B/Prog/is_tagged_reac_F_c.v), the form `<callee>_contract_F -> <fn>_contract_F` of
   proofs/libreac/fuzz_decode/lib/B/Prog/reac_decode_F.v reac_decode_holds_F. Its only other calls are the refuted
   __asan_report_load1 sinks. *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B Require Import Img0 AsanCells.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog Require Import AsanKA.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Lib Require Import ExecF.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YK11.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog Require Import rp_ds_accept_F_c LeafCgKit.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog Require is_tagged_reac_F_c.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Prog Require rp_ds_accept_c.
Import ListNotations.
Open Scope Z_scope.
Module PDA := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Prog.rp_ds_accept_c.
Module PIT := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog.is_tagged_reac_F_c.

(* The statement the walk will prove (close row H_PROG_RDS_F, discharged with is_tagged_reac's footprint row). *)
Definition wire_rp_ds_accept_holds_stmt : Prop := PIT.is_tagged_reac_contract_F -> rp_ds_accept_contract_F.

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
Let leaf_cg_of_evtF_stmt := @LeafCgKit.leaf_cg_of_evtF_stmt fx world w_H SRr alayout astate AR aview
  same_but_materialized ly_stk_lo ly_stk_hi ret_ok as_gp as_tp aowned.

(* The contract at RP_DS_ACCEPT: the footprint contract's premises at the call state; the post returns to ra with
   a0 = ds_accept_result of n (a1) and the frame bytes bs, and writes no byte outside the frame (empty write list). *)
Definition wire_rp_ds_accept_cg : Prop :=
  forall ly S (W : world) regs mem md (bs : list byte) (lo : Z),
    ecall_pre ly S W regs mem md ->
    let RNG := RNG_W W in let m := mem in let F := fp_regs in let fc := fp_csr in
    let ra := YK11.getr regs (Z_to_bv 5 1) in let sp := YK11.getr regs (Z_to_bv 5 2) in let gp := YK11.getr regs (Z_to_bv 5 3) in let tp := YK11.getr regs (Z_to_bv 5 4) in let t0 := YK11.getr regs (Z_to_bv 5 5) in let t1 := YK11.getr regs (Z_to_bv 5 6) in let t2 := YK11.getr regs (Z_to_bv 5 7) in let s0 := YK11.getr regs (Z_to_bv 5 8) in let s1 := YK11.getr regs (Z_to_bv 5 9) in let a0 := YK11.getr regs (Z_to_bv 5 10) in let a1 := YK11.getr regs (Z_to_bv 5 11) in let a2 := YK11.getr regs (Z_to_bv 5 12) in let a3 := YK11.getr regs (Z_to_bv 5 13) in let a4 := YK11.getr regs (Z_to_bv 5 14) in let a5 := YK11.getr regs (Z_to_bv 5 15) in let a6 := YK11.getr regs (Z_to_bv 5 16) in let a7 := YK11.getr regs (Z_to_bv 5 17) in let s2 := YK11.getr regs (Z_to_bv 5 18) in let s3 := YK11.getr regs (Z_to_bv 5 19) in let s4 := YK11.getr regs (Z_to_bv 5 20) in let s5 := YK11.getr regs (Z_to_bv 5 21) in let s6 := YK11.getr regs (Z_to_bv 5 22) in let s7 := YK11.getr regs (Z_to_bv 5 23) in let s8 := YK11.getr regs (Z_to_bv 5 24) in let s9 := YK11.getr regs (Z_to_bv 5 25) in let s10 := YK11.getr regs (Z_to_bv 5 26) in let s11 := YK11.getr regs (Z_to_bv 5 27) in let t3 := YK11.getr regs (Z_to_bv 5 28) in let t4 := YK11.getr regs (Z_to_bv 5 29) in let t5 := YK11.getr regs (Z_to_bv 5 30) in let t6 := YK11.getr regs (Z_to_bv 5 31) in
    stk rsegs m lo (bv_unsigned sp) ->
    lo + RP_DS_ACCEPT_FRAME <= bv_unsigned sp ->
    (18 <= bv_unsigned a1 ->
       (* Image B's UBSan premise: 0x80fa4 `beqz a0, 0x81018` traps (unimp at 0x81018) on f == NULL. *)
       bv_unsigned a0 <> 0 /\
       (18 <= length bs)%nat /\ bytes_at rsegs m (bv_unsigned a0) bs /\
       off_stk sp RP_DS_ACCEPT_FRAME (bv_unsigned a0) 18 /\
       app_mem (bv_unsigned sp - RP_DS_ACCEPT_FRAME) /\ app_mem (bv_unsigned sp - 1) /\
       asan_cells m /\
       off_stk sp RP_DS_ACCEPT_FRAME GOT_CELL_K (MIDEND + 8 - GOT_CELL_K) /\
       addressable m (bv_unsigned a0 + 12) 6) ->
    ExecF.rng RNG (bv_unsigned sp - RP_DS_ACCEPT_FRAME) RP_DS_ACCEPT_FRAME ->
    (18 <= bv_unsigned a1 ->
       ExecF.rng RNG GOT_CELL_K 8 /\ ExecF.rng RNG CELL_K 8 /\
       ExecF.rng RNG (bv_unsigned a0 + 12) 6 /\
       ExecF.rng RNG (shadow_addr (bv_unsigned a0 + 12))
         (shadow_addr (bv_unsigned a0 + 12 + 6 - 1) - shadow_addr (bv_unsigned a0 + 12) + 1)) ->
    SRr W (cfg_at RP_DS_ACCEPT regs mem md)
      (dleaf_post ly S W regs mem md (Some (PDA.ds_accept_result (bv_unsigned a1) bs)) [] (fun _ => True)).

Definition wire_rp_ds_accept_cg_of_F_stmt : Prop := rp_ds_accept_contract_F -> wire_rp_ds_accept_cg.

(* The proof applies the kit's generic translation (HGLUE) to the footprint walk. The run is the footprint
   contract's at RNG := RNG_W W and the call state's registers; the window is its munch range, the window's bytes
   come from its stk (as mrd), and the callee-saved registers are the mkR fields read back. *)
Hypothesis HGLUE : leaf_cg_of_evtF_stmt.

Local Abbreviation GR r k := (YK11.getr r (Z_to_bv 5 k)).

Lemma wire_rp_ds_accept_cg_of_F : wire_rp_ds_accept_cg_of_F_stmt.
Proof.
  intros HF. unfold wire_rp_ds_accept_cg.
  intros ly S W regs mem md bs lo HPRE. cbv zeta.
  intros ST HLO HB RFR RX.
  destruct (HF (RNG_W W) (GR regs 1) (GR regs 2) (GR regs 3) (GR regs 4) (GR regs 5) (GR regs 6) (GR regs 7)
    (GR regs 8) (GR regs 9) (GR regs 10) (GR regs 11) (GR regs 12) (GR regs 13) (GR regs 14) (GR regs 15)
    (GR regs 16) (GR regs 17) (GR regs 18) (GR regs 19) (GR regs 20) (GR regs 21) (GR regs 22) (GR regs 23)
    (GR regs 24) (GR regs 25) (GR regs 26) (GR regs 27) (GR regs 28) (GR regs 29) (GR regs 30) (GR regs 31)
    fp_regs fp_csr mem bs lo ST HLO HB RFR RX) as (msf & STEPS & POST).
  eapply (HGLUE ly S W regs mem md RP_DS_ACCEPT RP_DS_ACCEPT_FRAME (fun ms' : machine_state => ms' = msf)).
  - exact HPRE.
  - unfold RP_DS_ACCEPT_FRAME, LeafCgKit.ESTACK. lia.
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
