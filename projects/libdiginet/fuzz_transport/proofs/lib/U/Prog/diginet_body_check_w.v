(* proves the wide UBSan contract of diginet_body_check (fuzz_transport.ubsan, 0x186cc) and that it gives the narrow one. *)
(* Modified by Theorem Labs, 2026-10: relocated from libdiginet/fuzz_frame proofs/libdiginet/fuzz_frame/lib/U/Prog/diginet_body_check_w.v at bb3053036017d1d92db6eca9e973ce610be16c08 to fuzz_transport's images *)
(* Walk of diginet_body_check (src/diginet_codec.c:47-64 at 835f336c) in fuzz_transport.ubsan for
   U/Prog/diginet_body_check_w_c.v. With bytes, the premise gives body <> 0 and the narrow walk
   U/Prog/diginet_body_check.v applies, with the narrow contract of diginet_msg_next from its
   wide one. With no bytes the walk is the prologue of ubc_all, the call of
   diginet_cursor_init, one call of diginet_msg_next (its wide contract: the cursor holds the
   body, which can be 0), which answers 0, then the short exit of the prefix scan (len < 4) and
   the epilogue; no trap branch is on this path. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog Require Import diginet_cursor_init_c diginet_msg_next_c
  diginet_msg_next_w_c diginet_msg_next_w diginet_body_check_c diginet_body_check_w_c diginet_body_check.
Import ListNotations.
Open Scope Z_scope.

Theorem diginet_body_check_contract_of_w : diginet_body_check_contract_w -> diginet_body_check_contract.
Proof.
  unfold diginet_body_check_contract_w, diginet_body_check_contract.
  intros W ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m body lo bb
    HB0 BB SP8 ST LO0 LO DB MI.
  apply W; try assumption. left; exact HB0.
Qed.

(* A branch whose condition is a closed term. *)
Ltac bcw_br v := lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      replace c with v; [cbv iota | symmetry; vm_compute; reflexivity]
  end.

Lemma bcw_bytes_nil : forall m a, 0 <= a <= 2^64 -> bytes_at rsegs m a [].
Proof. intros m a H. split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. lia. Qed.

(* diginet_cursor_init gets the body reduced mod 2^64 (the contract allows body = 2^64 with no
   bytes); with len 0 the cursor holds the same cells. *)
Lemma bcw_cur0 : forall b,
  cursor_cells (b mod 2^64) (if b mod 2^64 =? 0 then 0 else 0) 0 0 = cursor_cells b 0 0 0.
Proof. intros b. unfold cursor_cells. rewrite Z_to_bv_mod64. destruct (b mod 2^64 =? 0); reflexivity. Qed.

(* The stack from lo to sp: below the frame, the message, the cursor and the rest. *)
Lemma bcw_stk4 : forall m lo s a b c,
  lo <= s + -144 ->
  stk rsegs m lo (s + -144) ->
  stk rsegs m (s + -144) a -> a = s + -104 ->
  stk rsegs m (s + -104) b -> b = s + -79 ->
  stk rsegs m (s + -79) c -> c = s ->
  stk rsegs m lo s.
Proof.
  intros m lo s a b c L H1 H2 Ea H3 Eb H4 Ec. subst a b c.
  eapply stk_merge; [|exact H4|lia]. eapply stk_merge; [|exact H3|lia].
  eapply stk_merge; [exact H1|exact H2|lia].
Qed.

Theorem diginet_body_check_holds_w :
  diginet_cursor_init_contract -> diginet_msg_next_contract_w -> diginet_body_check_contract_w.
Proof.
  intros CI MN. unfold diginet_body_check_contract_w.
  intros ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m body lo bb
    HB0 BB SP8 ST LO0 LO DB MI.
  destruct bb as [|b0 bb].
  2: { (* bytes: body is not 0, the narrow walk *)
       pose proof (diginet_body_check_holds CI (diginet_msg_next_contract_of_w MN)) as N.
       unfold diginet_body_check_contract in N.
       apply N; try assumption. destruct HB0 as [H|H]; [exact H | cbn [length] in H; discriminate]. }
  (* no bytes *)
  unfold DIGINET_BODY_CHECK.
  change (Z.of_nat (length (@nil byte))) with 0 in *.
  assert (E0 : body_check [] = 0) by reflexivity. rewrite E0.
  assert (RS : msg_step [] 0 0 = mr_plain MkEnd 0 0 0 0) by reflexivity.
  pose proof (bytes_at_bound _ _ _ _ BB) as BBb.
  pose proof (u64_range sp) as Rsp.
  pose proof (munch_refl [(bv_unsigned sp - 144, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 144%nat ST.
  (* 0x186cc .. 0x18704: the frame, the saved registers, the arguments of diginet_cursor_init *)
  do 15 step.
  lazymatch goal with H : rw_cells rsegs _ _ (CB 72 _ :: _) |- _ =>
    apply ubc_frame3 in H; destruct H as (MSG & CUR & SV) end.
  replace (bv_unsigned sp + -144 + 40) with (bv_unsigned sp + -104) in CUR by lia.
  replace (bv_unsigned sp + -144 + 65) with (bv_unsigned sp + -79) in SV by lia.
  (* 0x18708: diginet_cursor_init (sp - 104, body, 0) *)
  step.
  rewrite <- (Z_to_bv_mod64 body).
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    eapply evt_cut;
      [ eapply CI with (c := bv_unsigned sp + -104) (body := body mod 2^64) (len := 0)
      | post_call rsegs mm ] end.
  { exact a2. }
  { lia. }
  { apply ubc_mod8; [exact SP8 | vm_compute; reflexivity]. }
  { apply Z.mod_pos_bound; lia. }
  { lia. }
  { exact CUR. }
  { assumption. }
  rewrite (Z_to_bv_mod64 body).
  lazymatch goal with H : rw_cells rsegs _ (bv_unsigned sp + -104) _ |- _ => rename H into CUR1 end.
  rewrite (bcw_cur0 body) in CUR1.
  (* 0x1870c .. 0x18720: the constants of the loop *)
  do 6 step.
  destruct (rw_cells_forget rsegs _ _ _ MSG) as (mj1 & MSG1).
  cbn [cells_size csize Nat.add] in MSG1.
  (* 0x18724 .. 0x1872c: diginet_msg_next (sp - 104, sp - 144) *)
  do 2 step. step.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    eapply evt_cut;
      [ eapply MN with (c := bv_unsigned sp + -104) (mp := bv_unsigned sp + -144) (body := body)
                       (bb := @nil byte) (mj := mj1) (pos := 0%nat) (st := 0)
      | post_call rsegs mm ] end.
  { lia. } { lia. }
  { apply ubc_mod8; [exact SP8 | vm_compute; reflexivity]. }
  { apply ubc_mod8; [exact SP8 | vm_compute; reflexivity]. }
  { right; reflexivity. }
  { cbn [length]; lia. }
  { left; reflexivity. }
  { exact CUR1. }
  { apply bcw_bytes_nil; lia. }
  { exact MSG1. }
  { right; lia. }
  { change (Z.of_nat (length (@nil byte))) with 0. lia. }
  { change (Z.of_nat (length (@nil byte))) with 0. lia. }
  { assumption. }
  lazymatch goal with H : rw_cells rsegs _ (bv_unsigned sp + -144) (msg_cells _ _ _) |- _ =>
    rename H into MSG2 end.
  lazymatch goal with H : rw_cells rsegs _ (bv_unsigned sp + -104) (cursor_cells _ _ _ _) |- _ =>
    rename H into CUR2 end.
  rewrite RS in MSG2, CUR2 |- *.
  cbn [mr_code mr_pos mr_st mr_plain mr_kind msg_cells is_end] in MSG2, CUR2 |- *.
  (* 0x18730 beq a0, s2 (a0 = 0); 0x18734 bnez a0; 0x18738 j 0x18770 *)
  step. bcw_br false.
  step. bcw_br false.
  step.
  (* 0x18770 .. 0x18774: len < 4, no prefix scan *)
  do 2 step. bcw_br true.
  (* 0x187e0: a0 = 0 *)
  step.
  (* 0x187e4 .. 0x1880c: the epilogue *)
  pose proof (stk_of_rw_cells rsegs _ _ _ MSG2) as SM.
  pose proof (stk_of_rw_cells rsegs _ _ _ CUR2) as SC.
  pose proof (stk_of_rw_cells rsegs _ _ _ SV) as SS.
  cbn [cells_size csize cursor_cells Nat.add] in SM, SC, SS.
  do 11 step.
  apply evt_done. do 15 eexists. split; [reflexivity|].
  split; [assumption|]. split; [assumption|]. split; [assumption|].
  eapply bcw_stk4; [lia | eassumption | exact SM | lia | exact SC | lia | exact SS | lia].
Qed.
