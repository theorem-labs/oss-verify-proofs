(* crt_m1_ok: the segment 0x130c0 .. 0x13190 of check_round_trip in fuzz_frame.plain
   (crt_defs.crt_m1_stmt): want is not 0; the header h at sp + 0x18 from the struct spec_frame
   at w; the inlined spec_system_at over the body (crt_m1_sys); memset of out with 0xa5;
   diginet_frame_build in mode 0, from the memset and diginet_frame_build contracts.
   Written by Theorem Labs. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac
  ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.Prog Require Import check_parse_fields_c memset_c
  diginet_frame_build_c crt_defs crt_m1_lib crt_m1_sys.
Import ListNotations.
Open Scope Z_scope.

Lemma crt_m1_ok : crt_m1_stmt.
Proof.
  unfold crt_m1_stmt.
  intros MSC FBC ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s4 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    w buf out want n b j sv Hcode Hlen Hn LAY RO BA STo STs Hj Hsv FR MI.
  unfold memset_contract, MEMSET in MSC.
  unfold diginet_frame_build_contract, DIGINET_FRAME_BUILD in FBC.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  destruct LAY as (Lb0 & Lb1 & Lo0 & Lo1 & Lw0 & Lw1 & Dow & Dob & Dwb & Lsw & Lw80).
  clear Dow Dwb.
  destruct (fr_code_ok b Hcode) as (L30 & _ & _ & _).
  destruct (fr_body_len_ok b Hcode) as (BL0 & PL0 & BLs).
  pose proof (length_fr_body b Hcode) as LFB.
  assert (HL : Z.of_nat (length (fr_body b)) = fr_body_len b) by (rewrite LFB; lia).
  assert (Hn2 : n = Z.max 60 (30 + Z.of_nat (length (fr_body b)))) by (rewrite Hn; reflexivity).
  clear Hn LFB.
  apply crt_cells_of in RO; [|exact Hcode]. unfold crt_cells in RO.
  destruct (crt_frame_parts m buf b Hcode BA) as (BD & BS & BB & LD & LS).
  destruct (stk_carve rsegs m out (out + n) (Z.to_nat n) STo ltac:(lia)) as [_ [junk OC]].
  replace (out + n - Z.of_nat (Z.to_nat n)) with out in OC by lia.
  clear STo BA.
  pose proof (munch_refl [(bv_unsigned sp - 240, bv_unsigned sp + 40); (out, out + n)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  (* 0x130c0: beqz a0 (want is not 0) *)
  step. crt_br false.
  (* 0x130c4 .. 0x13100: mv s1; the seven loads from w; h at sp + 0x18 *)
  do 16 step.
  pose proof (crt_frame_fold _ _ _ _ _ _ _ _ _ sv (crt_hb b) (eq_sym (crt_hb_cells b)) FR) as FR2.
  clear FR.
  (* 0x1315c onwards: memset of out, diginet_frame_build *)
  lazymatch goal with |- evt _ ?Q (MS _ _ _ _ _ ?mS _) =>
  assert (AFTER : forall (x0 x1 x2 x3 x4 x5 x6 : word) (v : Z), v = crt_sys b ->
    evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 v) (Z_to_bv 64 want) x0 x1 x2 x3 x4 x5 x6 a7
                         (Z_to_bv 64 w) (Z_to_bv 64 n) s4 (Z_to_bv 64 (Z.of_nat (length (fr_body b))))
                         (Z_to_bv 64 out) s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (Z_to_bv 64 0x1315c) fc None mS (seg_rom rsegs)))
  end.
  { intros x0 x1 x2 x3 x4 x5 x6 v ->.
    do 4 step.
    eapply evt_cut.
    { eapply MSC; [| exact MI]. rewrite !unsigned_lit by lia. exact OC. }
    intros ms1 (u0 & u1 & u2 & ua1 & ua2 & ua3 & ua4 & ua5 & ua6 & ua7 & u3 & u4 & u5 & u6 & mA & -> & MU1 & WM1 &
      MI1 & OC1).
    rewrite ret_pc_even by first [lia | reflexivity].
    rewrite !unsigned_lit in MU1 by lia. rewrite !unsigned_lit in OC1 by lia.
    match type of OC1 with context [repeat ?x _] =>
      replace x with (b8 0xa5) in OC1 by (apply bv_eq; vm_compute; reflexivity) end.
    assert (SUB1 : sub_fp [(out, out + n)] [(bv_unsigned sp - 240, bv_unsigned sp + 40); (out, out + n)])
      by (intros x Hx; cbn [outside] in *; tauto).
    pose proof (munch_trans _ m _ mA MU (munch_weaken _ _ _ mA SUB1 MU1)) as MUa.
    pose proof (wmono_trans rsegs m _ mA WM WM1) as WMa.
    pose proof (ro_cells_transport rsegs _ _ _ _ _ RO MU1) as RO2. specialize (RO2 ltac:(crt_dj)).
    pose proof (bytes_at_transport rsegs _ _ _ _ _ BD MU1) as BD2. specialize (BD2 ltac:(crt_dj)).
    pose proof (bytes_at_transport rsegs _ _ _ _ _ BS MU1) as BS2. specialize (BS2 ltac:(crt_dj)).
    pose proof (bytes_at_transport rsegs _ _ _ _ _ BB MU1) as BB2. specialize (BB2 ltac:(crt_dj)).
    pose proof (rw_cells_transport rsegs _ _ _ _ _ FR2 MU1 WM1) as FRa. specialize (FRa ltac:(crt_dj)).
    pose proof (stk_transport_disjoint rsegs _ _ _ _ _ STs MU1 WM1) as STa. specialize (STa ltac:(crt_dj)).
    clear RO BD BS BB FR2 STs MU WM MU1 WM1 OC MI SUB1.
    (* 0x1316c .. 0x1318c: the arguments of diginet_frame_build *)
    do 9 step.
    replace (Z_to_bv 64 n) with (Z_to_bv 64 (Z.of_nat (length (repeat (b8 0xa5) (Z.to_nat n)))))
      by (rewrite repeat_length, Z2Nat.id by lia; reflexivity).
    eapply evt_cut.
    { eapply FBC with (lo := bv_unsigned sp - 240) (send := fr_send b) (ack := fr_ack b) (retry := fr_retry b)
        (cmd := fr_cmd b) (ncmds := fr_ncmds b) (dmac := fr_dst b) (smac := fr_src b).
      all: first
        [ exact (be32_range b 18) | exact (be32_range b 22) | exact (be16_range b 26)
        | exact (at8_range b 28) | exact (at8_range b 29)
        | exact BD2 | exact BS2 | exact BB2 | exact STa | exact MI1
        | (rewrite repeat_length; exact OC1)
        | (replace (bv_unsigned sp + 24 + 4) with (bv_unsigned sp + 28) by lia; exact (crt_hb_at _ _ _ _ _ FRa))
        | (rewrite ?repeat_length, ?Z2Nat.id by lia; lia) ]. }
    intros ms2 (v0 & v1 & v2 & vb1 & vb2 & vb3 & vb4 & vb5 & vb6 & vb7 & v3 & v4 & v5 & v6 & mB & -> & MU2 & WM2 &
      MI2 & ST2 & OC2).
    rewrite ret_pc_even by first [lia | reflexivity].
    rewrite repeat_length in MU2. rewrite repeat_length in OC2. rewrite !repeat_length.
    rewrite Z2Nat.id in MU2 by lia. rewrite !Z2Nat.id by lia.
    apply evt_done. unfold crt_m1_post.
    do 23 eexists. split; [reflexivity|].
    split.
    { refine (munch_trans _ m _ mB MUa (munch_weaken _ _ _ mB _ MU2)).
      intros x Hx. cbn [outside] in *. destruct Hx as (H1 & H2 & _).
      split; [lia | split; [exact H2 | exact I]]. }
    split; [exact (wmono_trans rsegs m _ mB WMa WM2)|].
    split; [exact MI2|].
    split; [eapply (rw_cells_transport rsegs _ _ _ _ _ FRa MU2 WM2); crt_dj|].
    split; [exact OC2 | exact ST2]. }
  (* 0x13104: bltu s5, a0 (body length under 4: s0 = 0 at 0x13158) *)
  step.
  destruct (Z.ltb_spec (Z.of_nat (length (fr_body b))) 4) as [LT|GE].
  - crt_br true. step. eapply AFTER. rewrite crt_sys_short by lia. reflexivity.
  - crt_br false. do 7 step.
    eapply crt_sys_loop with (B := buf + 30) (bb := fr_body b) (k := (length (fr_body b) - 4)%nat) (i := 0%nat).
    all: lazymatch goal with
         | |- bytes_at _ _ _ _ => exact BB
         | |- forall _ : word, _ => intros x0 x1 x2 x3 x4 x5 x6 v Hv; apply AFTER; exact Hv
         | |- forall _ : nat, _ => intros jj Hjj; lia
         | |- _ => first [reflexivity | lia]
         end.
Qed.
