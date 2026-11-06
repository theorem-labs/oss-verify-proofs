(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Walk of diginet_decoder_next in fuzz_decode.plain (0x13e80, 257 instructions, 160-byte frame)
   against lib/Prog/diginet_decoder_next_c.v. The prologue, the first diginet_msg_next call (0x13eb0) and,
   when it does not answer 1, the return of its code are walked here; on 1 the memset of the event's head
   (0x13ecc), the memcpy of the message to ev->msg (0x13edc) and the store of kind 13, then the three paths
   by the status: a note (diginet_decoder_next_note.v), a sysex (diginet_decoder_next_sysex.v and the case
   files it uses) and the other channel messages (diginet_decoder_next_ctl.v, diginet_decoder_next_fader.v).
   The model's diginet_msg_next is the callee contract's msg_step by diginet_decoder_next_bridge.v.
   Written by Theorem Labs. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Prog Require Import DgnLayout diginet_cursor_init_c
  diginet_msg_next_c memset_c memcpy_c diginet_meter_segments_c diginet_decoder_next_c
  diginet_decoder_next_bridge diginet_decoder_next_lib diginet_decoder_next_note diginet_decoder_next_sysex
  diginet_decoder_next_ctl.
Import ListNotations.
Open Scope Z_scope.

Section Walk.
Hypothesis MN : diginet_msg_next_contract.
Hypothesis MSET : memset_contract.
Hypothesis MCPY : memcpy_contract.
Hypothesis SEG : diginet_meter_segments_contract.

Theorem diginet_decoder_next_holds : diginet_decoder_next_contract.
Proof.
  unfold diginet_decoder_next_contract, DIGINET_DECODER_NEXT.
  intros ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m.
  intros d ev body lo bb ej cpad pos st p.
  intros HD0 HE0 HPOS HST HDC HBB HEV ST HLO DJ1 DJ2 DJ3 DJ4 DJ5 DJ6 MI.
  remember (diginet_decoder_next (map bz bb) (decoder_at (Z.of_nat (length bb)) pos st p) dgn_event_zero)
    as res eqn:Hres.
  rewrite dn_dec_cells_at in HDC.
  apply rw_cells_app in HDC as [HD HD2]. cbn [cells_size csize Nat.add cursor_cells] in HD2.
  replace (d + Z.of_nat 25) with (d + 25) in HD2 by lia.
  unfold cursor_cells in HD.
  pose proof (rw_cells_bound rsegs m d _ HD) as BD. cbn [cells_size csize Nat.add] in BD.
  pose proof (rw_cells_bound rsegs m (d + 25) _ HD2) as BD2. cbn [cells_size csize Nat.add] in BD2.
  pose proof (rw_cells_bound rsegs m ev _ HEV) as BE. cbn [cells_size csize Nat.add] in BE.
  pose proof (bytes_at_bound rsegs m body bb HBB) as BB.
  pose proof ST as (Hlo0 & Hhi0 & _).
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP.
  assert (Ud : bv_unsigned (Z_to_bv 64 d) = d) by (apply unsigned_lit; lia).
  assert (Ue : bv_unsigned (Z_to_bv 64 ev) = ev) by (apply unsigned_lit; lia).
  pose proof (munch_refl [(d, d + 40); (ev, ev + 80); (bv_unsigned sp - 160, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  (* the stack at the start, kept out of the transport tactics' reach (they match a bare stk) *)
  assert (ST0 : True /\ stk rsegs m lo (bv_unsigned sp)) by (split; [exact I | exact ST]).
  carve_frame 160%nat ST. clear ST.
  do 7 step.
  step. if_false.
  step. step. if_false.
  do 3 step.
  destruct (dn_frame_split _ _ _ _ _ _ _ _ _ FR) as (j0 & jl & jp & jm & H0 & HL & HP & HMj & HS). clear FR.
  replace (bv_unsigned sp + -160 + 8) with (bv_unsigned sp + -152) in HL by lia.
  replace (bv_unsigned sp + -160 + 48) with (bv_unsigned sp + -112) in HP by lia.
  replace (bv_unsigned sp + -160 + 80) with (bv_unsigned sp + -80) in HMj by lia.
  replace (bv_unsigned sp + -160 + 120) with (bv_unsigned sp + -40) in HS by lia.
  pose proof (rw_cells_wf _ _ _ _ HMj) as [Ljm _]. cbn [cell_wf] in Ljm.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    eapply evt_cut;
    [ eapply MN; [lia | lia | exact HPOS | exact HST | exact HD | exact HBB | exact HMj | lia | lia | lia | exact MI]
    | post_call rsegs mm ]
  end.
  rename POST into HM, PC into HDc, MI0 into MI.
  pose proof (mr_code_range (msg_step bb pos st)) as RC.
  step. step. step.
  rewrite (dn_eqb_int64 (mr_code (msg_step bb pos st)) 1) by lia.
  destruct (Z.eq_dec (mr_code (msg_step bb pos st)) 1) as [HC1|HC1].
  2: {
    (* diginet_msg_next did not answer 1: return its code; the event is not touched *)
    if_true.
    pose proof (dn_dec_merge rsegs _ d body cpad (Z.of_nat (length bb)) _ _ p HDc HD2) as HDEC.
    assert (HR : res = (mr_code (msg_step bb pos st), dgn_event_zero,
                        {| dd_c := cursor_of bb (mr_pos (msg_step bb pos st)) (mr_st (msg_step bb pos st)); dd_p := p |}))
      by (rewrite Hres; apply dn_res_n1; assumption).
    eapply (dn_epi ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m _ d ev body lo cpad ej [] res).
    - rewrite HR; reflexivity.
    - exact (proj2 ST0).
    - exact H0.
    - reflexivity.
    - exact HL.
    - reflexivity.
    - exact HP.
    - reflexivity.
    - exact HM.
    - apply msg_cells_size.
    - exact HS.
    - exact MU.
    - exact WM.
    - exact MI.
    - rewrite HR. exact HDEC.
    - rewrite HR. cbn [fst snd]. rewrite (proj2 (Z.eqb_neq _ 1) HC1). exact HEV. }
  if_false.
  rewrite (msg_cells_dmsg body jm bb pos st HC1) in HM.
  remember (firstn 4 (skipn 4 jm)) as mpad eqn:Hmpad.
  assert (Lmpad : length mpad = 4%nat) by (rewrite Hmpad, length_firstn, length_skipn; lia).
  remember (dn_msg (msg_step bb pos st)) as msg eqn:Hmsg.
  unfold dmsg_cells in HM. unfold cursor_cells in HDc.
  do 3 step. step.
  pose proof (rw_cells_CB2 rsegs _ ev 40 40 ej HEV) as [HE1 HE2]. clear HEV.
  replace (ev + Z.of_nat 40) with (ev + 40) in HE2 by lia.
  assert (U40 : bv_unsigned (Z_to_bv 64 40) = 40) by reflexivity.
  assert (U0 : bv_unsigned (Z_to_bv 64 0) = 0) by reflexivity.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    eapply evt_cut;
    [ eapply MSET; [ rewrite Ue, U40; exact HE1 | exact MI ]
    | post_call rsegs mm ]
  end.
  rename POST into HZ, MI0 into MI.
  rewrite Ue, U40, U0 in HZ. change (Z.to_nat 40) with 40%nat in HZ. change (0 mod 256) with 0 in HZ.
  apply dn_zero_head in HZ.
  unfold ev_head, arr_cells in HZ.
  cbn [map seq nth app de_kind de_strip de_button de_zone de_on de_right de_addr de_lsb_missing de_value
       de_delta de_mask de_segments de_len de_text de_seg de_dots de_device dgn_event_zero repeat] in HZ.
  do 3 step. step.
  assert (U80 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -80)) = bv_unsigned sp + -80) by (apply unsigned_lit; lia).
  assert (Ue40 : bv_unsigned (Z_to_bv 64 (ev + 40)) = ev + 40) by (apply unsigned_lit; lia).
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    eapply evt_cut;
    [ eapply MCPY;
      [ rewrite U80; exact (rw_cells_bytes_at _ _ _ _ HM)
      | rewrite U40, cells_bytes_length by exact (rw_cells_wf _ _ _ _ HM); reflexivity
      | rewrite Ue40, U40; exact HE2
      | rewrite U80, Ue40, U40; lia
      | exact MI ]
    | post_call rsegs mm ]
  end.
  rename PC into HC, MI0 into MI. clear POST.
  rewrite Ue40, U40 in HC. change (Z.to_nat 40) with 40%nat in HC.
  lazymatch type of HC with rw_cells _ ?mm _ _ =>
  assert (HEM : rw_cells rsegs mm (ev + 40) [C1 (b8 (dm_status msg)); C1 (b8 (dm_running msg));
    C1 (b8 (dm_d1 msg)); C1 (b8 (dm_d2 msg)); CB 4 mpad; C8 (Z_to_bv 64 (sysex_ptr body (dm_sysex msg)));
    C8 (Z_to_bv 64 (dm_sysex_len msg)); C8 (Z_to_bv 64 (dm_offset msg)); C8 (Z_to_bv 64 (dm_len msg))])
  end.
  { eapply rw_cells_bytes; [exact HC | cbn; repeat split; exact Lmpad |].
    cbn [cells_bytes cbytes]. rewrite !app_nil_r. reflexivity. }
  clear HC.
  (* lbu status; kind 13 stored; bne status & 0xf0, 0x90 *)
  do 6 step.
  pose proof (dn_msg_facts bb pos st HST HC1) as MF. rewrite <- Hmsg in MF.
  destruct MF as (R1 & R2 & MF).
  assert (RST : 0 <= dm_status msg < 256) by (destruct MF as [(-> & _)|]; lia).
  pose proof (byte_land_le (dm_status msg) 240 RST ltac:(lia)) as RL.
  assert (HRES : res = dn_tail (map bz bb) msg
                         (cursor_of bb (mr_pos (msg_step bb pos st)) (mr_st (msg_step bb pos st))) p).
  { rewrite Hres, dn_res_1 by assumption. rewrite Hmsg. reflexivity. }
  assert (HCTX : dn_ctx sp m d ev body lo bb p res msg (mr_pos (msg_step bb pos st)) (mr_st (msg_step bb pos st))
                   mpad).
  { unfold dn_ctx. split; [exact (proj2 ST0)|].
    split; [exact RSP|].
    repeat (split; [first [assumption | lia]|]). exact Lmpad. }
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (HAT : dn_at sp m mm d ev body bb cpad p (mr_pos (msg_step bb pos st)) (mr_st (msg_step bb pos st))
                    msg mpad j0 jl jp s3 s2 s1 s0 ra (dn_e0 msg))
      by (unfold dn_at; repeat (split; [eassumption|]); eassumption)
  end.
  rewrite (dn_zxb_b8 (dm_status msg)) by lia.
  rewrite (unsigned_lit (dm_status msg)) by lia.
  rewrite (dn_eqb_u64 (Z.land (dm_status msg) 240) 144) by lia.
  destruct (Z.eq_dec (Z.land (dm_status msg) 240) 144) as [N90|N90].
  - (* a note *)
    if_false. eapply dn_note; [exact HCTX | exact HAT | exact N90 | lia | lia].
  - if_true.
    (* bne status, 0xf0 *)
    step. step.
    rewrite (dn_eqb_u64 (dm_status msg) 240) by lia.
    destruct (Z.eq_dec (dm_status msg) 240) as [F0|F0].
    + (* a sysex *)
      if_false. destruct MF as [(_ & S1 & S2 & S3) | MF]; [|lia].
      eapply dn_sysex; [exact MCPY | exact SEG | exact HCTX | exact HAT | exact F0 | lia | lia | lia].
    + (* a channel message other than a note *)
      if_true.
      eapply dn_ctl; [exact MN | exact HCTX | exact HAT | exact N90 | exact F0 | lia | lia
                     | apply msg_step_pos_le; exact HPOS | apply msg_step_st_ok; exact HST].
Qed.

End Walk.
