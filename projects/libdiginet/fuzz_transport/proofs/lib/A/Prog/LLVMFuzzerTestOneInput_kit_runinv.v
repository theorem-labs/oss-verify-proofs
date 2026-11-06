(* LLVMFuzzerTestOneInput_kit_runinv: kit lemma K6 of the image-A walk of fuzz_transport.asan's LLVMFuzzerTestOneInput
   (statement lc_runinv_stmt, lib/A/Prog/LLVMFuzzerTestOneInput_segs.v section 8). Every conjunct is a field of
   TSim/Agree.v agree at the world: the frame in flight from B8 (b8_on01, b8_frames: a body of at most 1484 bytes, so
   frame_len <= 1514), the queue lengths from D1 (tagged: the entry is a PENDING command, D2 bounds its length) or D4
   (raw), s->queued from Deadline.v queued_le, g_ncmd from D3 (g_ncmd <= ops <= OPS_MAX = CMDS_MAX), the configured
   limits from A1 through TickTakeW.v tk_cfg_max_cmds / tk_cfg_max_body, g_fail_next from E1. *)
From Stdlib Require Import ZArith List Lia.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TCb TSess0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TSim Require Import Agree Deadline TickTakeW.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require LLVMFuzzerTestOneInput_segs.
Open Scope Z_scope.

Lemma lc_runinv_ok : LLVMFuzzerTestOneInput_segs.lc_runinv_stmt.
Proof.
  unfold LLVMFuzzerTestOneInput_segs.lc_runinv_stmt.
  intros ops Bw HA.
  pose proof (@ag_core _ _ _ HA) as HC.
  pose proof (@ac_cfg _ _ _ HC) as HCF.
  pose proof (@ac_fly _ _ _ HC) as HF.
  pose proof (@ac_q _ _ _ HC) as HQ.
  pose proof (@ac_misc _ _ _ HC) as HM.
  split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]].
  - (* (1) the frame in flight *)
    intros Hon. destruct (@b8_on01 _ HF) as [E|E]; [contradiction|].
    destruct (@b8_frames _ HF E) as (body & ncmds & Hb & _ & _ & Hlen & _).
    rewrite Hlen. unfold DgnSpec.frame_len, TCb.SPEC_MAX_FRAME. lia.
  - (* (2) the queue entries' lengths *)
    intros i Hi. destruct (Z.eq_dec (g_raw Bw) 0) as [R|R].
    + rewrite (@d1_queued _ _ HQ R) in Hi.
      destruct (@d1_entry _ _ HQ R i Hi) as (Hrng & Hst & _ & Hlen & _ & _).
      rewrite Hlen.
      assert (HNZ : Cmd_st Bw (Q_at Bw i) <> 0) by (rewrite Hst; unfold TCb.PENDING; lia).
      destruct (@d2_cmd _ _ HQ (Q_at Bw i) Hrng HNZ) as (_ & _ & _ & Hc & _ & _).
      unfold TSess0.DIGINET_CMD_MAX_LEN. lia.
    + destruct (@d4_entry _ _ HQ R i Hi) as (Hc & _).
      unfold TSess0.DIGINET_CMD_MAX_LEN. lia.
  - (* (3) s->queued *)
    exact (proj2 (queued_le ops Bw HQ)).
  - (* (4) the pending commands' lengths *)
    intros s Hs Hst.
    assert (HNZ : Cmd_st Bw s <> 0) by (rewrite Hst; unfold TCb.PENDING; lia).
    destruct (@d2_cmd _ _ HQ s Hs HNZ) as (_ & _ & _ & Hc & _ & _).
    unfold DgnSpec.SPEC_CMD_MAX. lia.
  - (* (5) g_ncmd *)
    pose proof (@d3_ncmd _ _ HQ) as H1. pose proof (@d3_ops _ _ HQ) as H2.
    unfold TCb.CMDS_MAX. unfold TCb.OPS_MAX in H2. lia.
  - (* (6) max_cmds *)
    rewrite (tk_cfg_max_cmds Bw HCF). exact (proj1 (@a1_max_cmds _ HCF)).
  - (* (7) max_body *)
    rewrite (tk_cfg_max_body Bw HCF). pose proof (@a1_max_body _ HCF). lia.
  - (* (8) g_fail_next *)
    destruct (@e1_fail_next _ _ HM) as [E|E]; rewrite E; lia.
Qed.
