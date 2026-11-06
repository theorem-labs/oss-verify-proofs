From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YO0i YO0f YO0d YO05 YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U Require Import Img0 Contract FrameAPI SlotKept SlotPack AllocPack.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import Statement.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import StatementKept.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import send_line_c gesture_end_c relay_event_c RelayFrame RelayModel RelayKeys.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import send_line_b_c gesture_end_b_c gestures_end_b_c relay_add_b_c relay_finish_b_c RelayRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import HarnessRep ListRep CheckRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import source_reset_c check_shape_ends_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import check_shape_done_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import drain_b_c SlotInv SlotSteps SlotRes SlotReads.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import KindB.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import SRCF SRCF3.
Import ListNotations.
Local Open Scope Z_scope.

Lemma exit_head : forall E t k,
  0 <= t <= OPS_MAX -> 0 <= k <= ss_n E -> t = OPS_MAX \/ k = ss_n E ->
  head_body E t k = false /\ head_pc E t k = LOOP_EXIT.
Proof.
  intros E t k Ht Hk HX.
  assert (HB : head_body E t k = false).
  { unfold head_body. apply andb_false_iff. destruct HX as [-> | ->].
    - left. apply Z.ltb_ge. lia.
    - right. apply Z.ltb_ge. lia. }
  split; [exact HB | unfold head_pc; rewrite HB; reflexivity].
Qed.

Lemma exit_entries_nonneg : forall es, 0 <= entries_total es.
Proof.
  induction es as [|e es IH]; cbn [entries_total fold_right].
  - lia.
  - fold (entries_total es). pose proof (keys_total_nonneg (re_keys e)). lia.
Qed.

Lemma exit_entries_length : forall es, Z.of_nat (length (entries_out es)) = entries_total es.
Proof.
  induction es as [|e es IH]; cbn [entries_out map concat entries_total fold_right].
  - reflexivity.
  - fold (entries_out es) (entries_total es). rewrite length_app, Nat2Z.inj_add, keys_out_length. lia.
Qed.

Lemma exit_entries_cost : forall es hj,
  length es = length hj -> Forall (fun e => 0 <= re_used e) es ->
  entries_total es <= slot_cost es hj.
Proof.
  induction es as [|e es IH]; intros [|p hj] HL HU; cbn [length] in HL; try discriminate HL.
  - cbn [entries_total slot_cost combine map fold_right]. lia.
  - inversion HU as [|? ? HE HT]; subst.
    specialize (IH hj ltac:(lia) HT).
    cbn [entries_total fold_right slot_cost combine map fst snd].
    fold (entries_total es) (slot_cost es hj).
    unfold pair_cost. destruct (re_skip e =? 0); lia.
Qed.

Lemma exit_texts_nodup : forall bs : list (list byte), NoDup bs -> NoDup (map bzs bs).
Proof.
  intros bs H. apply NoDup_ListNoDup in H. apply NoDup_ListNoDup.
  induction H as [|x bs Hx Hbs IH]; cbn [map]; constructor; [|exact IH].
  intros Hin. apply in_map_iff in Hin. destruct Hin as (y & Hy & HY).
  apply bzs_inj in Hy. subst y. exact (Hx HY).
Qed.

Lemma exit_keys_run : forall rc B L A mem t e p d,
  CF.RelayRep.entry_ok (rc := rc) B L A mem e ->
  pair_ok (rc := rc) B L A mem t e p ->
  exists rs ds,
    ends_run [] (hl_recs (hs_held (fst p))) (keys_out (re_keys e) ++ d)
      (want_of [] (hl_recs (hs_held (fst p)))) = Some (rs, ds, keys_total (re_keys e)).
Proof.
  intros rc B L A mem t e p d HE HP.
  destruct HE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & NK & HK).
  destruct HP as (_ & _ & _ & _ & HS & NH & _).
  rewrite want_of_nil, <- keys_out_length.
  apply ends_run_keys.
  - unfold keys_texts. rewrite <- map_map. apply exit_texts_nodup. exact NK.
  - exact NH.
  - exact HS.
  - eapply Forall_impl; [|exact HK]. intros k (_ & _ & _ & H0 & _). exact H0.
Qed.

Lemma exit_restore : forall ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (saved : bvmap 5 word) (F : bvmap 5 word) fc (m : word -> option byte) S,
  0 <= S -> S + 192 < 2 ^ 64 ->
  rw_cells rsegs m (S + 88) (saved_cells saved) ->
  evt rsegs
    (fun ms' => ms' =
      MS (mkR (getr saved 1) (Z_to_bv 64 (S + 192)) gp tp t0 t1 t2
              (getr saved 8) (getr saved 9) (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7
              (getr saved 18) (getr saved 19) (getr saved 20) (getr saved 21)
              (getr saved 22) (getr saved 23) (getr saved 24) (getr saved 25)
              (getr saved 26) (getr saved 27) t3 t4 t5 t6)
         F (ret_pc (getr saved 1)) fc None m (seg_rom rsegs))
    (MS (mkR ra (Z_to_bv 64 S) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x14760) fc None m (seg_rom rsegs)).
Proof.
  intros ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 saved F fc m S HS HT HC.
  unfold saved_cells in HC. do 16 step. apply evt_done. reflexivity.
Qed.
