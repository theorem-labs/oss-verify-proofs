(* The drain arm's count rule DR_CNT_grow for the image-B top (lib/B/ReplyBTop.v :135), at RINV := ReplyRINVB.fr_RINV:
   the image-B port of lib/A/ReplyCntArms.v :77 cnt_dr_grow.  proves no function (kind: segment lemma: a per-step count
   bound for one drain step of the B walk).
   - btcnt_DR_CNT_grow_kh: the text of ReplyBTop.v :135 with ONE premise added, after dr3_epost and before dr3_hpost:
       (re_hp e' = 0 /\ re_keys e' = []) \/ (re_hp e' <> 0 /\ 8 <= re_kh e')
     aentry_ok's held-array clause of the entry the drain leaves (lib/B/W_rep.v :133-134; A's premise at
     lib/A/ReplyCntArms.v :104-105).  Without it the rule is false: re_hp e' <> 0 with re_kh e' = 0 satisfies every
     premise of :135 (dr3_epost's second disjunct, ent_ka e' = 0 = ds_ka of the drain's final state), and then
     aentry_blks e' has a 0-byte block that no request made; at P := (fun n => n =? 0) the pre-state blocks count 0
     (the positivity premise) and the trace's peak is 0, but the post-state count is 1.
   - btcnt_DR_CNT_grow: A's shape, both premises of lib/A/ReplyCntArms.v :94-95 and :104-105 at A's places; the first,
     re_skip in {0, 1}, is fr_RINV's own (ReplyRINVB.v fr_entry_ok), so the proof does not read it.
   The proof: RI_pair (ReplyRINVBHead.RI_pair_b) and re_skip in {0, 1} from fr_RINV, the drain's start invariant
   (relay_instance_gone_b_lem.rig_dinit), the drain's exact count potential (W_rr_m_dcnt.rmc_drain_dr) and its closing
   arithmetic over variables (W_rr_m_dcnt.rmc_close, rmc_ocap), then net <= peak (W_rr_m_dcnt.rmc_net_peak).  The last
   step generalizes the counts before lia, so no proof term asks the kernel to unfold the drain run. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04 YI00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0d YP0c YC80 YC81 YO0a YN1e.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YI16 YE00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YE01 YE2k.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require YCfn.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import ZTraceSpec.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_syms W_listing W_place W_tbl W_kit W_pl W_img W_journal.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import
HarnessRep RelayRep CheckRep RelayKeys RelayModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require RelayRunT drain_b_c relay_instance_gone_b_lem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_rep W_contract W_sites W_frame.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyGuardB.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_LLVMFuzzerTestOneInput_cut.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyCnt W_tr_cnt W_rr_m_dcnt.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require
W_LLVMFuzzerTestOneInput_drain_defs W_LLVMFuzzerTestOneInput_drain_defs_x W_LLVMFuzzerTestOneInput_drain_calls.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyRINVB ReplyRINVBHead.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Local Notation dr_e0 := W_LLVMFuzzerTestOneInput_drain_defs.dr_e0.
Local Notation dr_at_op := W_LLVMFuzzerTestOneInput_drain_defs.dr_at_op.
Local Notation dr_pick := W_LLVMFuzzerTestOneInput_drain_defs.dr_pick.
Local Notation DX_msz_ok := W_LLVMFuzzerTestOneInput_drain_defs_x.msz_ok.
Local Notation DX_dr3_epre := W_LLVMFuzzerTestOneInput_drain_defs_x.dr3_epre.
Local Notation DX_ls3_kh := W_LLVMFuzzerTestOneInput_drain_defs_x.ls3_kh.
Local Notation DX_dr3_hpre := W_LLVMFuzzerTestOneInput_drain_defs_x.dr3_hpre.
Local Notation DX_ls3_hn := W_LLVMFuzzerTestOneInput_drain_defs_x.ls3_hn.
Local Notation DX_dr3_epost := W_LLVMFuzzerTestOneInput_drain_defs_x.dr3_epost.
Local Notation DX_dr3_hpost := W_LLVMFuzzerTestOneInput_drain_defs_x.dr3_hpost.
Local Notation DX_ls3_dpost := W_LLVMFuzzerTestOneInput_drain_defs_x.ls3_dpost.
Local Notation dr_dfun := W_LLVMFuzzerTestOneInput_drain_calls.dr_dfun.
Local Notation dr_cap1 := W_LLVMFuzzerTestOneInput_drain_calls.dr_cap1.

(* ReplyBTop.v :135 DR_CNT_grow with aentry_ok's held-array clause of e' (W_rep.v :133-134) after dr3_epost *)
Lemma btcnt_DR_CNT_grow_kh : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  forall (cx : @lfcx rc) (t : Z) (m : lmod) (si : nat) (h : hsrc) (j : nat) (e' : rentry) (h' : hsrc)
    (LB : list byte) (out' : Z) (P : Z -> bool),
  @ReplyRINVB.fr_RINV rc cx t m -> dr_at_op cx m -> dr_pick cx m si h ->
  (j < length (lm_es m))%nat -> re_fd (nth j (lm_es m) dr_e0) = hs_fd h ->
  re_eof (nth j (lm_es m) dr_e0) = 0 ->
  DX_msz_ok m -> 0 <= t < OPS_MAX ->
  Z.of_nat (length (re_U (nth j (lm_es m) dr_e0))) <= APARTIAL ->
  (forall b : Z * Z, In b (aentry_blks (nth j (lm_es m) dr_e0) ++ asrc_blks h ++ aout_blks (lm_cap m) (lm_out m)) ->
     0 < snd b) ->
  DX_dr3_epre (nth j (lm_es m) dr_e0) -> DX_ls3_kh (nth j (lm_es m) dr_e0) ->
  DX_dr3_hpre h -> DX_ls3_hn h -> 0 <= lm_cap m ->
  dr_dfun m si h j e' h' LB ->
  DX_dr3_epost (nth j (lm_es m) dr_e0) e' h ->
  ((re_hp e' = 0 /\ re_keys e' = []) \/ (re_hp e' <> 0 /\ 8 <= re_kh e')) ->
  DX_dr3_hpost h h' ->
  DX_ls3_dpost m j h e' h' ->
  (ReplyCnt.acnt P (aentry_blks e' ++ asrc_blks h' ++ aout_blks (dr_cap1 m j h) out') <=
   ReplyCnt.acnt P (aentry_blks (nth j (lm_es m) dr_e0) ++ asrc_blks h ++ aout_blks (lm_cap m) (lm_out m)) +
   Z.to_nat (ReplyCnt.tr_peakP P
     (dr_tr (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (nth j (lm_es m) dr_e0) h)))%nat.
Proof.
  intros rc fx cx t m si h j e' h' LB out' P HRI _ Hpk Hj Hfd Heof _ _ HU _ Hep _ Hhp _ Hcap Hdf _ Hk' Hhpo _.
  (* RI_pair and the entry's skip flag, from fr_RINV *)
  destruct (ReplyRINVBHead.RI_pair_b rc fx cx t m si h j HRI Hpk Hj Hfd Heof) as (SO & SW & _ & _).
  assert (Hsk : re_skip (nth j (lm_es m) dr_e0) = 0 \/ re_skip (nth j (lm_es m) dr_e0) = 1).
  { pose proof HRI as (_ & HR & _).
    destruct HR as (_ & _ & _ & Hent & _).
    rewrite Forall_forall in Hent.
    assert (He : In (nth j (lm_es m) dr_e0) (lm_es m)) by (apply nth_In; exact Hj).
    destruct (Hent _ He) as (_ & _ & _ & _ & X). exact X. }
  set (e := nth j (lm_es m) dr_e0) in *.
  set (c := lm_c m) in *. set (mx := lm_mx m) in *. set (no := Z.of_nat (length (lm_O m))) in *.
  set (cap := lm_cap m) in *.
  destruct Hep as (UC & _ & UZ & Hkh8 & _).
  destruct Hhp as (PD & PF).
  (* the drain's start state *)
  destruct (relay_instance_gone_b_lem.rig_dinit no cap e h Hsk SO SW ltac:(unfold APARTIAL in HU; lia) UZ
              ltac:(lia) PD PF) as [IV ER].
  destruct (W_rr_m_dcnt.rmc_drain_dr P c mx no cap e h Hcap IV ER) as [D DP].
  (* the held arrays: each is 0 or a block of nonzero size *)
  assert (HE : re_hp e = 0 \/ re_kh e <> 0).
  { destruct (Z.eq_dec (re_hp e) 0) as [X | X]; [left; exact X | right; specialize (Hkh8 X); lia]. }
  assert (HE' : re_hp e' = 0 \/ re_kh e' <> 0) by (destruct Hk' as [(X & _) | (_ & X)]; [left; exact X | right; lia]).
  (* dr_dfun's and dr3_hpost's clauses *)
  unfold dr_dfun in Hdf. cbv zeta in Hdf. fold e c mx no cap in Hdf.
  destruct Hdf as (_ & _ & _ & R4 & _ & _ & R7 & R8 & _ & _ & _ & _ & _ & R16 & _ & _ & R22 & R24 & _ & _ & _ & R11).
  destruct Hhpo as (_ & R19 & _).
  assert (OC : dr_cap1 m j h = drain_b_c.ds_ocap (dr_fin c mx no cap e h)).
  { unfold dr_cap1. fold e c mx no cap. exact (W_rr_m_dcnt.rmc_ocap c mx no cap e h). }
  pose proof (W_rr_m_dcnt.rmc_close P (dr_fin c mx no cap e h) (W_tr_cnt.tr_netP P (dr_tr c mx no cap e h))
                (dr_lines h) (Z_to_bv 8) no cap (lm_out m) (dr_cap1 m j h) out' e h e' h'
                HE HE' D DP OC R4 R7 R8 R11 R16 R19 R22 R24) as E.
  pose proof (W_rr_m_dcnt.rmc_net_peak _ P (dr_tr c mx no cap e h)) as N.
  pose proof (ReplyCnt.tr_peakP_nonneg _ P (dr_tr c mx no cap e h)) as N0.
  clear - E N N0.
  revert E N N0.
  generalize (ReplyCnt.acnt P (aentry_blks e' ++ asrc_blks h' ++ aout_blks (dr_cap1 m j h) out')) as a1.
  generalize (ReplyCnt.acnt P (aentry_blks e ++ asrc_blks h ++ aout_blks cap (lm_out m))) as a0.
  generalize (W_tr_cnt.tr_netP P (dr_tr c mx no cap e h)) as tn.
  generalize (ReplyCnt.tr_peakP P (dr_tr c mx no cap e h)) as tp.
  intros tp tn a0 a1 E N N0. lia.
Qed.

(* lib/A/ReplyCntArms.v :77 cnt_dr_grow's shape on image B: ReplyBTop.v :135 with both of A's added premises at A's
   places (re_skip in {0, 1} after re_eof, the held-array clause of e' after dr3_epost) *)
Lemma btcnt_DR_CNT_grow : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  forall (cx : @lfcx rc) (t : Z) (m : lmod) (si : nat) (h : hsrc) (j : nat) (e' : rentry) (h' : hsrc)
    (LB : list byte) (out' : Z) (P : Z -> bool),
  @ReplyRINVB.fr_RINV rc cx t m -> dr_at_op cx m -> dr_pick cx m si h ->
  (j < length (lm_es m))%nat -> re_fd (nth j (lm_es m) dr_e0) = hs_fd h ->
  re_eof (nth j (lm_es m) dr_e0) = 0 ->
  (re_skip (nth j (lm_es m) dr_e0) = 0 \/ re_skip (nth j (lm_es m) dr_e0) = 1) ->
  DX_msz_ok m -> 0 <= t < OPS_MAX ->
  Z.of_nat (length (re_U (nth j (lm_es m) dr_e0))) <= APARTIAL ->
  (forall b : Z * Z, In b (aentry_blks (nth j (lm_es m) dr_e0) ++ asrc_blks h ++ aout_blks (lm_cap m) (lm_out m)) ->
     0 < snd b) ->
  DX_dr3_epre (nth j (lm_es m) dr_e0) -> DX_ls3_kh (nth j (lm_es m) dr_e0) ->
  DX_dr3_hpre h -> DX_ls3_hn h -> 0 <= lm_cap m ->
  dr_dfun m si h j e' h' LB ->
  DX_dr3_epost (nth j (lm_es m) dr_e0) e' h ->
  ((re_hp e' = 0 /\ re_keys e' = []) \/ (re_hp e' <> 0 /\ 8 <= re_kh e')) ->
  DX_dr3_hpost h h' ->
  DX_ls3_dpost m j h e' h' ->
  (ReplyCnt.acnt P (aentry_blks e' ++ asrc_blks h' ++ aout_blks (dr_cap1 m j h) out') <=
   ReplyCnt.acnt P (aentry_blks (nth j (lm_es m) dr_e0) ++ asrc_blks h ++ aout_blks (lm_cap m) (lm_out m)) +
   Z.to_nat (ReplyCnt.tr_peakP P
     (dr_tr (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (nth j (lm_es m) dr_e0) h)))%nat.
Proof.
  intros rc fx cx t m si h j e' h' LB out' P HRI Hop Hpk Hj Hfd Heof _ Hmsz Ht HU Hpos Hep Hkh Hhp Hhn Hcap Hdf Hepo
    Hk' Hhpo Hdp.
  exact (btcnt_DR_CNT_grow_kh rc fx cx t m si h j e' h' LB out' P HRI Hop Hpk Hj Hfd Heof Hmsz Ht HU Hpos Hep Hkh Hhp
    Hhn Hcap Hdf Hepo Hk' Hhpo Hdp).
Qed.

Print Assumptions btcnt_DR_CNT_grow_kh.
Print Assumptions btcnt_DR_CNT_grow.
