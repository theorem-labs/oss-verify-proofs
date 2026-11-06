From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Lib Require Import PropExec MState Mem Cells Exec Frame Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Prog Require Import StdioModel __toread_c.
Import ListNotations.
Open Scope Z_scope.

Lemma le4_mod : forall v v', bv_unsigned v mod 2^32 = bv_unsigned v' mod 2^32 -> le4 v = le4 v'.
Proof.
  intros v v' H. unfold le4.
  rewrite <- (Z_to_le_bytes_mod 4 (bv_unsigned v) 32), <- (Z_to_le_bytes_mod 4 (bv_unsigned v') 32) by (cbn; lia).
  rewrite H. reflexivity.
Qed.

Lemma rw_cells_c4_upd : forall segs m A cs k v v',
  rw_cells segs m A cs -> cell_at cs k = Some (C4 v) -> le4 v = le4 v' ->
  rw_cells segs m A (cell_upd cs k (C4 v')).
Proof.
  intros segs m A cs k v v' [[Hwf Hb] Hw] Hc E.
  destruct (cell_at_split cs k (C4 v) (C4 v') Hc) as (pre & post & Ecs & _ & ->).
  subst cs.
  apply cells_wf_app in Hwf. destruct Hwf as [H1 [_ H3]].
  rewrite cells_bytes_app in Hb. rewrite cells_size_app in Hw. cbn [cells_bytes cbytes cells_size csize] in Hb, Hw.
  split; [split|].
  - apply cells_wf_app. split; [exact H1|]. split; [exact I|exact H3].
  - rewrite cells_bytes_app. cbn [cells_bytes cbytes]. rewrite <- E. exact Hb.
  - rewrite cells_size_app. cbn [cells_size csize]. exact Hw.
Qed.

Theorem __toread_holds : __toread_contract.
Proof.
  unfold __toread_contract, TOREAD, TOREAD_K.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo b Fc
    fl md q rb pv nx HM HR HFL HMD MI ST LO HLO HB.
  destruct HM as (buf & (pad0 & pad1 & pad2 & ung & HC & Lung & Lbuf & Hh0 & Hh16) & Hq & HRB & HFc & Hb0 & Hbh).
  unfold mfile_cells in HC.
  unfold A_MCLOSE, A_MREAD, A_MWRITE, A_MSEEK, wz in *.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  pose proof (zr_word a0) as Ra0. unfold inr64 in Ra0.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp); (bv_unsigned a0, bv_unsigned a0 + 1304)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  assert (L0 : 0 <= lo) by (destruct ST as [? _]; lia).
  carve_frame 16%nat ST.
  destruct HFL as [-> | ->]; destruct HMD as [-> | ->].
  all: do 11 step; if_true; do 6 step; if_false; do 10 step; release_frame FR ST (bv_unsigned sp); do 2 step.
  all: eapply rw_cells_c4_upd with (k := 136%nat) (v' := Z_to_bv 64 4294967295) in HC;
    [ | cells_cbv; reflexivity | apply le4_mod; vm_compute; reflexivity ].
  all: cbv beta iota zeta delta [cell_upd csize Nat.eqb Nat.sub] in HC.
  all: apply evt_done; unfold __toread_post, TOREAD_K; do 16 eexists; split; [reflexivity|].
  all: refine (conj _ (conj _ (conj _ (conj _ (conj _ _))))).
  all: try (apply bv_eq; vm_compute; reflexivity).
  all: try (replace (bv_unsigned sp - 16) with (bv_unsigned sp + -16) by lia; exact MU).
  all: try exact WM.
  all: try exact MI.
  all: try exact ST.
  all: unfold mfile; cbv zeta; exists buf.
  all: refine (conj _ (conj Hq (conj _ (conj HFc (conj Hb0 Hbh))))).
  all: try (refine (conj _ (conj _ (conj _ _))); [lia | lia | lia | reflexivity]).
  all: unfold mfile_raw, mfile_cells, rpos_of, rend_of, wz; exists pad0, pad1, pad2, ung.
  all: refine (conj _ (conj Lung (conj Lbuf (conj Hh0 Hh16)))).
  all: replace (bv_unsigned a0 + 280 + 1024) with (bv_unsigned a0 + 1304) by lia.
  all: exact HC.
Qed.
