(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From stdpp Require Import base list.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run Fs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac ZBridge STRW_tac Image Arr SysStep.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Top Require Import AllocIF AllocSpec SReach.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac HttpAlloc HttpAllocX.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Import Segs H_httpmsg_compare H_ListFind H_ListAddTail H_freelist H_obj
     H_membuffer_assign H_httpheader_free H_ListDestroy H_httpmsg_destroy.
Import ListNotations.
Open Scope Z_scope.
Set Printing Width 1000.

Definition LMAX : Z := 2^26 + 16.
Definition VMAX : Z := 2^29.

Definition POS_REQUEST_LINE : Z := 0. Definition POS_RESPONSE_LINE : Z := 1. Definition POS_HEADERS : Z := 2.
Definition POS_ENTITY : Z := 3. Definition POS_COMPLETE : Z := 4.

Section W.
Context {HCEIL : HasCeiling}.
  Variable AI : alloc_if rsegs.
  Notation K := (ai_K rsegs AI).
  Notation BLK := (block K).
  Notation hdr := (hdr AI).

  Definition okb (ok : option K) (A cap : Z) : list BLK := match ok with None => [] | Some k => [(k, A, cap + 1)] end.

  #[using="Type"] Lemma okb_mbo : forall ok A cap, (ok = None -> A = 0) -> mbo AI A cap (okb ok A cap).
  Proof. intros [k|] A cap H; cbn; [reflexivity| apply H; reflexivity]. Qed.

  #[using="Type"] Lemma mown_okb : forall m LB A cap ok bs, mown AI m LB A cap ok bs -> bsub AI (okb ok A cap) LB.
  Proof. intros m LB A cap [k|] bs OW b Hb; cbn in *; [| destruct Hb]. destruct Hb as [<-|[]]. exact (proj1 OW). Qed.

  Definition p_meth (m : mem) (P meth : Z) : Prop := rw_cells rsegs m P [C4 (wz 1); C4 (wz meth)] /\ 0 <= meth <= 11.

  Definition p_uri (m : mem) (P : Z) (uc : list cell) : Prop := rw_cells rsegs m (P + 8) uc /\ cells_size uc = 216%nat.

  Definition p_rs (m : mem) (P rm sc : Z) : Prop := rw_cells rsegs m (P + 224) [C4 (wz rm); C4 (wz sc)] /\ 0 <= rm <= 11 /\ - 2^31 <= sc < 2^31.

  Definition p_smsg (m : mem) (LB : list BLK) (P SA slen scap : Z) (sok : option K) (sbs : list byte) : Prop :=
    rw_cells rsegs m (P + 232) (mbuf_cells SA slen scap) /\ mown AI m LB SA scap sok sbs
    /\ 0 <= slen <= scap /\ scap + 1 <= LMAX /\ (sok <> None -> nth_error sbs (Z.to_nat slen) = Some (Z_to_bv 8 0)).

  Definition p_ver (m : mem) (P isreq maj min : Z) : Prop :=
    (exists pad, rw_cells rsegs m (P + 264) [C8 (wz 0); C4 (wz isreq); C4 (wz maj); C4 (wz min); C4 pad])
    /\ 0 <= isreq <= 1 /\ - 2^31 <= maj < 2^31 /\ - 2^31 <= min < 2^31.

  Definition p_hlist (m : mem) (P : Z) (ns : list (BLK * Z)) (hs : list hdr) (X : Z) : Prop :=
    rw_cells rsegs m (P + 288) (lhead_cells (hd_addr AI ns (P + 312)) (last_addr AI ns (P + 288)) (zlength ns))
    /\ rw_cells rsegs m (P + 344) (fl_cells 0 0)
    /\ rw_cells rsegs m (P + 368) [C8 (wz httpheader_free_entry); C8 (wz httpmsg_compare_entry)]
    /\ dlseg AI m ns (P + 288) (P + 312) /\ hdrs_mem AI m hs /\ map snd ns = map (hA AI) hs
    /\ (forall h, In h hs -> vlen AI h <= X /\ nlen AI h + 1 <= LMAX) /\ zlength ns <= X /\ 0 <= X.
  Definition hl_blocks (ns : list (BLK * Z)) (hs : list hdr) : list BLK := map fst ns ++ hdrs_blocks AI hs.

  Definition p_ent (m : mem) (P : Z) (eb el : word) : Prop := rw_cells rsegs m (P + 384) [C8 eb; C8 el].

  Definition p_msg (m : mem) (LB : list BLK) (P A len cap : Z) (okm : option K) (bs : list byte) : Prop :=
    rw_cells rsegs m (P + 400) (mbuf_cells A len cap) /\ mown AI m LB A cap okm bs
    /\ 0 <= len <= cap /\ cap + 1 <= LMAX
    /\ match okm with None => len = 0 | Some _ => nth_error bs (Z.to_nat len) = Some (Z_to_bv 8 0) end.

  Definition p_ctl_cells (err hack pos entp clen csz esp : Z) : list cell :=
    [C4 (wz err); C4 (wz hack); C4 (wz pos); C4 (wz entp); C4 (wz clen); C4 (wz 0); C8 (wz csz); C8 (wz esp)].

  Definition p_url (m : mem) (P ub : Z) : Prop := rw_cells rsegs m (P + 432) [C8 (wz ub)] /\ 0 <= ub < 2^64.

  Definition p_ctl (m : mem) (P err hack pos entp clen csz esp : Z) : Prop :=
    rw_cells rsegs m (P + 440) (p_ctl_cells err hack pos entp clen csz esp)
    /\ 0 <= err < 2^31 /\ 0 <= hack <= 1 /\ 0 <= pos <= 4 /\ 0 <= entp <= 6 /\ 0 <= clen < 2^32 /\ 0 <= csz < 2^64 /\ 0 <= esp < 2^64.

  Definition p_scan (m : mem) (P cur : Z) : Prop := rw_cells rsegs m (P + 480) [C8 (wz (P + 400)); C8 (wz cur); C4 (wz 0)].

  Definition p_blocks (ns : list (BLK * Z)) (hs : list hdr) (okm : option K) (A cap : Z) (sok : option K) (SA scap : Z) : list BLK :=
    hl_blocks ns hs ++ okb okm A cap ++ okb sok SA scap.

  Definition canary_ok : Prop :=
    forall s LB m, RHEAP rsegs AI s LB m -> rw_cells rsegs m 0x2a150 [C8 (wz 0x5ba88)] /\ exists c : word, rw_cells rsegs m 0x5ba88 [C8 c].

  Definition blk4096_ok : Prop := forall s LB m (b : BLK), RHEAP rsegs AI s LB m -> In b LB -> 4096 <= blk_addr b.

  #[using="Type"] Lemma p_msg_facts : forall m LB P A len cap okm bs s,
    RHEAP rsegs AI s LB m -> p_msg m LB P A len cap okm bs ->
    0 <= len <= cap /\ cap + 1 <= LMAX /\ Z.of_nat (length bs) = (match okm with None => 0 | Some _ => cap + 1 end)
    /\ (okm = None -> A = 0 /\ len = 0 /\ cap = 0)
    /\ (okm <> None -> 16 <= A /\ A + (cap + 1) <= alloc_ceiling /\ A mod 16 = 0).
  Proof.
    intros m LB P A len cap okm bs s HR (MBC & OWN & HL & HC & NUL). split; [exact HL|]. split; [exact HC|].
    destruct okm as [k|]; cbn in OWN.
    - destruct OWN as [HIN BLK]. destruct (ai_block_range rsegs AI _ _ _ _ HR HIN) as (R1 & R2 & R3 & R4 & _). cbn in R1, R2, R3, R4.
      destruct BLK as [[W _] _]. cbn in W. destruct W as [W _].
      split; [lia|]. split; [intros; discriminate|]. intros _. split; [Z.div_mod_to_equations; lia| split; [lia| exact R2]].
    - destruct OWN as (-> & -> & ->). cbn. split; [reflexivity|]. split; [intros _; repeat split; lia| intros X; exfalso; apply X; reflexivity].
  Qed.

  #[using="Type"] Lemma p_msg_bytes : forall m LB P A len cap k bs,
    p_msg m LB P A len cap (Some k) bs -> bytes_at rsegs m A bs /\ Z.of_nat (length bs) = cap + 1.
  Proof.
    intros m LB P A len cap k bs (MBC & [HIN BLK] & HL & HC & NUL).
    pose proof (rw_cells_bytes_at rsegs _ _ _ BLK) as B. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B.
    destruct BLK as [[W _] _]. cbn in W. destruct W as [W _]. split; [exact B| lia].
  Qed.
End W.
