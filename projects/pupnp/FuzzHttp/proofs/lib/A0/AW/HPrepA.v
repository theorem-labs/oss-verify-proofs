(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From stdpp Require Import base list.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac ZBridge STRW_tac Image Ceiling Arr SysStep.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Top Require Import AllocIF.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAW Require Import Segs Shadow Contracts ATac IcptA0 AllocA0 ATacAp.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.T7A0 Require Import ShadowKit.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.AW Require Import HttpAllocA HttpRepA AWKit HObjA HObjK H_freelist H_ListAddTail H_httpheader_free H_httpmsg_destroy.
Import ListNotations.
Open Scope Z_scope.

Definition LMAX_A : Z := 2^26 + 16.
Definition VMAX_A : Z := 2^29.

Definition POS_REQUEST_LINE_A : Z := 0. Definition POS_RESPONSE_LINE_A : Z := 1. Definition POS_HEADERS_A : Z := 2.
Definition POS_ENTITY_A : Z := 3. Definition POS_COMPLETE_A : Z := 4.

Section W.
Context {HC : HasCeiling}.
  Variable FI : fs_if.
  Variable AI : am_if FI.
  Notation K := (am_K FI AI).
  Notation BLK := (block K).
  Notation BL := (list (block K)).
  Notation hdr := (hdr FI AI).

  Definition p_obj (q : Z) (st : fsstate FI) (m : mem) (P : Z) : Prop :=
    mlocNB FI AI q st P 504 /\ P + 504 <= alloc_ceiling /\ P mod 8 = 0 /\ shw m P 504.

  Definition okbA (ok : option K) (A cap : Z) : BL := match ok with None => [] | Some k => [(k, A, cap + 1)] end.

  #[using="Type"] Lemma okbA_mbo : forall ok A cap, (ok = None -> A = 0) -> mbo FI AI A cap (okbA ok A cap).
  Proof. intros [k|] A cap H; cbn; [reflexivity| apply H; reflexivity]. Qed.

  #[using="Type"] Lemma mownA_okb : forall m LB A cap ok bs, mownA FI AI m LB A cap ok bs -> bsub FI AI (okbA ok A cap) LB.
  Proof. intros m LB A cap [k|] bs OW b Hb; cbn in *; [| destruct Hb]. destruct Hb as [<-|[]]. exact (proj1 OW). Qed.

  Definition p_meth (m : mem) (P meth : Z) : Prop := rw_cells asegs m P [C4 (wz 1); C4 (wz meth)] /\ 0 <= meth <= 11.

  Definition p_uri (m : mem) (P : Z) (uc : list cell) : Prop := rw_cells asegs m (P + 8) uc /\ cells_size uc = 216%nat.

  Definition p_rs (m : mem) (P rm sc : Z) : Prop := rw_cells asegs m (P + 224) [C4 (wz rm); C4 (wz sc)] /\ 0 <= rm <= 11 /\ - 2^31 <= sc < 2^31.

  Definition p_smsg (m : mem) (LB : BL) (P SA slen scap : Z) (sok : option K) (sbs : list byte) : Prop :=
    rw_cells asegs m (P + 232) (mbuf_cells SA slen scap) /\ mownA FI AI m LB SA scap sok sbs
    /\ 0 <= slen <= scap /\ scap + 1 <= LMAX_A /\ (sok <> None -> nth_error sbs (Z.to_nat slen) = Some (Z_to_bv 8 0)).

  Definition p_ver (m : mem) (P isreq maj min : Z) : Prop :=
    (exists pad, rw_cells asegs m (P + 264) [C8 (wz 0); C4 (wz isreq); C4 (wz maj); C4 (wz min); C4 pad])
    /\ 0 <= isreq <= 1 /\ - 2^31 <= maj < 2^31 /\ - 2^31 <= min < 2^31.

  Definition p_hlist (m : mem) (P : Z) (ns : list (BLK * Z)) (hs : list hdr) (X : Z) : Prop :=
    rw_cells asegs m (P + 288) (lhead_cells (hd_addr FI AI ns (P + 312)) (last_addr FI AI ns (P + 288)) (zlength ns))
    /\ rw_cells asegs m (P + 344) (fl_cells 0 0)
    /\ rw_cells asegs m (P + 368) [C8 (wz httpheader_free_entryA); C8 (wz httpmsg_compare_entryA)]
    /\ dlseg FI AI m ns (P + 288) (P + 312) /\ hdrs_mem FI AI m hs /\ map snd ns = map (hA FI AI) hs
    /\ (forall h, In h hs -> vlen FI AI h <= X /\ nlen FI AI h + 1 <= LMAX_A) /\ zlength ns <= X /\ 0 <= X.
  Definition hl_blocks (ns : list (BLK * Z)) (hs : list hdr) : BL := map fst ns ++ hdrs_blocks FI AI hs.

  Definition p_ent (m : mem) (P : Z) (eb el : word) : Prop := rw_cells asegs m (P + 384) [C8 eb; C8 el].

  Definition p_msg (m : mem) (LB : BL) (P A len cap : Z) (okm : option K) (bs : list byte) : Prop :=
    rw_cells asegs m (P + 400) (mbuf_cells A len cap) /\ mownA FI AI m LB A cap okm bs
    /\ 0 <= len <= cap /\ cap + 1 <= LMAX_A
    /\ match okm with None => len = 0 | Some _ => nth_error bs (Z.to_nat len) = Some (Z_to_bv 8 0) end.

  Definition p_ctl_cells (err hack pos entp clen csz esp : Z) : list cell :=
    [C4 (wz err); C4 (wz hack); C4 (wz pos); C4 (wz entp); C4 (wz clen); C4 (wz 0); C8 (wz csz); C8 (wz esp)].
  Definition p_url (m : mem) (P ub : Z) : Prop := rw_cells asegs m (P + 432) [C8 (wz ub)] /\ 0 <= ub < 2^64.
  Definition p_ctl (m : mem) (P err hack pos entp clen csz esp : Z) : Prop :=
    rw_cells asegs m (P + 440) (p_ctl_cells err hack pos entp clen csz esp)
    /\ 0 <= err < 2^31 /\ 0 <= hack <= 1 /\ 0 <= pos <= 4 /\ 0 <= entp <= 6 /\ 0 <= clen < 2^32 /\ 0 <= csz < 2^64 /\ 0 <= esp < 2^64.

  Definition p_scan (m : mem) (P cur : Z) : Prop := rw_cells asegs m (P + 480) [C8 (wz (P + 400)); C8 (wz cur); C4 (wz 0)].

  Definition p_blocks (ns : list (BLK * Z)) (hs : list hdr) (okm : option K) (A cap : Z) (sok : option K) (SA scap : Z) : BL :=
    hl_blocks ns hs ++ okbA okm A cap ++ okbA sok SA scap.

  #[using="Type"] Lemma p_msg_facts : forall m LB P A len cap okm bs s,
    RHEAP_A FI AI s LB m -> p_msg m LB P A len cap okm bs ->
    0 <= len <= cap /\ cap + 1 <= LMAX_A /\ Z.of_nat (length bs) = (match okm with None => 0 | Some _ => cap + 1 end)
    /\ (okm = None -> A = 0 /\ len = 0 /\ cap = 0)
    /\ (okm <> None -> 0x609000 <= A /\ A + (cap + 1) + 16 <= alloc_ceiling /\ A mod 16 = 0 /\ shw m A (cap + 1)
                       /\ (A + (cap + 1) <= FSB FI \/ FSB FI + A0_FS_SIZE <= A)
                       /\ (A + (cap + 1) + 16 <= 0x7fff7000 \/ 0x10007fff8000 <= A)).
  Proof.
    intros m LB P A len cap okm bs s HR (MBC & OWN & HL & HCp & NUL). split; [exact HL|]. split; [exact HCp|].
    destruct okm as [k|]; cbn in OWN.
    - destruct OWN as [HIN BLKc]. destruct (am_block_range FI AI _ _ _ _ HR HIN) as (R1 & R2 & R3 & R4 & R5 & R6 & R7). cbn in R1, R2, R3, R4, R5, R6, R7.
      pose proof (block_shw FI AI s LB m _ A (cap + 1) HR HIN ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia)) as SHWA.
      destruct BLKc as [[W _] _]. cbn in W. destruct W as [W _].
      split; [lia|]. split; [intros; discriminate|]. intros _.
      split; [exact R5|]. split; [exact R4|]. split; [exact R2|]. split; [exact SHWA|]. split; [exact R7| exact R6].
    - destruct OWN as (-> & -> & ->). cbn. split; [reflexivity|]. split; [intros _; repeat split; lia| intros X; exfalso; apply X; reflexivity].
  Qed.

  #[using="Type"] Lemma p_msg_bytes : forall m LB P A len cap k bs,
    p_msg m LB P A len cap (Some k) bs -> bytes_at asegs m A bs /\ Z.of_nat (length bs) = cap + 1.
  Proof.
    intros m LB P A len cap k bs (MBC & [HIN BLKc] & HL & HCp & NUL).
    pose proof (rw_cells_bytes_at asegs _ _ _ BLKc) as B. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B.
    destruct BLKc as [[W _] _]. cbn in W. destruct W as [W _]. split; [exact B| lia].
  Qed.
End W.
