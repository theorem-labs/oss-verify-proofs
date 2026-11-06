(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.openssl.punycode.lib.Common Require Import PropExec CatExec CatSim SeqExec StoreOk Frame.
From OSSVerify.Proofs.openssl.punycode.lib.LibA Require Import WpEngine LibKit WpTac.
From OSSVerify.Proofs.openssl.punycode.lib.LibA Require Import AShadow.
From OSSVerify.Proofs.openssl.punycode.lib.LibB Require Import BCode.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition B_IMG_END : Z := 0xbfd000.

(* [comment removed for export] *)
Definition G_SB : Z := 0x5e0f58.       (* [comment removed for export] *)
Definition G_MIDBEG : Z := 0x5e0f60.   (* [comment removed for export] *)
Definition G_MIDEND : Z := 0x5e0f68.   (* [comment removed for export] *)
Definition G_HIEND : Z := 0x5e0f70.    (* [comment removed for export] *)
Definition G_RINTRIN : Z := 0x5e1ae0.  (* [comment removed for export] *)
(* [comment removed for export] *)
Definition C_SB : Z := 0x6a3a78.
Definition C_MIDBEG : Z := 0x6a4768.
Definition C_MIDEND : Z := 0x6a4770.
Definition C_HIEND : Z := 0x6a4760.
Definition C_RINTRIN : Z := 0x6a4759.

(* [comment removed for export] *)
Definition rt_ok (M : mem) : Prop :=
  cell BSEGS M G_SB 8 (W C_SB) /\ cell BSEGS M C_SB 8 (W SB)
  /\ cell BSEGS M G_MIDBEG 8 (W C_MIDBEG) /\ cell BSEGS M C_MIDBEG 8 (W 0)
  /\ cell BSEGS M G_MIDEND 8 (W C_MIDEND) /\ (exists v, cell BSEGS M C_MIDEND 8 v)
  /\ cell BSEGS M G_HIEND 8 (W C_HIEND) /\ cell BSEGS M C_HIEND 8 (W (HIMEM_END - 1))
  /\ cell BSEGS M G_RINTRIN 8 (W C_RINTRIN) /\ (exists b, cell BSEGS M C_RINTRIN 1 b).

(* [comment removed for export] *)
Lemma rt_ok_unch : forall M0 M (P : word -> Prop),
  unch M0 M P -> (forall y, P y -> B_IMG_END <= bv_unsigned y) -> rt_ok M0 -> rt_ok M.
Proof.
  intros M0 M P HU HP (H1 & H2 & H3 & H4 & H5 & (v6 & H6) & H7 & H8 & H9 & (b10 & H10)).
  assert (T : forall a (k : nat) v, 0 <= a -> a + Z.of_nat k <= B_IMG_END -> cell BSEGS M0 a k v -> cell BSEGS M a k v).
  { intros a k v Ha Hk Hc. eapply cell_unch; [exact HU | lia | unfold B_IMG_END in *; lia | | exact Hc].
    intros x Hx HPx. apply HP in HPx. unfold inr in Hx. lia. }
  unfold rt_ok, G_SB, C_SB, G_MIDBEG, C_MIDBEG, G_MIDEND, C_MIDEND, G_HIEND, C_HIEND, G_RINTRIN, C_RINTRIN, B_IMG_END in *.
  repeat split; try (apply T; [lia | cbn; lia | assumption]).
  - exists v6. apply T; [lia | cbn; lia | assumption].
  - exists b10. apply T; [lia | cbn; lia | assumption].
Qed.

(* [comment removed for export] *)
Lemma bytes_eq_unsigned : forall bs bs' : list byte, map bv_unsigned bs = map bv_unsigned bs' -> bs = bs'.
Proof.
  induction bs as [|b bs IH]; intros [|b' bs'] H; cbn in H; try discriminate; [reflexivity|].
  injection H as Hb Hr. f_equal; [apply bv_eq; exact Hb | apply IH; exact Hr].
Qed.

(* [comment removed for export] *)
Lemma cell_of_img : forall M lo hi a v,
  img_ok M lo hi -> lo <= a -> a + 8 <= hi -> 0 <= a -> a + 8 < 2 ^ 64 ->
  (exists bs, rdn BSEGS (fun _ => None) (W a) 8 = Some bs
              /\ map bv_unsigned bs = map bv_unsigned (word_to_le_bytes 8 v)) ->
  cell BSEGS M a 8 v.
Proof.
  intros M lo hi a v Hi Hlo Hhi Ha Hn (bs & Hr & Hb). unfold cell.
  rewrite <- (bytes_eq_unsigned _ _ Hb). rewrite <- Hr.
  apply rdn_ext; [rewrite Wu by lia; lia|].
  intros x Hx. rewrite Wu in Hx by lia. rewrite <- (W_u x). apply Hi. cbn in Hx. lia.
Qed.

(* [comment removed for export] *)
Lemma got_cells : forall M, img_ok M 0x5e0f58 0x5e0f78 -> img_ok M 0x5e1ae0 0x5e1ae8 ->
  cell BSEGS M G_SB 8 (W C_SB) /\ cell BSEGS M G_MIDBEG 8 (W C_MIDBEG) /\ cell BSEGS M G_MIDEND 8 (W C_MIDEND)
  /\ cell BSEGS M G_HIEND 8 (W C_HIEND) /\ cell BSEGS M G_RINTRIN 8 (W C_RINTRIN).
Proof.
  intros M H1 H2. unfold G_SB, G_MIDBEG, G_MIDEND, G_HIEND, G_RINTRIN.
  repeat split.
  - eapply cell_of_img; [exact H1 | lia | lia | lia | lia | eexists; split; vm_compute; reflexivity].
  - eapply cell_of_img; [exact H1 | lia | lia | lia | lia | eexists; split; vm_compute; reflexivity].
  - eapply cell_of_img; [exact H1 | lia | lia | lia | lia | eexists; split; vm_compute; reflexivity].
  - eapply cell_of_img; [exact H1 | lia | lia | lia | lia | eexists; split; vm_compute; reflexivity].
  - eapply cell_of_img; [exact H2 | lia | lia | lia | lia | eexists; split; vm_compute; reflexivity].
Qed.
