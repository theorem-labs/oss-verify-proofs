(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.openssl.punycode.lib.Common Require Import PropExec CatExec CatSim SeqExec StoreOk Frame.
From OSSVerify.Proofs.openssl.punycode.lib.LibA Require Import WpEngine LibKit StrKit WpTac WpMem.
From OSSVerify.Proofs.openssl.punycode.lib.LibA Require Import AShadow.
From OSSVerify.Proofs.openssl.punycode.lib.LibB Require Import BCode BRt BrCode.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition KSC : list nat := [5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat.

(* [comment removed for export] *)
Definition C_INITED : Z := 0x6a4758.        (* [comment removed for export] *)
Definition G_CF : Z := 0x5e0f48.            (* [comment removed for export] *)
Definition C_CF : Z := 0x7355a8.            (* [comment removed for export] *)
Definition R_STRLEN : Z := 0x5e3f68.        (* [comment removed for export] *)
Definition R_STRCHR : Z := 0x5e3f80.        (* [comment removed for export] *)
Definition R_MEMCPY : Z := 0x5e4188.        (* [comment removed for export] *)

Definition ic_ok (M : mem) : Prop :=
  cell BSEGS M C_INITED 1 (W 1)
  /\ cell BSEGS M G_CF 8 (W C_CF)
  /\ cell BSEGS M (C_CF + 245) 1 (W 0)      (* [comment removed for export] *)
  /\ cell BSEGS M (C_CF + 251) 1 (W 1)      (* [comment removed for export] *)
  /\ cell BSEGS M (C_CF + 253) 1 (W 1)      (* [comment removed for export] *)
  /\ cell BSEGS M R_STRLEN 8 (W 0x563c34) /\ cell BSEGS M R_STRCHR 8 (W 0x563830) /\ cell BSEGS M R_MEMCPY 8 (W 0x563304)
  /\ img_ok M 0x104a8 0x104b0 /\ img_ok M 0x104e0 0x104e8.

Lemma ic_ok_unch : forall M0 M (P : word -> Prop),
  unch M0 M P -> (forall y, P y -> B_IMG_END <= bv_unsigned y) -> ic_ok M0 -> ic_ok M.
Proof.
  intros M0 M P HU HP (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10).
  assert (T : forall a (k : nat) v, 0 <= a -> a + Z.of_nat k <= B_IMG_END -> cell BSEGS M0 a k v -> cell BSEGS M a k v).
  { intros a k v Ha Hk Hc. eapply cell_unch; [exact HU | lia | unfold B_IMG_END in *; lia | | exact Hc].
    intros x Hx HPx. apply HP in HPx. unfold inr in Hx. lia. }
  assert (TI : forall lo hi, 0 <= lo -> hi <= B_IMG_END -> img_ok M0 lo hi -> img_ok M lo hi).
  { intros lo hi Hlo Hhi Hi. eapply img_unch; [exact HU | lia | unfold B_IMG_END in *; lia | | exact Hi].
    intros x Hx HPx. apply HP in HPx. unfold inr in Hx. lia. }
  unfold ic_ok, C_INITED, G_CF, C_CF, R_STRLEN, R_STRCHR, R_MEMCPY, B_IMG_END in *.
  repeat split; first [ apply T; [lia | cbn; lia | assumption] | apply TI; [lia | lia | assumption] ].
Qed.

(* [comment removed for export] *)
Ltac wp_ini stops := wp_go 0x1c4874 6%nat C_inited_eq C_inited stops.

Lemma inited_cps : forall rom Post M l,
  cell BSEGS M C_INITED 1 (W 1) -> length l = 32%nat ->
  (forall l', length l' = 32%nat -> same_except [10%nat] l l' -> rget l' 10 = W 1 ->
              reach BSEGS rom (v_jalr (rget l 1) 0) l' M Post) ->
  reach BSEGS rom (Z_to_bv 64 0x1c4874) l M Post.
Proof.
  intros rom Post M l Hc Hl K. unfold C_INITED in *. regs_open l Hl.
  wp_ini (@nil Z).
  eexists. split; [apply load_cell; [exact Hc | lia]|].
  apply K; [reflexivity | same_ex | cbn [lget]; apply bv_eq; reflexivity].
Qed.

(* [comment removed for export] *)
Ltac wp_tri stops := wp_go 0x1c5784 40%nat C_tryinit_eq C_tryinit stops.

Lemma tryinit_cps : forall rom Post M S l,
  cell BSEGS M C_INITED 1 (W 1) ->
  B_IMG_END <= S - 16 /\ S < 2 ^ 63 -> wr_ok BSEGS M (S - 16) 16 ->
  length l = 32%nat -> rget l 2 = W S ->
  (forall l' M', length l' = 32%nat -> same_except [10%nat; 11%nat] l l' -> rget l' 10 = W 1 ->
                 unch M M' (fun x => inr x (S - 16) 16) -> mem_grows M M' ->
                 reach BSEGS rom (v_jalr (rget l 1) 0) l' M' Post) ->
  reach BSEGS rom (Z_to_bv 64 0x1c5784) l M Post.
Proof.
  intros rom Post M S l Hc HS Hw Hl H2 K. unfold C_INITED, B_IMG_END in *. regs_open l Hl. subst sp.
  wp_tri [0x1c57b8]. mem_auto.
  change (bv_unsigned (Z_to_bv 64 1) mod 2 ^ (8 * Z.of_nat 1)) with 1.
  rewrite (lb_small 1) by lia.
  split; intros Hb; [exfalso; apply Hb; reflexivity|]. clear Hb.
  mem_auto. replace (S + -16 + 16) with S by lia.
  apply K; [reflexivity | same_ex | reflexivity | solve_unch ltac:(unfold inr in *; lia) | solve_grows].
Qed.

(* [comment removed for export] *)
Ltac wp_isl stops := wp_go 0x1cff4c 7%nat C_istrlen0_eq C_istrlen0 stops.

Section IStrlen0.
Variable rom : mem.
Variable Post : word -> regfile -> mem -> Prop.
Variables (M : mem) (p N : Z) (B : Z -> byte) (k z : Z).
Hypothesis HB : bytes_at M p N B.
Hypothesis Hp : 0 <= p.
Hypothesis HN : p + N < 2 ^ 64.
Hypothesis Hk : 0 <= k <= z.
Hypothesis Hz : z < N.
Hypothesis HBz : bv_unsigned (B z) = 0.
Hypothesis HBnz : forall j, k <= j < z -> bv_unsigned (B j) <> 0.

Definition KS_isl : list nat := [10; 11; 12]%nat.
Variable l0 : regfile.
Hypothesis K : forall l', length l' = 32%nat -> same_except KS_isl l0 l' -> rget l' 10 = W (z - k) ->
  reach BSEGS rom (v_jalr (rget l0 1) 0) l' M Post.

Lemma isl_loop : forall n t l, z - t = Z.of_nat n -> k <= t <= z ->
  length l = 32%nat -> same_except KS_isl l0 l -> rget l 10 = W (p + k) -> rget l 11 = W (t - k) ->
  reach BSEGS rom (Z_to_bv 64 0x1cff50) l M Post.
Proof.
  induction n as [|n IH]; intros t l Hm Ht Hl Hse H10 H11; regs_open l Hl; subst a0 a1;
    wp_isl [0x1cff50]; rewrite ?add_W;
    (exists (W (bv_unsigned (B t))); split;
       [replace (p + k + (t - k)) with (p + t) by lia; apply (load1_bytes_at BSEGS M p N B t HB); lia|]);
    pose proof (bv_unsigned_in_range 8 (B t)) as HBt; change (bv_modulus 8) with 256 in HBt;
    rewrite Wu by lia; split; intros Hb; rewrite ?addi_W.
  - exfalso. apply Hb. replace t with z by lia. exact HBz.
  - pose proof (Hse 1%nat ltac:(cbv; intuition lia)) as Hra. cbn [rget lget] in Hra. subst ra.
    apply K; [reflexivity | eapply same_except_trans; [exact Hse | same_ex] |].
    cbn [lget]. f_equal. lia.
  - assert (t <> z) by (intros ->; apply Hb, HBz).
    eapply (IH (t + 1)); [lia | lia | reflexivity | eapply same_except_trans; [exact Hse | same_ex] | | ];
      cbn [rget lget]; f_equal; lia.
  - assert (t = z).
    { destruct (Z.eq_dec t z) as [E|E]; [exact E|]. exfalso. apply (HBnz t); [lia | exact Hb]. }
    pose proof (Hse 1%nat ltac:(cbv; intuition lia)) as Hra. cbn [rget lget] in Hra. subst ra.
    apply K; [reflexivity | eapply same_except_trans; [exact Hse | same_ex] |].
    cbn [lget]. f_equal. lia.
Qed.

Lemma isl_body : forall l, l = l0 -> length l = 32%nat -> rget l 10 = W (p + k) ->
  reach BSEGS rom (Z_to_bv 64 0x1cff4c) l M Post.
Proof.
  intros l El Hl H10. assert (Hse : same_except KS_isl l0 l) by (rewrite El; apply same_except_refl). clear El.
  regs_open l Hl. subst a0. wp_isl [0x1cff50].
  eapply (isl_loop (Z.to_nat (z - k)) k); [lia | lia | reflexivity | eapply same_except_trans; [exact Hse | same_ex] | | ];
    cbn [rget lget]; f_equal; lia.
Qed.
End IStrlen0.

Theorem istrlen0_cps : forall rom Post M p N B k z l,
  bytes_at M p N B -> 0 <= p -> p + N < 2 ^ 64 -> 0 <= k <= z -> z < N ->
  bv_unsigned (B z) = 0 -> (forall j, k <= j < z -> bv_unsigned (B j) <> 0) ->
  length l = 32%nat -> rget l 10 = W (p + k) ->
  (forall l', length l' = 32%nat -> same_except KS_isl l l' -> rget l' 10 = W (z - k) ->
              reach BSEGS rom (v_jalr (rget l 1) 0) l' M Post) ->
  reach BSEGS rom (Z_to_bv 64 0x1cff4c) l M Post.
Proof. intros. eapply isl_body with (l0 := l); eauto. Qed.
