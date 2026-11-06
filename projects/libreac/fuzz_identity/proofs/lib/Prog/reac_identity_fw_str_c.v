From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.libreac.fuzz_identity.lib Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require Import IdentSpec.
Import ListNotations.
Open Scope Z_scope.

Definition REAC_IDENTITY_FW_STR : Z := 0x1479c.

Definition FW (v : Z) : list byte :=
  (if 10 <=? v / 1000 then [dg (v / 1000 / 10)] else [])
  ++ [dg (v / 1000 mod 10); Z_to_bv 8 0x2e; dg (v mod 1000 / 100); dg (v mod 1000 / 10 mod 10);
      dg (v mod 1000 mod 10)].

Definition L (v : Z) : Z := Z.of_nat (length (FW v)).

Definition reac_identity_fw_str_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (v o c : Z),
    a0 = Z_to_bv 64 v -> a1 = Z_to_bv 64 o -> a2 = Z_to_bv 64 c ->
    0 <= v < 65536 -> 0 <= o < 2^64 -> 0 <= c < 2^64 ->
    (o <> 0 -> 8 <= c -> wr_at rsegs m o 8) ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' r a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 r a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         wmono rsegs m m' /\
         (o = 0 \/ c < 8 -> r = Z_to_bv 64 (-1) /\ m' = m) /\
         (o <> 0 -> 8 <= c ->
            r = Z_to_bv 64 (L v) /\ bytes_at rsegs m' o (FW v ++ [Z_to_bv 8 0]) /\
            munch [(o, o + L v + 1)] m m'))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 REAC_IDENTITY_FW_STR) fc None m (seg_rom rsegs)).

Lemma reac_identity_fw_str_dec_h : forall h, 0 <= h < 66 ->
  DEC h 1 = (if 10 <=? h then [dg (h / 10)] else []) ++ [dg (h mod 10)].
Proof.
  intros h Hh. apply bytes_eqb_eq.
  apply (z_all_spec (fun h => bytes_eqb (DEC h 1) ((if 10 <=? h then [dg (h / 10)] else []) ++ [dg (h mod 10)]))
           (Z.to_nat 66) 0 ltac:(vm_compute; reflexivity) h).
  rewrite Z2Nat.id by lia. lia.
Qed.

Lemma reac_identity_fw_str_dec_f : forall f, 0 <= f < 1000 ->
  DEC f 3 = [dg (f / 100); dg (f / 10 mod 10); dg (f mod 10)].
Proof.
  intros f Hf. apply bytes_eqb_eq.
  apply (z_all_spec (fun f => bytes_eqb (DEC f 3) [dg (f / 100); dg (f / 10 mod 10); dg (f mod 10)])
           (Z.to_nat 1000) 0 ltac:(vm_compute; reflexivity) f).
  rewrite Z2Nat.id by lia. lia.
Qed.

Lemma reac_identity_fw_str_dg_nz : forall x, 0 <= x <= 9 -> bv_unsigned (dg x) <> 0.
Proof.
  intros x Hx. unfold dg. rewrite Z_to_bv_unsigned.
  change (bv_wrap 8 (0x30 + x)) with ((0x30 + x) mod 2^8). rewrite Z.mod_small by lia. lia.
Qed.

Lemma reac_identity_fw_str_c3 : forall v, 0 <= v < 65536 ->
  FW v = DEC (v / 1000) 1 ++ [Z_to_bv 8 0x2e] ++ DEC (v mod 1000) 3.
Proof.
  intros v Hv.
  rewrite reac_identity_fw_str_dec_h, reac_identity_fw_str_dec_f by (Z.div_mod_to_equations; lia).
  unfold FW. rewrite <- app_assoc. reflexivity.
Qed.

Lemma reac_identity_fw_str_c3_short : forall v, 0 <= v < 10000 ->
  FW v = [dg (v / 1000); Z_to_bv 8 0x2e; dg (v mod 1000 / 100); dg (v mod 1000 / 10 mod 10); dg (v mod 1000 mod 10)].
Proof.
  intros v Hv. unfold FW.
  rewrite (proj2 (Z.leb_gt 10 (v / 1000))) by (Z.div_mod_to_equations; lia).
  rewrite (Z.mod_small (v / 1000) 10) by (Z.div_mod_to_equations; lia).
  reflexivity.
Qed.

Lemma reac_identity_fw_str_c3_len : forall v, 0 <= v < 65536 ->
  L v = Z.of_nat (length (DEC (v / 1000) 1)) + 4 /\ L v = (if v <? 10000 then 5 else 6).
Proof.
  intros v Hv. unfold L. rewrite reac_identity_fw_str_dec_h by (Z.div_mod_to_equations; lia). unfold FW.
  destruct (Z.leb_spec 10 (v / 1000)); destruct (Z.ltb_spec v 10000);
    first [ split; reflexivity | exfalso; Z.div_mod_to_equations; lia ].
Qed.

Lemma reac_identity_fw_str_c3_nz : forall v, 0 <= v < 65536 -> forall b, In b (FW v) -> bv_unsigned b <> 0.
Proof.
  intros v Hv b Hb. unfold FW in Hb. apply in_app_or in Hb.
  destruct Hb as [Hb|Hb]; [destruct (10 <=? v / 1000)|]; cbn [In] in Hb;
    repeat (destruct Hb as [<-|Hb];
            [ first [ apply reac_identity_fw_str_dg_nz; Z.div_mod_to_equations; lia
                    | let Hc := fresh "Hc" in intro Hc; vm_compute in Hc; discriminate Hc ] | ]);
    contradiction.
Qed.
