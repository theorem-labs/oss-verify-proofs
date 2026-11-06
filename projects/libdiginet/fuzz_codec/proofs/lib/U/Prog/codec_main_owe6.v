(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/openssl/ct/lib/CtColA/W_set0A.v, with its module paths and module names changed; 116 of its 138 lines of code are new or changed and 122 lines of the source are left out. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_owe codec_agree.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.U.Prog Require Import codec_cells codec_img
  codec_main_inv codec_main_lib codec_main_owe0 codec_main_owe5.
Import ListNotations.
Open Scope Z_scope.

(** Segment OWE6 of the walk of LLVMFuzzerTestOneInput in the UBSan image: the METER case of owe()
    (fuzz_codec.c:190-200), 0x14890-0x14918 and the tail 0x1491c-0x14924 it shares with RING. The
    two range tests go to SPEC_E_RANGE at 0x14a2c; otherwise the mask ~(-1 << b) is built and
    owe_sysex, inlined, writes want[0..8), want_len, want_key and want_display before the checks at
    0x14a34. The null and alignment trap on the desk (0x148b4) is dead. *)

Ltac addr_eq_tac ::= first [ apply wa_of_var; lia
                           | symmetry; first [ apply wa_of_Z_to_bv; lia | apply wa_of_var; lia | unfold wa; f_equal; lia ] ].

Ltac cell_of_bytes bs ::=
  lazymatch bs with
  | le8 ?v => constr:(C8 v)
  | le4 ?v => constr:(C4 v)
  | le2 ?v => constr:(C2 v)
  | [?b] => constr:(C1 b)
  | le1 (zxb ?b) => constr:(C1 b)
  | le1 ?v => constr:(C1 (Z_to_bv 8 (bv_unsigned v)))
  end.

(** owe() of kind 6 (fuzz_codec.c:190-200) on a record with a desk. *)
Lemma owe_k6 : forall k d, k_kind k = 6 -> od_of k = Some d ->
  owe_k k = if (0x20 <=? k_a k) || (14 <? k_b k) then (E_RANGE, noc)
            else (0, ([0xf0; 0x13; u8 (d_dev d); u8 0x10] ++
                      [u8 (Z.lor (k_a k) (bit_or_0 (negb (k_c k =? 0)) 0x20));
                       u8 (Z.shiftr ((2 ^ k_b k - 1) mod 2 ^ 32) 7);
                       u8 (Z.land ((2 ^ k_b k - 1) mod 2 ^ 32) 0x7f)] ++ [0xf7],
                      KEY 4 (u8 (Z.lor (k_a k) (bit_or_0 (negb (k_c k =? 0)) 0x20))), 0)).
Proof. intros k d HK HO. unfold owe_k, owe_spec. rewrite HK, HO. reflexivity. Qed.

(** addi -1, sllw b, not (0x148b8-0x148d0): the mask ~(-1 << b) for b <= 14. *)
Lemma mask_lit : forall b, 0 <= b <= 14 ->
  Z.lxor (bv_swrap 32 (Z.shiftl 18446744073709551615 (b mod 32)) mod 18446744073709551616)
         18446744073709551615 = 2 ^ b - 1.
Proof.
  intros b Hb.
  assert (E : b = 0 \/ b = 1 \/ b = 2 \/ b = 3 \/ b = 4 \/ b = 5 \/ b = 6 \/ b = 7 \/ b = 8 \/ b = 9 \/
              b = 10 \/ b = 11 \/ b = 12 \/ b = 13 \/ b = 14) by lia.
  repeat (destruct E as [-> | E]; [vm_compute; reflexivity |]). subst b. vm_compute. reflexivity.
Qed.

(** snez, slli 5 (0x148f4-0x148f8): c != 0 as 0x20. *)
Lemma b2z_shl5 : forall t, Z.shiftl (Z.b2z t) 5 mod 18446744073709551616 = bit_or_0 t 32.
Proof. intros [|]; reflexivity. Qed.

(** ch | 0x40000 (0x14914-0x14918) is SPEC_KEY(4, ch). *)
Lemma key_meter : forall a t, 0 <= a < 32 ->
  Z.lor (Z.lor (bit_or_0 t 32) a) 262144 = KEY 4 (u8 (Z.lor a (bit_or_0 t 32))).
Proof.
  intros a t Ha.
  assert (R : 0 <= Z.lor a (bit_or_0 t 32) < 2 ^ 6).
  { apply lor_lt_pow2; [lia | destruct t; cbn [bit_or_0]; lia]. }
  unfold KEY, u8. rewrite (Z.mod_small _ 256) by lia.
  change 0xffff with (Z.ones 16). rewrite Z.land_ones by lia. rewrite Z.mod_small by lia.
  rewrite (Z.lor_comm (bit_or_0 t 32) a), Z.lor_comm. reflexivity.
Qed.

Lemma codec_main_owe6 : seg_owe6_stmt.
Proof.
  unfold seg_owe6_stmt.
  intros [ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 p F fc m lo data] n ENV CHK k WF K6.
  pose proof (fun m1 => relro_at _ m1 ENV) as RELRO.
  unfold owe_ok, chk_ok, fr in *. cenv_cbn.
  intros ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' s5' t3' t4' t5' t6' cur rem u0 pj tj plj c ops m1
         _ ND HOPS HOPS2 HCUR HC0 HCN FR ST MU WM HMI.
  pose proof WF as (HK & HDK & HBF & HOUT & HRC & HWRC & HWL & HWK & HWD & HRD).
  destruct (ND ltac:(rewrite K6; reflexivity)) as [-> HDNZ]. clear ND.
  destruct (desk5 k HDK HDNZ) as (d & HOD & HDC).
  destruct (desk_rd5 m1 k d (RELRO m1 MU) HDC) as [_ RDD].
  assert (HDR : 0x1f690 <= k_desk k <= 0x1f6a0)
    by (destruct HDC as [[E _]|[E _]]; rewrite E; unfold SDESK_C24, SDESK_PC; lia).
  assert (HD7 : Z.land (k_desk k) 7 = 0)
    by (destruct HDC as [[E _]|[E _]]; rewrite E; reflexivity).
  assert (HDD : 0 <= d_dev d <= 1) by (destruct HDC as [[_ ->]|[_ ->]]; cbn; lia).
  pose proof HRD as (Ra & Rb & Rc & Rdl & Rlen & Rby & Rn & _ & _ & _).
  destruct ENV as (BY & HMI0 & ST0 & LO & SPA & DJ & HPB & HPNZ & RI & DJR).
  destruct FR as (HS & F0 & F8 & FK & FIN & FPD & FTX & FPL & FSV).
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  pose proof ST0 as (Hlo0 & Hhi0 & _).
  unfold kcall_cells, k_run, with_rc, with_out in FK.
  cbn [k_kind k_pad k_p k_desk k_a k_b k_c k_delta k_bytes k_n k_rc k_before k_out k_want_rc k_want
       k_want_len k_want_key k_want_display] in FK.
  rewrite K6. replace (pc_owe 6) with 0x14890 by reflexivity.
  (* 0x14890-0x14898: a > 0x1f *)
  zstep. zstep. zstep. if_cases T1.
  { zify_cond T1. rewrite sx32_u in T1 by lia.
    assert (Ha : 0x20 <= k_a k) by (destruct (Z.ltb_spec (k_a k) (2 ^ 31)); lia).
    zstep. zstep.
    eapply (CHK _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (with_want_rc (k_run k) E_RANGE)); try eassumption.
    - apply (chk_wf_rng_o0 k WF). rewrite (owe_k6 k d K6 HOD).
      replace (0x20 <=? k_a k) with true by (symmetry; apply Z.leb_le; lia). reflexivity.
    - exact (conj (kcall_cells_size _) (conj F0 (conj F8 (conj FK (conj FIN (conj FPD (conj FTX (conj FPL FSV)))))))). }
  zify_cond T1. rewrite sx32_u in T1 by lia.
  assert (Ha : k_a k < 0x20) by (destruct (Z.ltb_spec (k_a k) (2 ^ 31)); lia).
  rewrite (sx32_small (k_a k)) by lia.
  (* 0x1489c-0x148a4: b > 14 *)
  zstep. zstep. zstep. if_cases T2.
  { zify_cond T2. rewrite sx32_u in T2 by lia.
    assert (Hb : 14 < k_b k) by (destruct (Z.ltb_spec (k_b k) (2 ^ 31)); lia).
    zstep. zstep.
    eapply (CHK _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (with_want_rc (k_run k) E_RANGE)); try eassumption.
    - apply (chk_wf_rng_o0 k WF). rewrite (owe_k6 k d K6 HOD).
      replace (14 <? k_b k) with true by (symmetry; apply Z.ltb_lt; lia). rewrite orb_true_r. reflexivity.
    - exact (conj (kcall_cells_size _) (conj F0 (conj F8 (conj FK (conj FIN (conj FPD (conj FTX (conj FPL FSV)))))))). }
  zify_cond T2. rewrite sx32_u in T2 by lia.
  assert (Hb : k_b k <= 14) by (destruct (Z.ltb_spec (k_b k) (2 ^ 31)); lia).
  rewrite (sx32_small (k_b k)) by lia.
  (* 0x148a8-0x148b4: d != NULL and aligned (the trap edge is dead) *)
  do 4 zstep.
  if_cases T3.
  { exfalso. rewrite HD7 in T3. vm_compute in T3. discriminate T3. }
  (* 0x148b8-0x148c4: the mask, c, d->device *)
  zstep. zstep. zstep. zstep. cbv beta. rewrite (u8_unsigned (d_dev d)) by lia.
  (* 0x148c8-0x14918: owe_sysex inlined; 0x1491c-0x14924 the shared tail *)
  do 24 zstep.
  (* 0x14a34: the record with owe()'s want, want_len 8, the key and display 0 *)
  rewrite (snez_sx_o0 (k_c k)) in FK by lia. rewrite !b2z_shl5 in FK.
  rewrite (key_meter (k_a k) (negb (k_c k =? 0))) in FK by lia.
  match goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    apply (rw_cells_merge_at mm _ _ 14 8) in FK
  end.
  cbn [firstn skipn cells_size csize cells_bytes cbytes app Nat.add] in FK.
  match type of FK with context [CB 24 ?W :: C8 (Z_to_bv 64 8) :: _] => set (Wv := W) in FK end.
  eapply (CHK _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
            (k_owed k Wv 8 (KEY 4 (u8 (Z.lor (k_a k) (bit_or_0 (negb (k_c k =? 0)) 0x20))))));
    try eassumption.
  - pose proof (pow_m1 (k_b k) ltac:(lia)) as Hm.
    apply (chk_wf_succ_o0 k
             ([0xf0; 0x13; u8 (d_dev d); u8 0x10] ++
              [u8 (Z.lor (k_a k) (bit_or_0 (negb (k_c k =? 0)) 0x20));
               u8 (Z.shiftr ((2 ^ k_b k - 1) mod 2 ^ 32) 7);
               u8 (Z.land ((2 ^ k_b k - 1) mod 2 ^ 32) 0x7f)] ++ [0xf7])
             (KEY 4 (u8 (Z.lor (k_a k) (bit_or_0 (negb (k_c k =? 0)) 0x20)))) Wv 8 _ WF).
    + rewrite (owe_k6 k d K6 HOD).
      replace (0x20 <=? k_a k) with false by (symmetry; apply Z.leb_gt; lia).
      replace (14 <? k_b k) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
    + cbn [length app]. unfold Wv.
      replace (le2 (Z_to_bv 64 5104)) with [b8 0xf0; b8 0x13]
        by (apply bytes_eq_of_unsigned; vm_compute; reflexivity).
      cbn [firstn app bz map].
      rewrite !b8_lit, !b8_u8.
      rewrite (mask_lit (k_b k)) by lia. rewrite (Z.mod_small (2 ^ k_b k - 1) (2 ^ 32)) by lia.
      rewrite (Z.lor_comm (bit_or_0 _ _) (k_a k)).
      replace (b8 (-9)) with (b8 0xf7) by (apply bv_eq; reflexivity).
      reflexivity.
    + reflexivity.
    + cbn [length app]. lia.
    + reflexivity.
    + apply KEY_range. lia.
  - exact (conj (kcall_cells_size _) (conj F0 (conj F8 (conj FK (conj FIN (conj FPD (conj FTX (conj FPL FSV)))))))).
Qed.
