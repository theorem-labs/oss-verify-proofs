From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_owe.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.U.Prog Require Import codec_cells codec_img
  memset_c diginet_personality_of_c codec_main_inv codec_main_lib.
Import ListNotations.
Open Scope Z_scope.

Ltac addr_eq_tac ::= first [ apply wa_of_var; lia
                           | symmetry; first [ apply wa_of_Z_to_bv; lia | apply wa_of_var; lia | unfold wa; f_equal; lia ] ].

(** The record after memset(&k, 0, 184): the 76 bytes up to [before], the 64 bytes of [before] and [out],
    and the 44 bytes after them, each in the cells the later stores and the second memset use. *)
Definition hz_pre : list cell :=
  [C4 (Z_to_bv 64 0); CB 4 (repeat (b8 0) 4); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
   C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0);
   CB 24 (repeat (b8 0) 24); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)].
Definition hz_post : list cell :=
  [C4 (Z_to_bv 64 0); CB 24 (repeat (b8 0) 24); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)].

Lemma head_zero : forall m A,
  rw_cells rsegs m A [CB (Z.to_nat (bv_unsigned (Z_to_bv 64 184)))
                        (repeat (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 0) mod 256)) (Z.to_nat (bv_unsigned (Z_to_bv 64 184))))] ->
  rw_cells rsegs m A hz_pre /\ rw_cells rsegs m (A + 76) [CB 64 (repeat (b8 0) 64)] /\
  rw_cells rsegs m (A + 140) hz_post.
Proof.
  intros m A H.
  apply (rw_cells_same_bytes m A _ (hz_pre ++ [CB 64 (repeat (b8 0) 64)] ++ hz_post)) in H;
    [ | cbn; repeat split; try reflexivity | vm_compute; reflexivity | vm_compute; reflexivity ].
  apply rw_cells_app_split in H. destruct H as [H1 H].
  apply rw_cells_app_split in H. destruct H as [H2 H3].
  change (Z.of_nat (cells_size hz_pre)) with 76 in H2, H3.
  change (Z.of_nat (cells_size [CB 64 (repeat (b8 0) 64)])) with 64 in H3.
  replace (A + 76 + 64) with (A + 140) in H3 by lia.
  auto.
Qed.

(** SPEC_DESK[i] is the desk [sdesk] names. *)
Lemma sdesk_nth : forall i, 0 <= i <= 2 -> nth (Z.to_nat i) codec_SPEC_DESK 0 = sdesk i.
Proof. intros i Hi. assert (i = 0 \/ i = 1 \/ i = 2) as [-> | [-> | ->]] by lia; reflexivity. Qed.

(** The record after the three stores and the second memset is the head's record. *)
Lemma head_rec : forall m A kind i,
  rw_cells rsegs m A
    [C4 (Z_to_bv 64 kind); CB 4 (repeat (b8 0) 4); C8 (Z_to_bv 64 (pers_of i)); C8 (Z_to_bv 64 (sdesk i));
     C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0);
     CB 24 (repeat (b8 0) 24); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)] ->
  rw_cells rsegs m (A + 76)
    [CB (Z.to_nat (bv_unsigned (Z_to_bv 64 64)))
        (repeat (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 165) mod 256)) (Z.to_nat (bv_unsigned (Z_to_bv 64 64))))] ->
  rw_cells rsegs m (A + 140) hz_post ->
  rw_cells rsegs m A (kcall_cells (k_head kind i)).
Proof.
  intros m A kind i H1 H2 H3.
  apply (rw_cells_same_bytes m (A + 76) _ [CB 32 (repeat (b8 0xa5) 32); CB 32 (repeat (b8 0xa5) 32)]) in H2;
    [ | cbn; repeat split; try reflexivity | vm_compute; reflexivity | vm_compute; reflexivity ].
  change (kcall_cells (k_head kind i)) with
    ([C4 (Z_to_bv 64 kind); CB 4 (repeat (b8 0) 4); C8 (Z_to_bv 64 (pers_of i)); C8 (Z_to_bv 64 (sdesk i));
      C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0);
      CB 24 (repeat (b8 0) 24); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)]
     ++ [CB 32 (repeat (b8 0xa5) 32); CB 32 (repeat (b8 0xa5) 32)] ++ hz_post).
  apply rw_cells_app_join; [exact H1 |].
  match goal with |- rw_cells _ _ (A + ?z) _ => replace z with 76 by reflexivity end.
  apply rw_cells_app_join; [exact H2 |].
  match goal with |- rw_cells _ _ (A + 76 + ?z) _ => replace z with 64 by reflexivity end.
  replace (A + 76 + 64) with (A + 140) by lia. exact H3.
Qed.

(** T1[k] is the reader pc_rd names, and it is even. *)
Lemma t1_pc : forall k, 0 <= k <= 13 -> nth (Z.to_nat k) codec_T1 0 = pc_rd k.
Proof.
  intros k Hk. apply Z.eqb_eq.
  refine (zall_range (fun k => nth (Z.to_nat k) codec_T1 0 =? pc_rd k) 0 14 _ k ltac:(lia)).
  vm_compute. reflexivity.
Qed.

Lemma pc_rd_range : forall k, 0 <= k <= 14 -> 0 <= pc_rd k < 2 ^ 64 /\ pc_rd k mod 2 = 0.
Proof.
  intros k Hk.
  pose (P := fun k => (0 <=? pc_rd k) && (pc_rd k <? 2 ^ 64) && (pc_rd k mod 2 =? 0)).
  assert (H : P k = true) by (refine (zall_range P 0 15 _ k ltac:(lia)); vm_compute; reflexivity).
  unfold P in H. apply andb_prop in H as [H H2]. apply andb_prop in H as [H0 H1].
  apply Z.leb_le in H0. apply Z.ltb_lt in H1. apply Z.eqb_eq in H2. lia.
Qed.

(** An identity of byte values, checked on all 256 of them. *)
Lemma z256 : forall (f g : Z -> Z), zall (fun x => f x =? g x) 0 256 = true ->
  forall x, 0 <= x < 256 -> f x = g x.
Proof. intros f g H x Hx. apply Z.eqb_eq. exact (zall_spec _ 256 0 H x ltac:(lia)). Qed.

(** Replace a register value computed from the op byte [op] by one of the three clean forms. *)
Ltac clean_op op Rop :=
  repeat match goal with
  | |- context [Z_to_bv 64 ?e] =>
      lazymatch e with
      | op mod 15 => fail
      | op / 15 mod 3 => fail
      | 4 * (op / 15 mod 3) => fail
      | context [op] =>
          let e' := eval pattern op in e in
          lazymatch e' with
          | ?f op =>
              first [ replace e with (op mod 15)
                        by (symmetry; apply (z256 f (fun x => x mod 15)); [vm_compute; reflexivity | exact Rop])
                    | replace e with (op / 15 mod 3)
                        by (symmetry; apply (z256 f (fun x => x / 15 mod 3)); [vm_compute; reflexivity | exact Rop])
                    | replace e with (4 * (op / 15 mod 3))
                        by (symmetry; apply (z256 f (fun x => 4 * (x / 15 mod 3))); [vm_compute; reflexivity | exact Rop]) ]
          end
      end
  end.

Lemma codec_main_head : seg_head_stmt.
Proof.
  unfold seg_head_stmt.
  intros [ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 p F fc m lo data] n ENV MEMS PERSOF RD.
  cenv_cbn.
  unfold loop_ok. cenv_cbn.
  intros ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s7' t3' t4' t5' t6' cur nl rem kc u0 pj tj plj c ops m1
    HN HOPS HREM HCUR HC0 HCN FR ST MU WM HMI.
  pose proof ENV as ENV0.
  unfold env_ok in ENV. cenv_cbn.
  destruct ENV as (HD & HMI0 & ST0 & HLO & SPA & DJ & HPB & HPNZ & RI & DJR).
  unfold fr in FR. cenv_cbn.
  destruct FR as (HKS & F0 & F8 & FK & FIN & FPD & FTX & FPL & FSV).
  pose proof (data_at _ m1 ENV0 MU) as HDAT. cenv_cbn.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  pose proof (bv_unsigned_in_range 64 p) as Rp. unfold bv_modulus in Rp.
  pose proof (bv_unsigned_in_range 64 rem) as Rrem. unfold bv_modulus in Rrem.
  pose proof (bv_unsigned_in_range 64 cur) as Rcur. unfold bv_modulus in Rcur.
  pose proof ST as (Hlo0 & _).
  assert (Hp1 : 0 < bv_unsigned p) by (apply HPNZ; lia).
  change (2 ^ Z.of_N 64) with (2 ^ 64) in Rsp, Rp, Rrem, Rcur.
  clear HD RI.
  (* 0x13368-0x13384: op = fuzz_u8(&in); the trap edge needs cur + 1 <=u 1 *)
  do 5 zstep.
  if_cases T0; [ | refute_trap T0 ].
  zstep.
  match goal with H : bytes_at rsegs ?mm (bv_unsigned p) data |- _ =>
    assert (HB0 : ov_read_bytes rsegs mm cur 1 = Some [nth (Z.to_nat c) data (Z_to_bv 8 0)])
    by (rewrite <- (Z_to_bv_bv_unsigned cur), HCUR; apply (bytes_at_byte mm (bv_unsigned p) data c); [exact H | lia]) end.
  zstep. clear HB0 T0.
  pose proof (bv_unsigned_in_range 8 (nth (Z.to_nat c) data (Z_to_bv 8 0))) as Rb.
  change (bv_modulus 8) with 256 in Rb.
  remember (nth (Z.to_nat c) data (Z_to_bv 8 0)) as b eqn:Eb. clear Eb.
  (* 0x13388-0x13394: memset(&k, 0, 184) *)
  do 4 zstep.
  destruct (rw_cells_forget rsegs _ _ _ FK) as [jk FK0]. rewrite HKS in FK0. clear FK.
  assert (U384 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -384)) = bv_unsigned sp + -384) by (apply unsigned_lit; lia).
  assert (U184 : bv_unsigned (Z_to_bv 64 184) = 184) by reflexivity.
  call MEMS.
  { rewrite U384, U184. exact FK0. }
  { exact HMI. }
  rewrite U384 in POST. apply head_zero in POST. destruct POST as (R1 & R2 & R3).
  replace (bv_unsigned sp + -384 + 76) with (bv_unsigned sp + -308) in R2 by lia.
  replace (bv_unsigned sp + -384 + 140) with (bv_unsigned sp + -244) in R3 by lia.
  unfold hz_pre in R1. unfold hz_post in R3.
  clear U184 U384.
  (* 0x13398-0x133d4: kind = op % 15, i = op / 15 % 3 by the two magic multiplies *)
  do 16 zstep.
  remember (bv_unsigned b) as op eqn:Eop. clear Eop.
  clean_op op Rb.
  assert (Kr : 0 <= op mod 15 <= 14) by (pose proof (Z.mod_pos_bound op 15); lia).
  assert (Ir : 0 <= op / 15 mod 3 <= 2) by (pose proof (Z.mod_pos_bound (op / 15) 3); lia).
  remember (op mod 15) as kind eqn:Ekind. remember (op / 15 mod 3) as i eqn:Ei. clear Ekind Ei.
  (* 0x133d8-0x133e8: k.kind, the DESK array-base trap (4 * i <= 8), DESK[i] *)
  zstep. zstep.
  if_cases T1; [ | refute_trap T1 ].
  zstep.
  match goal with HM : mem_inv rsegs ?mm |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (codec_DESK_read mm i HM ltac:(lia)) as HDK end.
  unfold wa, CODEC_DESK in HDK.
  zstep. clear HDK.
  rewrite (sx32_small i) by lia.
  (* 0x133ec: diginet_personality_of(DESK[i]) *)
  zstep.
  eapply evt_cut; [ apply PERSOF | ].
  intros ms' [a1p ->]. fix_ret.
  rewrite (unsigned_lit i) by lia.
  (* 0x133f0-0x13408: k.p, the SPEC_DESK array-base trap (8 * i <= 16), SPEC_DESK[i] from .data.rel.ro *)
  zstep.
  replace (Z.shiftl i 3) with (8 * i) by (rewrite Z.shiftl_mul_pow2 by lia; change (2 ^ 3) with 8; lia).
  zstep. zstep.
  if_cases T2; [ | refute_trap T2 ].
  zstep. zstep.
  match goal with MUq : munch _ m ?mm |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (codec_SPEC_DESK_read mm i (relro_at _ mm ENV0 MUq) ltac:(lia)) as HSD end.
  unfold wa, CODEC_SPEC_DESK in HSD.
  zstep. clear HSD.
  rewrite (sdesk_nth i) by lia.
  (* 0x1340c-0x1341c: k.desk, then memset(&k.before, 0xa5, 64) *)
  do 5 zstep.
  assert (U308 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -308)) = bv_unsigned sp + -308) by (apply unsigned_lit; lia).
  assert (U64 : bv_unsigned (Z_to_bv 64 64) = 64) by reflexivity.
  call MEMS.
  { rewrite U308, U64. exact R2. }
  { assumption. }
  rewrite U308 in POST. clear U308 U64.
  (* 0x13420-0x13428: the switch bound; kind 14 is the default 0x13b68, kinds 0-13 go through T1 *)
  zstep.
  rewrite (sx32_small kind) by lia.
  replace (bv_unsigned sp + -308) with (bv_unsigned sp + -384 + 76) in POST by lia.
  replace (bv_unsigned sp + -244) with (bv_unsigned sp + -384 + 140) in R3 by lia.
  pose proof (head_rec _ _ kind i R1 POST R3) as RK. clear R1 POST R3.
  specialize (RD kind i ltac:(lia) ltac:(lia)). unfold rd_ok in RD. cenv_cbn.
  zstep. zstep.
  if_cases KB.
  - zify_cond KB.
    assert (kind = 14) by lia. subst kind.
    change (Z_to_bv 64 80744) with (Z_to_bv 64 (pc_rd 14)).
    eapply RD with (c := c + 1) (cur := Z_to_bv 64 (bv_unsigned cur + 1))
                   (rem := Z_to_bv 64 (bv_unsigned rem + -1)) (ops := ops).
    all: first [ lia
               | (rewrite unsigned_lit by lia; lia)
               | (unfold fr; cenv_cbn;
                  exact (conj eq_refl (conj F0 (conj F8 (conj RK (conj FIN (conj FPD (conj FTX (conj FPL FSV)))))))))
               | eassumption ].
  - zify_cond KB.
    zstep.
    replace (Z.shiftl kind 2) with (4 * kind) by (rewrite Z.shiftl_mul_pow2 by lia; change (2 ^ 2) with 4; lia).
    zstep. zstep. zstep.
    match goal with HM : mem_inv rsegs ?mm |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (codec_T1_read mm kind HM ltac:(lia)) as HT end.
    pose proof (codec_T1_sx kind ltac:(lia)) as SX.
    pose proof (codec_T1_entry kind ltac:(lia)) as [EN _].
    rewrite (t1_pc kind) in HT, SX, EN by lia.
    unfold wa, CODEC_T1 in HT, SX, EN.
    zstep. clear HT. rewrite SX. clear SX.
    zstep.
    replace (pc_rd kind - 66628 + 66628) with (pc_rd kind) by lia.
    zstep.
    destruct (pc_rd_range kind ltac:(lia)) as [PR PE].
    rewrite (ret_pc_even (pc_rd kind) PR PE).
    eapply RD with (c := c + 1) (cur := Z_to_bv 64 (bv_unsigned cur + 1))
                   (rem := Z_to_bv 64 (bv_unsigned rem + -1)) (ops := ops).
    all: first [ lia
               | (rewrite unsigned_lit by lia; lia)
               | (unfold fr; cenv_cbn;
                  exact (conj eq_refl (conj F0 (conj F8 (conj RK (conj FIN (conj FPD (conj FTX (conj FPL FSV)))))))))
               | eassumption ].
Qed.
