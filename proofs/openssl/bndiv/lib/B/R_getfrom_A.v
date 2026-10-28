(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Lib Require Import Tac ImageA Arr Walk SysStep ITree.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Malloc Require Import MallocKit_AB.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Import Layout. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.A Require Import Shadow. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Import R_small R_m2s R_thread R_cache_defs R_sizeclass R_prim_defs R_mmapfixed R_popfree R_getfrom.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
Local Definition zal (k x r : Z) : Prop := (x mod k = r)%Z.
Local Lemma zal_ex : forall k x r : Z, (0 < k)%Z -> (x mod k = r)%Z -> exists q, x = (k * q + r)%Z.
Proof. intros k x r Hk H. exists (x / k)%Z. rewrite <- H. apply Z.div_mod. lia. Qed.
Local Ltac zlit x := lazymatch x with Zpos _ => idtac | Z0 => idtac | Zneg _ => idtac end.
Local Ltac zget_mod t :=
  lazymatch type of t with
  | (?x mod ?k = ?r)%Z => let H' := fresh "Hzm" in pose proof t as H'
  | ?A /\ ?B => first [ zget_mod constr:(proj1 t) | zget_mod constr:(proj2 t) ]
  end.
Local Ltac zhide :=
  repeat match goal with
  | H : context [(?x mod ?k)%Z] |- _ => zlit x; zlit k; let v := eval cbv in (x mod k)%Z in change (x mod k)%Z with v in H
  end;
  repeat match goal with
  | H : (?x mod ?k = ?r)%Z |- _ =>
      let q := fresh "zq" in let Hq := fresh "Hzq" in
      destruct (zal_ex k x r (eq_refl : (0 < k)%Z) H) as [q Hq]; change (zal k x r) in H
  | H : context [(?x mod ?k = ?r)%Z] |- _ =>
      lazymatch type of H with (_ mod _ = _)%Z => fail | _ => idtac end;
      (try zget_mod H); change (x mod k = r)%Z with (zal k x r) in H
  end;
  repeat match goal with
  | H : context [(2 ^ ?k)%Z] |- _ => let T := type of H in zify_arith_prop T;
      let v := eval cbv in (2 ^ k)%Z in lazymatch v with Zpos _ => change (2 ^ k)%Z with v in H end
  end.
(* [comment removed for export] *)
Local Definition zidle (P : Prop) : Prop := P.
Local Ltac zidle1 H := let T := type of H in change (zidle T) in H.
Local Ltac zidle_nsp H A sp := lazymatch A with context [bv_unsigned sp] => fail | _ => zidle1 H end.
Local Ltac zidle_begin sp n MUz WMz :=
  lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?m _) =>
    pose proof (munch_refl [(bv_unsigned sp - n, bv_unsigned sp)]%Z m) as MUz; pose proof (wmono_refl segs m) as WMz;
    repeat match goal with
    | H : rw_cells segs m ?A _ |- _ => zidle_nsp H A sp
    | H : ro_cells segs m ?A _ |- _ => zidle_nsp H A sp
    | H : u8arr segs m ?A _ |- _ => zidle_nsp H A sp
    | H : u32arr segs m ?A _ |- _ => zidle_nsp H A sp
    | H : u64arr segs m ?A _ |- _ => zidle_nsp H A sp
    | H : bytes_at segs m ?A _ |- _ => zidle_nsp H A sp
    | H : u8ro segs m ?A _ |- _ => zidle_nsp H A sp
    end
  end.
Local Ltac zidle_end MUz WMz :=
  lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch type of MUz with munch _ ?m _ =>
      try unfold zidle in *; transport_after_call segs m mm MUz WMz; clear MUz WMz end end.
(* [comment removed for export] *)
Local Ltac zidle_end_m m :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch goal with MU : munch _ m mm, WM : wmono _ m mm |- _ =>
      unfold zidle in *; transport_after_call bsegs m mm MU WM end end.
Open Scope bv_scope.
Notation mem := (word -> option byte).

Definition gfa_retP : Z := 0x19af94.

(* [comment removed for export] *)
Definition gfa_A_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (SB c R stat CH n muser msz lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a6' t3' t4' t5' t6' : word) (m' : mem) (junk : list byte),
    ms' = MSsvc (mfi_regs (Z_to_bv 64 pfa_retB1) (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (bv_unsigned sp - 128)) - 64)) gp tp
                          t0' t1' t2' a6' (rb SB c + muser) msz (Z_to_bv 64 str_regiondata) (Z_to_bv 64 (ClassSize c))
                          (Z_to_bv 64 INST) (Z_to_bv 64 1152921504606846976) (Z_to_bv 64 1500)
                          (Z_to_bv 64 16140901064495857663) s10 s11 t3' t4' t5' t6') F
                (Z_to_bv 64 mmap_ecall_pc) (Z_to_bv 64 222) fc None m' (seg_rom bsegs)
    /\ munch [(R, R + 8); (bv_unsigned sp - 592, bv_unsigned sp)]%Z m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ pfa_cells1 m' (Z_to_bv 64 (bv_unsigned sp - 128)) (Z_to_bv 64 gfa_retP) (Z_to_bv 64 R) (Z_to_bv 64 INST)
         (Z_to_bv 64 (R + 8)) (Z_to_bv 64 2305843009213693952) (Z_to_bv 64 (fa SB c)) (Z_to_bv 64 CH) (Z_to_bv 64 n)
         R stat (rb SB c) muser msz lo
    /\ rw_cells bsegs m' (bv_unsigned sp - 128)
         [CB 24 junk; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ ri_lock m' R 1152921504606846976.

Lemma gfa_A_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (ACEIL SB c R stat CH n nfree mfa auser muser lo : Z),
  SB_ok ACEIL SB -> (1 <= c <= 31)%Z -> R = rinfo (RIS_of SB) c ->
  (1 <= n <= 16)%Z -> (0 <= nfree < n)%Z ->
  (0 <= auser <= muser)%Z -> (muser < auser + (n - nfree) * ClassSize c)%Z -> (muser mod 2^18 = 0)%Z ->
  (muser + umap_size auser muser (n - nfree) (ClassSize c) <= 0xE0000000)%Z -> (0 <= mfa < 2^64)%Z ->
  inst_cells SB m -> ri_lock m R 0 -> ri_core m R nfree mfa auser muser -> mm_gcells m ->
  stk bsegs m lo (bv_unsigned sp) -> (ACEIL <= lo)%Z -> (kHighShadowEnd + 8 <= lo)%Z -> (lo <= bv_unsigned sp - 592)%Z ->
  (bv_unsigned sp <= 2^47)%Z ->
  mem_inv bsegs m ->
  evt bsegs (gfa_A_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SB c R stat CH n muser
               (umap_size auser muser (n - nfree) (ClassSize c)) lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 INST) (Z_to_bv 64 stat) (Z_to_bv 64 c) (Z_to_bv 64 CH) (Z_to_bv 64 n)
             a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 gfa_entry) fc None m (seg_rom bsegs)).
Proof.
  intros until lo. intros HSB Hc ER Hn Hnf Hau Htot Hmual Hcap Hmfa IC LK RC GC ST HLO HLOH HLO2 HSP MI.
  pose proof HSB as (HSB1 & HSB2 & HSB3 & HSB4).
  pose proof IC as IC0. pose proof GC as GC0.
  eapply gfa_head; try eassumption; [lia|].
  intros m1 junk FR LK1 ST1 MU WM MI1.
  destruct IC0 as (IC1 & IC2). destruct GC0 as (G1 & G2 & G3 & G4 & G5).
  unfold kHighShadowEnd, rinfo, RIS_of, ri_core, i_spacebeg, i_premapped, INST, g_instance in *.
  change (6947736 + 32)%Z with 6947768%Z in IC1. change (6947736 + 56)%Z with 6947792%Z in IC2.
  tr_from0 m MU WM RC. tr_from0 m MU WM IC1. tr_from0 m MU WM IC2.
  tr_from0 m MU WM G1. tr_from0 m MU WM G2. tr_from0 m MU WM G3. tr_from0 m MU WM G4. tr_from0 m MU WM G5.
  clear IC GC.
  apply (munch_weaken _ [(R, R + 8); (bv_unsigned sp - 592, bv_unsigned sp)]%Z) in MU; [| unfold sub_fp; cbn [outside]; intros; lia].
  zhide.
  zstep. zstep. ifT.
  do 6 zstep.
  zstep.
  assert (Esp : bv_unsigned (Z_to_bv 64 (bv_unsigned sp - 128)) = (bv_unsigned sp - 128)%Z).
  { apply unsigned_lit. pose proof (bv_unsigned_in_range 64 sp) as Hr. unfold bv_modulus in Hr. cbn [Z.of_N] in Hr. lia. }
  eapply evt_cut; [eapply pfa_A_spec with (k := (n - nfree)%Z) (nfree := nfree) (mfa := mfa) (ACEIL := ACEIL) (lo := lo)
                     (SB := SB) (auser := auser) (muser := muser) | post_call bsegs m1].
  all: first [ assumption | (unfold rinfo, RIS_of; lia) | lia
             | (unfold inst_cells, i_spacebeg, i_premapped, INST, g_instance; split; assumption)
             | (unfold ri_core; assumption) | (unfold mm_gcells; repeat (split; [assumption|]); assumption)
             | (rewrite ?Esp; unfold kHighShadowEnd; lia) | (rewrite Esp; assumption) | idtac ].
  apply evt_done. unfold gfa_A_post.
  do 10 eexists. split; [reflexivity|].
  split; [exact MU|split; [exact WM|split; [exact MI0|split; [exact POST|split; [eassumption| unfold ri_lock; assumption]]]]].
Qed.
