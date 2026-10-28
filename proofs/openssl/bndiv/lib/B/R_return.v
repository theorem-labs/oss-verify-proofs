(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Lib Require Import Tac ImageA Arr Walk SysStep ITree.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Malloc Require Import MallocKit_AB.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Import Layout. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.A Require Import Shadow. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Import R_small R_m2s R_thread R_cache_defs R_sizeclass R_classid R_prim_defs R_prim_kit R_mmapfixed R_ensurefa R_popfree R_getfrom.
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

Definition rta_entry : Z := 0x19897c.
Definition mrto_entry : Z := 0x198e24.

(* [comment removed for export] *)
Lemma mrto_j34824 : forall ra sp gp tp t0 t1 t2 a0 a2 a3 a4 a5 a6 a7 s4 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m0 m : mem) (s0o s1o s2o s3o s4o s5o s6o s7o : word) (ACEIL SB c R mapper nfree mfa auser muser : Z)
    (rand : word) (exh : byte) (pad : list byte) (nalloc nfreed r0 r1 r2 r3 lo : Z) junk,
  SB_ok ACEIL SB -> (1 <= c <= 31)%Z -> R = (SB + 2^37 + 128 * c)%Z ->
  (0 <= nfree < 2^32)%Z -> (0 <= nfreed < 2^64)%Z -> (0 <= r0 < 2^64)%Z ->
  rw_cells bsegs m (bv_unsigned sp - 80) [CB 8 junk; C8 s7o; C8 s6o; C8 s5o; C8 s4o; C8 s3o; C8 s2o; C8 s1o; C8 s0o; C8 ra] ->
  rw_cells bsegs m 6947768 [C8 (Z_to_bv 64 SB); C4 (Z_to_bv 64 0xffffffff); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 (SB + 2^37))] ->
  rw_cells bsegs m 6163640 [C8 (Z_to_bv 64 7550112)] -> rw_cells bsegs m 7550112 [C8 (Z_to_bv 64 4096)] ->
  rw_cells bsegs m (R + 16) [C8 (Z_to_bv 64 nfree); C8 (Z_to_bv 64 mfa); C8 (Z_to_bv 64 auser); C8 (Z_to_bv 64 0);
                             C8 (Z_to_bv 64 muser); C8 (Z_to_bv 64 0)] ->
  rw_cells bsegs m (R + 64) [C4 rand; C1 exh; CB 3 pad; C8 (Z_to_bv 64 nalloc); C8 (Z_to_bv 64 nfreed);
                             C8 (Z_to_bv 64 r0); C8 (Z_to_bv 64 r1); C8 (Z_to_bv 64 r2); C8 (Z_to_bv 64 r3)] ->
  stk bsegs m lo (bv_unsigned sp - 80) -> (ACEIL <= lo)%Z -> (17594333495295 + 8 <= lo)%Z -> (lo <= bv_unsigned sp - 80)%Z ->
  (bv_unsigned sp <= 2^47)%Z ->
  munch [(bv_unsigned sp - 80, bv_unsigned sp)]%Z m0 m -> wmono bsegs m0 m -> mem_inv bsegs m ->
  evt bsegs (frame_post ra sp gp tp s0o s1o s2o s3o s4o s5o s6o s7o s8 s9 s10 s11 F fc 4096
               [(bv_unsigned sp - 80, bv_unsigned sp)]%Z lo m0)
    (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp - 80)) gp tp t0 t1 t2 (Z_to_bv 64 mapper) (Z_to_bv 64 c) a0 (Z_to_bv 64 (c ≪ 7))
             a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (ClassSize c)) (Z_to_bv 64 INST) s4 (Z_to_bv 64 0) (Z_to_bv 64 (SB + 137438953472)) s7
             s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x198ea0) fc None m (seg_rom bsegs)).
Proof.
  intros until junk. intros HSB Hc ER Hnf Hnfd Hr0 FR IC1 G1 G3 RC RT ST HLO HLOH HLO2 HSP MU WM MI.
  pose proof HSB as (HSB1 & HSB2 & HSB3 & HSB4).
  pose proof (ClassSize_range c Hc) as HCS. unfold INST, g_instance.
  zhide.
  do 4 zstep.
  replace (SB + 137438953472 + c ≪ 7)%Z with R by (rewrite ER, Z.shiftl_mul_pow2 by lia; lia).
  zstep. ifF.
  do 2 zstep.
  zstep. if_cases K1.
  - (* [comment removed for export] *)
    do 4 zstep. zstep. if_cases K2.
    + (* [comment removed for export] *)
      do 10 zstep.
      replace (bv_unsigned sp - 80 + 80)%Z with (bv_unsigned sp) by lia. rewrite Z_to_bv_bv_unsigned.
      release_frame FR ST (bv_unsigned sp).
      zstep. finish.
    + zstep. ifF.
      zstep. zstep. ifT.
      do 10 zstep.
      replace (bv_unsigned sp - 80 + 80)%Z with (bv_unsigned sp) by lia. rewrite Z_to_bv_bv_unsigned.
      release_frame FR ST (bv_unsigned sp).
      zstep. finish.
  - zstep.
    do 10 zstep.
    replace (bv_unsigned sp - 80 + 80)%Z with (bv_unsigned sp) by lia. rewrite Z_to_bv_bv_unsigned.
    release_frame FR ST (bv_unsigned sp).
    zstep. finish.
Qed.

(* [comment removed for export] *)
Lemma mrto_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (ACEIL SB c R mapper nfree mfa auser muser : Z) (rand : word) (exh : byte)
    (pad : list byte) (nalloc nfreed r0 r1 r2 r3 lo : Z),
  SB_ok ACEIL SB -> (1 <= c <= 31)%Z -> R = rinfo (RIS_of SB) c ->
  (0 <= nfree < 2^32)%Z -> (0 <= nfreed < 2^64)%Z -> (0 <= r0 < 2^64)%Z -> (0 <= mfa < 2^64)%Z -> (0 <= auser < 2^64)%Z ->
  (0 <= muser < 2^64)%Z ->
  inst_cells SB m -> mm_gcells m -> ri_core m R nfree mfa auser muser -> ri_tail m R rand exh pad nalloc nfreed r0 r1 r2 r3 ->
  stk bsegs m lo (bv_unsigned sp) -> (ACEIL <= lo)%Z -> (kHighShadowEnd + 8 <= lo)%Z -> (lo <= bv_unsigned sp - 80)%Z ->
  (bv_unsigned sp <= 2^47)%Z ->
  mem_inv bsegs m ->
  evt bsegs (frame_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc 4096 [(bv_unsigned sp - 80, bv_unsigned sp)]%Z lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 INST) (Z_to_bv 64 mapper) (Z_to_bv 64 c) (Z_to_bv 64 0) a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 mrto_entry) fc None m (seg_rom bsegs)).
Proof.
  intros until lo. intros HSB Hc ER Hnf Hnfd Hr0 Hmfa Hau Hmu IC GC RC RT ST HLO HLOH HLO2 HSP MI.
  pose proof HSB as (HSB1 & HSB2 & HSB3 & HSB4).
  destruct IC as (IC1 & IC2). destruct GC as (G1 & G2 & G3 & G4 & G5).
  move IC1 after G2. move IC2 after IC1.
  unfold i_spacebeg, i_premapped, INST, g_instance, mrto_entry, kHighShadowEnd, rinfo, RIS_of, ri_core, ri_tail in *.
  change (6947736 + 32)%Z with 6947768%Z in IC1. change (6947736 + 56)%Z with 6947792%Z in IC2.
  apply (rwc_recast _ _ _ [C8 (Z_to_bv 64 SB); C4 (Z_to_bv 64 0xffffffff); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 (SB + 2^37))]) in IC1;
    [| cbn; tauto| reflexivity| reflexivity].
  pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl bsegs m) as WM.
  pose proof (ClassSize_range c Hc) as HCS.
  carve_frame 80%nat ST.
  zhide.
  zidle_begin sp 80%Z MUz WMz.
  do 9 zstep.
  zidle_end MUz WMz.
  do 1 zstep.
  do 5 zstep.
  do 2 zstep. zstep.
  replace (bv_unsigned sp + -80)%Z with (bv_unsigned sp - 80)%Z in * by lia.
  destruct (Z.eq_dec c 31) as [E31|N31].
  - subst c. ifT. replace (ClassSize 31) with 64%Z in * by reflexivity.
    do 2 zstep.
    change (Z_to_bv 64 64) with (Z_to_bv 64 (ClassSize 31)).
    eapply (mrto_j34824 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m _ _ _ _ _ _ _ _ _ ACEIL SB 31 _ mapper nfree mfa auser muser
              rand exh pad nalloc nfreed r0 r1 r2 r3 lo);
      try eassumption; try lia.
  - ifF. zstep. zstep.
    destruct (Z.le_gt_cases c 16) as [C16|C17].
    + ifF.
      assert (ES : ClassSize c = (32 * c)%Z).
      { unfold ClassSize. rewrite (proj2 (Z.eqb_neq c 31)) by lia. rewrite (proj2 (Z.leb_le c 16)) by lia. reflexivity. }
      do 2 zstep.
      replace (c ≪ 5)%Z with (ClassSize c) by (rewrite ES, Z.shiftl_mul_pow2 by lia; lia).
      eapply (mrto_j34824 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m _ _ _ _ _ _ _ _ _ ACEIL SB c _ mapper nfree mfa auser muser
                rand exh pad nalloc nfreed r0 r1 r2 r3 lo);
        try eassumption; try lia.
    + ifT.
      do 9 zstep.
      let e := getreg 18%Z in lazymatch e with Z_to_bv 64 ?E => replace E with (size_pfa c) by reflexivity end.
      rewrite size_pfa_ok by lia.
      eapply (mrto_j34824 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m _ _ _ _ _ _ _ _ _ ACEIL SB c _ mapper nfree mfa auser muser
                rand exh pad nalloc nfreed r0 r1 r2 r3 lo);
        try eassumption; try lia.
Qed.

(* [comment removed for export] *)
Fixpoint dest2 (ws chs : list word) (nf cb : Z) (i : nat) : list word :=
  match i with
  | O => ws
  | S j => upd (dest2 ws chs nf cb j) (Z.to_nat nf + j) (sx32 (nth (Z.to_nat cb + j) chs (Z_to_bv 64 0)))
  end.

Lemma dest2_length : forall ws chs nf cb i, length (dest2 ws chs nf cb i) = length ws.
Proof. intros ws chs nf cb i. induction i as [|i IH]; cbn [dest2]; [reflexivity|]. rewrite upd_length. exact IH. Qed.

