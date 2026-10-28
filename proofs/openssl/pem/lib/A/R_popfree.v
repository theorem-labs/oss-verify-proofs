(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac ImageA Arr Walk SysStep ITree.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import MallocKit_AB.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow R_sizeclass.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout R_small R_m2s R_thread R_cache_defs R_classid R_refill_ic R_prim_defs R_mmapfixed.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
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
Local Ltac zidle_begin_rw sp n MUz WMz :=
  lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?m _) =>
    pose proof (munch_refl [(bv_unsigned sp - n, bv_unsigned sp)]%Z m) as MUz; pose proof (wmono_refl segs m) as WMz;
    repeat match goal with
    | H : rw_cells segs m ?A _ |- _ => zidle_nsp H A sp
    | H : u8arr segs m ?A _ |- _ => zidle_nsp H A sp
    | H : u32arr segs m ?A _ |- _ => zidle_nsp H A sp
    | H : u64arr segs m ?A _ |- _ => zidle_nsp H A sp
    | H : bytes_at segs m ?A _ |- _ => zidle_nsp H A sp
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
      unfold zidle in *; transport_after_call asegs m mm MU WM end end.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Open Scope bv_scope.
Notation mem := (word -> option byte).

Definition pfa_entry : Z := 0x1a0024.
Definition pfa_retB1 : Z := 0x1a0144.
Definition str_regiondata : Z := 0x276ab.   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition umap_size (auser muser k size : Z) : Z := round_fa (auser + k * size - muser).

(* [comment removed for export] *)
Definition pfa_frame (m : mem) (sp : word) (ra s0 s1 s2 s3 s4 s5 s6 : word) : Prop :=
  rw_cells asegs m (bv_unsigned sp - 64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

(* [comment removed for export] *)
Definition pfa_cells1 (m : mem) (sp ra s0 s1 s2 s3 s4 s5 s6 : word) (R stat rbeg muser msz lo : Z) : Prop :=
  rmap_frame m (Z_to_bv 64 (bv_unsigned sp - 64)) (Z_to_bv 64 pfa_retB1) (Z_to_bv 64 R) (Z_to_bv 64 stat) (Z_to_bv 64 rbeg)
            (Z_to_bv 64 msz) (Z_to_bv 64 (rbeg + muser))
  /\ pfa_frame m sp ra s0 s1 s2 s3 s4 s5 s6
  /\ stk asegs m lo (bv_unsigned (Z_to_bv 64 (bv_unsigned sp - 64)) - 128)
  /\ mm_gcells m.

Definition pfa_A_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (R stat rbeg size muser msz lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a6' t3' t4' t5' t6' : word) (m' : mem),
    ms' = MSsvc (mfi_regs (Z_to_bv 64 pfa_retB1) (Z_to_bv 64 (bv_unsigned sp - 64)) gp tp t0' t1' t2' a6' (rbeg + muser) msz
                          (Z_to_bv 64 str_regiondata) (Z_to_bv 64 size) (Z_to_bv 64 INST) s7 s8 s9 s10 s11 t3' t4' t5' t6') F
                (Z_to_bv 64 mmap_ecall_pc) (Z_to_bv 64 222) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 464, bv_unsigned sp)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ pfa_cells1 m' sp ra s0 s1 s2 s3 s4 s5 s6 R stat rbeg muser msz lo.

(* [comment removed for export] *)
Lemma umap_code : forall total muser, (0 <= muser < total)%Z -> (total < 2^63)%Z ->
  (Z.land (Z.land (total + Z.lxor muser 18446744073709551615) 18446744073709551615)
          18446744073709289472 + 262144 = round_fa (total - muser))%Z.
Proof.
  intros total muser H1 H2.
  rewrite lnot_mod64 by lia.
  assert (E2 : ((Z.lnot muser) mod 2^64 = 2^64 - muser - 1)%Z).
  { unfold Z.lnot. symmetry. apply Z.mod_unique with (-1)%Z; lia. }
  rewrite E2.
  assert (E3 : Z.land (total + (2^64 - muser - 1)) 18446744073709551615 = (total - muser - 1)%Z).
  { change 18446744073709551615%Z with (Z.ones 64). rewrite Z.land_ones by lia. symmetry. apply Z.mod_unique with 1%Z; lia. }
  rewrite E3, land_famask by lia. unfold round_fa.
  replace (total - muser + 0x3ffff)%Z with ((total - muser - 1) + 1 * 262144)%Z by lia.
  rewrite Z.div_add by lia. lia.
Qed.

(* [comment removed for export] *)
Lemma pfa_j36a08 : forall ra sp gp tp t0 t1 t2 a1 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m0 m : mem) (s0o s1o s2o s3o s4o s5o s6o : word) (ACEIL SB c R k nfree mfa auser muser stat lo : Z),
  SB_ok ACEIL SB -> (1 <= c <= 31)%Z -> R = rinfo (RIS_of SB) c ->
  (0 <= auser <= muser)%Z -> (muser < auser + k * ClassSize c)%Z -> (1 <= k <= 64)%Z -> (muser mod 2^18 = 0)%Z ->
  (muser + umap_size auser muser k (ClassSize c) <= 0xE0000000)%Z ->
  (0 <= nfree < 2^64)%Z -> (0 <= mfa < 2^64)%Z ->
  pfa_frame m sp ra s0o s1o s2o s3o s4o s5o s6o ->
  rw_cells asegs m (R + 16) [C8 (Z_to_bv 64 nfree); C8 (Z_to_bv 64 mfa); C8 (Z_to_bv 64 auser); C8 (Z_to_bv 64 0);
                             C8 (Z_to_bv 64 muser); C8 (Z_to_bv 64 0)] ->
  mm_gcells m -> rw_cells asegs m i_premapped [C1 (Z_to_bv 8 0)] ->
  stk asegs m lo (bv_unsigned sp - 64) -> (ACEIL <= lo)%Z -> (kHighShadowEnd + 8 <= lo)%Z -> (lo <= bv_unsigned sp - 464)%Z ->
  (bv_unsigned sp <= 2^47)%Z ->
  munch [(bv_unsigned sp - 464, bv_unsigned sp)]%Z m0 m -> wmono asegs m0 m -> mem_inv asegs m ->
  evt asegs (pfa_A_post ra sp gp tp s0o s1o s2o s3o s4o s5o s6o s7 s8 s9 s10 s11 F fc R stat (rb SB c) (ClassSize c) muser
               (umap_size auser muser k (ClassSize c)) lo m0)
    (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp - 64)) gp tp t0 t1 t2 (Z_to_bv 64 R) (Z_to_bv 64 stat) (Z_to_bv 64 INST) a1
             (Z_to_bv 64 c) (Z_to_bv 64 auser) (Z_to_bv 64 k) a5 a6 a7 (Z_to_bv 64 (rb SB c))
             (Z_to_bv 64 (auser + k * ClassSize c)) (Z_to_bv 64 muser) (Z_to_bv 64 (ClassSize c)) s6 s7 s8 s9 s10 s11
             t3 t4 t5 t6)
        F (Z_to_bv 64 0x1a00c8) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros HSB Hc ER Hau Htot Hk Hmual Hcap Hnf Hmfa FR RC GC IC2 ST HLO HLOH HLO2 HSP MU WM MI.
  destruct HSB as (HSB1 & HSB2 & HSB3 & HSB4). destruct GC as (G1 & G2 & G3 & G4 & G5).
  move IC2 after G2.
  unfold rinfo, RIS_of, i_premapped, INST, g_instance, kHighShadowEnd, pfa_frame in *.
  change (6722776 + 56)%Z with 6722832%Z in IC2.
  pose proof (ClassSize_range c Hc) as HCS.
  assert (Hks : (k * ClassSize c <= 2^22)%Z) by nia.
  pose proof (round_fa_ge (auser + k * ClassSize c - muser) ltac:(lia)) as RG.
  pose proof (round_fa_aligned (auser + k * ClassSize c - muser)) as RA.
  unfold umap_size in *.
  do 7 zstep.
  rewrite (umap_code (auser + k * ClassSize c) muser) by lia.
  remember (round_fa (auser + k * ClassSize c - muser)) as msz eqn:Emsz.
  do 6 zstep. ifF.
  do 3 zstep. ifT.
  do 5 zstep.
  replace (muser + rb SB c)%Z with (rb SB c + muser)%Z by lia.
  zstep.
  assert (Esp : bv_unsigned (Z_to_bv 64 (bv_unsigned sp - 64)) = (bv_unsigned sp - 64)%Z).
  { apply unsigned_lit. pose proof (bv_unsigned_in_range 64 sp) as Hr. unfold bv_modulus in Hr. cbn [Z.of_N] in Hr. lia. }
  call (rmap_A_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ (rb SB c + muser) msz _ lo).
  1:{ unfold rb. lia. }
  1:{ unfold rb. Z.div_mod_to_equations. lia. }
  1:{ lia. }
  1:{ Z.div_mod_to_equations. lia. }
  1:{ unfold rb. lia. }
  1:{ rewrite unsigned_lit by lia. lia. }
  1:{ unfold mm_gcells. repeat (split; [assumption|]). assumption. }
  all: rewrite ?Esp; try lia; try assumption.
  apply evt_done. unfold pfa_A_post, pfa_cells1, pfa_frame.
  do 9 eexists. split; [reflexivity|].
  split; [exact MU|split; [exact WM|split; [exact MI0|split; [exact PC|split; [exact FR|split; [exact PC0|exact POST]]]]]].
Qed.

Lemma rwc_recast : forall m A cs cs',
  rw_cells asegs m A cs -> cells_wf cs' -> cells_bytes cs' = cells_bytes cs -> cells_size cs' = cells_size cs ->
  rw_cells asegs m A cs'.
Proof. intros m A cs cs' [[Hwf Hb] Hw] Hwf' Eb Es. split; [split; [exact Hwf'| rewrite Eb; exact Hb] | rewrite Es; exact Hw]. Qed.

(* [comment removed for export] *)
Definition size_pfa (c : Z) : Z :=
  (Z.land (Z.land (Z.shiftr (bv_signed (Z_to_bv 64 (Z.shiftl c 63))) 63) 18446744073709551615)
          (Z.shiftr (Z.land (Z.shiftl 512 (Z.land (Z.shiftr (c + -16) 1) 63)) 18446744073709551615) 1)
   + Z.shiftl 512 (Z.land (Z.shiftr (c + -16) 1) 63))%Z.
Lemma size_pfa_ok : forall c, (17 <= c <= 30)%Z -> size_pfa c = ClassSize c.
Proof. intros c Hc. exact (brute_eq size_pfa ClassSize 17 30 ltac:(vm_compute; reflexivity) c Hc). Qed.

(* [comment removed for export] *)
Lemma pfa_j36a04 : forall ra sp gp tp t0 t1 t2 a1 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m0 m : mem) (s0o s1o s2o s3o s4o s5o s6o : word) (ACEIL SB c R k nfree mfa auser muser stat lo : Z),
  SB_ok ACEIL SB -> (1 <= c <= 31)%Z -> R = rinfo (RIS_of SB) c ->
  (0 <= auser <= muser)%Z -> (muser < auser + k * ClassSize c)%Z -> (1 <= k <= 64)%Z -> (muser mod 2^18 = 0)%Z ->
  (muser + umap_size auser muser k (ClassSize c) <= 0xE0000000)%Z ->
  (0 <= nfree < 2^64)%Z -> (0 <= mfa < 2^64)%Z ->
  pfa_frame m sp ra s0o s1o s2o s3o s4o s5o s6o ->
  rw_cells asegs m (R + 16) [C8 (Z_to_bv 64 nfree); C8 (Z_to_bv 64 mfa); C8 (Z_to_bv 64 auser); C8 (Z_to_bv 64 0);
                             C8 (Z_to_bv 64 muser); C8 (Z_to_bv 64 0)] ->
  mm_gcells m -> rw_cells asegs m i_premapped [C1 (Z_to_bv 8 0)] ->
  rw_cells asegs m 6722808 [C8 (Z_to_bv 64 SB); C4 (Z_to_bv 64 0xffffffff); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 (RIS_of SB))] ->
  stk asegs m lo (bv_unsigned sp - 64) -> (ACEIL <= lo)%Z -> (kHighShadowEnd + 8 <= lo)%Z -> (lo <= bv_unsigned sp - 464)%Z ->
  (bv_unsigned sp <= 2^47)%Z ->
  munch [(bv_unsigned sp - 464, bv_unsigned sp)]%Z m0 m -> wmono asegs m0 m -> mem_inv asegs m ->
  evt asegs (pfa_A_post ra sp gp tp s0o s1o s2o s3o s4o s5o s6o s7 s8 s9 s10 s11 F fc R stat (rb SB c) (ClassSize c) muser
               (umap_size auser muser k (ClassSize c)) lo m0)
    (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp - 64)) gp tp t0 t1 t2 (Z_to_bv 64 R) (Z_to_bv 64 stat) (Z_to_bv 64 INST) a1
             (Z_to_bv 64 c) (Z_to_bv 64 auser) (Z_to_bv 64 k) a5 a6 a7 (Z_to_bv 64 (rb SB c))
             (Z_to_bv 64 (auser + k * ClassSize c)) (Z_to_bv 64 muser) (Z_to_bv 64 (ClassSize c)) s6 s7 s8 s9 s10 s11
             t3 t4 t5 t6)
        F (Z_to_bv 64 0x1a00c4) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros HSB Hc ER Hau Htot Hk Hmual Hcap Hnf Hmfa FR RC GC IC2 IC1 ST HLO HLOH HLO2 HSP MU WM MI.
  unfold INST, g_instance in *.
  assert (Hmu : (muser <= 0xE0000000)%Z).
  { pose proof (round_fa_ge (auser + k * ClassSize c - muser) ltac:(lia)) as RG. unfold umap_size in Hcap. lia. }
  zstep.
  destruct (Z.eq_dec muser 0) as [M0|M0].
  - subst muser. ifT.
    zstep. zstep. ifT.
    do 2 zstep.
    eapply pfa_j36a08 with (nfree := nfree) (mfa := mfa) (ACEIL := ACEIL); eassumption.
  - ifF.
    eapply pfa_j36a08 with (nfree := nfree) (mfa := mfa) (ACEIL := ACEIL); eassumption.
Qed.

Lemma pfa_A_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (ACEIL SB c R k nfree mfa auser muser stat lo : Z),
  SB_ok ACEIL SB -> (1 <= c <= 31)%Z -> R = rinfo (RIS_of SB) c ->
  (0 <= auser <= muser)%Z -> (muser < auser + k * ClassSize c)%Z -> (1 <= k <= 64)%Z -> (muser mod 2^18 = 0)%Z ->
  (muser + umap_size auser muser k (ClassSize c) <= 0xE0000000)%Z ->
  (0 <= nfree < 2^64)%Z -> (0 <= mfa < 2^64)%Z ->
  inst_cells SB m -> ri_core m R nfree mfa auser muser -> mm_gcells m ->
  stk asegs m lo (bv_unsigned sp) -> (ACEIL <= lo)%Z -> (kHighShadowEnd + 8 <= lo)%Z -> (lo <= bv_unsigned sp - 464)%Z ->
  (bv_unsigned sp <= 2^47)%Z ->
  mem_inv asegs m ->
  evt asegs (pfa_A_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R stat (rb SB c) (ClassSize c) muser
               (umap_size auser muser k (ClassSize c)) lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 INST) (Z_to_bv 64 stat) (Z_to_bv 64 c) (Z_to_bv 64 R) (Z_to_bv 64 k)
             a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pfa_entry) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros HSB Hc ER Hau Htot Hk Hmual Hcap Hnf Hmfa IC RC GC ST HLO HLOH HLO2 HSP MI.
  pose proof HSB as (HSB1 & HSB2 & HSB3 & HSB4).
  destruct IC as (IC1 & IC2). unfold ri_core in RC. destruct GC as (G1 & G2 & G3 & G4 & G5).
  move IC1 after G2. move IC2 after IC1.
  unfold i_spacebeg, i_premapped, INST, g_instance, pfa_entry, kHighShadowEnd, rinfo, RIS_of in *.
  change (6722776 + 32)%Z with 6722808%Z in IC1. change (6722776 + 56)%Z with 6722832%Z in IC2.
  apply (rwc_recast _ _ _ [C8 (Z_to_bv 64 SB); C4 (Z_to_bv 64 0xffffffff); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 (RIS_of SB))]) in IC1;
    [| cbn; tauto| reflexivity| reflexivity].
  pose proof (munch_refl [(bv_unsigned sp - 464, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  pose proof (ClassSize_range c Hc) as HCS.
  assert (Hks : (k * ClassSize c <= 2^22)%Z) by nia.
  pose proof (round_fa_ge (auser + k * ClassSize c - muser) ltac:(lia)) as RG.
  apply box in Hau, Htot, Hk, Hmual, Hcap, Hnf, Hmfa, HSB2, HSB4, HSB, HCS, Hks, RG.
  carve_frame 64%nat ST.
  zidle_begin_rw sp 64%Z MUz WMz.
  do 8 zstep.
  do 1 zstep.
  zidle_end MUz WMz.
  do 5 zstep.
  apply unbox in Hau, Htot, Hk, Hmual, Hcap, Hnf, Hmfa, HSB2, HSB4, HSB, HCS, Hks, RG.
  unfold umap_size in Hcap.
  zstep.
  destruct (Z.eq_dec c 31) as [E31|N31].
  - (* [comment removed for export] *)
    subst c. ifT.
    replace (ClassSize 31) with 64%Z in * by reflexivity.
    do 7 zstep. ifT.
    replace (SB + 31 ≪ 32)%Z with (rb SB 31) by (unfold rb; rewrite Z.shiftl_mul_pow2 by lia; lia).
    replace (auser + 64 * k)%Z with (auser + k * 64)%Z by lia.
    eapply pfa_j36a04 with (nfree := nfree) (mfa := mfa) (ACEIL := ACEIL); try eassumption.
    unfold mm_gcells. repeat (split; [assumption|]). assumption.
  - ifF.
    zstep. zstep. destruct (Z.le_gt_cases c 16) as [C16|C17].
    + ifF.
      assert (ES : ClassSize c = (32 * c)%Z).
      { unfold ClassSize. rewrite (proj2 (Z.eqb_neq c 31)) by lia. rewrite (proj2 (Z.leb_le c 16)) by lia. reflexivity. }
      do 7 zstep.
      assert (E5 : (c ≪ 5)%Z = ClassSize c) by (rewrite ES, Z.shiftl_mul_pow2 by lia; lia).
      assert (E5' : Z.land (c ≪ 5) 18446744073709551615 = ClassSize c).
      { rewrite E5. change 18446744073709551615%Z with (Z.ones 64). rewrite Z.land_ones by lia. rewrite Z.mod_small by lia. lia. }
      rewrite E5', E5. ifT.
      replace (SB + c ≪ 32)%Z with (rb SB c) by (unfold rb; rewrite Z.shiftl_mul_pow2 by lia; lia).
      replace (auser + ClassSize c * k)%Z with (auser + k * ClassSize c)%Z by lia.
      eapply pfa_j36a04 with (nfree := nfree) (mfa := mfa) (ACEIL := ACEIL); try eassumption.
      unfold mm_gcells. repeat (split; [assumption|]). assumption.
    + ifT.
      do 9 zstep.
      let e := getreg 21%Z in lazymatch e with Z_to_bv 64 ?E => replace E with (size_pfa c) by reflexivity end.
      rewrite size_pfa_ok by lia.
      do 6 zstep.
      assert (E5' : Z.land (ClassSize c) 18446744073709551615 = ClassSize c).
      { change 18446744073709551615%Z with (Z.ones 64). rewrite Z.land_ones by lia. rewrite Z.mod_small by lia. lia. }
      rewrite ?E5'. ifF.
      replace (SB + c ≪ 32)%Z with (rb SB c) by (unfold rb; rewrite Z.shiftl_mul_pow2 by lia; lia).
      replace (auser + ClassSize c * k)%Z with (auser + k * ClassSize c)%Z by lia.
      eapply pfa_j36a04 with (nfree := nfree) (mfa := mfa) (ACEIL := ACEIL); try eassumption.
      unfold mm_gcells. repeat (split; [assumption|]). assumption.
Qed.
