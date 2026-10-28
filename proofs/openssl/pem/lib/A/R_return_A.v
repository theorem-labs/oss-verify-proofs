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
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout R_small R_m2s R_thread R_cache_defs R_classid R_prim_defs R_prim_kit R_mmapfixed R_ensurefa R_popfree R_getfrom R_return R_return_T.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
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
      unfold zidle in *; transport_after_call asegs m mm MU WM end end.
Open Scope bv_scope.
Notation mem := (word -> option byte).

Definition rta_retE : Z := 0x19db24.

(* [comment removed for export] *)
Lemma rta_fast_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (ACEIL SB c R mapper stat CH cb n nfree mfa auser muser : Z) (ws chs : list word)
    (rand : word) (exh : byte) (pad : list byte) (nalloc nfreed r0 r1 r2 r3 lo : Z),
  SB_ok ACEIL SB -> (1 <= c <= 31)%Z -> R = rinfo (RIS_of SB) c ->
  (1 <= n <= 16)%Z -> (0 <= cb /\ cb + n <= 16)%Z -> (0 <= nfree < 2^32)%Z ->
  (4 * (nfree + n) <= mfa)%Z -> (4 * Z.of_nat (length ws) = mfa)%Z -> (mfa <= 2^29)%Z -> length chs = 16%nat ->
  (0 < CH /\ CH + 64 <= ACEIL /\ (CH + 64 <= SB \/ SB + 2^37 + 4096 <= CH))%Z ->
  (0 <= nfreed < 2^64 /\ 0 <= r0 < 2^64 /\ 0 <= auser < 2^64 /\ 0 <= muser < 2^64)%Z ->
  inst_cells SB m -> mm_gcells m -> ri_lock m R 0 -> ri_core m R nfree mfa auser muser ->
  ri_tail m R rand exh pad nalloc nfreed r0 r1 r2 r3 -> fl_arr m SB c ws -> u32arr asegs m CH chs ->
  stk asegs m lo (bv_unsigned sp) -> (ACEIL <= lo)%Z -> (kHighShadowEnd + 8 <= lo)%Z -> (lo <= bv_unsigned sp - 208)%Z ->
  (bv_unsigned sp <= 2^47)%Z ->
  mem_inv asegs m ->
  evt asegs (rta_ret_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SB c R nfree n mfa auser muser
               (dest2 ws chs nfree cb (Z.to_nat n)) rand exh pad nalloc nfreed r0 r1 r2 r3 lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 INST) (Z_to_bv 64 mapper) (Z_to_bv 64 stat) (Z_to_bv 64 c)
             (Z_to_bv 64 (CH + 4 * cb)) (Z_to_bv 64 n) a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 rta_entry) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros HSB Hc ER Hn Hcb Hnf Hfast Hws Hmfa Hchs HCH Hrng IC GC LK RC RT FL CHS ST HLO HLOH HLO2 HSP MI.
  pose proof HSB as (HSB1 & HSB2 & HSB3 & HSB4).
  pose proof IC as IC0. pose proof GC as GC0.
  eapply rta_head; try eassumption; [lia|].
  intros m1 junk FR LK1 ST1 MU WM MI1.
  destruct IC0 as (IC1 & IC2). destruct GC0 as (G1 & G2 & G3 & G4 & G5).
  unfold kHighShadowEnd, rinfo, RIS_of, ri_core, ri_tail, fl_arr, i_spacebeg, i_premapped, INST, g_instance in *.
  change (6722776 + 32)%Z with 6722808%Z in IC1. change (6722776 + 56)%Z with 6722832%Z in IC2.
  assert (FAB : (SB + 2^32 <= fa SB c /\ fa SB c + 2^29 <= SB + 2^37)%Z) by (unfold fa, rb; lia).
  tr_from0 m MU WM RC. tr_from0 m MU WM RT. tr_from0a m MU WM FL. tr_from0a m MU WM CHS.
  tr_from0 m MU WM IC1. tr_from0 m MU WM IC2.
  tr_from0 m MU WM G1. tr_from0 m MU WM G2. tr_from0 m MU WM G3. tr_from0 m MU WM G4. tr_from0 m MU WM G5.
  clear IC GC.
  apply (munch_weaken _ (rta_tail_W sp SB c R nfree n)) in MU; [| unfold sub_fp, rta_tail_W; cbn [outside]; intros; lia].
  unfold rta_tail_W in MU.
  zhide.
  do 6 zstep.
  assert (Esp : bv_unsigned (Z_to_bv 64 (bv_unsigned sp - 128)) = (bv_unsigned sp - 128)%Z).
  { apply unsigned_lit. pose proof (bv_unsigned_in_range 64 sp) as Hr. unfold bv_modulus in Hr. cbn [Z.of_N] in Hr. lia. }
  call (efs_fast_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ R (nfree + n) nfree mfa auser muser lo).
  all: first [ assumption | lia | (rewrite Esp; assumption) | (rewrite Esp; lia) | idtac ].
  unfold rta_retE.
  eapply evt_mono; [eapply rta_tail_spec with (ACEIL := ACEIL) (lo := lo) (ra := ra) (mfa := mfa) (auser := auser)
     (muser := muser) (s0o := s0) (s1o := s1) (s2o := s2) (s3o := s3) (s4o := s4) (s5o := s5) (s6o := s6) (s7o := s7)
     (s8o := s8) (s9o := s9) (s10o := s10) (s11o := s11); try eassumption; try lia | ].
  all: first [ (eexists; eassumption) | (eexists; rewrite Esp in FR; eassumption)
             | (unfold inst_cells, i_spacebeg, i_premapped, INST, g_instance; split; assumption)
             | (unfold mm_gcells; repeat (split; [assumption|]); assumption)
             | (rewrite Esp in POST; exact POST) | idtac ].
  intros ms' PO. unfold rta_Q, rta_ret_post in PO. destruct_exs PO. destruct PO as (E & MU2 & WM2 & MI2 & PO). subst ms'.
  unfold rta_ret_post.
  do 16 eexists. split; [reflexivity|].
  split; [eapply munch_trans; [exact MU| exact MU2]|].
  split; [eapply wmono_trans; eassumption|].
  split; assumption.
Qed.

(* [comment removed for export] *)
Definition rta_A_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (SB c R mapper CH cb n nfree mfa lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a6' t3' t4' t5' t6' : word) (m' : mem) (junk : list byte),
    ms' = MSsvc (mfi_regs (Z_to_bv 64 efs_retB) (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (bv_unsigned sp - 128)) - 48)) gp tp
                          t0' t1' t2' a6' (fa SB c + mfa) (round_fa (4 * (nfree + n)) - mfa) (Z_to_bv 64 str_freearray)
                          (Z_to_bv 64 n) (Z_to_bv 64 (CH + 4 * cb)) (Z_to_bv 64 (nfree + n))
                          (Z_to_bv 64 2305843009213693952) (Z_to_bv 64 (fa SB c)) (Z_to_bv 64 1152921504607895551)
                          (Z_to_bv 64 1152921504606846976) t3' t4' t5' t6') F
                (Z_to_bv 64 mmap_ecall_pc) (Z_to_bv 64 222) fc None m' (seg_rom asegs)
    /\ munch [(R, R + 8); (bv_unsigned sp - 576, bv_unsigned sp)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ efs_A_cells m' (Z_to_bv 64 (bv_unsigned sp - 128)) (Z_to_bv 64 rta_retE) (Z_to_bv 64 R) (Z_to_bv 64 nfree)
         (Z_to_bv 64 c) (Z_to_bv 64 mapper) (Z_to_bv 64 INST) R (fa SB c + mfa) (round_fa (4 * (nfree + n)) - mfa)
         (round_fa (4 * (nfree + n))) lo
    /\ rw_cells asegs m' (bv_unsigned sp - 128)
         [CB 16 junk; C8 (Z_to_bv 64 (R + 8)); C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2;
          C8 s1; C8 s0; C8 ra]
    /\ ri_lock m' R 1152921504606846976.

(* [comment removed for export] *)
Lemma rta_A_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (ACEIL SB c R mapper stat CH cb n nfree mfa auser muser lo : Z),
  SB_ok ACEIL SB -> (1 <= c <= 31)%Z -> R = rinfo (RIS_of SB) c ->
  (1 <= n <= 16)%Z -> (0 <= nfree < 2^32)%Z ->
  (mfa < 4 * (nfree + n))%Z -> (0 <= mfa <= 2^29)%Z -> (mfa mod 2^18 = 0)%Z -> (round_fa (4 * (nfree + n)) <= 2^29)%Z ->
  (0 <= auser < 2^64)%Z -> (0 <= muser < 2^64)%Z ->
  inst_cells SB m -> mm_gcells m -> ri_lock m R 0 -> ri_core m R nfree mfa auser muser ->
  stk asegs m lo (bv_unsigned sp) -> (ACEIL <= lo)%Z -> (kHighShadowEnd + 8 <= lo)%Z -> (lo <= bv_unsigned sp - 576)%Z ->
  (bv_unsigned sp <= 2^47)%Z ->
  mem_inv asegs m ->
  evt asegs (rta_A_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SB c R mapper CH cb n nfree mfa lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 INST) (Z_to_bv 64 mapper) (Z_to_bv 64 stat) (Z_to_bv 64 c)
             (Z_to_bv 64 (CH + 4 * cb)) (Z_to_bv 64 n) a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 rta_entry) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros HSB Hc ER Hn Hnf Hslow Hmfa Hmfal Hnew Hau Hmu IC GC LK RC ST HLO HLOH HLO2 HSP MI.
  pose proof HSB as (HSB1 & HSB2 & HSB3 & HSB4).
  pose proof (round_fa_ge (4 * (nfree + n)) ltac:(lia)) as RGN.
  pose proof IC as IC0. pose proof GC as GC0.
  eapply rta_head; try eassumption; [lia|].
  intros m1 junk FR LK1 ST1 MU WM MI1.
  destruct IC0 as (IC1 & IC2). destruct GC0 as (G1 & G2 & G3 & G4 & G5).
  unfold kHighShadowEnd, rinfo, RIS_of, ri_core, i_spacebeg, i_premapped, INST, g_instance in *.
  change (6722776 + 32)%Z with 6722808%Z in IC1. change (6722776 + 56)%Z with 6722832%Z in IC2.
  tr_from0 m MU WM RC. tr_from0 m MU WM IC1. tr_from0 m MU WM IC2.
  tr_from0 m MU WM G1. tr_from0 m MU WM G2. tr_from0 m MU WM G3. tr_from0 m MU WM G4. tr_from0 m MU WM G5.
  clear IC GC.
  apply (munch_weaken _ [(R, R + 8); (bv_unsigned sp - 576, bv_unsigned sp)]%Z) in MU; [| unfold sub_fp; cbn [outside]; intros; lia].
  zhide.
  do 6 zstep.
  assert (Esp : bv_unsigned (Z_to_bv 64 (bv_unsigned sp - 128)) = (bv_unsigned sp - 128)%Z).
  { apply unsigned_lit. pose proof (bv_unsigned_in_range 64 sp) as Hr. unfold bv_modulus in Hr. cbn [Z.of_N] in Hr. lia. }
  eapply evt_cut; [eapply efs_A_spec with (num := (nfree + n)%Z) (nfree := nfree) (mfa := mfa) (ACEIL := ACEIL) (lo := lo)
                     (SB := SB) (c := c) (auser := auser) (muser := muser) | post_call asegs m1].
  all: first [ assumption | (unfold rinfo, RIS_of; lia) | lia
             | (unfold inst_cells, i_spacebeg, i_premapped, INST, g_instance; split; assumption)
             | (unfold ri_core; assumption) | (unfold mm_gcells; repeat (split; [assumption|]); assumption)
             | (rewrite ?Esp; unfold kHighShadowEnd; lia) | (rewrite Esp; assumption) | idtac ].
  apply evt_done. unfold rta_A_post.
  do 10 eexists. split; [reflexivity|].
  split; [exact MU|split; [exact WM|split; [exact MI0|split; [exact POST|split; [eassumption| unfold ri_lock; assumption]]]]].
Qed.
