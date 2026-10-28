(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Lib Require Import Tac ImageA Arr Walk SysStep ITree.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Malloc Require Import MallocKit_AB.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.B Require Import Layout R_small R_m2s R_thread R_cache_defs R_prim_defs R_mmapfixed R_ensurefa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Open Scope bv_scope.

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

Local Ltac zidle_end_m m :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch goal with MU : munch _ m mm, WM : wmono _ m mm |- _ =>
      unfold zidle in *; transport_after_call bsegs m mm MU WM end end.
Notation mem := (word -> option byte).

Ltac tr_from m0 MU WM H :=
  lazymatch type of MU with munch ?W _ ?mc =>
    apply (rw_cells_transport bsegs W m0 mc _ _) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; lia ]
  end.

Section EFSB.
Variable PC : mem -> Prop.
Hypothesis HPS : poison_stmt PC.
Hypothesis HPF : PC_framed PC.

Definition efs_WB (sp : word) (fam n esa esn T R : Z) : list (Z * Z) :=
  [(fam, fam + n); (esa, esa + esn); (T + 2872, T + 2888); (R + 24, R + 32); (bv_unsigned sp - 448, bv_unsigned sp)]%Z.

Definition efs_B_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (R fam n new esa esn T TCX nfree auser muser : Z) (mm0 md0 : word) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 1) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                  t3' t4' t5' t6') F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch (efs_WB sp fam n esa esn T R) m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ rw_cells bsegs m' fam [CB (Z.to_nat n) (repeat (Z_to_bv 8 0) (Z.to_nat n))]
    /\ rw_cells bsegs m' esa [CB (Z.to_nat esn) (repeat (Z_to_bv 8 250) (Z.to_nat esn))]
    /\ ri_core m' R nfree new auser muser
    /\ rw_cells bsegs m' (T + 2872) [C8 (Z_to_bv 64 (bv_unsigned mm0 + 1)); C8 (Z_to_bv 64 (bv_unsigned md0 + n))]
    /\ mm_gcells m' /\ thread_cells TCX T m' /\ PC m'
    /\ stk bsegs m' lo (bv_unsigned sp).

Lemma efs_B_spec : forall ra sp gp t0 t1 t2 a6 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (ACEIL SB c R mfa new fam n esa esn T TCX nfree auser muser : Z)
    (mm0 md0 : word) (shj : list byte) (lo : Z),
  SB_ok ACEIL SB -> (1 <= c <= 31)%Z -> R = rinfo (RIS_of SB) c ->
  fam = (fa SB c + mfa)%Z -> n = (new - mfa)%Z -> (mfa mod 2^18 = 0)%Z -> (new mod 2^18 = 0)%Z -> (0 <= mfa < new)%Z ->
  (new <= 2^29)%Z -> esa = shad fam -> esn = (n / 8)%Z ->
  tsep ACEIL SB T TCX ->
  efs_A_cells m sp ra s0 s1 s2 s3 s4 R fam n new lo ->
  ri_core m R nfree mfa auser muser ->
  thread_cells TCX T m ->
  rw_cells bsegs m (T + 2872) [C8 mm0; C8 md0] ->
  rw_cells bsegs m esa [CB (Z.to_nat esn) shj] ->
  PC m ->
  (ACEIL <= lo)%Z -> (kHighShadowEnd + 8 <= lo)%Z -> (lo <= bv_unsigned sp - 448)%Z -> (bv_unsigned sp <= 2^47)%Z ->
  mem_inv bsegs m ->
  evt bsegs (efs_B_post ra sp gp (Z_to_bv 64 tpA) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R fam n new esa esn T TCX
               nfree auser muser mm0 md0 lo m)
    (nret (MSsvc (mfi_regs (Z_to_bv 64 efs_retB) (Z_to_bv 64 (bv_unsigned sp - 48)) gp (Z_to_bv 64 tpA) t0 t1 t2 a6 fam n
                           (Z_to_bv 64 str_freearray) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F
                 (Z_to_bv 64 mmap_ecall_pc) (Z_to_bv 64 222) fc None m (seg_rom bsegs))
          (mkEffect (Z_to_bv 64 fam) [] [(Z_to_bv 64 fam, Z_to_bv 64 n)])).
Proof.
  intros until lo. intros HSB Hc ER Efam En Hmfal Hnewl Hmfa Hnew Eesa Eesn HTS
    AC RC TC ST8 SH PCm HLO HLOH HLO2 HSP MI.
  destruct HTS as (HT & HTCX0 & HTCX1 & HTCXI & SEPT & SEPTCX & SEPTT & OUTT & OUTTCX).
  destruct HSB as (HSB1 & HSB2 & HSB3 & HSB4). destruct HT as (HT1 & HT2 & HT3 & HT4 & HT5).
  destruct AC as (FM & (junk & FR) & ST & GC).
  unfold ri_core in RC. unfold kHighShadowEnd, img_hull_lo, img_hull_hi in *. unfold rinfo, RIS_of in ER.
  assert (Esp : bv_unsigned (Z_to_bv 64 (bv_unsigned sp - 48)) = (bv_unsigned sp - 48)%Z).
  { apply unsigned_lit. pose proof (bv_unsigned_in_range 64 sp) as Hr. unfold bv_modulus in Hr. cbn [Z.of_N] in Hr.
    lia. }
  rewrite Esp in ST.
  assert (FAM : (SB + 2^32 <= fam /\ fam + n <= SB + 2^37)%Z) by (subst fam n; unfold fa, rb; lia).
  assert (Hn8 : (fam mod 8 = 0 /\ n mod 8 = 0)%Z).
  { subst fam n. unfold fa, rb. split; Z.div_mod_to_equations; lia. }
  destruct (shad_range fam n ltac:(lia) ltac:(lia) (proj1 Hn8) (proj2 Hn8) ltac:(lia)) as (SH1 & SH2 & SH3).
  rewrite <- Eesa in SH1, SH2. rewrite <- Eesn in SH2, SH3. unfold kHighShadowEnd in SH2.
  assert (Hn0 : (0 < n)%Z) by lia. assert (Hesn : (0 < esn)%Z) by lia.
  pose proof (munch_refl (efs_WB sp fam n esa esn T R) m) as MU. pose proof (wmono_refl bsegs m) as WM.
  unfold efs_WB in MU.

  pose proof GC as GC0. apply box in TC, GC0, PCm.

  apply box in Efam, En, Eesa, Eesn, Hmfal, Hnewl, HSB2, HT2, Hn8, HT5, HTCXI, SEPTT, OUTT, OUTTCX, SEPTCX, SEPT, Hmfa, Hnew, SH3.

  pose proof (unbox _ SEPT) as SEPT'.
  eapply evt_cut; [eapply (mfi_B_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m _ _ _ _ _ fam n _ lo) | post_call bsegs m].
  1:{ unfold img_hull_hi. lia. }
  1:{ lia. }
  1:{ lia. }
  1:{ exact FM. }
  1:{ exact GC. }
  all: rewrite ?Esp; try lia; try assumption.
  clear POST SEPT'.

  lazymatch type of MU with munch _ _ ?mc =>
    pose proof (munch_refl [(esa, esa + esn); (T + 2872, T + 2888); (R + 24, R + 32); (bv_unsigned sp - 448, bv_unsigned sp)]%Z mc)
      as MU2; pose proof (wmono_refl bsegs mc) as WM2; rename mc into m1 end.
  apply box in PC0.
  unfold efs_retB.
  replace (ret_pc (Z_to_bv 64 378420)) with (Z_to_bv 64 378420) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
  zhide.
  zstep. ifF.
  zstep.
  zstep. ifF.
  do 3 zstep.
  zstep.

  pose proof (unbox _ Eesa) as Eesa'. pose proof (unbox _ Eesn) as Eesn'. pose proof (unbox _ Hn8) as Hn8'.
  rewrite Eesa', Eesn' in SH.
  assert (PCm1 : PC m1).
  { pose proof (unbox _ HT5). apply (HPF m m1 _ (unbox _ PCm) MU WM). unfold img_hull_lo, img_hull_hi. cbn [disjoint_from]. lia. }
  pose proof (unbox _ OUTT) as OUTT'.
  eapply evt_cut; [eapply (HPS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ fam n lo shj) | ].
  1-3: try unfold zal in *; lia. 1: unfold kHighShadowEnd; lia. 1: lia. 1: exact SH. 1: exact PCm1. 1: exact PC1.
  1-3: unfold kHighShadowEnd; rewrite ?Esp; lia. 1: assumption.
  intros ms' PO. destruct_exs PO. destruct PO as [E [MUc [WMc [MIc PO]]]]. subst ms'.
  rewrite <- Eesa', <- Eesn' in MUc, PO. clear Eesa' Eesn' Hn8' SH PCm1.
  lazymatch type of MUc with munch _ _ ?mc => transport_after_call bsegs m1 mc MUc WMc; rename mc into m2 end.
  clear MUc WMc MI0 OUTT'.
  destruct PO as (SHN & ST1 & PCm2). clear PCm2.
  pose proof (munch_refl [(T + 2872, T + 2888); (R + 24, R + 32); (bv_unsigned sp - 448, bv_unsigned sp)]%Z m2) as MU3.
  pose proof (wmono_refl bsegs m2) as WM3.
  apply box in SHN.
  replace (ret_pc (Z_to_bv 64 378448)) with (Z_to_bv 64 378448) by (symmetry; apply ret_pc_even; [lia|reflexivity]).

  zstep.
  destruct (unbox _ TC) as [(KI & K & TS & T0) TT].
  unfold g_tsd_key_inited, g_tsd_key, pth_tsd, g_pthread_tsd_main in KI, K, TS, T0.
  pose proof (unbox _ HT5) as HT5'.
  tr_from m MU WM KI. tr_from m MU WM K. tr_from m MU WM TS. tr_from m MU WM T0.
  clear HT5'.
  pose proof (unbox _ SEPTCX) as SEPTCX'. pose proof (unbox _ OUTTCX) as OUTTCX'. pose proof (unbox _ SEPTT) as SEPTT'.
  tr_from m MU WM TT.
  clear SEPTCX' OUTTCX' SEPTT'.
  call (gcts_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ TCX T lo).
  1:{ unfold thread_cells, tsd_cells, g_tsd_key_inited, g_tsd_key, pth_tsd, g_pthread_tsd_main.
      split; [split; [exact KI|split; [exact K|split; [exact TS|exact T0]]]|exact TT]. }
  all: rewrite ?Esp in *; try lia; try assumption.
  clear KI K TS T0 TT.

  pose proof (unbox _ SEPT) as SEPT'.
  do 6 zstep.
  do 3 zstep.
  do 7 zstep.
  replace (bv_unsigned sp - 48 + 48)%Z with (bv_unsigned sp) by lia. rewrite Z_to_bv_bv_unsigned.
  release_frame FR POST (bv_unsigned sp).
  zstep.

  pose proof (unbox _ OUTT) as OUTT'.
  apply unbox in PC0, SHN.
  tr_from m1 MU2 WM2 PC0. tr_from m2 MU3 WM3 SHN.
  clear OUTT'.
  destruct (unbox _ TC) as [(KI & K & TS & T0) TT].
  unfold g_tsd_key_inited, g_tsd_key, pth_tsd, g_pthread_tsd_main in KI, K, TS, T0.
  destruct (unbox _ GC0) as (G1 & G2 & G3 & G4 & G5).
  pose proof (unbox _ HT5) as HT5'.
  tr_from m MU WM KI. tr_from m MU WM K. tr_from m MU WM TS. tr_from m MU WM T0.
  tr_from m MU WM G1. tr_from m MU WM G2. tr_from m MU WM G3. tr_from m MU WM G4. tr_from m MU WM G5.
  lazymatch type of MU with munch _ _ ?mc =>
    assert (PCf : PC mc) by (apply (HPF m mc _ (unbox _ PCm) MU WM); unfold img_hull_lo, img_hull_hi; cbn [disjoint_from]; lia) end.
  clear HT5'.
  pose proof (unbox _ SEPTCX) as SEPTCX'. pose proof (unbox _ OUTTCX) as OUTTCX'. pose proof (unbox _ SEPTT) as SEPTT'.
  tr_from m MU WM TT.
  finish.
  1:{ unfold mm_gcells. repeat (split; [assumption|]). assumption. }
  1:{ unfold thread_cells, tsd_cells, g_tsd_key_inited, g_tsd_key, pth_tsd, g_pthread_tsd_main.
      split; [split; [exact KI|split; [exact K|split; [exact TS|exact T0]]]|exact TT]. }
Qed.
End EFSB.
