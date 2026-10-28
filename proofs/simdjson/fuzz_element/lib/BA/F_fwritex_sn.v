(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import SFModel.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import FX_lib F_memcpy F_fwritex. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import R_m2s I_consts I_qck. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import F_achk F_fwritex_fit.

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
      unfold zidle in *; transport_after_call asegs m mm MU WM end end.
Import ListNotations.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Local Ltac lia_ndx xz := first [ (repeat match goal with H : ?T |- _ => lazymatch T with context [xz] => fail | _ \/ _ => clear H end end); lia | lia ].

Local Ltac lia_nd := first [ (repeat match goal with H : _ \/ _ |- _ => clear H end); lia | lia ].

Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.

Module DJ.
  Import Ltac2.
  Ltac2 prune_reld () : unit :=
    let bad := SF2.bad_heads () in
    let gv := SF2.vars_of [] (Control.goal ()) in
    SF2.prune_with (fun ty => if SF2.plain_arith false ty then SF2.clean bad ty else SF2.meets (SF2.vars_of [] ty) gv).
  Ltac2 prune_reld1 () : unit := Control.enter prune_reld.
End DJ.
Local Ltac dj_prune := ltac2:(DJ.prune_reld1 ()).
Local Ltac dj_one := first [ Zify.zify; xlia zchecker | sf_unhide; dj_prune; Zify.zify; xlia zchecker | tlia ].
Local Ltac tslia ::= first [ exact I | repeat lazymatch goal with |- _ /\ _ => split end; first [ exact I | dj_one ] ].
Open Scope bv_scope.

Definition fwritex_postA (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (Fp : Z) (fl0 : byte) (j1 j2 : list byte) (lbfw : word) (B : Z) (content junk : list byte)
    (S : Z) (bs : list byte) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (Z.of_nat (length bs))) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 2304, bv_unsigned sp);
              (B + Z.of_nat (length content), B + Z.of_nat (length content) + Z.of_nat (length bs));
              (Fp + 40, Fp + 48)]%Z m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ wfile m' Fp fl0 j1 j2 lbfw B (content ++ bs) (skipn (length bs) junk)
    /\ bytes_at asegs m' S bs.

Definition memcpy_postZA (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (D : Z) (a1 a2 : word) (src : list byte) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(D, D + bv_unsigned a2); (bv_unsigned sp - 2240, bv_unsigned sp)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' D [CB (Z.to_nat (bv_unsigned a2)) src]
    /\ bytes_at asegs m' (bv_unsigned a1) src
    /\ stk asegs m' lo (bv_unsigned sp).

Section WithRIP.
Hypothesis RIP : rip_stmt.

Lemma imemcpy_callZ : forall ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (D : Z) (src junk : list byte) (lo : Z),
  bytes_at asegs m (bv_unsigned a1) src ->
  length src = Z.to_nat (bv_unsigned a2) ->
  rw_cells asegs m D [CB (Z.to_nat (bv_unsigned a2)) junk] ->
  (0 <= D < 2^64)%Z ->
  (bv_unsigned a1 + bv_unsigned a2 <= D \/ D + bv_unsigned a2 <= bv_unsigned a1)%Z ->
  stk asegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 2240)%Z -> (kHighShadowEnd + 8 <= lo)%Z -> (bv_unsigned sp < 2^63)%Z ->
  (bv_unsigned a1 + bv_unsigned a2 <= lo \/ bv_unsigned sp <= bv_unsigned a1)%Z -> (D + bv_unsigned a2 <= lo \/ bv_unsigned sp <= D)%Z ->
  chkr m (bv_unsigned a1) (bv_unsigned a2) -> chkr m D (bv_unsigned a2) -> ictx m ->
  mem_inv asegs m ->
  evt asegs (memcpy_postZA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc D a1 a2 src lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x812f4) fc None m (seg_rom asegs)).
Proof using RIP.
  intros until lo. intros SRC LEN DST HD SEP ST LO HSH SPH SEPS SEPD CS CD IC MI.
  pose proof (bv_unsigned_in_range 64 a2) as R2. unfold bv_modulus in R2. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in R2.
  rewrite <- (Z_to_bv_bv_unsigned a1), <- (Z_to_bv_bv_unsigned a2).
  eapply evt_mono.
  { eapply (imemcpy_callw RIP ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
              D (bv_unsigned a1) (bv_unsigned a2) src junk lo).
    all: first [exact SRC | exact LEN | exact DST | exact ST | exact CS | exact CD | exact IC | exact MI | lia]. }
  intros ms' P. unfold memcpy_posti in P. unfold memcpy_postZA. rewrite ?Z_to_bv_bv_unsigned. exact P.
Qed.

Ltac unwrap_in K := rewrite ?land_W64 in K; change (2^64)%Z with 18446744073709551616%Z in K; rewrite ?Z.mod_small in K by lia.

Lemma fwritex_spec_A : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte)
    (fl0 : byte) (j1 j2 : list byte) (lbfw : word) (B : Z) (content junk bs : list byte) (lo : Z),
  wfile m (bv_unsigned a2) fl0 j1 j2 lbfw B content junk ->
  bytes_at asegs m (bv_unsigned a0) bs ->
  Z.of_nat (length bs) = bv_unsigned a1 ->
  (length bs <= length junk)%nat ->
  stk asegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 2304)%Z -> (kHighShadowEnd + 8 <= lo)%Z -> (bv_unsigned sp < 2^63)%Z ->
  mem_inv asegs m ->
  (64 <= bv_unsigned sp)%Z ->
  (bv_unsigned a2 + 148 <= lo \/ bv_unsigned sp <= bv_unsigned a2)%Z ->
  (B + Z.of_nat (length content) + Z.of_nat (length junk) <= lo \/ bv_unsigned sp <= B)%Z ->
  (bv_unsigned a0 + Z.of_nat (length bs) <= lo \/ bv_unsigned sp <= bv_unsigned a0)%Z ->
  (bv_unsigned a0 + Z.of_nat (length bs) <= B + Z.of_nat (length content)
   \/ B + Z.of_nat (length content) + Z.of_nat (length bs) <= bv_unsigned a0)%Z ->
  (bv_unsigned a0 + Z.of_nat (length bs) <= bv_unsigned a2 \/ bv_unsigned a2 + 148 <= bv_unsigned a0)%Z ->

  chkr m (bv_unsigned a0) (Z.of_nat (length bs)) -> chkr m (B + Z.of_nat (length content)) (Z.of_nat (length bs)) -> ictx m ->
  evt asegs (fwritex_postA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
               (bv_unsigned a2) fl0 j1 j2 lbfw B content junk (bv_unsigned a0) bs lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1537ec) fc None m (seg_rom asegs)).
Proof using RIP.
  intros until lo. intros (FC & BUF & FL & LBF & Bpos & Bhi & SEPfb) SRC LEN LE ST LO HSH SPH MI SPLO SEP1 SEP2 SEP3 SEP4 SEP5 CHS CHD IC.
  unfold kHighShadowEnd in HSH.
  pose_word_ranges.
  set (Fp := bv_unsigned a2) in *. replace a2 with (Z_to_bv 64 Fp) by (unfold Fp; rewrite Z_to_bv_bv_unsigned; reflexivity).
  set (S := bv_unsigned a0) in *.
  set (nc := length content) in *. set (nj := length junk) in *. set (lb := length bs) in *.
  pose proof (rw_cells_bound _ _ _ _ FC) as BF. cbn [cells_size csize Nat.add length] in BF.
  pose proof (rw_cells_bound _ _ _ _ BUF) as BB. cbn [cells_size csize Nat.add] in BB. rewrite Nat.add_0_r, Nat2Z.inj_add in BB.
  pose proof (munch_refl [(bv_unsigned sp - 2304, bv_unsigned sp); (B + Z.of_nat nc, B + Z.of_nat nc + Z.of_nat lb); (Fp + 40, Fp + 48)]%Z m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  pose proof (munch_refl [(bv_unsigned sp - 2304, bv_unsigned sp)]%Z m) as MUs. pose proof (wmono_refl asegs m) as WMs.
  unfold FILE_cells in FC.
  carve_frame 64%nat ST.
  zidle_begin sp 64%Z MUz WMz.
  do 8 zstep.
  zidle_end MUz WMz.
  zstep. zstep. zstep. zstep.
  zstep. if_cases Kw; zify_cond Kw; unwrap_in Kw.
  { exfalso. lia. }
  zstep. zstep.
  zstep. if_cases Kr; zify_cond Kr; unwrap_in Kr.
  2:{ exfalso. lia. }
  zstep. zstep. zstep. if_cases Kl; zify_cond Kl.
  2:{ exfalso. pose proof (sx32_neg lbfw LBF). lia. }
  zstep. zstep.

  apply (rw_cells_split_CB asegs _ _ [CB nc content] nj junk [] [lb; nj - lb]%nat) in BUF; [ | cbn; lia ].
  cbn [mk_CB_cells app] in BUF.
  apply (proj1 (rw_cells_app asegs _ _ [_] _)) in BUF. destruct BUF as [BUFa BUF].
  cbn [cells_size csize Nat.add] in BUF. rewrite Nat.add_0_r in BUF.
  apply (proj1 (rw_cells_app asegs _ _ [_] _)) in BUF. destruct BUF as [BUFb BUFc].
  cbn [cells_size csize] in BUFc. rewrite Nat.add_0_r in BUFc.
  zstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (CHS1 : chkr mm S (Z.of_nat lb))
      by (apply (chkr_munch _ m mm S _ CHS MUs); intros xz Hxz; cbn [outside]; unfold SHADOW_LO, SHADOW_HI in *; lia_ndx xz);
    assert (CHD1 : chkr mm (B + Z.of_nat nc) (Z.of_nat lb))
      by (apply (chkr_munch _ m mm _ _ CHD MUs); intros xz Hxz; cbn [outside]; unfold SHADOW_LO, SHADOW_HI in *; lia_ndx xz);
    assert (IC1 : ictx mm) by (apply (ictx_munch _ m mm IC MUs WMs); intros xz Hxz; cbn [in_rl ICR outside] in Hxz |- *; lia_ndx xz) end.
  clear MUs WMs.
  assert (EU : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -64)) = (bv_unsigned sp + -64)%Z) by (apply unsigned_lit; lia).
  call imemcpy_callZ.
  1:{ exact SRC. }
  1:{ unfold lb in LEN. rewrite <- LEN, Nat2Z.id. reflexivity. }
  1:{ rewrite <- LEN, Nat2Z.id. exact BUFb. }
  1:{ lia. } 1:{ lia. }
  1:{ rewrite unsigned_lit by lia. exact ST. }
  1:{ rewrite unsigned_lit by lia. lia. } 1:{ unfold kHighShadowEnd; lia. } 1:{ rewrite unsigned_lit by lia. lia. }
  1:{ rewrite unsigned_lit by lia. lia. } 1:{ rewrite unsigned_lit by lia. lia. }
  1:{ rewrite <- LEN. exact CHS1. } 1:{ rewrite <- LEN. exact CHD1. } 1:{ exact IC1. }
  1:{ assumption. }
  rewrite <- !LEN in *. rewrite !Nat2Z.id in *.
  rewrite firstn_all2 in BUFc by (rewrite length_skipn; lia).
  match goal with MC : rw_cells _ _ (B + Z.of_nat nc)%Z [CB lb bs] |- _ => rename MC into BUFb end.
  match goal with H : stk _ _ lo _ |- _ => rewrite unsigned_lit in H by lia; try clear ST; rename H into ST end.
  zstep. zstep. zstep. zstep.
  replace (0 + bv_unsigned a1)%Z with (Z.of_nat lb) by lia.
  replace (B + Z.of_nat nc + bv_unsigned a1)%Z with (B + Z.of_nat (length (content ++ bs)))%Z by (rewrite length_app; lia).
  do 9 zstep. release_frame FR ST (bv_unsigned sp).

  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (BUF : rw_cells asegs mm B ([] ++ [CB nc content; CB lb bs] ++ [CB (nj - lb)%nat (skipn lb junk)]));
    [ cbn [app]; apply (proj2 (rw_cells_app asegs _ _ [_] _)); split; [ exact BUFa |];
      cbn [cells_size csize]; rewrite Nat.add_0_r;
      apply (proj2 (rw_cells_app asegs _ _ [_] _)); split; [ exact BUFb |];
      cbn [cells_size csize]; rewrite Nat.add_0_r; exact BUFc
    | apply rw_cells_merge in BUF; cbn [cells_size cells_bytes csize cbytes app Nat.add] in BUF;
      rewrite Nat.add_0_r, app_nil_r in BUF; clear BUFa BUFb BUFc ]
  end.
  apply evt_done. unfold fwritex_postA.
  repeat (lazymatch goal with |- ex _ => eexists end).
  split; [ ms_eq | ].
  repeat match goal with |- _ /\ _ => split end; try assumption;
    try (replace (bv_unsigned sp - 64)%Z with (bv_unsigned sp + -64)%Z by lia; assumption).

  unfold wfile, FILE_cells. rewrite !length_app, !length_skipn. fold nc lb nj.
  rewrite !Nat2Z.inj_add, !Nat2Z.inj_sub by lia.
  replace (B + (Z.of_nat nc + Z.of_nat lb) + (Z.of_nat nj - Z.of_nat lb))%Z with (B + Z.of_nat nc + Z.of_nat nj)%Z by lia.
  replace (B + Z.of_nat nc + bv_unsigned a1)%Z with (B + (Z.of_nat nc + Z.of_nat lb))%Z in FC by lia.
  split; [exact FC|]. split; [exact BUF|]. split; [exact FL|]. split; [exact LBF|]. split; [lia|]. split; lia.
Qed.

End WithRIP.
