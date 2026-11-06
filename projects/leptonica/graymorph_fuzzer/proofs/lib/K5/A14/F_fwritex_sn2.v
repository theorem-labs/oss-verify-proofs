(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.Lib Require Import SFModel Arr.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.Spec Require Import Prelim.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.A14 Require Import FX_lib F_memcpy F_fwritex R_m2s I_consts I_qck F_achk F_fwritex_fit F_sn_write F_sn_write2.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.Lib Require Import StoreFast.
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
Import ListNotations.
(* [comment removed for export] *)
Local Ltac lia_ndx xz := first [ (repeat match goal with H : ?T |- _ => lazymatch T with context [xz] => fail | _ \/ _ => clear H end end); lia | lia ].
Open Scope Z_scope.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
(* [comment removed for export] *)
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
Local Ltac lia ::= lia3.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Notation mem := (word -> option byte).
Ltac zs := zstep; try (fix_litstore; mem_after_store_opt).
Ltac fixK K := try (rewrite ?swrap32_small in K by lia); try (rewrite ?signed_of_Z in K by lia); try (rewrite ?Z.add_0_r in K).
Ltac brf K := if_cases K; zify_cond K; fixK K.
Ltac br K := brf K; try (exfalso; lia).
Ltac if_lit :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => let v := eval vm_compute in c in change c with v; cbv iota
  end.


Section WithRIP.
Hypothesis RIP : rip_stmt.

Lemma fwritex_over_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (Fp CK D n B bufp SA room : Z) (o bs : list Z) (dn : nat) (junk : list byte) (lo : Z),
  a0 = Z_to_bv 64 SA -> a1 = Z_to_bv 64 (zlength bs) -> a2 = Z_to_bv 64 Fp ->
  rw_cells asegs m (Fp + 32) [C8 (Z_to_bv 64 (B + zlength o + room))] ->
  rw_cells asegs m (Fp + 40) [C8 (Z_to_bv 64 (B + zlength o))] ->
  rw_cells asegs m (Fp + 56) [C8 (Z_to_bv 64 B)] ->
  rw_cells asegs m (Fp + 72) [C8 (Z_to_bv 64 0xd7d7c)] ->
  rw_cells asegs m (Fp + 88) [C8 (Z_to_bv 64 bufp)] ->
  rw_cells asegs m (Fp + 152) [C8 (Z_to_bv 64 CK)] ->
  rw_cells asegs m CK [C8 (Z_to_bv 64 D); C8 (Z_to_bv 64 n)] ->
  bytes_at asegs m B (zb o) -> bytes_at asegs m SA (zb bs) ->
  rw_cells asegs m D [CB dn junk] -> (length o + length bs < dn)%nat -> (zlength o + zlength bs <= n < 2^63)%Z ->
  (0 <= room < zlength bs)%Z -> (0 < B)%Z -> (B + zlength o + room < 2^63)%Z ->
  (0 <= bufp < 2^64)%Z -> (0 <= SA)%Z -> (SA + zlength bs < 2^63)%Z ->
  stk asegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 2304)%Z -> (kHighShadowEnd + 8 <= lo)%Z -> (bv_unsigned sp < 2^63)%Z ->
  mem_inv asegs m ->
  chkr m B (zlength o) -> chkr m SA (zlength bs) -> chkr m D (zlength o + zlength bs) -> ictx m ->
  (D + Z.of_nat dn <= SHADOW_LO \/ SHADOW_HI <= D)%Z -> (D + Z.of_nat dn <= 65536 \/ GLOBALS_TOP <= D)%Z ->
  (D + Z.of_nat dn <= lo)%Z -> (bv_unsigned sp <= CK)%Z -> (bv_unsigned sp <= Fp)%Z -> (bv_unsigned sp <= B)%Z -> (Fp + 160 <= CK)%Z ->
  (SA + zlength bs <= D \/ D + Z.of_nat dn <= SA)%Z ->
  (SA + zlength bs <= lo \/ bv_unsigned sp <= SA)%Z ->
  (SA + zlength bs <= CK \/ CK + 16 <= SA)%Z -> (SA + zlength bs <= Fp + 40 \/ Fp + 160 <= SA)%Z ->
  (B + zlength o <= CK \/ CK + 16 <= B)%Z -> (B + zlength o <= Fp + 40 \/ Fp + 160 <= B)%Z ->
  evt asegs (sn_write_gen_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Fp CK D n B bufp SA o bs dn junk lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0xd4818) fc None m (seg_rom asegs)).
Proof using RIP.
  intros until lo. intros -> -> -> WEND WPOS WBASE WRITE BUF COOKIE CKC SRC SRC2 DST ROOM Hn HR HB0 BHI Hbufp HS0 HSHI ST LO LOLO SPH MI CHB CHS CHD IC DSH DGL
    DLO S1 S2 S3 S4 D1s S3s S7 S8 S5 S6.
  unfold kHighShadowEnd in LOLO.
  pose proof (bytes_at_bound _ _ _ _ SRC) as BB. pose proof (zb_length o) as LZ. rewrite LZ in BB.
  pose proof (bytes_at_bound _ _ _ _ SRC2) as BB2. pose proof (zb_length bs) as LZ2. rewrite LZ2 in BB2. unfold zlength in *.
  pose proof (rw_cells_bound _ _ _ _ COOKIE) as FB. cbn [cells_size csize Nat.add] in FB.
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)]%Z m) as MUs. pose proof (wmono_refl asegs m) as WMs.
  pose_word_ranges.
  carve_frame 64%nat ST.
  zidle_begin sp 64%Z MUz WMz.
  do 8 zs.
  zidle_end MUz WMz.
  zs. zs. zs. zs.
  zs. brf Kw; [exfalso; lia|].
  zs. zs.
  zs. brf Kr; [exfalso; lia|].
  do 4 zs.
  do 8 zs.
  release_frame FR ST (bv_unsigned sp).
  zs.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (CHB1 : chkr mm B (Z.of_nat (length o)))
      by (apply (chkr_munch _ m mm B _ CHB MUs); intros xz Hxz; cbn [outside]; unfold SHADOW_LO, SHADOW_HI in *; lia_ndx xz);
    assert (CHS1 : chkr mm SA (Z.of_nat (length bs)))
      by (apply (chkr_munch _ m mm SA _ CHS MUs); intros xz Hxz; cbn [outside]; unfold SHADOW_LO, SHADOW_HI in *; lia_ndx xz);
    assert (CHD1 : chkr mm D (Z.of_nat (length o) + Z.of_nat (length bs)))
      by (apply (chkr_munch _ m mm D _ CHD MUs); intros xz Hxz; cbn [outside]; unfold SHADOW_LO, SHADOW_HI in *; lia_ndx xz);
    assert (IC1 : ictx mm) by (apply (ictx_munch _ m mm IC MUs WMs); intros xz Hxz; cbn [in_rl ICR outside] in Hxz |- *; lia_ndx xz) end.
  eapply evt_mono.
  { eapply (sn_write_gen_spec RIP) with (Fp := Fp) (CK := CK) (D := D) (n := n) (B := B) (bufp := bufp) (SA := SA) (o := o) (bs := bs)
      (dn := dn) (junk := junk) (lo := lo); unfold zlength, kHighShadowEnd; try reflexivity; try eassumption; try lia. }
  cbv beta. intros ms' P. unfold sn_write_gen_post in *.
  destruct P as (y5 & y6 & y7 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & y28 & y29 & y30 & y31 & m' & -> & MUc & WMc & MIc & STc & P1 & P2 & P3 & P4 & P5 & P6).
  exists y5, y6, y7, c1, c2, c3, c4, c5, c6, c7, y28, y29, y30, y31, m'.
  split; [reflexivity|].
  split.
  { eapply munch_trans; [|exact MUc]. eapply munch_weaken; [|exact MUs]. unfold sub_fp. cbn [outside]. intros x Hx. split; [lia | exact I]. }
  split; [exact (wmono_trans asegs _ _ _ WMs WMc)|].
  split; [exact MIc|]. split; [exact STc|].
  split; [exact P1|]. split; [exact P2|]. split; [exact P3|]. split; [exact P4|]. split; [exact P5 | exact P6].
Qed.

End WithRIP.
