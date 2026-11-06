(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.K5.Lib Require Import SFModel Arr.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.K5.Spec Require Import Prelim.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.K5.A08 Require Import FX_lib F_memcpy F_fwritex R_m2s I_consts I_qck F_achk F_fwritex_fit F_sn_write.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.K5.Lib Require Import StoreFast.
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

Definition sn_write_gen_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (Fp CK D n B bufp SA : Z) (o bs : list Z) (dn : nat) (junk : list byte) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (zlength bs)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 2304, bv_unsigned sp); (CK, CK + 16); (D, D + Z.of_nat dn); (Fp + 40, Fp + 48); (Fp + 56, Fp + 64)]%Z m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' CK [C8 (Z_to_bv 64 (D + zlength o + zlength bs)); C8 (Z_to_bv 64 (n - zlength o - zlength bs))]
    /\ rw_cells asegs m' D [CB dn (zb o ++ zb bs ++ Z_to_bv 8 0 :: skipn (S (length o + length bs)%nat) junk)]
    /\ rw_cells asegs m' (Fp + 40) [C8 (Z_to_bv 64 bufp)]
    /\ rw_cells asegs m' (Fp + 56) [C8 (Z_to_bv 64 bufp)]
    /\ bytes_at asegs m' B (zb o) /\ bytes_at asegs m' SA (zb bs).

(* [comment removed for export] *)
Local Definition zpark (P : Prop) : Prop := P.
Local Ltac park H := let T := type of H in change (zpark T) in H.
Local Ltac unpark H H' := pose proof H as H'; unfold zpark in H'.

(* [comment removed for export] *)

Lemma sn_write_gen_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (Fp CK D n B bufp SA : Z) (o bs : list Z) (dn : nat) (junk : list byte) (lo : Z),
  a0 = Z_to_bv 64 Fp -> a1 = Z_to_bv 64 SA -> a2 = Z_to_bv 64 (zlength bs) ->
  rw_cells asegs m (Fp + 40) [C8 (Z_to_bv 64 (B + zlength o))] ->
  rw_cells asegs m (Fp + 56) [C8 (Z_to_bv 64 B)] ->
  rw_cells asegs m (Fp + 88) [C8 (Z_to_bv 64 bufp)] ->
  rw_cells asegs m (Fp + 152) [C8 (Z_to_bv 64 CK)] ->
  rw_cells asegs m CK [C8 (Z_to_bv 64 D); C8 (Z_to_bv 64 n)] ->
  bytes_at asegs m B (zb o) -> bytes_at asegs m SA (zb bs) ->
  rw_cells asegs m D [CB dn junk] -> (length o + length bs < dn)%nat -> (zlength o + zlength bs <= n < 2^63)%Z ->
  (0 <= bufp < 2^64)%Z -> (B + zlength o < 2^63)%Z -> (0 <= SA)%Z -> (SA + zlength bs < 2^63)%Z ->
  stk asegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 2304)%Z -> (kHighShadowEnd + 8 <= lo)%Z -> (bv_unsigned sp < 2^63)%Z ->
  mem_inv asegs m ->
  (* [comment removed for export] *)
  chkr m B (zlength o) -> chkr m SA (zlength bs) -> chkr m D (zlength o + zlength bs) -> ictx m ->
  (D + Z.of_nat dn <= SHADOW_LO \/ SHADOW_HI <= D)%Z -> (D + Z.of_nat dn <= 65536 \/ GLOBALS_TOP <= D)%Z ->
  (* [comment removed for export] *)
  (D + Z.of_nat dn <= lo)%Z -> (bv_unsigned sp <= CK)%Z -> (bv_unsigned sp <= Fp)%Z -> (bv_unsigned sp <= B)%Z -> (Fp + 160 <= CK)%Z ->
  (SA + zlength bs <= D \/ D + Z.of_nat dn <= SA)%Z ->
  (SA + zlength bs <= lo \/ bv_unsigned sp <= SA)%Z ->
  (SA + zlength bs <= CK \/ CK + 16 <= SA)%Z -> (SA + zlength bs <= Fp + 40 \/ Fp + 160 <= SA)%Z ->
  (B + zlength o <= CK \/ CK + 16 <= B)%Z -> (B + zlength o <= Fp + 40 \/ Fp + 160 <= B)%Z ->
  evt asegs (sn_write_gen_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Fp CK D n B bufp SA o bs dn junk lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0xc1b68) fc None m (seg_rom asegs)).
Proof using RIP.
  intros until lo. intros -> -> -> WPOS WBASE BUF COOKIE CKC SRC SRC2 DST ROOM Hn Hbufp BHI HS0 HSHI ST LO LOLO SPH MI CHB CHS CHD IC DSH DGL
    DLO S1 S2 S3 S4 D1s S3s S7 S8 S5 S6.
  unfold kHighShadowEnd in LOLO.
  pose proof (rw_cells_bound _ _ _ _ DST) as DB. cbn [cells_size csize Nat.add] in DB.
  pose proof (rw_cells_bound _ _ _ _ CKC) as CB_. cbn [cells_size csize Nat.add] in CB_.
  pose proof (rw_cells_bound _ _ _ _ COOKIE) as FB. cbn [cells_size csize Nat.add] in FB.
  pose proof (bytes_at_bound _ _ _ _ SRC) as BB. pose proof (zb_length o) as LZ. rewrite LZ in BB.
  pose proof (bytes_at_bound _ _ _ _ SRC2) as BB2. pose proof (zb_length bs) as LZ2. rewrite LZ2 in BB2. unfold zlength in *.
  pose proof (munch_refl [(bv_unsigned sp - 2304, bv_unsigned sp); (CK, CK + 16); (D, D + Z.of_nat dn); (Fp + 40, Fp + 48); (Fp + 56, Fp + 64)]%Z m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  pose_word_ranges.
  (* [comment removed for export] *)
  assert (FIN : forall m', munch [(bv_unsigned sp - 2304, bv_unsigned sp); (CK, CK + 16); (D, D + Z.of_nat dn); (Fp + 40, Fp + 48); (Fp + 56, Fp + 64)]%Z m m' ->
                  bytes_at asegs m' B (zb o) /\ bytes_at asegs m' SA (zb bs)).
  { intros m' MU'. split.
    - apply (bytes_at_transport asegs _ m m' _ _ SRC MU'). rewrite LZ. cbn [disjoint_from]. repeat split; lia.
    - apply (bytes_at_transport asegs _ m m' _ _ SRC2 MU'). rewrite LZ2. cbn [disjoint_from]. repeat split; lia. }
  (* [comment removed for export] *)
  assert (CHK : forall m' p k, chkr m p k -> munch [(bv_unsigned sp - 2304, bv_unsigned sp); (CK, CK + 16); (D, D + Z.of_nat dn); (Fp + 40, Fp + 48); (Fp + 56, Fp + 64)]%Z m m' -> chkr m' p k).
  { intros m' p k C MU'. apply (chkr_munch _ m m' p k C MU'). intros xz Hxz. cbn [outside]. unfold SHADOW_LO, SHADOW_HI in *. repeat split; lia. }
  assert (ICX : forall m', munch [(bv_unsigned sp - 2304, bv_unsigned sp); (CK, CK + 16); (D, D + Z.of_nat dn); (Fp + 40, Fp + 48); (Fp + 56, Fp + 64)]%Z m m' -> wmono asegs m m' -> ictx m').
  { intros m' MU' WM'. apply (ictx_munch _ m m' IC MU' WM'). intros xz Hxz. cbn [in_rl ICR outside] in Hxz |- *. unfold GLOBALS_TOP in *. repeat split; lia. }
  (* [comment removed for export] *)
  assert (SEPsD : (SA + Z.of_nat (length bs) <= D + Z.of_nat (length o) \/ D + Z.of_nat (length o) + Z.of_nat (length bs) <= SA)%Z) by lia.
  assert (SEPsK : (Z.of_nat (length bs) = 0 \/ SA + Z.of_nat (length bs) <= lo \/ bv_unsigned sp + -64 <= SA)%Z) by lia.
  park SEPsD. park SEPsK. park D1s. park S3s. park S7. park S8. park S5. park S6. park DSH. park DGL. park FIN. park CHK. park ICX.
  park SRC2. park CHS.
  carve_frame 64%nat ST.
  zidle_begin sp 64%Z MUz WMz.
  do 8 zs.
  zidle_end MUz WMz.
  do 7 zs.
  zs. replace (B + Z.of_nat (length o) - B)%Z with (Z.of_nat (length o)) by lia.
  zs. zs. brf K1; [exfalso; lia|]. zs. zs. zs. brf K2.
  - (* [comment removed for export] *)
    assert (O0 : length o = 0%nat) by lia. destruct o as [|c o']; [|cbn in O0; lia]. cbn [length Z.of_nat] in *.
    zs. brf K3; [exfalso; lia|]. zs. zs. brf K4.
    + (* [comment removed for export] *)
      assert (L0 : length bs = 0%nat) by lia. destruct bs as [|c bs']; [|cbn in L0; lia]. cbn [length Z.of_nat] in *.
      pose proof (rw_CB_length _ _ _ _ DST) as LJ.
      pose proof (u8arr_of_rw_cells _ _ _ _ _ DST) as DA. clear DST.
      pose proof (u8arr_store_ok asegs _ _ _ 0%Z (Z_to_bv 64 D) DA ltac:(rewrite LJ; lia) ltac:(f_equal; lia)) as SOK.
      zs. rewrite le1_zero. replace (Z_to_bv 64 D) with (wa (D + 0)) by (unfold wa; f_equal; lia).
      pose proof (u8arr_write asegs _ _ _ 0%Z (Z_to_bv 8 0) DA ltac:(rewrite LJ; lia)) as DA2. clear DA. store_done.
      pose proof (rw_cells_of_u8arr _ _ _ _ DA2) as DST. rewrite upd_length, LJ in DST.
      zs. zs. zs. zs.
      do 9 zs.
      release_frame FR ST (bv_unsigned sp).
      apply evt_done. unfold sn_write_gen_post. repeat (lazymatch goal with |- ex _ => eexists end).
      split; [cbv delta [mkR]; rewrite ?Z.add_0_r; reflexivity|].
      split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|].
      split. { cbn [zlength length Z.of_nat]. rewrite !Z.add_0_r, !Z.sub_0_r. match goal with H : rw_cells _ _ CK _ |- _ => exact H end. }
      split. { cbn [zb map app length skipn Nat.add]. rewrite upd_firstn_skipn in DST by (rewrite LJ; lia). cbn [firstn app] in DST. exact DST. }
      split; [assumption|]. split; [assumption|]. unfold zpark in FIN. exact (FIN _ MU).
    + (* [comment removed for export] *)
      pose proof (rw_CB_length _ _ _ _ DST) as LJ.
      apply (rw_cells_split_CB asegs _ _ [] dn _ [] [length bs; dn - length bs]%nat) in DST; [ | cbn; lia ].
      cbn [mk_CB_cells app] in DST.
      apply (proj1 (rw_cells_app asegs _ _ [_] _)) in DST. destruct DST as [DSTa DSTb]. cbn [cells_size csize Nat.add] in DSTb. rewrite Nat.add_0_r in DSTb.
      zs. zs. zs.
      unpark FIN FIN'. unpark CHK CHK'. unpark ICX ICX'. unpark CHS CHS'. unpark SEPsD SD'. unpark SEPsK SK'.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        pose proof (proj2 (FIN' mm MU)) as SRCm;
        pose proof (CHK' mm SA _ CHS' MU) as CHS1;
        pose proof (CHK' mm D _ (chkr_sub m D _ D (Z.of_nat (length bs)) CHD ltac:(lia) ltac:(lia) ltac:(lia)) MU) as CHD1;
        pose proof (ICX' mm MU WM) as IC1 end.
      clear FIN' CHK' ICX' CHS'.
      eapply evt_cut.
      { eapply (imemcpy_callw RIP) with (src := zb bs) (junk := firstn (length bs) junk) (lo := lo);
          rewrite ?unsigned_lit by lia;
          [ exact SRCm | rewrite LZ2; lia | rewrite Nat2Z.id; exact DSTa | lia | lia
          | match goal with H : stk _ _ lo _ |- _ => exact H end | lia | unfold kHighShadowEnd; lia | lia | lia | lia
          | exact CHS1 | exact CHD1 | exact IC1 | exact MI ]. }
      clear SD' SK' SRCm CHS1 CHD1 IC1.
      cbv beta. intros ms' P. unfold memcpy_posti in P.
      destruct P as (x5 & x6 & x7 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & x28 & x29 & x30 & x31 & m' & -> & MUc & WMc & MIc & DSTa' & SRC' & STc).
      clear SRC'. rewrite ?unsigned_lit in MUc, STc by lia.
      lazymatch type of MUc with munch _ ?mm _ => transport_after_call asegs mm m' MUc WMc; clear MUc WMc; try clear MI end.
      try clear ST. rename STc into ST.
      replace (ret_pc (Z_to_bv 64 793588)) with (Z_to_bv 64 793588) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
      zs. zs. zs. zs. zs. zs.
      pose proof (rw_CB_length _ _ _ _ DSTb) as LJb.
      pose proof (u8arr_of_rw_cells _ _ _ _ _ DSTb) as DA. clear DSTb.
      pose proof (u8arr_store_ok asegs _ _ _ 0%Z (Z_to_bv 64 (D + Z.of_nat (length bs))) DA ltac:(rewrite LJb; lia) ltac:(f_equal; lia)) as SOK.
      zs. rewrite le1_zero. replace (Z_to_bv 64 (D + Z.of_nat (length bs))) with (wa (D + Z.of_nat (length bs) + 0)) by (unfold wa; f_equal; lia).
      pose proof (u8arr_write asegs _ _ _ 0%Z (Z_to_bv 8 0) DA ltac:(rewrite LJb; lia)) as DA2. clear DA. store_done.
      pose proof (rw_cells_of_u8arr _ _ _ _ DA2) as DSTb. rewrite upd_length, LJb in DSTb.
      zs. zs. zs. zs.
      do 9 zs.
      release_frame FR ST (bv_unsigned sp).
      apply evt_done. unfold sn_write_gen_post. repeat (lazymatch goal with |- ex _ => eexists end).
      split; [cbv delta [mkR]; rewrite ?Z.add_0_r; reflexivity|].
      split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|].
      split. { unfold zlength. cbn [length Z.of_nat]. rewrite ?Z.add_0_r, ?Z.sub_0_r. match goal with H : rw_cells _ _ CK _ |- _ => exact H end. }
      split.
      { match goal with Ha : rw_cells _ ?mm D [CB _ ?l1], Hb : rw_cells _ ?mm (D + _)%Z [CB _ ?l2] |- _ =>
          assert (J : rw_cells asegs mm D ([] ++ [CB (length bs) l1; CB (dn - length bs) l2] ++ []));
          [ cbn [app]; apply (proj2 (rw_cells_app asegs _ _ [_] _)); split; [rewrite Nat2Z.id in Ha; exact Ha|]; cbn [cells_size csize]; rewrite Nat.add_0_r; exact Hb
          | apply rw_cells_merge in J; cbn [cells_size cells_bytes csize cbytes app] in J; rewrite app_nil_r in J ] end.
        replace (length bs + (dn - length bs + 0))%nat with dn in J by lia.
        rewrite upd_firstn_skipn in J by (rewrite length_firstn, length_skipn, LJ; lia). change (Z.to_nat 0) with 0%nat in J. rewrite firstn_O, app_nil_l in J.
        rewrite skipn_firstn_comm, skipn_skipn in J. replace (1 + length bs)%nat with (S (length bs)) in J by lia.
        rewrite firstn_all2 in J by (rewrite length_skipn, LJ; lia). cbn [zb map app length Nat.add]. exact J. }
      split; [assumption|]. split; [assumption|]. unfold zpark in FIN. exact (FIN _ MU).
  - (* [comment removed for export] *)
    pose proof (rw_CB_length _ _ _ _ DST) as LJ.
    apply (rw_cells_split_CB asegs _ _ [] dn _ [] [length o; dn - length o]%nat) in DST; [ | cbn; lia ].
    cbn [mk_CB_cells app] in DST.
    apply (proj1 (rw_cells_app asegs _ _ [_] _)) in DST. destruct DST as [DSTa DSTb]. cbn [cells_size csize Nat.add] in DSTb. rewrite Nat.add_0_r in DSTb.
    zs. zs.
    unpark FIN FIN'. unpark CHK CHK'. unpark ICX ICX'. unpark S5 S5'. unpark S6 S6'.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (proj1 (FIN' mm MU)) as SRCm;
      pose proof (CHK' mm B _ CHB MU) as CHB1;
      pose proof (CHK' mm D _ (chkr_sub m D _ D (Z.of_nat (length o)) CHD ltac:(lia) ltac:(lia) ltac:(lia)) MU) as CHD1;
      pose proof (ICX' mm MU WM) as IC1 end.
    clear FIN' CHK' ICX'.
    eapply evt_cut.
    { eapply (imemcpy_callw RIP) with (src := zb o) (junk := firstn (length o) junk) (lo := lo);
        rewrite ?unsigned_lit by lia;
        [ exact SRCm | rewrite LZ; lia | rewrite Nat2Z.id; exact DSTa | lia | lia
        | match goal with H : stk _ _ lo _ |- _ => exact H end | lia | unfold kHighShadowEnd; lia | lia | lia | lia
        | exact CHB1 | exact CHD1 | exact IC1 | exact MI ]. }
    clear S5' S6' SRCm CHB1 CHD1 IC1.
    cbv beta. intros ms' P. unfold memcpy_posti in P.
    destruct P as (x5 & x6 & x7 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & x28 & x29 & x30 & x31 & m' & -> & MUc & WMc & MIc & DSTa' & SRC' & STc).
    clear SRC'. rewrite ?unsigned_lit in MUc, STc by lia.
    lazymatch type of MUc with munch _ ?mm _ => transport_after_call asegs mm m' MUc WMc; clear MUc WMc; try clear MI end.
    try clear ST. rename STc into ST.
    replace (ret_pc (Z_to_bv 64 793540)) with (Z_to_bv 64 793540) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
    zs. zs. zs. zs. zs. zs.
    zs. brf K3; [exfalso; lia|]. zs. zs. brf K4.
    + (* [comment removed for export] *)
      assert (L0 : length bs = 0%nat) by lia. destruct bs as [|c bs']; [|cbn in L0; lia]. cbn [length Z.of_nat] in *.
      pose proof (rw_CB_length _ _ _ _ DSTb) as LJb.
      pose proof (u8arr_of_rw_cells _ _ _ _ _ DSTb) as DA. clear DSTb.
      pose proof (u8arr_store_ok asegs _ _ _ 0%Z (Z_to_bv 64 (D + Z.of_nat (length o))) DA ltac:(rewrite LJb; lia) ltac:(f_equal; lia)) as SOK.
      zs. rewrite le1_zero. replace (Z_to_bv 64 (D + Z.of_nat (length o))) with (wa (D + Z.of_nat (length o) + 0)) by (unfold wa; f_equal; lia).
      pose proof (u8arr_write asegs _ _ _ 0%Z (Z_to_bv 8 0) DA ltac:(rewrite LJb; lia)) as DA2. clear DA. store_done.
      pose proof (rw_cells_of_u8arr _ _ _ _ DA2) as DSTb. rewrite upd_length, LJb in DSTb.
      zs. zs. zs. zs.
      do 9 zs.
      release_frame FR ST (bv_unsigned sp).
      apply evt_done. unfold sn_write_gen_post. repeat (lazymatch goal with |- ex _ => eexists end).
      split; [cbv delta [mkR]; rewrite ?Z.add_0_r; reflexivity|].
      split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|].
      split. { unfold zlength. cbn [length Z.of_nat]. rewrite ?Z.add_0_r, ?Z.sub_0_r. match goal with H : rw_cells _ _ CK _ |- _ => exact H end. }
      split.
      { match goal with Ha : rw_cells _ ?mm D [CB _ ?l1], Hb : rw_cells _ ?mm (D + _)%Z [CB _ ?l2] |- _ =>
          assert (J : rw_cells asegs mm D ([] ++ [CB (length o) l1; CB (dn - length o) l2] ++ []));
          [ cbn [app]; apply (proj2 (rw_cells_app asegs _ _ [_] _)); split; [rewrite Nat2Z.id in Ha; exact Ha|]; cbn [cells_size csize]; rewrite Nat.add_0_r; exact Hb
          | apply rw_cells_merge in J; cbn [cells_size cells_bytes csize cbytes app] in J; rewrite app_nil_r in J ] end.
        replace (length o + (dn - length o + 0))%nat with dn in J by lia.
        rewrite upd_firstn_skipn in J by (rewrite length_firstn, length_skipn, LJ; lia). change (Z.to_nat 0) with 0%nat in J. rewrite firstn_O, app_nil_l in J.
        rewrite skipn_firstn_comm, skipn_skipn in J. replace (1 + length o)%nat with (S (length o)) in J by lia.
        rewrite firstn_all2 in J by (rewrite length_skipn, LJ; lia). cbn [zb map app length Nat.add]. rewrite Nat.add_0_r. exact J. }
      split; [assumption|]. split; [assumption|]. unfold zpark in FIN. exact (FIN _ MU).
    + (* [comment removed for export] *)
      pose proof (rw_CB_length _ _ _ _ DSTb) as LJb.
      apply (rw_cells_split_CB asegs _ _ [] (dn - length o) _ [] [length bs; dn - length o - length bs]%nat) in DSTb; [ | cbn; lia ].
      cbn [mk_CB_cells app] in DSTb.
      apply (proj1 (rw_cells_app asegs _ _ [_] _)) in DSTb. destruct DSTb as [DSTb DSTc]. cbn [cells_size csize Nat.add] in DSTc. rewrite Nat.add_0_r in DSTc.
      zs. zs. zs.
      unpark FIN FIN'. unpark CHK CHK'. unpark ICX ICX'. unpark CHS CHS'. unpark SEPsD SD'. unpark SEPsK SK'.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        pose proof (proj2 (FIN' mm MU)) as SRCm;
        pose proof (CHK' mm SA _ CHS' MU) as CHS1;
        pose proof (CHK' mm (D + Z.of_nat (length o))%Z _ (chkr_sub m D _ (D + Z.of_nat (length o))%Z (Z.of_nat (length bs)) CHD ltac:(lia) ltac:(lia) ltac:(lia)) MU) as CHD1;
        pose proof (ICX' mm MU WM) as IC1 end.
      clear FIN' CHK' ICX' CHS'.
      eapply evt_cut.
      { eapply (imemcpy_callw RIP) with (src := zb bs) (junk := firstn (length bs) (firstn (dn - length o) (skipn (length o) junk))) (lo := lo);
          rewrite ?unsigned_lit by lia;
          [ exact SRCm | rewrite LZ2; lia | rewrite Nat2Z.id; exact DSTb | lia | lia
          | match goal with H : stk _ _ lo _ |- _ => exact H end | lia | unfold kHighShadowEnd; lia | lia | lia | lia
          | exact CHS1 | exact CHD1 | exact IC1 | assumption ]. }
      clear SD' SK' SRCm CHS1 CHD1 IC1.
      cbv beta. intros ms' P. unfold memcpy_posti in P.
      destruct P as (y5 & y6 & y7 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & y28 & y29 & y30 & y31 & m'' & -> & MUc & WMc & MIc2 & DSTb' & SRC' & STc).
      clear SRC'. rewrite ?unsigned_lit in MUc, STc by lia.
      lazymatch type of MUc with munch _ ?mm _ => transport_after_call asegs mm m'' MUc WMc; clear MUc WMc; try clear MIc end.
      try clear ST. rename STc into ST.
      replace (ret_pc (Z_to_bv 64 793588)) with (Z_to_bv 64 793588) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
      zs. zs. zs. zs. zs. zs.
      pose proof (rw_CB_length _ _ _ _ DSTc) as LJc.
      pose proof (u8arr_of_rw_cells _ _ _ _ _ DSTc) as DA. clear DSTc.
      pose proof (u8arr_store_ok asegs _ _ _ 0%Z (Z_to_bv 64 (D + Z.of_nat (length o) + Z.of_nat (length bs))) DA ltac:(rewrite LJc; lia) ltac:(f_equal; lia)) as SOK.
      zs. rewrite le1_zero. replace (Z_to_bv 64 (D + Z.of_nat (length o) + Z.of_nat (length bs))) with (wa (D + Z.of_nat (length o) + Z.of_nat (length bs) + 0)) by (unfold wa; f_equal; lia).
      pose proof (u8arr_write asegs _ _ _ 0%Z (Z_to_bv 8 0) DA ltac:(rewrite LJc; lia)) as DA2. clear DA. store_done.
      pose proof (rw_cells_of_u8arr _ _ _ _ DA2) as DSTc. rewrite upd_length, LJc in DSTc.
      zs. zs. zs. zs.
      do 9 zs.
      release_frame FR ST (bv_unsigned sp).
      apply evt_done. unfold sn_write_gen_post. repeat (lazymatch goal with |- ex _ => eexists end).
      split; [cbv delta [mkR]; rewrite ?Z.add_0_r; reflexivity|].
      split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|].
      split. { unfold zlength. exact CKC. }
      split.
      { rewrite !Nat2Z.id in *.
        assert (J : rw_cells asegs m1 D ([] ++ [CB (length o) (zb o); CB (length bs) (zb bs);
                      CB (dn - length o - length bs) (upd (firstn (dn - length o - length bs) (skipn (length bs) (firstn (dn - length o) (skipn (length o) junk)))) (Z.to_nat 0) (Z_to_bv 8 0))] ++ [])).
        { cbn [app]. apply (proj2 (rw_cells_app asegs _ _ [_] _)). split; [exact DSTa'|]. cbn [cells_size csize]. rewrite Nat.add_0_r.
          apply (proj2 (rw_cells_app asegs _ _ [_] _)). split; [exact DSTb'|]. cbn [cells_size csize]. rewrite Nat.add_0_r. exact DSTc. }
        apply rw_cells_merge in J. cbn [cells_size cells_bytes csize cbytes app] in J. rewrite app_nil_r in J.
        replace (length o + (length bs + (dn - length o - length bs + 0)))%nat with dn in J by lia.
        rewrite (firstn_all2 (n := (dn - length o)%nat)) in J by (rewrite length_skipn, LJ; lia).
        rewrite skipn_skipn in J.
        rewrite firstn_all2 in J by (rewrite length_skipn, LJ; lia).
        rewrite upd_firstn_skipn in J by (rewrite length_skipn, LJ; lia). change (Z.to_nat 0) with 0%nat in J. rewrite firstn_O, app_nil_l in J.
        rewrite skipn_skipn in J. replace (1 + (length bs + length o))%nat with (S (length o + length bs)) in J by lia.
        exact J. }
      split; [assumption|]. split; [assumption|]. unfold zpark in FIN. exact (FIN _ MU).
Qed.

End WithRIP.
