(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import SFModel Arr.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec Require Import Prelim.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import FX_lib F_memcpy F_fwritex. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import R_m2s I_consts I_qck. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import F_achk F_fwritex_fit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

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

Local Ltac lia_ndx xz := first [ (repeat match goal with H : ?T |- _ => lazymatch T with context [xz] => fail | _ \/ _ => clear H end end); lia | lia ].
Open Scope Z_scope.
Open Scope bv_scope.

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

Lemma zb_length : forall l, length (zb l) = length l.
Proof. intros. unfold zb. apply length_map. Qed.
Lemma rw_CB_length : forall m A n (bs : list byte), rw_cells asegs m A [CB n bs] -> length bs = n.
Proof. intros m A n bs [[[H _] _] _]. exact H. Qed.
Lemma le1_zero : le1 (Z_to_bv 64 0) = [Z_to_bv 8 0].
Proof. reflexivity. Qed.

Section WithRIP.
Hypothesis RIP : rip_stmt.

Definition sn_write_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (Fp CK D n B bufp : Z) (o : list Z) (dn : nat) (junk : list byte) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 2304, bv_unsigned sp); (CK, CK + 16); (D, D + Z.of_nat dn); (Fp + 40, Fp + 48); (Fp + 56, Fp + 64)]%Z m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' CK [C8 (Z_to_bv 64 (D + zlength o)); C8 (Z_to_bv 64 (n - zlength o))]
    /\ rw_cells asegs m' D [CB dn (zb o ++ Z_to_bv 8 0 :: skipn (S (length o)) junk)]
    /\ rw_cells asegs m' (Fp + 40) [C8 (Z_to_bv 64 bufp)]
    /\ rw_cells asegs m' (Fp + 56) [C8 (Z_to_bv 64 bufp)]
    /\ bytes_at asegs m' B (zb o).

Lemma sn_write_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (Fp CK D n B bufp : Z) (o : list Z) (dn : nat) (junk : list byte) (lo : Z),
  a0 = Z_to_bv 64 Fp -> a2 = Z_to_bv 64 0 ->
  rw_cells asegs m (Fp + 40) [C8 (Z_to_bv 64 (B + zlength o))] ->
  rw_cells asegs m (Fp + 56) [C8 (Z_to_bv 64 B)] ->
  rw_cells asegs m (Fp + 88) [C8 (Z_to_bv 64 bufp)] ->
  rw_cells asegs m (Fp + 152) [C8 (Z_to_bv 64 CK)] ->
  rw_cells asegs m CK [C8 (Z_to_bv 64 D); C8 (Z_to_bv 64 n)] ->
  bytes_at asegs m B (zb o) ->
  rw_cells asegs m D [CB dn junk] -> (length o < dn)%nat -> (zlength o <= n < 2^63)%Z -> (0 <= bufp < 2^64)%Z -> (B + zlength o < 2^63)%Z ->
  stk asegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 2304)%Z -> (kHighShadowEnd + 8 <= lo)%Z -> (bv_unsigned sp < 2^63)%Z ->
  mem_inv asegs m ->

  chkr m B (zlength o) -> chkr m D (zlength o) -> ictx m ->

  (B + zlength o <= D \/ D + Z.of_nat dn <= B)%Z ->
  (CK + 16 <= D \/ D + Z.of_nat dn <= CK)%Z ->
  (Fp + 160 <= D \/ D + Z.of_nat dn <= Fp + 40)%Z ->
  (D + Z.of_nat dn <= lo \/ bv_unsigned sp <= D)%Z ->
  (bv_unsigned sp <= CK)%Z -> (bv_unsigned sp <= Fp)%Z -> (bv_unsigned sp <= B)%Z ->
  (CK + 16 <= Fp + 40 \/ Fp + 160 <= CK)%Z ->
  (B + zlength o <= CK \/ CK + 16 <= B)%Z -> (B + zlength o <= Fp + 40 \/ Fp + 160 <= B)%Z ->
  evt asegs (sn_write_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Fp CK D n B bufp o dn junk lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x15a108) fc None m (seg_rom asegs)).
Proof using RIP.
  intros until lo. intros -> -> WPOS WBASE BUF COOKIE CKC SRC DST ROOM Hn Hbufp BHI ST LO LOLO SPH MI CHB CHD IC D1 D2 D3 D4 S1 S2 S3 S4 S5 S6.
  unfold kHighShadowEnd in LOLO.
  pose proof (rw_cells_bound _ _ _ _ DST) as DB. cbn [cells_size csize Nat.add] in DB.
  pose proof (rw_cells_bound _ _ _ _ CKC) as CB_. cbn [cells_size csize Nat.add] in CB_.
  pose proof (rw_cells_bound _ _ _ _ COOKIE) as FB. cbn [cells_size csize Nat.add] in FB.
  pose proof (bytes_at_bound _ _ _ _ SRC) as BB. pose proof (zb_length o) as LZ. rewrite LZ in BB. unfold zlength in *.
  pose proof (munch_refl [(bv_unsigned sp - 2304, bv_unsigned sp); (CK, CK + 16); (D, D + Z.of_nat dn); (Fp + 40, Fp + 48); (Fp + 56, Fp + 64)]%Z m) as MU.
  pose proof (munch_refl [(bv_unsigned sp - 2304, bv_unsigned sp)]%Z m) as MUs. pose proof (wmono_refl asegs m) as WMs.
  pose proof (wmono_refl asegs m) as WM.
  pose_word_ranges.
  carve_frame 64%nat ST.
  zidle_begin sp 64%Z MUz WMz.
  do 8 zs.
  zidle_end MUz WMz.
  do 7 zs.
  zs. replace (B + Z.of_nat (length o) - B)%Z with (Z.of_nat (length o)) by lia.
  zs. zs. brf K1; [exfalso; lia|]. zs. zs. zs. brf K2.
  -
    clear MUs WMs. assert (O0 : length o = 0%nat) by lia. destruct o as [|c o']; [|cbn in O0; lia]. cbn [length Z.of_nat] in *.
    zs. brf K3; [exfalso; lia|]. zs. zs. if_lit.
    pose proof (rw_CB_length _ _ _ _ DST) as LJ.
    pose proof (u8arr_of_rw_cells _ _ _ _ _ DST) as DA. clear DST.
    pose proof (u8arr_store_ok asegs _ _ _ 0%Z (Z_to_bv 64 D) DA ltac:(rewrite LJ; lia) ltac:(f_equal; lia)) as SOK.
    zs. rewrite le1_zero. replace (Z_to_bv 64 D) with (wa (D + 0)) by (unfold wa; f_equal; lia).
    pose proof (u8arr_write asegs _ _ _ 0%Z (Z_to_bv 8 0) DA ltac:(rewrite LJ; lia)) as DA2. clear DA. store_done.
    pose proof (rw_cells_of_u8arr _ _ _ _ DA2) as DST. rewrite upd_length, LJ in DST.
    zs. zs. zs. zs.
    do 9 zs.
    release_frame FR ST (bv_unsigned sp).
    apply evt_done. unfold sn_write_post. repeat (lazymatch goal with |- ex _ => eexists end).
    split; [cbv delta [mkR]; rewrite ?Z.add_0_r; reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|].
    split. { cbn [zlength length Z.of_nat]. rewrite Z.add_0_r, Z.sub_0_r. match goal with H : rw_cells _ _ CK _ |- _ => exact H end. }
    split. { cbn [zb map app length skipn]. rewrite upd_firstn_skipn in DST by (rewrite LJ; lia). cbn [firstn app] in DST. exact DST. }
    split; [assumption|]. split; [assumption|]. assumption.
  -
    pose proof (rw_CB_length _ _ _ _ DST) as LJ.
    apply (rw_cells_split_CB asegs _ _ [] dn _ [] [length o; dn - length o]%nat) in DST; [ | cbn; lia ].
    cbn [mk_CB_cells app] in DST.
    apply (proj1 (rw_cells_app asegs _ _ [_] _)) in DST. destruct DST as [DSTa DSTb]. cbn [cells_size csize Nat.add] in DSTb. rewrite Nat.add_0_r in DSTb.
    zs. zs.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (CHB1 : chkr mm B (Z.of_nat (length o)))
        by (apply (chkr_munch _ m mm B _ CHB MUs); intros xz Hxz; cbn [outside]; unfold SHADOW_LO, SHADOW_HI in *; lia_ndx xz);
      assert (CHD1 : chkr mm D (Z.of_nat (length o)))
        by (apply (chkr_munch _ m mm D _ CHD MUs); intros xz Hxz; cbn [outside]; unfold SHADOW_LO, SHADOW_HI in *; lia_ndx xz);
      assert (IC1 : ictx mm) by (apply (ictx_munch _ m mm IC MUs WMs); intros xz Hxz; cbn [in_rl ICR outside] in Hxz |- *; lia_ndx xz) end.
    clear MUs WMs.
    eapply evt_cut.
    { eapply (imemcpy_callw RIP) with (src := zb o) (junk := firstn (length o) junk) (lo := lo);
        rewrite ?unsigned_lit by lia;
        [ exact SRC | rewrite LZ; lia | rewrite Nat2Z.id; exact DSTa | lia | lia
        | match goal with H : stk _ _ lo _ |- _ => exact H end | lia | unfold kHighShadowEnd; lia | lia | lia | lia
        | exact CHB1 | exact CHD1 | exact IC1 | exact MI ]. }
    cbv beta. intros ms' P. unfold memcpy_posti in P.
    destruct P as (x5 & x6 & x7 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & x28 & x29 & x30 & x31 & m' & -> & MUc & WMc & MIc & DSTa' & SRC' & STc).
    rewrite ?unsigned_lit in MUc, STc by lia.
    lazymatch type of MUc with munch _ ?mm _ => transport_after_call asegs mm m' MUc WMc; clear MUc WMc; try clear MI end.
    try clear ST. rename STc into ST.
    replace (ret_pc (Z_to_bv 64 1417572)) with (Z_to_bv 64 1417572) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
    zs. zs. zs. zs. zs. zs.
    zs. brf K3; [exfalso; lia|]. zs. zs. if_lit.
    pose proof (rw_CB_length _ _ _ _ DSTb) as LJb.
    pose proof (u8arr_of_rw_cells _ _ _ _ _ DSTb) as DA. clear DSTb.
    pose proof (u8arr_store_ok asegs _ _ _ 0%Z (Z_to_bv 64 (D + Z.of_nat (length o))) DA ltac:(rewrite LJb; lia) ltac:(f_equal; lia)) as SOK.
    zs. rewrite le1_zero. replace (Z_to_bv 64 (D + Z.of_nat (length o))) with (wa (D + Z.of_nat (length o) + 0)) by (unfold wa; f_equal; lia).
    pose proof (u8arr_write asegs _ _ _ 0%Z (Z_to_bv 8 0) DA ltac:(rewrite LJb; lia)) as DA2. clear DA. store_done.
    pose proof (rw_cells_of_u8arr _ _ _ _ DA2) as DSTb. rewrite upd_length, LJb in DSTb.
    zs. zs. zs. zs.
    do 9 zs.
    release_frame FR ST (bv_unsigned sp).
    apply evt_done. unfold sn_write_post. repeat (lazymatch goal with |- ex _ => eexists end).
    split; [cbv delta [mkR]; rewrite ?Z.add_0_r; reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|].
    split. { unfold zlength. match goal with H : rw_cells _ _ CK _ |- _ => exact H end. }
    split.
    { match goal with Ha : rw_cells _ ?mm D [CB _ ?l1], Hb : rw_cells _ ?mm (D + _)%Z [CB _ ?l2] |- _ =>
        assert (J : rw_cells asegs mm D ([] ++ [CB (length o) l1; CB (dn - length o) l2] ++ []));
        [ cbn [app]; apply (proj2 (rw_cells_app asegs _ _ [_] _)); split; [rewrite Nat2Z.id in Ha; exact Ha|]; cbn [cells_size csize]; rewrite Nat.add_0_r; exact Hb
        | apply rw_cells_merge in J; cbn [cells_size cells_bytes csize cbytes app] in J; rewrite app_nil_r in J ] end.
      replace (length o + (dn - length o + 0))%nat with dn in J by lia.
      rewrite upd_firstn_skipn in J by (rewrite length_firstn, length_skipn, LJ; lia). change (Z.to_nat 0) with 0%nat in J. rewrite firstn_O, app_nil_l in J.
      rewrite skipn_firstn_comm, skipn_skipn in J. replace (1 + length o)%nat with (S (length o)) in J by lia.
      rewrite firstn_all2 in J by (rewrite length_skipn, LJ; lia). first [exact J | let t := type of J in idtac "J:" t; match goal with |- ?g => idtac g end; fail]. }
    split; [assumption|]. split; [assumption|]. assumption.
Qed.

End WithRIP.
