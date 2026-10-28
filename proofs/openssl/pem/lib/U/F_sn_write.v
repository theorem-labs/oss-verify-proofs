(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import SFModel Arr.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Spec Require Import Prelim.
From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Printf_lib F_memcpy F_fwritex.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
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
(* [comment removed for export] *)
Module DJR.
  Import Ltac2.
  Ltac2 is_hidden (t : constr) : constr option := lazy_match! t with sf_hide ?p => Some p | _ => None end.
  Ltac2 unhide_rel () : unit :=
    let gv := SF2.vars_of [] (Control.goal ()) in
    let rm := List.map_filter (fun h => let (id, body, ty) := h in
      match body with
      | Some _ => None
      | None =>
          match is_hidden ty with
          | Some p => if SF2.meets (SF2.vars_of [] p) gv
                      then (let c := Control.hyp id in ltac1:(c |- unfold sf_hide in c) (Ltac1.of_constr c); None)
                      else Some id
          | None => None
          end
      end) (Control.hyps ()) in
    match rm with [] => () | _ :: _ => Std.clear rm end.
  Ltac2 unhide_rel1 () : unit := Control.enter unhide_rel.
End DJR.
Local Ltac dj_unhide_rel := ltac2:(DJR.unhide_rel1 ()).
Local Ltac dj_one := first [ Zify.zify; xlia zchecker | dj_unhide_rel; Zify.zify; xlia zchecker | sf_unhide; dj_prune; Zify.zify; xlia zchecker | tlia ].
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
Lemma rw_CB_length : forall m A n (bs : list byte), rw_cells usegs m A [CB n bs] -> length bs = n.
Proof. intros m A n bs [[[H _] _] _]. exact H. Qed.
Lemma le1_zero : le1 (Z_to_bv 64 0) = [Z_to_bv 8 0].
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition memcpy_postv (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (Dst Src N : Z) (src : list byte) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Dst) a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(Dst, Dst + N)]%Z m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ rw_cells usegs m' Dst [CB (Z.to_nat N) src]
    /\ bytes_at usegs m' Src src.
Lemma memcpy_callv : forall ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (Dst Src N : Z) (src junk : list byte),
  bytes_at usegs m Src src -> length src = Z.to_nat N -> rw_cells usegs m Dst [CB (Z.to_nat N) junk] ->
  (Src + N <= Dst \/ Dst + N <= Src)%Z -> (0 <= N < 2^64)%Z -> (0 <= Src < 2^64)%Z -> (0 <= Dst < 2^64)%Z -> mem_inv usegs m ->
  evt usegs (memcpy_postv ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Dst Src N src m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Dst) (Z_to_bv 64 Src) (Z_to_bv 64 N) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x2baf30) fc None m (seg_rom usegs)).
Proof.
  intros until junk. intros BA LEN DC SEP HN HS HD MI.
  assert (ED : bv_unsigned (Z_to_bv 64 Dst) = Dst) by (apply unsigned_lit; lia).
  assert (ES : bv_unsigned (Z_to_bv 64 Src) = Src) by (apply unsigned_lit; lia).
  assert (EN : bv_unsigned (Z_to_bv 64 N) = N) by (apply unsigned_lit; lia).
  eapply evt_mono. { eapply memcpy_spec with (src := src) (junk := junk); rewrite ?ED, ?ES, ?EN; [exact BA | exact LEN | exact DC | exact SEP | exact MI]. }
  intros ms' P. unfold memcpy_post, memcpy_postv in *. rewrite ED, ES, EN in P. exact P.
Qed.

Definition sn_write_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (Fp CK D n B bufp : Z) (o : list Z) (dn : nat) (junk : list byte) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(bv_unsigned sp - 64, bv_unsigned sp); (CK, CK + 16); (D, D + Z.of_nat dn); (Fp + 40, Fp + 48); (Fp + 56, Fp + 64)]%Z m m'
    /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ stk usegs m' (bv_unsigned sp - 64) (bv_unsigned sp)
    /\ rw_cells usegs m' CK [C8 (Z_to_bv 64 (D + zlength o)); C8 (Z_to_bv 64 (n - zlength o))]
    /\ rw_cells usegs m' D [CB dn (zb o ++ Z_to_bv 8 0 :: skipn (S (length o)) junk)]
    /\ rw_cells usegs m' (Fp + 40) [C8 (Z_to_bv 64 bufp)]
    /\ rw_cells usegs m' (Fp + 56) [C8 (Z_to_bv 64 bufp)]
    /\ bytes_at usegs m' B (zb o).

Lemma sn_write_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (Fp CK D n B bufp : Z) (o : list Z) (dn : nat) (junk : list byte),
  a0 = Z_to_bv 64 Fp -> a2 = Z_to_bv 64 0 ->
  rw_cells usegs m (Fp + 40) [C8 (Z_to_bv 64 (B + zlength o))] ->
  rw_cells usegs m (Fp + 56) [C8 (Z_to_bv 64 B)] ->
  rw_cells usegs m (Fp + 88) [C8 (Z_to_bv 64 bufp)] ->
  rw_cells usegs m (Fp + 152) [C8 (Z_to_bv 64 CK)] ->
  rw_cells usegs m CK [C8 (Z_to_bv 64 D); C8 (Z_to_bv 64 n)] ->
  bytes_at usegs m B (zb o) ->
  rw_cells usegs m D [CB dn junk] -> (length o < dn)%nat -> (zlength o <= n < 2^63)%Z -> (0 <= bufp < 2^64)%Z -> (B + zlength o < 2^63)%Z ->
  stk usegs m (bv_unsigned sp - 64) (bv_unsigned sp) -> (64 <= bv_unsigned sp)%Z -> mem_inv usegs m ->
  (* [comment removed for export] *)
  (B + zlength o <= D \/ D + Z.of_nat dn <= B)%Z ->
  (CK + 16 <= D \/ D + Z.of_nat dn <= CK)%Z ->
  (Fp + 160 <= D \/ D + Z.of_nat dn <= Fp + 40)%Z ->
  (D + Z.of_nat dn <= bv_unsigned sp - 64 \/ bv_unsigned sp <= D)%Z ->
  (bv_unsigned sp <= CK)%Z -> (bv_unsigned sp <= Fp)%Z -> (bv_unsigned sp <= B)%Z ->
  (CK + 16 <= Fp + 40 \/ Fp + 160 <= CK)%Z ->
  (B + zlength o <= CK \/ CK + 16 <= B)%Z -> (B + zlength o <= Fp + 40 \/ Fp + 160 <= B)%Z ->
  evt usegs (sn_write_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Fp CK D n B bufp o dn junk m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x2b9a8c) fc None m (seg_rom usegs)).
Proof.
  intros until junk. intros -> -> WPOS WBASE BUF COOKIE CKC SRC DST ROOM Hn Hbufp BHI ST SPLO MI D1 D2 D3 D4 S1 S2 S3 S4 S5 S6.
  pose proof (rw_cells_bound _ _ _ _ DST) as DB. cbn [cells_size csize Nat.add] in DB.
  pose proof (rw_cells_bound _ _ _ _ CKC) as CB_. cbn [cells_size csize Nat.add] in CB_.
  pose proof (rw_cells_bound _ _ _ _ COOKIE) as FB. cbn [cells_size csize Nat.add] in FB.
  pose proof (bytes_at_bound _ _ _ _ SRC) as BB. pose proof (zb_length o) as LZ. rewrite LZ in BB. unfold zlength in *.
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (CK, CK + 16); (D, D + Z.of_nat dn); (Fp + 40, Fp + 48); (Fp + 56, Fp + 64)]%Z m) as MU.
  pose proof (wmono_refl usegs m) as WM.
  pose_word_ranges.
  carve_frame 64%nat ST.
  do 15 zs.
  zs. replace (B + Z.of_nat (length o) - B)%Z with (Z.of_nat (length o)) by lia.
  zs. zs. brf K1; [exfalso; lia|]. zs. zs. zs. brf K2.
  - (* [comment removed for export] *)
    assert (O0 : length o = 0%nat) by lia. destruct o as [|c o']; [|cbn in O0; lia]. cbn [length Z.of_nat] in *.
    zs. brf K3; [exfalso; lia|]. zs. zs. if_lit.
    pose proof (rw_CB_length _ _ _ _ DST) as LJ.
    pose proof (u8arr_of_rw_cells _ _ _ _ _ DST) as DA. clear DST.
    pose proof (u8arr_store_ok usegs _ _ _ 0%Z (Z_to_bv 64 D) DA ltac:(rewrite LJ; lia) ltac:(f_equal; lia)) as SOK.
    zs. rewrite le1_zero. replace (Z_to_bv 64 D) with (wa (D + 0)) by (unfold wa; f_equal; lia).
    pose proof (u8arr_write usegs _ _ _ 0%Z (Z_to_bv 8 0) DA ltac:(rewrite LJ; lia)) as DA2. clear DA. store_done.
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
  - (* [comment removed for export] *)
    pose proof (rw_CB_length _ _ _ _ DST) as LJ.
    apply (rw_cells_split_CB usegs _ _ [] dn _ [] [length o; dn - length o]%nat) in DST; [ | cbn; lia ].
    cbn [mk_CB_cells app] in DST.
    apply (proj1 (rw_cells_app usegs _ _ [_] _)) in DST. destruct DST as [DSTa DSTb]. cbn [cells_size csize Nat.add] in DSTb. rewrite Nat.add_0_r in DSTb.
    zs. zs.
    eapply evt_cut.
    { eapply memcpy_callv with (src := zb o) (junk := firstn (length o) junk);
        [ exact SRC | rewrite LZ; lia | rewrite Nat2Z.id; exact DSTa | lia | lia | lia | lia | exact MI ]. }
    cbv beta. intros ms' P. unfold memcpy_postv in P.
    destruct P as (x5 & x6 & x7 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & x28 & x29 & x30 & x31 & m' & -> & MUc & WMc & MIc & DSTa' & SRC').
    lazymatch type of MUc with munch _ ?mm _ => transport_after_call usegs mm m' MUc WMc; clear MUc WMc; try clear MI end.
    replace (ret_pc (Z_to_bv 64 2857704)) with (Z_to_bv 64 2857704) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
    zs. zs. zs. zs. zs. zs.
    zs. brf K3; [exfalso; lia|]. zs. zs. if_lit.
    pose proof (rw_CB_length _ _ _ _ DSTb) as LJb.
    pose proof (u8arr_of_rw_cells _ _ _ _ _ DSTb) as DA. clear DSTb.
    pose proof (u8arr_store_ok usegs _ _ _ 0%Z (Z_to_bv 64 (D + Z.of_nat (length o))) DA ltac:(rewrite LJb; lia) ltac:(f_equal; lia)) as SOK.
    zs. rewrite le1_zero. replace (Z_to_bv 64 (D + Z.of_nat (length o))) with (wa (D + Z.of_nat (length o) + 0)) by (unfold wa; f_equal; lia).
    pose proof (u8arr_write usegs _ _ _ 0%Z (Z_to_bv 8 0) DA ltac:(rewrite LJb; lia)) as DA2. clear DA. store_done.
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
        assert (J : rw_cells usegs mm D ([] ++ [CB (length o) l1; CB (dn - length o) l2] ++ []));
        [ cbn [app]; apply (proj2 (rw_cells_app usegs _ _ [_] _)); split; [rewrite Nat2Z.id in Ha; exact Ha|]; cbn [cells_size csize]; rewrite Nat.add_0_r; exact Hb
        | apply rw_cells_merge in J; cbn [cells_size cells_bytes csize cbytes app] in J; rewrite app_nil_r in J ] end.
      replace (length o + (dn - length o + 0))%nat with dn in J by lia.
      rewrite upd_firstn_skipn in J by (rewrite length_firstn, length_skipn, LJ; lia). change (Z.to_nat 0) with 0%nat in J. rewrite firstn_O, app_nil_l in J.
      rewrite skipn_firstn_comm, skipn_skipn in J. replace (1 + length o)%nat with (S (length o)) in J by lia.
      rewrite firstn_all2 in J by (rewrite length_skipn, LJ; lia). first [exact J | let t := type of J in idtac "J:" t; match goal with |- ?g => idtac g end; fail]. }
    split; [assumption|]. split; [assumption|]. assumption.
Qed.
