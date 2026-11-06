(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import RT_defs CJ_iface AShadow ICPT_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require ICPT_pcsdefs.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_pcsdefs.SO_shadow.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import ICPT_musl.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import SFModel Arr.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Import Prelim.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import SFW1_lemmas.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import F_memset F_memcpy F_fwritex F_fmt_fp_lib.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import AImg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require StoreCache.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.StoreFast.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import StoreCache.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.
Open Scope bv_scope.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require StoreCache.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.LiaClosure.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.


(* [comment removed for export] *)
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac mem_after_store ::= mem_after_store_cached.
Local Ltac addr_eq_tac ::= addr_eq_tac_cached.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_cached segs m m' MU WM.
Local Ltac lia ::= lia3.
Local Ltac lia ::= lia4.
Local Ltac tlia ::= tlia4.
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
Proof using . intros. unfold zb. apply length_map. Qed.
Lemma rw_CB_length : forall m A n (bs : list byte), rw_cells asegs m A [CB n bs] -> length bs = n.
Proof using . intros m A n bs [[[H _] _] _]. exact H. Qed.
Lemma le1_zero : le1 (Z_to_bv 64 0) = [Z_to_bv 8 0].
Proof using . reflexivity. Qed.

(* [comment removed for export] *)
Definition SNW_DEPTH : Z := 2368.   (* [comment removed for export] *)

Definition sn_write_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (Fp CK D n B bufp : Z) (o : list Z) (dn : nat) (junk : list byte) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 2368, bv_unsigned sp); (CK, CK + 16); (D, D + Z.of_nat dn); (Fp + 40, Fp + 48); (Fp + 56, Fp + 64)]%Z m m'
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
  stk asegs m lo (bv_unsigned sp) -> (64 <= bv_unsigned sp)%Z -> mem_inv asegs m ->
  (* [comment removed for export] *)
  (B + zlength o <= D \/ D + Z.of_nat dn <= B)%Z ->
  (CK + 16 <= D \/ D + Z.of_nat dn <= CK)%Z ->
  (Fp + 160 <= D \/ D + Z.of_nat dn <= Fp + 40)%Z ->
  (D + Z.of_nat dn <= lo \/ bv_unsigned sp <= D)%Z ->
  (bv_unsigned sp <= CK)%Z -> (bv_unsigned sp <= Fp)%Z -> (bv_unsigned sp <= B)%Z ->
  (CK + 16 <= Fp + 40 \/ Fp + 160 <= CK)%Z ->
  (B + zlength o <= CK \/ CK + 16 <= B)%Z -> (B + zlength o <= Fp + 40 \/ Fp + 160 <= B)%Z ->
  (* [comment removed for export] *)
  MRT m -> (alloc_ceiling <= lo)%Z -> (lo + SNW_DEPTH <= bv_unsigned sp)%Z -> (B + zlength o + 64 <= 2^47)%Z ->
  app_range D (zlength o) -> wr_range_ok D (zlength o) -> ((0 < zlength o)%Z -> shadow_ok m D (zlength o)) ->
  evt asegs (sn_write_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Fp CK D n B bufp o dn junk lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x9aa30) fc None m (seg_rom asegs)).
Proof using .
  intros until lo. intros -> -> WPOS WBASE BUF COOKIE CKC SRC DST ROOM Hn Hbufp BHI ST SPLO MI D1 D2 D3 D4 S1 S2 S3 S4 S5 S6.
  intros MR CEIL SPB B47 ARd WRd SOd.
  unfold SNW_DEPTH in SPB. pose proof CEIL as CE. unfold alloc_ceiling, sp_window_lo, stack_max_size in CE.
  pose proof AINTRIN_STACK_val as AIS.
  pose proof (rw_cells_bound _ _ _ _ DST) as DB. cbn [cells_size csize Nat.add] in DB.
  pose proof (rw_cells_bound _ _ _ _ CKC) as CB_. cbn [cells_size csize Nat.add] in CB_.
  pose proof (rw_cells_bound _ _ _ _ COOKIE) as FB. cbn [cells_size csize Nat.add] in FB.
  pose proof (bytes_at_bound _ _ _ _ SRC) as BB. pose proof (zb_length o) as LZ. rewrite LZ in BB. unfold zlength in *.
  pose proof (munch_refl [(bv_unsigned sp - 2368, bv_unsigned sp); (CK, CK + 16); (D, D + Z.of_nat dn); (Fp + 40, Fp + 48); (Fp + 56, Fp + 64)]%Z m) as MU.
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)]%Z m) as MUf.   (* [comment removed for export] *)
  pose proof (wmono_refl asegs m) as WM.
  pose_word_ranges.
  carve_frame 64%nat ST.
  do 15 zs.
  zs. replace (B + Z.of_nat (length o) - B)%Z with (Z.of_nat (length o)) by lia.
  zs. zs. brf K1; [exfalso; lia|]. zs. zs. zs. brf K2.
  - (* [comment removed for export] *)
    clear MUf.
    assert (O0 : length o = 0%nat) by lia. destruct o as [|c o']; [|cbn in O0; lia]. cbn [length Z.of_nat] in *.
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
  - (* [comment removed for export] *)
    pose proof (rw_CB_length _ _ _ _ DST) as LJ.
    apply (rw_cells_split_CB asegs _ _ [] dn _ [] [length o; dn - length o]%nat) in DST; [ | cbn; lia ].
    cbn [mk_CB_cells app] in DST.
    apply (proj1 (rw_cells_app asegs _ _ [_] _)) in DST. destruct DST as [DSTa DSTb]. cbn [cells_size csize Nat.add] in DSTb. rewrite Nat.add_0_r in DSTb.
    zs. zs.
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m0 _) =>
    assert (AIf : Forall app_iv [(bv_unsigned sp - 64, bv_unsigned sp)]%Z)
      by (apply Forall_cons; [apply app_iv_stack; lia| apply Forall_nil]);
    assert (MR1 : MRT m0)
      by (eapply (MRT_munch _ m m0); [exact MR| exact MUf|]; apply Forall_cons; [apply mrt_iv_ok_stack; lia| apply Forall_nil]);
    assert (SOd1 : (0 < Z.of_nat (length o))%Z -> shadow_ok m0 D (Z.of_nat (length o)))
      by (intros Hl; eapply shadow_ok_munch_app; [apply SOd; exact Hl| exact MUf| lia| exact ARd| exact AIf])
    end.
    clear MUf.
    callsp memcpy_icpt_callv.
    1:{ exact SRC. } 1:{ rewrite LZ. reflexivity. } 1:{ rewrite Nat2Z.id. exact DSTa. }
    1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ exact MI. }
    1:{ exact (MRT_icpt _ MR1). } 1:{ exact ST. } 1:{ exact CEIL. } 1:{ lia. } 1:{ lia. }
    1:{ apply app_range_stack; unfold KHIGHMEM_END; lia. } 1:{ exact ARd. } 1:{ exact WRd. }
    1:{ intros Hl. apply (MRT_shadow_ok_stack _ _ _ MR1); lia. } 1:{ exact SOd1. }
    1:{ lia. } 1:{ lia. }
    clear MR1 SOd1. match goal with H : stk asegs _ lo _ |- _ => rename H into ST end.
    match goal with H : mem_inv asegs _ |- _ => rename H into MIc end.
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


End CeilWrap.
(* [comment removed for export] *)
Notation mem := (word -> option byte).
Ltac zs := zstep; try (fix_litstore; mem_after_store_opt).
Ltac fixK K := try (rewrite ?swrap32_small in K by lia); try (rewrite ?signed_of_Z in K by lia); try (rewrite ?Z.add_0_r in K).
Ltac brf K := if_cases K; zify_cond K; fixK K.
Ltac br K := brf K; try (exfalso; lia).
Ltac if_lit :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => let v := eval vm_compute in c in change c with v; cbv iota
  end.
