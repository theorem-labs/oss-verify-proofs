(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP SFModel Ubs.
From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Layout. From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Str_cpy. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import F_memcpy. From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Th_kit Fz_T_kit. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Fz_T_ekit Fz_W1_defs Fz_W1_bits Fz_W1_bits2 Fz_W1_bioflags Fz_W1_sync Fz_W1_write.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Lemma t_sextw_small : forall z, 0 <= z < 2 ^ 31 -> bv_swrap 32 (bv_unsigned (Z_to_bv 64 z) + 0) = z.
Proof.
  intros z Hz. rewrite unsigned_lit by lia. rewrite Z.add_0_r. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 32) with (2 ^ 32). change (2 ^ 32 `div` 2) with (2 ^ 31). rewrite Z.mod_small by lia. lia.
Qed.

Definition W1_read_data_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo BI BB BM RP D len max off fl outl OUT : Z) (rmaxw flw : word) (junk ojunk : list byte),
    a0 = Z_to_bv 64 BI -> a1 = Z_to_bv 64 OUT -> a2 = Z_to_bv 64 outl -> 0 < BI -> 0 < OUT -> 0 < outl < 2 ^ 31 ->
    rw_cells usegs m (BI + 48) [C4 (Z_to_bv 64 fl)] -> fl_ok fl -> ro_cells usegs m (BI + 64) [C8 (Z_to_bv 64 BB)] ->
    0 < BB -> BB + 16 < 2 ^ 63 -> ro_cells usegs m BB [C8 (Z_to_bv 64 BM); C8 (Z_to_bv 64 RP)] ->
    0 < RP -> rw_cells usegs m RP (readp_cells len D off rmaxw flw) ->
    0 < D -> 0 <= off -> off < len -> len <= max -> max < 2 ^ 31 -> D + max < 2 ^ 63 ->
    length junk = Z.to_nat max -> rw_cells usegs m D [CB (Z.to_nat max) junk] ->
    length ojunk = Z.to_nat outl -> rw_cells usegs m OUT [CB (Z.to_nat outl) ojunk] ->
    BI mod 8 = 0 -> BB mod 8 = 0 -> RP mod 8 = 0 ->
    stk usegs m lo (bv_unsigned sp) -> 0 <= lo -> lo <= bv_unsigned sp - 80 ->
    BI + 72 <= lo -> BB + 16 <= lo -> RP + 32 <= lo -> D + max <= lo ->
    (D + max <= RP \/ RP + 32 <= D) -> (OUT + outl <= D \/ D + max <= OUT) -> (OUT + outl <= RP \/ RP + 32 <= OUT) ->
    tbox ((OUT + outl <= lo \/ bv_unsigned sp <= OUT) /\ (OUT + outl <= BI + 48 \/ BI + 52 <= OUT)
          /\ (BI + 52 <= D \/ D + max <= BI + 48) /\ (BI + 52 <= RP \/ RP + 32 <= BI + 48)) ->
    mem_inv usegs m ->
    evt usegs (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' rmaxw' : word) (fl' : Z) (ojunk' : list byte) (m' : mem),
                 ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (Z.min outl (len - off))) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                          F (ret_pc ra) fc None m' (seg_rom usegs)
                 /\ munch [(bv_unsigned sp - 80, bv_unsigned sp); (BI + 48, BI + 52); (OUT, OUT + outl); (RP, RP + 24)] m m'
                 /\ wmono usegs m m' /\ mem_inv usegs m'
                 /\ stk usegs m' lo (bv_unsigned sp)
                 /\ fl_ok fl' /\ rw_cells usegs m' (BI + 48) [C4 (Z_to_bv 64 fl')]
                 /\ rw_cells usegs m' RP (readp_cells len D (off + Z.min outl (len - off)) rmaxw' flw)
                 /\ length ojunk' = Z.to_nat outl /\ rw_cells usegs m' OUT [CB (Z.to_nat outl) ojunk'])
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x183440) fc None m (seg_rom usegs)).

Theorem W1_read_data_proof : W1_read_data_stmt.
Proof.
  unfold W1_read_data_stmt, readp_cells. intros until ojunk.
  intros -> -> -> HBI HOUT HOUTL FLC FLOK PTRC HBB HBB63 BBC HRP RPC HD HOFF0 HOFF HLEN HMAX HD63 LJ DBLK LOJ OUTB ALBI ALBB ALRP ST LO0 LO SBI SBB SRP SD APDR APOD APOR BOX MI.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp); (BI + 48, BI + 52); (OUT, OUT + outl); (RP, RP + 24)]%Z m) as MU.
  pose proof (wmono_refl usegs m) as WM.
  pose proof (fl_ok_sel fl FLOK) as SEL. destruct FLOK as [FLR FLB].
  pose proof (rw_cells_bound _ _ _ _ OUTB) as OB. cbn [cells_size csize Nat.add] in OB. rewrite Nat.add_0_r, Z2Nat.id in OB by lia.
  (* [comment removed for export] *)
  box RPC. box DBLK. box OUTB.
  pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp); (BI + 48, BI + 52)]%Z m) as MUp. pose proof (wmono_refl usegs m) as WMp.
  ths. th_frame 64%nat [8; 8; 8; 8; 8; 8; 8; 8]%nat ST. do 8 ths.
  ths. ubs_if. ths. ths. ths. ubs_if. ths. ths. ubs_if. ths. ths. ths. ubs_if.
  ths. ths. rewrite (t_sx32_small fl) by lia. ths. ths. ths. ths.
  rewrite SEL.
  ths. ths. ths. ths.
  tcallr W1_bio_clear15_proof.
  all: try first [eassumption | lia].
  cbv beta delta [mkR].
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename mc into mb end.
  unbox RPC. unbox DBLK. unbox OUTB. unfold tbox in BOX. destruct BOX as (B1 & B2 & B3 & B4).
  assert (RPCb : rw_cells usegs mb RP [C8 (Z_to_bv 64 (len - off)); C8 (Z_to_bv 64 (D + off)); C8 rmaxw; C8 flw])
    by (eapply rw_cells_transport; [exact RPC| exact MUp| exact WMp| cbn [disjoint_from cells_size csize Nat.add]; lia]).
  assert (DBLKb : rw_cells usegs mb D [CB (Z.to_nat max) junk])
    by (eapply rw_cells_transport; [exact DBLK| exact MUp| exact WMp| cbn [disjoint_from cells_size csize Nat.add]; lia]).
  assert (OUTBb : rw_cells usegs mb OUT [CB (Z.to_nat outl) ojunk])
    by (eapply rw_cells_transport; [exact OUTB| exact MUp| exact WMp| cbn [disjoint_from cells_size csize Nat.add]; lia]).
  clear RPC DBLK OUTB MUp WMp.
  lazymatch goal with H : rw_cells usegs mb (BI + 48) _ |- _ => rename H into FLCb end.
  assert (FLAT : forall mx, munch [(OUT, OUT + outl); (RP, RP + 24)]%Z mb mx -> wmono usegs mb mx ->
                            rw_cells usegs mx (BI + 48) [C4 (Z_to_bv 64 (Z.land fl 18446744073709551600))]).
  { intros mx MX WX. eapply rw_cells_transport; [exact FLCb| exact MX| exact WX| cbn [disjoint_from cells_size csize Nat.add]; lia]. }
  clear B2 B3 B4. box FLCb.
  pose proof (munch_refl [(OUT, OUT + outl); (RP, RP + 24)]%Z mb) as MUb. pose proof (wmono_refl usegs mb) as WMb.
  (* [comment removed for export] *)
  ths. if_cases KS; zify_cond KS. { exfalso. lia. }
  ths. ubs_if. ths. ths. ubs_if.
  ths.
  assert (EMIN : forall P : Z -> Prop, P (Z.min outl (len - off)) -> (len - off < outl -> P (len - off)) /\ (outl <= len - off -> P outl)).
  { intros P HP. split; intros HH; [rewrite Z.min_r in HP by lia| rewrite Z.min_l in HP by lia]; exact HP. }
  clear EMIN.
  ths. if_cases KM; zify_cond KM.
  - (* [comment removed for export] *)
    ths. ths. if_cases KO; zify_cond KO. { exfalso. rewrite ?unsigned_lit in KO by lia. lia. }
    ths. if_cases KR; zify_cond KR. { exfalso. rewrite ?unsigned_lit in KR by lia. lia. }
    ths. ths. ths. ths.
    destruct (rw_cells_CB_split_at usegs mb D (Z.to_nat max) junk (Z.to_nat off) ltac:(lia) DBLKb) as [DA DBC].
    destruct (rw_cells_CB_split_at usegs mb (D + Z.of_nat (Z.to_nat off)) (Z.to_nat max - Z.to_nat off) (skipn (Z.to_nat off) junk) (Z.to_nat (len - off)) ltac:(lia) DBC) as [DB DC].
    rewrite Z2Nat.id in DB by lia. clear DBC DC DA.
    pose proof (rw_cells_bytes_at usegs mb (D + off) _ DB) as SRCB. cbn [cells_bytes cbytes] in SRCB. rewrite app_nil_r in SRCB.
    destruct (rw_cells_CB_split_at usegs mb OUT (Z.to_nat outl) ojunk (Z.to_nat (len - off)) ltac:(lia) OUTBb) as [OA OB2].
    rewrite Z2Nat.id in OB2 by lia. clear OUTBb DB.
    assert (SEPS : D + off + (len - off) <= OUT \/ OUT + (len - off) <= D + off) by lia.
    tcall (memcpy_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (firstn (Z.to_nat (len - off)) (skipn (Z.to_nat off) junk)) _).
    all: try first [eassumption | lia | rewrite firstn_length, skipn_length; lia].
    cbv beta delta [mkR]. clear SEPS.
    lazymatch goal with Ha : rw_cells _ ?mm OUT [CB _ (firstn _ (skipn _ junk))], Hb : rw_cells _ ?mm (OUT + (len - off)) _ |- _ =>
      pose proof (rw_cells_CB_join usegs mm OUT _ _ _ _ Ha ltac:(rewrite Z2Nat.id by lia; exact Hb)) as JO end.
    replace (Z.to_nat (len - off) + (Z.to_nat outl - Z.to_nat (len - off)))%nat with (Z.to_nat outl) in JO by lia.
    ths. ths. ths. ths. ths. ths. ths. ths.
    ths. if_cases KP; zify_cond KP. { exfalso. rewrite ?unsigned_lit in KP by lia. lia. }
    ths. ubs_if. ths. ubs_if.
    ths. ths.
    ths. rewrite (t_sextw_small (len - off)) by lia.
    do 7 ths.
    lazymatch goal with FRh : rw_cells _ _ (bv_unsigned sp + -64) _ |- _ => th_release FRh (bv_unsigned sp) end.
    ths. ths.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into me end.
    pose proof (FLAT _ MUb WMb) as FLCe.
    replace (Z.min outl (len - off)) with (len - off) by lia.
    apply evt_done. do 15 eexists. exists (Z.land fl 18446744073709551600). eexists. eexists. split; [cbv delta [mkR]; reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [eassumption|].
    split; [apply fl_ok_land; [split; assumption| lia]|]. split; [exact FLCe|].
    split. { rewrite ?(unsigned_lit (len - off)) in * by lia. rewrite ?(Z.add_comm (len - off) (D + off)) in *. replace (len - (off + (len - off))) with (len - off + - (len - off)) by lia. replace (D + (off + (len - off))) with (D + off + (len - off)) by lia. eassumption. }
    split; [| exact JO].
    rewrite length_app, firstn_length, !skipn_length. lia.
  - (* [comment removed for export] *)
    ths. ths.
    ths. if_cases KO; zify_cond KO. { exfalso. rewrite ?unsigned_lit in KO by lia. lia. }
    ths. if_cases KR; zify_cond KR. { exfalso. rewrite ?unsigned_lit in KR by lia. lia. }
    ths. ths. ths. ths.
    destruct (rw_cells_CB_split_at usegs mb D (Z.to_nat max) junk (Z.to_nat off) ltac:(lia) DBLKb) as [DA DBC].
    destruct (rw_cells_CB_split_at usegs mb (D + Z.of_nat (Z.to_nat off)) (Z.to_nat max - Z.to_nat off) (skipn (Z.to_nat off) junk) (Z.to_nat (outl)) ltac:(lia) DBC) as [DB DC].
    rewrite Z2Nat.id in DB by lia. clear DBC DC DA.
    pose proof (rw_cells_bytes_at usegs mb (D + off) _ DB) as SRCB. cbn [cells_bytes cbytes] in SRCB. rewrite app_nil_r in SRCB.
    destruct (rw_cells_CB_split_at usegs mb OUT (Z.to_nat outl) ojunk (Z.to_nat (outl)) ltac:(lia) OUTBb) as [OA OB2].
    rewrite Z2Nat.id in OB2 by lia. clear OUTBb DB.
    assert (SEPS : D + off + (outl) <= OUT \/ OUT + (outl) <= D + off) by lia.
    tcall (memcpy_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (firstn (Z.to_nat (outl)) (skipn (Z.to_nat off) junk)) _).
    all: try first [eassumption | lia | rewrite firstn_length, skipn_length; lia].
    cbv beta delta [mkR]. clear SEPS.
    lazymatch goal with Ha : rw_cells _ ?mm OUT [CB _ (firstn _ (skipn _ junk))], Hb : rw_cells _ ?mm (OUT + (outl)) _ |- _ =>
      pose proof (rw_cells_CB_join usegs mm OUT _ _ _ _ Ha ltac:(rewrite Z2Nat.id by lia; exact Hb)) as JO end.
    replace (Z.to_nat (outl) + (Z.to_nat outl - Z.to_nat (outl)))%nat with (Z.to_nat outl) in JO by lia.
    ths. ths. ths. ths. ths. ths. ths. ths.
    ths. if_cases KP; zify_cond KP. { exfalso. rewrite ?unsigned_lit in KP by lia. lia. }
    ths. ubs_if. ths. ubs_if.
    ths. ths.
    ths. rewrite (t_sextw_small (outl)) by lia.
    do 7 ths.
    lazymatch goal with FRh : rw_cells _ _ (bv_unsigned sp + -64) _ |- _ => th_release FRh (bv_unsigned sp) end.
    ths. ths.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into me end.
    pose proof (FLAT _ MUb WMb) as FLCe.
    replace (Z.min outl (len - off)) with (outl) by lia.
    apply evt_done. do 15 eexists. exists (Z.land fl 18446744073709551600). eexists. eexists. split; [cbv delta [mkR]; reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [eassumption|].
    split; [apply fl_ok_land; [split; assumption| lia]|]. split; [exact FLCe|].
    split. { rewrite ?(unsigned_lit (outl)) in * by lia. rewrite ?(Z.add_comm outl (D + off)) in *. replace (len - (off + (outl))) with (len - off + - (outl)) by lia. replace (D + (off + (outl))) with (D + off + (outl)) by lia. eassumption. }
    split; [| exact JO].
    rewrite length_app, firstn_length, !skipn_length. lia.
Qed.
