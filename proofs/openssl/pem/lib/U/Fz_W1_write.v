(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP SFModel Ubs.
From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Layout. From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Str_cpy. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import F_memcpy. From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Th_kit Fz_T_kit. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Fz_T_ekit Fz_W1_defs Fz_W1_bits Fz_W1_bioflags Fz_W1_sync Fz_W1_grow.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Notation z64 := (Z_to_bv 64 0) (only parsing).

(* [comment removed for export] *)
Definition tbox (P : Prop) : Prop := P.

Ltac box H := let T := type of H in change (tbox T) in H.
Ltac unbox H := unfold tbox in H.

(* [comment removed for export] *)
Lemma c4_bytes_view : forall segs m A fl, 0 <= fl < 2 ^ 31 ->
  rw_cells segs m A [C4 (Z_to_bv 64 fl)] <-> rw_cells segs m A [C1 (Z_to_bv 8 fl); C1 (Z_to_bv 8 (fl ≫ 8)); C1 (Z_to_bv 8 (fl ≫ 8 ≫ 8)); C1 (Z_to_bv 8 (fl ≫ 8 ≫ 8 ≫ 8))].
Proof.
  intros segs m A fl R.
  assert (EB : cells_bytes [C4 (Z_to_bv 64 fl)] = cells_bytes [C1 (Z_to_bv 8 fl); C1 (Z_to_bv 8 (fl ≫ 8)); C1 (Z_to_bv 8 (fl ≫ 8 ≫ 8)); C1 (Z_to_bv 8 (fl ≫ 8 ≫ 8 ≫ 8))]).
  { cbn [cells_bytes cbytes app]. unfold le4. rewrite unsigned_lit by lia. reflexivity. }
  split; intros H.
  - apply (th_cells_congr segs m A _ _ EB); [reflexivity| cbn; tauto| exact H].
  - apply (th_cells_congr segs m A _ _ (eq_sym EB)); [reflexivity| cbn; tauto| exact H].
Qed.

Definition W1_write_fit_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo BI BB BM RP D len max off fl inl IN : Z) (rmaxw flw : word) (junk src : list byte),
    a0 = Z_to_bv 64 BI -> a1 = Z_to_bv 64 IN -> a2 = Z_to_bv 64 inl -> 0 < BI -> 0 < IN -> 0 < inl ->
    ro_cells usegs m (BI + 40) [C4 (Z_to_bv 64 1)] -> rw_cells usegs m (BI + 48) [C4 (Z_to_bv 64 fl)] -> fl_ok fl ->
    ro_cells usegs m (BI + 64) [C8 (Z_to_bv 64 BB)] ->
    0 < BB -> ro_cells usegs m BB [C8 (Z_to_bv 64 BM); C8 (Z_to_bv 64 RP)] ->
    0 < BM -> rw_cells usegs m BM (bufmem_cells len D max flw) ->
    0 < RP -> rw_cells usegs m RP (readp_cells len D off rmaxw flw) ->
    0 < D -> 0 <= off <= len -> len <= max -> max < 2 ^ 31 -> D + max < 2 ^ 63 -> len - off + inl <= max ->
    length junk = Z.to_nat max -> rw_cells usegs m D [CB (Z.to_nat max) junk] ->
    bytes_at usegs m IN src -> length src = Z.to_nat inl ->
    BI mod 8 = 0 -> BB mod 8 = 0 -> BM mod 8 = 0 -> RP mod 8 = 0 ->
    stk usegs m lo (bv_unsigned sp) -> 0 <= lo -> lo <= bv_unsigned sp - 112 ->
    BI + 72 <= lo -> BB + 16 <= lo -> BM + 32 <= lo -> RP + 32 <= lo -> D + max <= lo ->
    (D + max <= BB \/ BB + 16 <= D) -> (D + max <= BM \/ BM + 32 <= D) -> (D + max <= RP \/ RP + 32 <= D) -> (BM + 32 <= RP \/ RP + 32 <= BM) ->
    tbox ((IN + inl <= lo \/ bv_unsigned sp <= IN) /\ (IN + inl <= BI + 48 \/ BI + 52 <= IN) /\ (IN + inl <= D \/ D + max <= IN)
          /\ (IN + inl <= BM \/ BM + 32 <= IN) /\ (IN + inl <= RP \/ RP + 32 <= IN)
          /\ (BI + 52 <= D \/ D + max <= BI + 48) /\ (BI + 52 <= BM \/ BM + 32 <= BI + 48) /\ (BI + 52 <= RP \/ RP + 32 <= BI + 48)
          /\ (BI + 52 <= BB \/ BB + 16 <= BI + 48) /\ (BB + 16 <= BM \/ BM + 32 <= BB) /\ (BB + 16 <= RP \/ RP + 32 <= BB)) ->
    mem_inv usegs m ->
    evt usegs (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (fl' : Z) (junk' : list byte) (m' : mem),
                 ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 inl) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                          F (ret_pc ra) fc None m' (seg_rom usegs)
                 /\ munch [(bv_unsigned sp - 112, bv_unsigned sp); (BI + 48, BI + 52); (D, D + max); (BM, BM + 8); (RP, RP + 32)] m m'
                 /\ wmono usegs m m' /\ mem_inv usegs m'
                 /\ stk usegs m' lo (bv_unsigned sp)
                 /\ fl_ok fl' /\ rw_cells usegs m' (BI + 48) [C4 (Z_to_bv 64 fl')]
                 /\ rw_cells usegs m' BM (bufmem_cells (len - off + inl) D max flw)
                 /\ rw_cells usegs m' RP (readp_cells (len - off + inl) D 0 (Z_to_bv 64 max) flw)
                 /\ length junk' = Z.to_nat max /\ rw_cells usegs m' D [CB (Z.to_nat max) junk'])
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x1832b0) fc None m (seg_rom usegs)).

Theorem W1_write_fit_proof : W1_write_fit_stmt.
Proof.
  unfold W1_write_fit_stmt, bufmem_cells, readp_cells. intros until src.
  intros -> -> -> HBI HIN HINL INITC FLC FLOK PTRC HBB BBC HBM BMC HRP RPC HD HOFF HLEN HMAX HD63 HFIT LJ DBLK SRC LSRC ALBI ALBB ALBM ALRP ST LO0 LO
         SBI SBB SBM SRP SD APDB APDM APDR APMR BOX MI.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 112, bv_unsigned sp); (BI + 48, BI + 52); (D, D + max); (BM, BM + 8); (RP, RP + 32)]%Z m) as MU.
  pose proof (wmono_refl usegs m) as WM.
  pose proof (fl_ok_byte1 fl FLOK) as RDO. destruct FLOK as [FLR FLB].
  pose proof (bytes_at_bound _ _ _ _ SRC) as INB. rewrite LSRC, Z2Nat.id in INB by lia.
  change (bytes_at usegs m IN src) with (tbox (bytes_at usegs m IN src)) in SRC.
  apply (proj1 (c4_bytes_view usegs m (BI + 48) fl FLR)) in FLC.
  (* [comment removed for export] *)
  ths. th_frame 64%nat [8; 8; 8; 8; 8; 8; 8; 8]%nat ST. do 8 ths.
  ths. ubs_if. ths. ths. ths. ubs_if. ths. ths. ths. if_cases K0; zify_cond K0. { exfalso. apply K0. exact RDO. }
  do 5 ths. ths.
  lazymatch goal with H : rw_cells usegs ?mm (BI + 48) _ |- _ => apply (proj2 (c4_bytes_view usegs mm (BI + 48) fl FLR)) in H end.
  (* [comment removed for export] *)
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename mc into ma end.
  box BBC. box BMC. box RPC. box DBLK.
  pose proof (munch_refl [(bv_unsigned sp - 112, bv_unsigned sp); (BI + 48, BI + 52)]%Z ma) as MUcf. pose proof (wmono_refl usegs ma) as WMcf.
  tcallr W1_bio_clear15_proof.
  all: try first [eassumption | lia].
  cbv beta delta [mkR].
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename mc into mb end.
  unbox BBC. unbox BMC. unbox RPC. unbox DBLK.
  assert (BBCb : ro_cells usegs mb BB [C8 (Z_to_bv 64 BM); C8 (Z_to_bv 64 RP)]).
  { unfold tbox in BOX. destruct BOX as (_ & _ & _ & _ & _ & _ & _ & _ & B9 & _ & _). eapply ro_cells_transport; [exact BBC| exact MUcf| cbn [disjoint_from cells_size csize Nat.add]; lia]. }
  assert (BMCb : rw_cells usegs mb BM [C8 (Z_to_bv 64 len); C8 (Z_to_bv 64 D); C8 (Z_to_bv 64 max); C8 flw]).
  { unfold tbox in BOX. destruct BOX as (_ & _ & _ & _ & _ & _ & B7 & _ & _ & _ & _). eapply rw_cells_transport; [exact BMC| exact MUcf| exact WMcf| cbn [disjoint_from cells_size csize Nat.add]; lia]. }
  assert (RPCb : rw_cells usegs mb RP [C8 (Z_to_bv 64 (len - off)); C8 (Z_to_bv 64 (D + off)); C8 rmaxw; C8 flw]).
  { unfold tbox in BOX. destruct BOX as (_ & _ & _ & _ & _ & _ & _ & B8 & _ & _ & _). eapply rw_cells_transport; [exact RPC| exact MUcf| exact WMcf| cbn [disjoint_from cells_size csize Nat.add]; lia]. }
  assert (DBLKb : rw_cells usegs mb D [CB (Z.to_nat max) junk]).
  { unfold tbox in BOX. destruct BOX as (_ & _ & _ & _ & _ & B6 & _ & _ & _ & _ & _). eapply rw_cells_transport; [exact DBLK| exact MUcf| exact WMcf| cbn [disjoint_from cells_size csize Nat.add]; lia]. }
  clear BBC BMC RPC DBLK MUcf WMcf.
  (* [comment removed for export] *)
  lazymatch goal with H : rw_cells usegs mb (BI + 48) _ |- _ => rename H into FLCb end.
  box FLCb.
  pose proof (munch_refl [(bv_unsigned sp - 112, bv_unsigned sp); (D, D + max); (BM, BM + 8); (RP, RP + 32)]%Z mb) as MUb. pose proof (wmono_refl usegs mb) as WMb.
  (* [comment removed for export] *)
  pose proof BBCb as BBX. box BBX.
  assert (BBAT : forall mx, munch [(bv_unsigned sp - 112, bv_unsigned sp); (D, D + max); (BM, BM + 8); (RP, RP + 32)]%Z mb mx ->
                            ro_cells usegs mx BB [C8 (Z_to_bv 64 BM); C8 (Z_to_bv 64 RP)]).
  { intros mx MX. unfold tbox in BOX, BBX. destruct BOX as (_ & _ & _ & _ & _ & _ & _ & _ & _ & B10 & B11).
    eapply ro_cells_transport; [exact BBX| exact MX| cbn [disjoint_from cells_size csize Nat.add]; lia]. }
  (* [comment removed for export] *)
  ths. if_cases KA; zify_cond KA. { exfalso. apply andb_false_iff in KA. destruct KA as [KA|KA]; apply Z.ltb_ge in KA; lia. }
  ths. if_cases KB; zify_cond KB. { exfalso. rewrite ?unsigned_lit in KB by lia. lia. }
  ths. ubs_if. ths. ths. ubs_if. ths. ths. ubs_if. ths. ths. ubs_if. ths. ths. ths.
  tcallr W1_sync_proof.
  all: try first [eassumption | lia].
  cbv beta delta [mkR]. unfold bufmem_cells, readp_cells in *.
  (* [comment removed for export] *)
  pose proof (BBAT _ MUb) as BBC1.
  ths. ths. ths.
  pose proof W1_grow_fit_proof as FIT. unfold W1_grow_fit_stmt, bufmem_cells in FIT.
  tcall (FIT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo BM D (len - off) max (len - off + inl) _ _).
  all: try first [eassumption | reflexivity | lia].
  clear FIT. cbv beta delta [mkR]. unfold bufmem_cells, readp_cells in *.
  (* [comment removed for export] *)
  pose proof (BBAT _ MUb) as BBC2.
  ths. if_cases KC; zify_cond KC. { exfalso. rewrite ?unsigned_lit in KC by lia. lia. }
  ths. ths. ubs_if. ths. ths. ubs_if. ths. ths. ths. if_cases KD; zify_cond KD. { exfalso. rewrite ?unsigned_lit in KD by lia. lia. }
  ths. ths. ths. ths.
  rewrite ?v_sltu_b2z, ?v_sltiu_b2z. rewrite ?(unsigned_lit 0), ?(unsigned_lit D), ?(unsigned_lit (len - off + D)) by lia. try change (bv_wrap 64 1) with 1.
  replace (0 <? D) with true by (symmetry; apply Z.ltb_lt; lia). replace (len - off + D <? 1) with false by (symmetry; apply Z.ltb_ge; lia). cbn [Z.b2z]. th_if_lit.
  ths. ths. ths.
  replace (len - off + D) with (D + (len - off)) by lia.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into mc end.
  assert (SRCc : bytes_at usegs mc IN src).
  { unfold tbox in BOX, SRC. destruct BOX as (B1 & B2 & B3 & B4 & B5 & _).
    eapply bytes_at_transport; [exact SRC| exact MU| rewrite LSRC, Z2Nat.id by lia; cbn [disjoint_from]; lia]. }
  lazymatch goal with H : rw_cells usegs mc D [CB (Z.to_nat max) ?jj], HL : length ?jj = Z.to_nat max |- _ => rename H into DBc; rename jj into jc; rename HL into LJc end.
  destruct (rw_cells_CB_split_at usegs mc D (Z.to_nat max) jc (Z.to_nat (len - off)) ltac:(lia) DBc) as [DA DBC].
  destruct (rw_cells_CB_split_at usegs mc (D + Z.of_nat (Z.to_nat (len - off))) (Z.to_nat max - Z.to_nat (len - off)) (skipn (Z.to_nat (len - off)) jc) (Z.to_nat inl) ltac:(lia) DBC) as [DB DC].
  rewrite Z2Nat.id in DB, DC by lia. rewrite Z2Nat.id in DC by lia. clear DBC DBc.
  assert (SEPS : IN + inl <= D + (len - off) \/ D + (len - off) + inl <= IN) by (unfold tbox in BOX; destruct BOX as (_ & _ & B3 & _); lia).
  tcall (memcpy_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ src _).
  all: try first [eassumption | lia].
  cbv beta delta [mkR]. clear SEPS.
  lazymatch goal with Hz : rw_cells _ ?mm (D + (len - off)) [CB _ src] |- _ =>
    pose proof (rw_cells_CB_join usegs mm D _ _ _ _ ltac:(eassumption) ltac:(rewrite Z2Nat.id by lia; exact Hz)) as J1 end.
  lazymatch goal with Hc : rw_cells _ ?mm (D + (len - off) + inl) _ |- _ =>
    pose proof (rw_cells_CB_join usegs mm D _ _ _ _ J1 ltac:(rewrite Nat2Z.inj_add, !Z2Nat.id by lia; rewrite Z.add_assoc; exact Hc)) as J2 end.
  replace (Z.to_nat (len - off) + Z.to_nat inl + (Z.to_nat max - Z.to_nat (len - off) - Z.to_nat inl))%nat with (Z.to_nat max) in J2 by lia.
  (* [comment removed for export] *)
  pose proof (BBAT _ MUb) as BBC3.
  ths. ths. ths. ths. ths. ths. ths. ths. ths. ths.
  ths. ths. do 7 ths.
  lazymatch goal with FRh : rw_cells _ _ (bv_unsigned sp + -64) _ |- _ => th_release FRh (bv_unsigned sp) end.
  ths. ths.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into me end.
  assert (FLCe : rw_cells usegs me (BI + 48) [C4 (Z_to_bv 64 (Z.land fl 18446744073709551600))]).
  { unfold tbox in BOX, FLCb. destruct BOX as (_ & _ & _ & _ & _ & B6 & B7 & B8 & _).
    eapply rw_cells_transport; [exact FLCb| exact MUb| exact WMb| cbn [disjoint_from cells_size csize Nat.add]; lia]. }
  apply evt_done. do 14 eexists. exists (Z.land fl 18446744073709551600). eexists. eexists. split; [cbv delta [mkR]; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [eassumption|].
  split; [apply fl_ok_land; [split; assumption| lia]|]. split; [exact FLCe|].
  split; [eassumption|].
  split; [replace (len - off + inl - 0) with (len - off + inl) by lia; replace (D + 0) with D by lia; eassumption|].
  split; [| eassumption].
  rewrite !length_app, firstn_length, !skipn_length. lia.
Qed.
