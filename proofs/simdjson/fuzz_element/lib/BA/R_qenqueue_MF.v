(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac ImageA Arr Walk Image.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Malloc Require Import MallocKit_AB.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Layout R_small R_m2s. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import R_cache_defs R_prim_defs R_asan_defs R_prim_kit R_glue_defs R_depot_defs R_quar_defs R_qenqueue R_qenqueue_N R_refill R_qenqueue_M.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
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
Local Ltac zidle_end m :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch goal with MU : munch _ m mm, WM : wmono _ m mm |- _ =>
      unfold zidle in *; transport_after_call_fast asegs m mm MU WM end end.
Notation mem := (word -> option byte).
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.

Lemma qenq_miss_B_full_spec : forall ra0 sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    ra s0 s1 s2 s3 s4 s5 (F : bvmap 5 word) fc (m : mem) (T stack M n SB lo cnt mc : Z) (ws24 : list word) (w stj : word)
    (jb jf : list byte) (pre : list batch) (b0 : Z) (ents0 : list (Z * Z)),
  (1 <= n <= 2^28)%Z -> length ents0 = 1021%nat ->
  qcache_rep m (qcacheT T) (pre ++ [(b0, ents0)]) ->
  qwf SB (pre ++ [(b0, ents0); (chunk_addr SB 24 w, [(M, n)])]) ->
  (qbytes (pre ++ [(b0, ents0)]) + n + 8192 < 2^63)%Z ->
  qnew_cells m T SB cnt mc ws24 w stj jb -> (1 <= cnt <= 16)%Z -> (0 <= mc < 2^31)%Z -> length ws24 = 16%nat ->
  nth_error ws24 (Z.to_nat (cnt - 1)) = Some w ->
  (T + 4096 <= r24 SB \/ r24 SB + 2^32 <= T)%Z -> (0 < T)%Z -> (T + 4096 <= 0x10000 \/ 0x6ca000 <= T)%Z -> (T mod 4096 = 0)%Z -> (0 < SB)%Z ->
  rw_cells asegs m (bv_unsigned sp + -64) [CB 8 jf; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  stk asegs m lo (bv_unsigned sp + -64) -> (lo <= bv_unsigned sp - 64)%Z -> (T + 4096 <= lo)%Z -> (r24 SB + 2^32 <= lo)%Z ->
  (bv_unsigned sp <= 2^47)%Z ->
  mem_inv asegs m ->
  evt asegs (qenq_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
               [(qcacheT T, qcacheT T + 32); (pc_addr T 24, pc_addr T 24 + 4); (cstat_alloc T, cstat_alloc T + 8);
                (b0, b0 + 8192); (chunk_addr SB 24 w, chunk_addr SB 24 w + 8192); (bv_unsigned sp - 64, bv_unsigned sp)]%Z
               (qcacheT T) (pre ++ [(b0, ents0); (chunk_addr SB 24 w, [(M, n)])]) lo m (fun m' => qnew_after m' T SB cnt mc ws24))
    (MS (mkR ra0 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 (pc_addr T 24)) (Z_to_bv 64 (cacheT T))
             (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 M) (Z_to_bv 64 (qcacheT T)) (Z_to_bv 64 stack) (Z_to_bv 64 n)
             s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 qenq_refill_ret) fc None m (seg_rom asegs)).
Proof.
  intros until ents0. intros Hn HL0 QR WF HBY NC Hcnt Hmc Hlen Hw HTS HT0 HT HT4 HSB FR ST HLO HTl HRl HSP MI.
  replace (pre ++ [(b0, ents0); (chunk_addr SB 24 w, [(M, n)])]) with ((pre ++ [(b0, ents0)]) ++ [(chunk_addr SB 24 w, [(M, n)])])
    in * by (rewrite <- app_assoc; reflexivity).
  pose proof (qwf_last _ _ _ _ WF) as (HB8 & HB1 & HB2 & _ & _).
  pose proof (qwf_snoc_disj _ _ _ _ WF) as DISJ.
  pose proof (proj1 (Forall_forall _ _) DISJ (b0, ents0) ltac:(apply in_or_app; right; left; reflexivity)) as HB0B.
  cbv beta in HB0B. cbn [fst] in HB0B. apply box in DISJ.
  pose proof (qwf_region _ _ WF) as RG. apply box in RG.
  destruct NC as (PC & ARR & STA & SBC & JB).
  pose proof (qbytes_ge _ _ WF) as QGE. rewrite !qbytes_snoc, app_length, Nat2Z.inj_add in QGE. cbn [length bsum fold_right snd] in QGE.
  rewrite qbytes_snoc in HBY.
  pose proof (proj1 (Forall_forall _ _) (proj2 WF) (b0, ents0) ltac:(apply in_or_app; left; apply in_or_app; right; left; reflexivity))
    as (Hb08 & Hb01 & Hb02 & _ & Hents0).
  cbn [fst snd] in Hb08, Hb01, Hb02, Hents0.
  pose proof (bsum_nonneg ents0 Hents0) as BSN0.
  apply (proj1 (qcache_rep_iff _ _ _)) in QR. destruct QR as (QH & QC).
  apply (proj1 (qchain_to_0 _ _)) in QC. apply (proj1 (qchain_to_snoc _ _ _ _ _)) in QC.
  destruct QC as (QP & QB). apply box in QP.
  apply (proj1 (qbatch_iff _ _ _ _)) in QB. destruct QB as (QBH & QBA & Hle). apply box in QBA.
  rewrite qlast_snoc, qbytes_snoc in QH.
  unfold qcacheT, cacheT, pc_cells, pc_addr, cstat_alloc, i_spacebeg, INST, g_instance, r24, kHighShadowEnd, qenq_refill_ret in *.
  change (1508824 + 32)%Z with 1508856%Z in SBC.
  replace (T + 208 + 80 * 24)%Z with (T + 2128)%Z in * by lia. replace (T + 2128 + 16)%Z with (T + 2144)%Z in * by lia.
  pose proof (cptr_range w) as RW.
  remember (chunk_addr SB 24 w) as B eqn:EB.
  change (24 * 2^32)%Z with 103079215104%Z in *. change (2^32)%Z with 4294967296%Z in *.
  rewrite HL0 in QBH. cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in QBH.
  remember (Z.of_nat (length (pre ++ [(b0, ents0)]))) as NB eqn:ENB.
  assert (RNB : (1 <= NB)%Z) by (subst NB; rewrite app_length; cbn [length]; lia).
  remember (qfirst (pre ++ [(b0, ents0)])) as FST eqn:EFST.
  remember (bsum ents0) as BS eqn:EBS. remember (qbytes pre) as QBP eqn:EQBP.
  assert (RNB2 : (NB < 2^50)%Z) by (clear - QGE HBY Hn BSN0; lia). clear QGE.
  pose proof (munch_refl [(T + 80, T + 80 + 32); (T + 2128, T + 2128 + 4); (T + 2784, T + 2784 + 8); (b0, b0 + 8192);
                          (B, B + 8192); (bv_unsigned sp - 64, bv_unsigned sp)]%Z m) as MU.
  pose proof (munch_refl [(T + 2128, T + 2128 + 4); (T + 2784, T + 2784 + 8); (bv_unsigned sp - 64, bv_unsigned sp)]%Z m) as MUj.
  pose proof (munch_refl [(T + 80, T + 80 + 32); (T + 2128, T + 2128 + 4); (T + 2784, T + 2784 + 8); (b0, b0 + 8);
                          (B, B + 8192); (bv_unsigned sp - 64, bv_unsigned sp)]%Z m) as MUb.
  pose proof (wmono_refl asegs m) as WM.
  apply box in JB.
  apply box in HTS. apply box in HB0B.
  zhide.
  zstep. zstep. ifF.
  pose proof (unbox _ HTS) as HTS'. clear HTS.
  do 3 zstep. zstep. rewrite (sx32_small_A cnt) by lia. zstep. zstep.
  do 3 zstep. zstep.
  rewrite (shl32_shr30 (cnt + -1)) by lia.
  do 4 zstep.
  pose proof (u32arr_read asegs _ (T + 2144) ws24 (cnt - 1) w (Z_to_bv 64 (T + 208 + 4 * (cnt + -1) + 1936)) ARR Hw ltac:(lia)
                ltac:(unfold wa; f_equal; lia)) as RD.
  zstep. change (zx32 w) with (Z_to_bv 64 (cptr w)). clear RD.
  assert (AMO : amo_aligned AD (Z_to_bv 64 (T + 2784)) = true).
  { unfold amo_aligned, amo_bytes. rewrite unsigned_lit by lia. apply Z.eqb_eq. lia. }
  amo_step AMO.
  do 7 zstep.
  replace (Z.shiftl (cptr w) 4 + (SB + 103079215104))%Z with B by (subst B; unfold chunk_addr; rewrite Z.shiftl_mul_pow2 by lia; lia).
  zstep. ifF.
  do 4 zstep.
  let mm := amem in
  pose proof (rw_cells_transport asegs _ m mm B _ (unbox _ JB) MUj WM
                ltac:(change (Z.of_nat (cells_size [CB 8192 jb])) with 8192%Z; cbn [disjoint_from]; lia)) as JB'.
  clear MUj JB.
  destruct (batch_of_cb _ _ _ JB') as (w0 & w1 & w2 & bws & BH & BA & BL). clear JB'.
  pose proof (unbox _ HB0B) as HB0B'. clear HB0B.
  zstep; fix_lit_store. zstep. zstep; fix_lit_store.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    match goal with TB0 : u64arr asegs mm (B + 24) _ |- _ =>
      pose proof (u64arr_store_ok asegs mm (B + 24) _ 0 (Z_to_bv 64 (B + 24)) TB0 ltac:(lia)
                    ltac:(unfold wa; f_equal; lia)) as SO;
      pose proof (u64arr_bound asegs mm (B + 24) _ TB0) as HBA;
      zstep;
      pose proof (u64arr_write asegs mm (B + 24) _ 0 (Z_to_bv 64 M) TB0 ltac:(lia)) as TB';
      clear TB0 end end.
  replace (B + 24 + 8 * 0)%Z with (B + 24)%Z in TB' by lia.
  store_done. clear HBA.
  zstep. ifF.
  do 4 zstep.
  do 5 zstep.
  move FR at bottom.
  do 8 zstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    match goal with H : stk asegs mm _ _ |- _ => release_frame FR H (bv_unsigned sp) end end.
  zstep.
  pose proof (qwf_snoc_disj _ _ _ _ (qwf_prefix _ _ _ WF)) as DISJ0.
  apply evt_done. unfold qenq_post.
  do 16 eexists. split; [reflexivity|].
  split; [eapply munch_weaken; [| exact MU]; unfold sub_fp; cbn [outside]; intros; lia|].
  split; [eassumption|]. split; [eassumption|].
  split; [| split; [| eassumption]].
  - apply (proj2 (qcache_rep_iff _ _ _)). split.
    + rewrite app_length, Nat2Z.inj_add, <- ENB. rewrite (qfirst_app_ne _ _ (snoc_ne _ _)), <- EFST. rewrite qlast_snoc.
      rewrite !qbytes_snoc, <- EBS, <- EQBP. cbn [length bsum fold_right snd Z.of_nat Pos.of_succ_nat].
      replace (QBP + 8192 + BS + 8192 + (n + 0))%Z with (QBP + 8192 + BS + (n + 8192))%Z by lia. eassumption.
    + apply (proj2 (qchain_to_0 _ _)). apply (proj2 (qchain_to_snoc _ _ _ _ _)). split.
      * apply (proj2 (qchain_to_snoc _ _ _ _ _)). split.
        -- lazymatch goal with |- qchain_to ?mm _ _ =>
             apply (qchain_to_frame _ m mm _ _ (unbox _ QP) MU WM) end.
           pose proof (unbox _ RG) as RG'. apply Forall_app in RG'. destruct RG' as (RG' & _). apply Forall_app in RG'.
           destruct RG' as (RG' & _).
           pose proof (unbox _ DISJ) as DJ. apply Forall_app in DJ. destruct DJ as (DJ & _).
           apply Forall_forall. intros e He.
           pose proof (proj1 (Forall_forall _ _) RG' e He) as (E1 & E2).
           pose proof (proj1 (Forall_forall _ _) DJ e He) as E3.
           pose proof (proj1 (Forall_forall _ _) DISJ0 e He) as E4.
           unfold r24 in E1, E2. cbv beta in E3, E4. change (24 * 2^32)%Z with 103079215104%Z in *.
           change (2^32)%Z with 4294967296%Z in *. cbn [disjoint_from]. repeat split; lia.
        -- apply (proj2 (qbatch_iff _ _ _ _)). split; [| split; [| exact Hle]].
           ++ rewrite HL0, <- EBS. eassumption.
           ++ destruct (unbox _ QBA) as (bws0 & BA0 & BL0 & BP0).
              exists bws0. split; [| split; [exact BL0| exact BP0]].
              lazymatch goal with |- u64arr asegs ?mm _ _ =>
                apply (u64arr_transport asegs _ m mm _ _ BA0 MUb WM) end.
              rewrite BL0. cbn [disjoint_from]. lia.
      * apply (proj2 (qbatch_iff _ _ _ _)). cbn [bsum fold_right snd length Z.of_nat]. split; [| split].
        -- replace (8192 + (n + 0))%Z with (n + 8192)%Z by lia. eassumption.
        -- eexists. split; [eassumption| split; [rewrite upd_length; exact BL|]].
           destruct bws as [|x bws']; [cbn in BL; lia|]. reflexivity.
        -- cbn. lia.
  - unfold qnew_after, pc_cells, pc_addr, cstat_alloc, i_spacebeg, INST, g_instance.
    replace (T + 208 + 80 * 24)%Z with (T + 2128)%Z by lia. replace (T + 2128 + 16)%Z with (T + 2144)%Z by lia.
    split; [eassumption| split; [eassumption| split; [eexists; eassumption| eassumption]]].
Qed.
