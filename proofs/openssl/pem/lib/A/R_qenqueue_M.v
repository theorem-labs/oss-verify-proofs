(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac ImageA Arr Walk Image.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import MallocKit_AB.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout R_small R_m2s R_cache_defs R_prim_defs R_asan_defs R_prim_kit R_glue_defs R_depot_defs R_quar_defs R_qenqueue R_qenqueue_N R_refill.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
(* [comment removed for export] *)
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
Notation mem := (word -> option byte).
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.


Definition qenq_refill_ret : Z := 0x19f43c.

(* [comment removed for export] *)
Definition qenq_missA_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (T stack M n lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
    ms' = MS (mkR (Z_to_bv 64 qenq_refill_ret) (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0' t1' t2'
                  (Z_to_bv 64 (pc_addr T 24)) (Z_to_bv 64 (cacheT T)) (Z_to_bv 64 (cacheT T)) (Z_to_bv 64 (pc_addr T 24))
                  (Z_to_bv 64 INST) (Z_to_bv 64 24) a4' a5' a6' a7' (Z_to_bv 64 M) (Z_to_bv 64 (qcacheT T)) (Z_to_bv 64 stack)
                  (Z_to_bv 64 n) s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F (Z_to_bv 64 refill_entry) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 64, bv_unsigned sp)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ (exists jf, rw_cells asegs m' (bv_unsigned sp + -64) [CB 8 jf; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])
    /\ stk asegs m' lo (bv_unsigned sp + -64).

Lemma qenq_miss_A_empty_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (T stack M n lo mc cs : Z),
  qcache_rep m (qcacheT T) [] -> pc_cells m (pc_addr T 24) 0 mc cs ->
  (0 < T)%Z -> (T + 4096 <= 0x10000 \/ 0xbc6000 <= T)%Z -> (T + 4096 <= lo)%Z ->
  stk asegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 64)%Z -> (bv_unsigned sp <= 2^47)%Z ->
  mem_inv asegs m ->
  evt asegs (qenq_missA_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc T stack M n lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (qcacheT T)) (Z_to_bv 64 (cacheT T)) (Z_to_bv 64 stack) (Z_to_bv 64 M)
             (Z_to_bv 64 n) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 qenq_entry') fc None m (seg_rom asegs)).
Proof.
  intros until cs. intros QR PC HT0 HT HTl ST HLO HSP MI.
  apply (proj1 (qcache_rep_iff _ _ _)) in QR. destruct QR as (QH & _). cbn [length qfirst qlast qbytes map last fold_right] in QH.
  unfold qcacheT, cacheT, pc_cells, pc_addr, INST, g_instance, kHighShadowEnd, qenq_entry', qenq_refill_ret, refill_entry in *.
  replace (T + 208 + 80 * 24)%Z with (T + 2128)%Z in * by lia.
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)]%Z m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  carve_frame 64%nat ST.
  zhide.
  do 8 zstep.
  zstep. zstep. ifT.
  zstep. rewrite (sx32_small_A 0) by lia.
  zstep. ifT.
  do 13 zstep.
  unfold qenq_missA_post, pc_addr, cacheT, qcacheT, INST, g_instance. replace (T + 208 + 80 * 24)%Z with (T + 2128)%Z by lia.
  finish. eexists. eassumption.
Qed.

(* [comment removed for export] *)
Lemma qenq_miss_B_empty_spec : forall ra0 sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    ra s0 s1 s2 s3 s4 s5 (F : bvmap 5 word) fc (m : mem) (T stack M n SB lo cnt mc : Z) (ws24 : list word) (w stj : word)
    (jb jf : list byte),
  (1 <= n <= 2^28)%Z ->
  qcache_rep m (qcacheT T) [] ->
  qnew_cells m T SB cnt mc ws24 w stj jb -> (1 <= cnt <= 16)%Z -> (0 <= mc < 2^31)%Z -> length ws24 = 16%nat ->
  nth_error ws24 (Z.to_nat (cnt - 1)) = Some w ->
  (chunk_addr SB 24 w) mod 8192 = 0%Z -> (chunk_addr SB 24 w + 8192 <= r24 SB + 2^32)%Z ->
  (T + 4096 <= r24 SB \/ r24 SB + 2^32 <= T)%Z -> (0 < T)%Z -> (T + 4096 <= 0x10000 \/ 0xbc6000 <= T)%Z -> (T mod 4096 = 0)%Z -> (0 < SB)%Z ->
  rw_cells asegs m (bv_unsigned sp + -64) [CB 8 jf; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  stk asegs m lo (bv_unsigned sp + -64) -> (lo <= bv_unsigned sp - 64)%Z -> (T + 4096 <= lo)%Z -> (r24 SB + 2^32 <= lo)%Z ->
  (bv_unsigned sp <= 2^47)%Z ->
  mem_inv asegs m ->
  evt asegs (qenq_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
               [(qcacheT T, qcacheT T + 32); (pc_addr T 24, pc_addr T 24 + 4); (cstat_alloc T, cstat_alloc T + 8);
                (chunk_addr SB 24 w, chunk_addr SB 24 w + 8192); (bv_unsigned sp - 64, bv_unsigned sp)]%Z
               (qcacheT T) [(chunk_addr SB 24 w, [(M, n)])] lo m (fun m' => qnew_after m' T SB cnt mc ws24))
    (MS (mkR ra0 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 (pc_addr T 24)) (Z_to_bv 64 (cacheT T))
             (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 M) (Z_to_bv 64 (qcacheT T)) (Z_to_bv 64 stack) (Z_to_bv 64 n)
             s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 qenq_refill_ret) fc None m (seg_rom asegs)).
Proof.
  intros until jf. intros Hn QR NC Hcnt Hmc Hlen Hw HB8 HB2 HTS HT0 HT HT4 HSB FR ST HLO HTl HRl HSP MI.
  destruct NC as (PC & ARR & STA & SBC & JB).
  apply (proj1 (qcache_rep_iff _ _ _)) in QR. destruct QR as (QH & _). cbn [length qfirst qlast qbytes map last fold_right] in QH.
  unfold qcacheT, cacheT, pc_cells, pc_addr, cstat_alloc, i_spacebeg, INST, g_instance, r24, kHighShadowEnd, qenq_refill_ret in *.
  change (6722776 + 32)%Z with 6722808%Z in SBC.
  replace (T + 208 + 80 * 24)%Z with (T + 2128)%Z in * by lia. replace (T + 2128 + 16)%Z with (T + 2144)%Z in * by lia.
  pose proof (cptr_range w) as RW.
  remember (chunk_addr SB 24 w) as B eqn:EB.
  assert (HB1 : (SB + 24 * 2^32 <= B)%Z) by (subst B; unfold chunk_addr; lia).
  change (24 * 2^32)%Z with 103079215104%Z in *. change (2^32)%Z with 4294967296%Z in *.
  pose proof (munch_refl [(T + 80, T + 80 + 32); (T + 2128, T + 2128 + 4); (T + 2784, T + 2784 + 8);
                          (B, B + 8192); (bv_unsigned sp - 64, bv_unsigned sp)]%Z m) as MU.
  pose proof (munch_refl [(T + 2128, T + 2128 + 4); (T + 2784, T + 2784 + 8); (bv_unsigned sp - 64, bv_unsigned sp)]%Z m) as MUj.
  pose proof (wmono_refl asegs m) as WM.
  apply box in JB.
  zhide.
  zstep. zstep. ifF.
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
  zstep. ifT.
  zstep. zstep; fix_lit_store. zstep.
  do 3 zstep.
  do 8 zstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    match goal with H : stk asegs mm _ _ |- _ => release_frame FR H (bv_unsigned sp) end end.
  zstep.
  apply evt_done. unfold qenq_post.
  do 16 eexists. split; [reflexivity|].
  split; [eapply munch_weaken; [| eassumption]; unfold sub_fp; cbn [outside]; intros; lia|].
  split; [eassumption|]. split; [eassumption|].
  split; [| split; [| eassumption]].
  - apply (proj2 (qcache_rep_iff _ _ _)). cbn [length qfirst qlast qbytes map last fold_right bsum snd fst Z.of_nat]. split.
    + replace (8192 + (n + 0) + 0)%Z with (0 + (n + 8192))%Z by lia. eassumption.
    + cbn [qchain]. split; [| exact I].
      apply (proj2 (qbatch_iff _ _ _ _)). cbn [bsum fold_right snd length Z.of_nat]. split; [| split].
      * replace (8192 + (n + 0))%Z with (n + 8192)%Z by lia. eassumption.
      * eexists. split; [eassumption| split; [rewrite upd_length; exact BL|]].
        destruct bws as [|x bws']; [cbn in BL; lia|]. reflexivity.
      * cbn. lia.
  - unfold qnew_after, pc_cells, pc_addr, cstat_alloc, i_spacebeg, INST, g_instance.
    replace (T + 208 + 80 * 24)%Z with (T + 2128)%Z by lia. replace (T + 2128 + 16)%Z with (T + 2144)%Z by lia.
    split; [eassumption| split; [eassumption| split; [eexists; eassumption| eassumption]]].
Qed.

(* [comment removed for export] *)
Lemma qenq_miss_A_full_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (T stack M n lo mc cs SB : Z) (pre : list batch) (b0 : Z) (ents0 : list (Z * Z)),
  length ents0 = 1021%nat ->
  qcache_rep m (qcacheT T) (pre ++ [(b0, ents0)]) -> qwf SB (pre ++ [(b0, ents0)]) ->
  (qbytes (pre ++ [(b0, ents0)]) < 2^63)%Z -> pc_cells m (pc_addr T 24) 0 mc cs ->
  (0 < T)%Z -> (T + 4096 <= 0x10000 \/ 0xbc6000 <= T)%Z -> (T + 4096 <= lo)%Z -> (r24 SB + 2^32 <= lo)%Z ->
  (T + 4096 <= r24 SB \/ r24 SB + 2^32 <= T)%Z -> (0 < SB)%Z ->
  stk asegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 64)%Z -> (bv_unsigned sp <= 2^47)%Z ->
  mem_inv asegs m ->
  evt asegs (qenq_missA_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc T stack M n lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (qcacheT T)) (Z_to_bv 64 (cacheT T)) (Z_to_bv 64 stack) (Z_to_bv 64 M)
             (Z_to_bv 64 n) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 qenq_entry') fc None m (seg_rom asegs)).
Proof.
  intros until ents0. intros HL0 QR WF HBY PC HT0 HT HTl HRl HTS HSB ST HLO HSP MI.
  pose proof (qbytes_ge _ _ WF) as QGE.
  pose proof (qwf_last _ _ _ _ WF) as (Hb8 & Hb1 & Hb2 & _ & _).
  apply (proj1 (qcache_rep_iff _ _ _)) in QR. destruct QR as (QH & QC).
  apply (proj1 (qchain_to_0 _ _)) in QC. apply (proj1 (qchain_to_snoc _ _ _ _ _)) in QC.
  destruct QC as (_ & QB). apply (proj1 (qbatch_iff _ _ _ _)) in QB. destruct QB as (QBH & _ & _).
  rewrite qlast_snoc in QH. rewrite HL0 in QBH.
  unfold qcacheT, cacheT, pc_cells, pc_addr, INST, g_instance, kHighShadowEnd, qenq_entry', qenq_refill_ret, refill_entry, r24 in *.
  replace (T + 208 + 80 * 24)%Z with (T + 2128)%Z in * by lia.
  remember (Z.of_nat (length (pre ++ [(b0, ents0)]))) as NB eqn:ENB.
  assert (RNB : (1 <= NB < 2^50)%Z) by (subst NB; rewrite app_length in *; cbn [length] in *; lia).
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)]%Z m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  carve_frame 64%nat ST.
  zhide.
  do 8 zstep.
  zstep. zstep. ifF.
  do 3 zstep. zstep. ifF.
  zstep. rewrite (sx32_small_A 0) by lia.
  zstep. ifT.
  do 13 zstep.
  unfold qenq_missA_post, pc_addr, cacheT, qcacheT, INST, g_instance. replace (T + 208 + 80 * 24)%Z with (T + 2128)%Z by lia.
  finish. eexists. eassumption.
Qed.
