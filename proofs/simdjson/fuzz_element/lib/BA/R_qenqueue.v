(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac ImageA Arr Walk Image.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Malloc Require Import MallocKit_AB.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Layout R_small R_m2s. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import R_cache_defs R_prim_defs R_asan_defs R_prim_kit R_glue_defs R_depot_defs R_quar_defs.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

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
Local Ltac zidle_begin_rw sp n MUz WMz :=
  lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?m _) =>
    pose proof (munch_refl [(bv_unsigned sp - n, bv_unsigned sp)]%Z m) as MUz; pose proof (wmono_refl segs m) as WMz;
    repeat match goal with
    | H : rw_cells segs m ?A _ |- _ => zidle_nsp H A sp
    | H : u8arr segs m ?A _ |- _ => zidle_nsp H A sp
    | H : u32arr segs m ?A _ |- _ => zidle_nsp H A sp
    | H : u64arr segs m ?A _ |- _ => zidle_nsp H A sp
    | H : bytes_at segs m ?A _ |- _ => zidle_nsp H A sp
    end
  end.
Local Ltac zidle_nspZ H A q := lazymatch A with context [q] => fail | _ => zidle1 H end.
Local Ltac zidle_beginZ q n MUz WMz :=
  lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?m _) =>
    pose proof (munch_refl [(q - n, q)]%Z m) as MUz; pose proof (wmono_refl segs m) as WMz;
    repeat match goal with
    | H : rw_cells segs m ?A _ |- _ => zidle_nspZ H A q
    | H : u8arr segs m ?A _ |- _ => zidle_nspZ H A q
    | H : u32arr segs m ?A _ |- _ => zidle_nspZ H A q
    | H : u64arr segs m ?A _ |- _ => zidle_nspZ H A q
    | H : bytes_at segs m ?A _ |- _ => zidle_nspZ H A q
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
Open Scope bv_scope.
Notation mem := (word -> option byte).
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.

Definition qenq_entry' : Z := 0x5fbdc.

Definition qenq_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (W : list (Z * Z)) (Q : Z) (bs' : list batch) (lo : Z) (m : mem) (P : mem -> Prop) : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                  t3' t4' t5' t6') F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch W m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ qcache_rep m' Q bs' /\ P m' /\ stk asegs m' lo (bv_unsigned sp).

Lemma qenq_app_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (Q CA stack M n SB lo : Z) (pre : list batch) (b : Z) (ents : list (Z * Z)),
  (length ents < 1021)%nat -> (1 <= n <= 2^28)%Z ->
  qcache_rep m Q (pre ++ [(b, ents)]) -> qwf SB (pre ++ [(b, ents)]) ->
  (qbytes (pre ++ [(b, ents)]) + n < 2^63)%Z ->
  (Q + 32 <= r24 SB \/ r24 SB + 2^32 <= Q)%Z -> (0 < Q)%Z -> (0 < SB)%Z ->
  stk asegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 64)%Z -> (Q + 32 <= lo)%Z -> (r24 SB + 2^32 <= lo)%Z ->
  mem_inv asegs m ->
  evt asegs (qenq_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
               [(Q, Q + 32); (b, b + 8192); (bv_unsigned sp - 64, bv_unsigned sp)]%Z Q (pre ++ [(b, ents ++ [(M, n)])]) lo m
               (fun _ => True))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Q) (Z_to_bv 64 CA) (Z_to_bv 64 stack) (Z_to_bv 64 M) (Z_to_bv 64 n) a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 qenq_entry') fc None m (seg_rom asegs)).
Proof.
  intros until ents. intros HL Hn QR WF HBY HQS HQ HSB ST HLO HQl HRl MI.
  pose proof (qwf_last _ _ _ _ WF) as (Hb8 & Hb1 & Hb2 & _ & Hents).
  pose proof (qwf_snoc_disj _ _ _ _ WF) as DISJ. apply box in DISJ.
  pose proof (qbytes_ge _ _ WF) as QGE. rewrite qbytes_snoc in QGE, HBY.
  pose proof (bsum_nonneg _ Hents) as BSN. pose proof (qbytes_nonneg SB pre) as QPN.
  apply (proj1 (qcache_rep_iff _ _ _)) in QR. destruct QR as (QH & QC).
  apply (proj1 (qchain_to_0 _ _)) in QC. apply (proj1 (qchain_to_snoc _ _ _ _ _)) in QC.
  destruct QC as (QP & QB). apply box in QP.
  apply (proj1 (qbatch_iff _ _ _ _)) in QB. destruct QB as (QBH & (ws & QWS & HLws & Hpre) & _).
  rewrite qlast_snoc, qbytes_snoc in QH.
  unfold r24, qenq_entry' in *.
  remember (Z.of_nat (length (pre ++ [(b, ents)]))) as NB eqn:ENB.
  assert (RNB : (1 <= NB)%Z) by (subst NB; rewrite app_length; cbn [length]; lia).
  remember (Z.of_nat (length ents)) as CNT eqn:ECNT.
  assert (RCNT : (0 <= CNT < 1021)%Z) by lia.
  remember (qfirst (pre ++ [(b, ents)])) as FST eqn:EFST.
  remember (bsum ents) as BS eqn:EBS. remember (qbytes pre) as QBP eqn:EQBP.
  assert (RNB2 : (NB < 2^50)%Z) by (clear - QGE HBY Hn BSN QPN; lia). clear QGE.
  pose proof (munch_refl [(Q, Q + 32); (b, b + 8192); (bv_unsigned sp - 64, bv_unsigned sp)]%Z m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  carve_frame 64%nat ST.
  zhide.
  zidle_begin_rw sp 64%Z MUz WMz.
  do 8 zstep.
  zidle_end MUz WMz.
  zstep. zstep. ifF.
  do 3 zstep. zstep. ifT.
  zstep. ifF.
  do 5 zstep. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 3)%Z with 8%Z.
  zstep. zstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    match goal with TB0 : u64arr asegs mm (b + 24) _ |- _ =>
      pose proof (u64arr_store_ok asegs mm (b + 24) _ CNT (Z_to_bv 64 (b + 24 + 8 * CNT)) TB0 ltac:(lia)
                    ltac:(unfold wa; f_equal; lia)) as SO;
      pose proof (u64arr_bound asegs mm (b + 24) _ TB0) as HBA;
      zstep;
      pose proof (u64arr_write asegs mm (b + 24) _ CNT (Z_to_bv 64 M) TB0 ltac:(lia)) as TB';
      clear TB0 end end.
  store_done. clear HBA.
  do 4 zstep.
  do 8 zstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    match goal with H : stk asegs mm _ _ |- _ => release_frame FR H (bv_unsigned sp) end end.
  zstep.
  apply evt_done. unfold qenq_post.
  do 16 eexists. split; [reflexivity|].
  split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
  split; [| split; [exact I| eassumption]].
  apply (proj2 (qcache_rep_iff _ _ _)). split.
  - rewrite (length_snoc' pre (b, ents ++ [(M, n)]) (b, ents)), <- ENB.
    rewrite (qfirst_snoc pre b (ents ++ [(M, n)]) ents), <- EFST, qlast_snoc, qbytes_snoc, bsum_app, <- EBS, <- EQBP.
    cbn [bsum fold_right snd]. replace (QBP + 8192 + (BS + (n + 0)))%Z with (QBP + 8192 + BS + n)%Z by lia. eassumption.
  - apply (proj2 (qchain_to_0 _ _)). apply (proj2 (qchain_to_snoc _ _ _ _ _)). split.
    + lazymatch goal with |- qchain_to ?mm _ _ =>
        apply (qchain_to_frame _ m mm _ _ (unbox _ QP) MU WM) end.
      pose proof (qwf_region _ _ WF) as RG. apply Forall_app in RG. destruct RG as (RG & _).
      apply Forall_forall. intros e He.
      pose proof (proj1 (Forall_forall _ _) RG e He) as (E1 & E2).
      pose proof (proj1 (Forall_forall _ _) (unbox _ DISJ) e He) as E3.
      unfold r24 in E1, E2. cbv beta in E3. cbn [disjoint_from]. repeat split; lia.
    + apply (proj2 (qbatch_iff _ _ _ _)). split; [| split].
      * rewrite bsum_app, app_length, <- EBS. cbn [bsum fold_right snd length].
        replace (8192 + (BS + (n + 0)))%Z with (8192 + BS + n)%Z by lia.
        replace (Z.of_nat (length ents + 1)) with (CNT + 1)%Z by lia. eassumption.
      * eexists. split; [eassumption| split; [rewrite upd_length; exact HLws|]].
        rewrite app_length. cbn [length]. replace (length ents + 1)%nat with (S (Z.to_nat CNT)) by lia.
        rewrite firstn_upd_snoc by lia. replace (Z.to_nat CNT) with (length ents) by lia. rewrite Hpre, map_app. reflexivity.
      * rewrite app_length. cbn [length]. lia.
Qed.

