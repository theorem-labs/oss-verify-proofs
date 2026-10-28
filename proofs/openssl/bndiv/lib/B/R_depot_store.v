(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Lib Require Import Tac ImageA Arr Walk.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Malloc Require Import MallocKit_AB.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Import F_memcpy R_imemcpy R_small R_cache_defs R_prim_defs R_prim_kit R_depot_defs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Lib Require Import StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
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
      unfold zidle in *; transport_after_call bsegs m mm MU WM end end.
Notation mem := (word -> option byte).

Lemma shl44_shr41 : forall x, (0 <= x < 2^20)%Z -> Z.shiftr (Z.land (Z.shiftl x 44) 18446744073709551615) 41 = (8 * x)%Z.
Proof.
  intros x Hx. rewrite Z.shiftl_mul_pow2 by lia. change 18446744073709551615%Z with (Z.ones 64).
  rewrite Z.land_ones, Z.mod_small by lia. rewrite Z.shiftr_div_pow2 by lia.
  replace (x * 2 ^ 44)%Z with ((8 * x) * 2 ^ 41)%Z by lia. apply Z.div_mul. lia.
Qed.

Lemma land_m16_small : forall x, (0 <= x < 16)%Z -> Z.land x 18446744073709551600 = 0%Z.
Proof.
  intros x Hx. assert (C : (x = 0 \/ x = 1 \/ x = 2 \/ x = 3 \/ x = 4 \/ x = 5 \/ x = 6 \/ x = 7 \/ x = 8 \/ x = 9 \/ x = 10
    \/ x = 11 \/ x = 12 \/ x = 13 \/ x = 14 \/ x = 15)%Z) by lia.
  repeat (destruct C as [->|C]; [reflexivity|]). subst x. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma amo32_add_bytes : forall a b, (0 <= a < 2^32)%Z -> (0 <= b < 2^32)%Z ->
  Z_to_le_bytes 4 (bv_unsigned (amo_val AMO_ADD (bv_extract 0 32 (le_bytes_to_word (le4 (Z_to_bv 64 a)))) (low32 (Z_to_bv 64 b))))
  = le4 (Z_to_bv 64 (a + b)).
Proof.
  intros a b Ha Hb. cbn [amo_val]. rewrite bv_add_unsigned.
  rewrite !low32_unsigned, le_bytes_to_word_le4, !unsigned_lit by lia.
  unfold le4. rewrite unsigned_lit by lia. unfold bv_wrap. change (bv_modulus 32) with (2 ^ 32)%Z.
  rewrite (Z.mod_small a (2^32)) by lia. rewrite (Z.mod_small a (2^32)) by lia. rewrite (Z.mod_small b (2^32)) by lia.
  apply (Z_to_le_bytes_mod 4 (a + b) 32). lia.
Qed.

Ltac amo32_fix := lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 (bv_unsigned (amo_val AMO_ADD
         (bv_extract 0 32 (le_bytes_to_word (le4 (Z_to_bv 64 ?a)))) (low32 (Z_to_bv 64 ?b)))))) _) =>
      rewrite (amo32_add_bytes a b) by lia; mem_after_store
  end.

Ltac curmem := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => mm end.

(* [comment removed for export] *)
Definition salloc_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (SSB tot cnt IDX lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (SSB + 8 * tot)) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8
                  s9 s10 s11 t3' t4' t5' t6') F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(s_total, s_total + 8); (IDX, IDX + 8); (bv_unsigned sp - 16, bv_unsigned sp)]%Z m m'
    /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ rw_cells bsegs m' s_total [C8 (Z_to_bv 64 (tot + cnt))]
    /\ rw_cells bsegs m' IDX [C8 (Z_to_bv 64 tot)]
    /\ stk bsegs m' lo (bv_unsigned sp).

(* [comment removed for export] *)
Lemma salloc_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (SSB tot cnt IDX lo : Z) (junk : word),
  (0 <= tot)%Z -> (1 <= cnt)%Z -> (tot + cnt <= 2^20)%Z -> (0 < SSB < 2^63)%Z ->
  rw_cells bsegs m s_total [C8 (Z_to_bv 64 tot)] -> rw_cells bsegs m s_data0 [C8 (Z_to_bv 64 SSB)] ->
  IDX = bv_unsigned sp -> rw_cells bsegs m IDX [C8 junk] ->
  stk bsegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 16)%Z -> (0xbfd000 <= lo)%Z -> (bv_unsigned sp + 8 <= 2^63)%Z ->
  mem_inv bsegs m ->
  evt bsegs (salloc_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SSB tot cnt IDX lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 s_total) (Z_to_bv 64 cnt) (Z_to_bv 64 IDX) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6
             s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 salloc_entry) fc None m (seg_rom bsegs)).
Proof.
  intros until junk. intros Htot Hcnt Hroom HSSB TT DT EIDX IX ST HLO HIMG HSP MI. unfold salloc_entry.
  pose proof (munch_refl [(s_total, s_total + 8); (IDX, IDX + 8); (bv_unsigned sp - 16, bv_unsigned sp)]%Z m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  carve_frame 16%nat ST.
  zhide.
  zidle_begin sp 16%Z MUz WMz.
  do 5 zstep.
  zidle_end MUz WMz.
  assert (AMO : amo_aligned AD (Z_to_bv 64 s_total) = true) by (vm_compute; reflexivity).
  amo_step AMO.
  do 4 zstep.
  assert (E1 : Z.shiftr tot 20 = 0%Z) by (rewrite Z.shiftr_div_pow2 by lia; apply Z.div_small; lia).
  assert (E2 : Z.shiftr (cnt + -1 + tot) 20 = 0%Z) by (rewrite Z.shiftr_div_pow2 by lia; apply Z.div_small; lia).
  rewrite ?E1, ?E2.
  zstep. ifF.
  do 2 zstep.
  assert (E3 : Z.shiftr tot 32 = 0%Z) by (rewrite Z.shiftr_div_pow2 by lia; apply Z.div_small; lia).
  rewrite E3. dIf_closed.
  do 5 zstep. ifF.
  do 3 zstep.
  rewrite shl44_shr41 by lia.
  do 3 zstep.
  release_frame FR ST (bv_unsigned sp).
  zstep.
  lazymatch goal with H : rw_cells bsegs _ 7821512 [C8 (amo_val AMO_ADD _ _)] |- _ =>
    cbn [amo_val] in H; rewrite lit_add_lit in H end.
  finish.
Qed.

(* [comment removed for export] *)
Definition imemcpy_postZ (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (D S N : Z) (src : list byte) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 D) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                  t3' t4' t5' t6') F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(D, D + N)]%Z m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ rw_cells bsegs m' D [CB (Z.to_nat N) src] /\ bytes_at bsegs m' S src.

Lemma imemcpy_callZ : forall ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (D S N : Z) (src junk : list byte),
  length src = Z.to_nat N -> (0 <= S)%Z -> (S + N < 2^64)%Z -> (0 <= D)%Z -> (D + N < 2^64)%Z -> (0 <= N < 2^64)%Z ->
  (S + N <= D \/ D + N <= S)%Z ->
  rw_cells bsegs m D [CB (Z.to_nat N) junk] -> bytes_at bsegs m S src -> mem_inv bsegs m ->
  evt bsegs (imemcpy_postZ ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc D S N src m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) (Z_to_bv 64 S) (Z_to_bv 64 N) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10
             s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1d012c) fc None m (seg_rom bsegs)).
Proof.
  intros until junk. intros LEN HS HSN HD HDN HN SEP DST SRC MI.
  assert (ES : bv_unsigned (Z_to_bv 64 S) = S) by (apply unsigned_lit; lia).
  assert (ED : bv_unsigned (Z_to_bv 64 D) = D) by (apply unsigned_lit; lia).
  assert (EN : bv_unsigned (Z_to_bv 64 N) = N) by (apply unsigned_lit; lia).
  eapply evt_mono.
  { eapply (imemcpy_spec ra sp) with (junk := junk); rewrite ?ES, ?ED, ?EN; eassumption || lia. }
  intros ms' P. unfold memcpy_post in P. unfold imemcpy_postZ. rewrite ES, ED, EN in P. exact P.
Qed.

(* [comment removed for export] *)
Definition sstore_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (SSB tot sz PACK lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (tot + 1)) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8
                  s9 s10 s11 t3' t4' t5' t6') F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(s_total, s_total + 8); (s_stored0, s_stored0 + 4); (PACK, PACK + 8); (SSB + 8 * tot, SSB + 8 * (tot + sz + 1));
             (bv_unsigned sp - 80, bv_unsigned sp)]%Z m m'
    /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ rw_cells bsegs m' s_total [C8 (Z_to_bv 64 (tot + sz + 1))]
    /\ rw_cells bsegs m' s_stored0 [C4 (Z_to_bv 64 (tot + sz + 1))]
    /\ stk bsegs m' (SSB + 8 * (tot + sz + 1)) (SSB + 2 ^ 23)
    /\ rw_cells bsegs m' PACK [C8 (Z_to_bv 64 0)]
    /\ stk bsegs m' lo (bv_unsigned sp).

(* [comment removed for export] *)
Lemma sstore_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (SSB tot ARGS PACK TR lo : Z) (ws rest : list word) (pw : word),
  (1 <= Z.of_nat (length ws) <= 254)%Z -> (0 <= tot)%Z -> (tot + Z.of_nat (length ws) + 1 < 2^20)%Z ->
  (0xbfd000 <= SSB)%Z -> (SSB + 2^23 <= lo)%Z ->
  rw_cells bsegs m s_total [C8 (Z_to_bv 64 tot)] -> rw_cells bsegs m s_data0 [C8 (Z_to_bv 64 SSB)] ->
  rw_cells bsegs m s_stored0 [C4 (Z_to_bv 64 tot)] -> stk bsegs m (SSB + 8 * tot) (SSB + 2 ^ 23) ->
  rw_cells bsegs m ARGS [C8 (Z_to_bv 64 TR); C4 (Z_to_bv 64 (Z.of_nat (length ws))); C4 (Z_to_bv 64 0)] ->
  rw_cells bsegs m PACK [C8 pw] -> u64arr bsegs m TR (ws ++ rest) ->
  stk bsegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 80)%Z ->
  (bv_unsigned sp <= PACK)%Z -> (PACK + 8 <= ARGS)%Z -> (ARGS + 16 <= TR)%Z -> (TR + 8 * Z.of_nat (length (ws ++ rest)) <= 2^63)%Z ->
  mem_inv bsegs m ->
  evt bsegs (sstore_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SSB tot (Z.of_nat (length ws)) PACK lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 s_total) (Z_to_bv 64 ARGS) (Z_to_bv 64 PACK) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6
             s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 sstore_entry) fc None m (seg_rom bsegs)).
Proof.
  intros until pw. intros Hsz Htot Hroom HSSB HSSBl TT DT SD FF AR PK TB ST HLO HP1 HP2 HP3 HP4 MI. unfold sstore_entry.
  remember (Z.of_nat (length ws)) as sz eqn:Esz.
  pose proof (munch_refl [(s_total, s_total + 8); (s_stored0, s_stored0 + 4); (PACK, PACK + 8); (SSB + 8 * tot, SSB + 8 * (tot + sz + 1));
             (bv_unsigned sp - 80, bv_unsigned sp)]%Z m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  carve_frame 56%nat ST. carve_frame 8%nat ST.
  zhide.
  zidle_begin sp 64%Z MUz WMz.
  do 8 zstep.
  zidle_end MUz WMz.
  do 4 zstep.
  rewrite (sx32_small_A sz), (sx32_small_A 0) by lia. rewrite (unsigned_lit sz), (unsigned_lit 0), Z.lor_0_r by lia.
  zstep. ifT.
  do 3 zstep. ifF.
  do 3 zstep. ifT.
  zstep; fix_lit_store. zstep; fix_lit_store.
  do 6 zstep.
  sp_facts.
  call (salloc_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ SSB tot (sz + 1)%Z (bv_unsigned sp + -64)%Z lo _).
  all: rewrite ?Esp in *; try lia; try eassumption.
  zstep. ifF.
  remember (SSB + 8 * tot)%Z as FA eqn:EFA.
  let mm := curmem in
  destruct (stk_carve_lo mm FA (SSB + 2 ^ 23) 8%nat FF ltac:(lia)) as [FF1 (hj & HC)]; clear FF;
  destruct (stk_carve_lo mm (FA + 8)%Z (SSB + 2 ^ 23) (Z.to_nat (8 * sz)) FF1 ltac:(lia)) as [FF2 (fj & FC)]; clear FF1.
  do 4 zstep.
  do 3 zstep.
  rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 3)%Z with 8%Z. replace (sz * 8)%Z with (8 * sz)%Z by lia.
  pose proof TB as TB2. destruct TB2 as [TBb _]. rewrite u64s_app in TBb. apply bytes_at_app in TBb. destruct TBb as [TBb _].
  rewrite <- (Z2Nat.id (8 * sz)) in FF2 by lia.
  call (imemcpy_callZ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ (FA + 8)%Z TR (8 * sz)%Z (u64s ws) fj).
  all: try (rewrite u64s_length; lia); try lia; try eassumption.
  do 5 zstep.
  rewrite land_m16_small by (rewrite Z.shiftr_div_pow2 by lia; split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]).
  change (7821512 + 0 + 24)%Z with 7821536%Z.
  assert (AMO : amo_aligned AW (Z_to_bv 64 7821536) = true) by (vm_compute; reflexivity).
  amo_step AMO. amo32_fix.
  rewrite (sx32_small_A tot) by lia.
  do 3 zstep.
  change 4294967295%Z with (Z.ones 32). rewrite Z.land_ones, (Z.mod_small tot) by lia.
  do 3 zstep.
  lazymatch goal with H : rw_cells bsegs _ (bv_unsigned sp + -64)%Z [C8 (Z_to_bv 64 tot)] |- _ =>
    apply (rw_cells_c8_split _ _ [] []) in H; [cbn [app] in H| lia] end.
  do 5 zstep.
  rewrite (sx32_small_A tot), (unsigned_lit tot) by lia. rewrite bv_swrap_small by (change (bv_half_modulus 32) with (2^31)%Z; lia).
  do 8 zstep.
  assert (EQX : (Z.lxor (sz + 1 + tot) 1048576 <? 1)%Z = false).
  { apply Z.ltb_ge. assert (0 <= Z.lxor (sz + 1 + tot) 1048576)%Z by (apply Z.lxor_nonneg; split; lia).
    assert (Z.lxor (sz + 1 + tot) 1048576 <> 0)%Z by (intro E; apply (proj1 (Z.lxor_eq_0_iff _ _)) in E; lia). lia. }
  rewrite EQX in *. cbn [Z.b2z] in *. change (0 + 0)%Z with 0%Z in *.
  replace (tot + (sz + 1))%Z with (tot + sz + 1)%Z in * by lia.
  lazymatch goal with H : stk bsegs ?mm (FA + 8 + ?k)%Z _ |- _ => replace (FA + 8 + k)%Z with (SSB + 8 * (tot + sz + 1))%Z in H by lia end.
  lazymatch goal with H : stk bsegs _ lo (bv_unsigned sp + -64)%Z |- _ => rename H into STK end.
  lazymatch goal with H : rw_cells bsegs _ (bv_unsigned sp + -64)%Z [C4 _; C4 _] |- _ => rename H into IDC end.
  release_frame IDC STK (bv_unsigned sp - 56)%Z.
  release_frame FR STK (bv_unsigned sp).
  zstep.
  finish.
  rewrite EFA in MU. exact MU.
Qed.

(* [comment removed for export] *)
Definition nstore_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (N h : Z) (lnk : word) (SSB tot sz lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                  t3' t4' t5' t6') F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(N, N + 16); (s_total, s_total + 8); (s_stored0, s_stored0 + 4); (SSB + 8 * tot, SSB + 8 * (tot + sz + 1));
             (bv_unsigned sp - 112, bv_unsigned sp)]%Z m m'
    /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ rw_cells bsegs m' N [C8 (Z_to_bv 64 h); C4 lnk; C4 (Z_to_bv 64 (tot + 1))]
    /\ rw_cells bsegs m' s_total [C8 (Z_to_bv 64 (tot + sz + 1))]
    /\ rw_cells bsegs m' s_stored0 [C4 (Z_to_bv 64 (tot + sz + 1))]
    /\ stk bsegs m' (SSB + 8 * (tot + sz + 1)) (SSB + 2 ^ 23)
    /\ stk bsegs m' lo (bv_unsigned sp).

(* [comment removed for export] *)
Lemma nstore_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (N h SSB tot ARGS TR lo : Z) (ws rest : list word) (x lnk y : word),
  (1 <= Z.of_nat (length ws) <= 254)%Z -> (0 <= tot)%Z -> (tot + Z.of_nat (length ws) + 1 < 2^20)%Z -> (0 <= h < 2^64)%Z ->
  (0xbfd000 <= SSB)%Z -> (SSB + 2^23 <= lo)%Z -> (0xbfd000 <= N)%Z -> (N + 16 <= lo)%Z ->
  (N + 16 <= SSB \/ SSB + 2^23 <= N)%Z ->
  rw_cells bsegs m N [C8 x; C4 lnk; C4 y] ->
  rw_cells bsegs m s_total [C8 (Z_to_bv 64 tot)] -> rw_cells bsegs m s_data0 [C8 (Z_to_bv 64 SSB)] ->
  rw_cells bsegs m s_stored0 [C4 (Z_to_bv 64 tot)] -> stk bsegs m (SSB + 8 * tot) (SSB + 2 ^ 23) ->
  rw_cells bsegs m ARGS [C8 (Z_to_bv 64 TR); C4 (Z_to_bv 64 (Z.of_nat (length ws))); C4 (Z_to_bv 64 0)] ->
  u64arr bsegs m TR (ws ++ rest) ->
  stk bsegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 112)%Z ->
  (bv_unsigned sp <= ARGS)%Z -> (ARGS + 16 <= TR)%Z -> (TR + 8 * Z.of_nat (length (ws ++ rest)) <= 2^63)%Z ->
  mem_inv bsegs m ->
  evt bsegs (nstore_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc N h lnk SSB tot (Z.of_nat (length ws)) lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 N) a1 (Z_to_bv 64 ARGS) (Z_to_bv 64 h) a4 a5 a6 a7 s2 s3 s4 s5 s6
             s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 nstore_entry) fc None m (seg_rom bsegs)).
Proof.
  intros until y. intros Hsz Htot Hroom Hh HSSB HSSBl HN HNl HNS ND TT DT SD FF AR TB ST HLO HP1 HP2 HP3 MI. unfold nstore_entry.
  remember (Z.of_nat (length ws)) as sz eqn:Esz.
  pose proof (munch_refl [(N, N + 16); (s_total, s_total + 8); (s_stored0, s_stored0 + 4); (SSB + 8 * tot, SSB + 8 * (tot + sz + 1));
             (bv_unsigned sp - 112, bv_unsigned sp)]%Z m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  carve_frame 16%nat ST. carve_frame 8%nat ST. carve_frame 8%nat ST.
  zhide.
  zidle_begin sp 32%Z MUz WMz.
  do 5 zstep.
  zidle_end MUz WMz.
  zstep.
  zstep; fix_lit_store.
  do 3 zstep.
  zstep.
  sp_facts.
  call (sstore_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ SSB tot ARGS (bv_unsigned sp + -24)%Z TR lo ws rest _).
  all: rewrite ?Esp, ?Esp0, ?Esp1 in *; rewrite <- ?Esz; try lia; try eassumption.
  zstep. zstep. zstep. ifF.
  do 3 zstep.
  lazymatch goal with H : stk bsegs _ lo (bv_unsigned sp + -32)%Z |- _ => rename H into STK end.
  lazymatch goal with H : rw_cells bsegs _ (bv_unsigned sp + -32)%Z [_] |- _ => rename H into C1 end.
  lazymatch goal with H : rw_cells bsegs _ (bv_unsigned sp + -24)%Z [_] |- _ => rename H into C2 end.
  release_frame C1 STK (bv_unsigned sp - 24)%Z.
  release_frame C2 STK (bv_unsigned sp - 16)%Z.
  release_frame FR STK (bv_unsigned sp).
  zstep.
  finish.
  all: rewrite <- Esz in *; eassumption.
Qed.
