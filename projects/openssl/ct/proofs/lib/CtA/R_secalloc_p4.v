(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.ct.lib.Lib Require Import Tac Arr Walk StoreFast. 
From OSSVerify.Proofs.openssl.ct.lib.Malloc Require Import MallocKit_AB.
From OSSVerify.Proofs.openssl.ct.lib.A Require Import Shadow.
From OSSVerify.Proofs.openssl.ct.lib.CtA Require Import Layout R_small R_m2s R_thread R_cache_defs R_prim_defs R_glue_defs R_sec_defs R_mmapordie R_secalloc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
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
Local Ltac zidle_end_m MUz :=
  lazymatch type of MUz with munch _ ?m0 ?m1 =>
    lazymatch goal with WMz : wmono _ m0 m1 |- _ => zidle_end MUz WMz end end.
Open Scope bv_scope.
Notation mem := (word -> option byte).
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

Ltac hide_disj := repeat match goal with
  | H : (?A \/ ?B) |- _ => change (hide (A \/ B)) in H
  end.

Lemma lxor63_k : forall k, (0 <= k < 64)%Z -> Z.lxor (63 - k) 63 = k.
Proof.
  intros k Hk.
  assert (H : forallb (fun j => Z.eqb (Z.lxor (63 - Z.of_nat j) 63) (Z.of_nat j)) (seq 0 64) = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in H. specialize (H (Z.to_nat k)). rewrite Z2Nat.id in H by lia. apply Z.eqb_eq, H, in_seq. lia.
Qed.

(* [comment removed for export] *)
Definition secalloc_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (W : list (Z * Z)) (res lo : Z) (m : mem) (K : mem -> Prop) : machine_state -> Prop :=
  fun fin => exists (u0 u1 u2 r1 r2 r3 r4 r5 r6 r7 u3 u4 u5 u6 : word) (mf : mem),
    fin = MS (mkR ra sp gp tp u0 u1 u2 s0 s1 (Z_to_bv 64 res) r1 r2 r3 r4 r5 r6 r7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                  u3 u4 u5 u6) F (ret_pc ra) fc None mf (seg_rom ctasegs)
    /\ munch W m mf /\ wmono ctasegs m mf /\ mem_inv ctasegs mf /\ stk ctasegs mf lo (bv_unsigned sp) /\ K mf.

(* [comment removed for export] *)
Definition sa_W4 (PAB n P : Z) : list (Z * Z) :=
  [(P + 24, P + 32); (PAB + 8 * n, PAB + 8 * n + 8); (i_sec_nres + 8, i_sec_nres + 16); (i_sec_sorted, i_sec_sorted + 40);
   (i_sec_bylog, i_sec_bylog + 512); (i_gstat_alloc, i_gstat_alloc + 16); (i_sec_mutex, i_sec_mutex + 4)]%Z.

(* [comment removed for export] *)
Definition sa_K4 (PAB nres n P : Z) (ws : list word) (m : mem) : Prop :=
  rw_cells ctasegs m (P + 24)%Z [C8 (Z_to_bv 64 n)]
  /\ u64arr ctasegs m PAB (upd ws (Z.to_nat n) (Z_to_bv 64 P))
  /\ rw_cells ctasegs m i_sec_nres [C8 (Z_to_bv 64 nres); C8 (Z_to_bv 64 (n + 1)%Z)]
  /\ sec_junk m
  /\ rw_cells ctasegs m i_sec_mutex [C1 (Z_to_bv 8 0)]
  /\ sec_pad m.

(* [comment removed for export] *)
Lemma sa_p4b : forall (ra t0 t1 t2 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 t3 t4 t5 t6 sp gp tp s10 s11 : word)
    (F : bvmap 5 word) (fc : bv 32) (rac s0c s1c s2c s3c s4c s5c s6c s7c s8c s9c : word) (j : list byte)
    (m m1 : mem) (P SZ PAB nres n k lo : Z) (ws : list word) (b : byte) (jj : list byte) (w1 w2 w3 w4 ga gm : word)
    (bl : list word),
  (0 < SZ /\ SZ + 16384 <= 2^47)%Z -> (0 <= k < 64)%Z ->
  gobj P (sa_msz SZ) lo -> gobj PAB (8 * Z.of_nat (length ws)) lo ->
  (0 <= n < Z.of_nat (length ws))%Z ->
  rw_cells ctasegs m1 (bv_unsigned sp) [CB 8 j; C8 s9c; C8 s8c; C8 s7c; C8 s6c; C8 s5c; C8 s4c; C8 s3c; C8 s2c; C8 s1c; C8 s0c; C8 rac] ->
  stk ctasegs m1 lo (bv_unsigned sp) -> (kHighShadowEnd + 8 <= lo)%Z -> (lo <= bv_unsigned sp)%Z -> (bv_unsigned sp + 96 <= 2^47)%Z ->
  rw_cells ctasegs m1 i_sec_chunks [C8 (Z_to_bv 64 PAB)] ->
  rw_cells ctasegs m1 i_sec_nres [C8 (Z_to_bv 64 nres); C8 (Z_to_bv 64 (n + 1))] ->
  rw_cells ctasegs m1 i_sec_sorted [C1 b; CB 7 jj; C8 w1; C8 w2; C8 w3; C8 w4] ->
  length bl = 64%nat -> u64arr ctasegs m1 i_sec_bylog bl ->
  rw_cells ctasegs m1 i_gstat_alloc [C8 ga; C8 gm] ->
  rw_cells ctasegs m1 i_sec_mutex [C4 (Z_to_bv 64 1)] ->
  u64arr ctasegs m1 PAB (upd ws (Z.to_nat n) (Z_to_bv 64 P)) ->
  rw_cells ctasegs m1 (P + 24) [C8 (Z_to_bv 64 n)] ->
  munch (sa_W4 PAB n P) m m1 -> wmono ctasegs m m1 ->
  mem_inv ctasegs m1 ->
  evt ctasegs (secalloc_post rac (Z_to_bv 64 (bv_unsigned sp + 96)) gp tp s0c s1c s2c s3c s4c s5c s6c s7c s8c s9c s10 s11 F fc
               (sa_W4 PAB n P) (P + 4096) lo m (sa_K4 PAB nres n P ws))
    (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 GSTAT) (Z_to_bv 64 SEC) (Z_to_bv 64 (P + 4096)) (Z_to_bv 64 k) a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 (sa_msz SZ)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1a0b00) fc None m1 (seg_rom ctasegs)).
Proof.
  intros ra t0 t1 t2 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 t3 t4 t5 t6 sp gp tp s10 s11 F fc
    rac s0c s1c s2c s3c s4c s5c s6c s7c s8c s9c j m m1 P SZ PAB nres n k lo ws b jj w1 w2 w3 w4 ga gm bl
    sz_ok k_ok obj_p obj_pab n_ok frame stack lo_hi lo_sp sp_top chunks nres_c sorted bl_len bylog gstat mutex arr hidx
    foot mono inv.
  apply lockw_to1 in mutex.
  unfold gobj in obj_p, obj_pab. unfold kHighShadowEnd, img_hull_lo, img_hull_hi in *.
  pose proof (sa_msz_facts SZ ltac:(lia)) as msz_ok.
  change SEC with 6744600%Z. change GSTAT with 6745224%Z.
  change i_sec_chunks with 6744608%Z in chunks. change i_sec_nres with 6744648%Z in nres_c.
  change i_sec_sorted with 6744664%Z in sorted. change i_sec_bylog with 6744704%Z in bylog.
  change i_gstat_alloc with 6745240%Z in gstat. change i_sec_mutex with 6745216%Z in mutex.
  unfold sa_W4, i_sec_nres, i_sec_sorted, i_sec_bylog, i_gstat_alloc, i_sec_mutex, INST, g_instance in foot.
  destruct (nth_error bl (Z.to_nat k)) as [cnt|] eqn:cnt_at; [| apply nth_error_None in cnt_at; lia].
  assert (bylog_rd : ov_read_bytes ctasegs m1 (Z_to_bv 64 (6744600 + Z.shiftl k 3 + 104)%Z) 8 = Some (le8 cnt)).
  { apply (u64arr_read ctasegs m1 6744704 bl k cnt _ bylog cnt_at); [lia|].
    rewrite Z.shiftl_mul_pow2 by lia. unfold wa. f_equal. lia. }
  assert (al_a : amo_aligned AD (Z_to_bv 64 6745240) = true) by (vm_compute; reflexivity).
  assert (al_m : amo_aligned AD (Z_to_bv 64 6745248) = true) by (vm_compute; reflexivity).
  zstep. zstep. zstep. clear bylog_rd. zstep. zstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
    assert (bylog_ok : store_ok ctasegs mc (Z_to_bv 64 (6744600 + Z.shiftl k 3 + 104)%Z) 8 = true)
      by (apply (u64arr_store_ok ctasegs mc 6744704 bl k _ bylog); [lia|];
          rewrite Z.shiftl_mul_pow2 by lia; unfold wa; f_equal; lia) end.
  zstep.
  replace (Z_to_bv 64 (6744600 + Z.shiftl k 3 + 104)%Z) with (wa (6744704 + 8 * k)%Z) in *
    by (rewrite Z.shiftl_mul_pow2 by lia; unfold wa; f_equal; lia).
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mc _ _) _) =>
    pose proof (u64arr_write ctasegs mc 6744704 bl k (Z_to_bv 64 (bv_unsigned cnt + 1)%Z) bylog ltac:(lia)) as bylog' end.
  clear bylog. store_done.
  zstep. zstep. zstep. zstep. zstep. zstep.
  fix_lit_store.
  do 13 zstep.
  release_frame frame stack (bv_unsigned sp + 96)%Z.
  destruct (lockw_split _ _ mutex) as [lock_free pad_ok].
  apply evt_done. hnf. do 15 eexists. split; [reflexivity|].
  split; [exact foot|]. split; [exact mono|]. split; [exact inv|].
  split; [rewrite unsigned_lit by lia; exact stack|].
  unfold sa_K4, sec_junk.
  refine (conj hidx (conj arr (conj nres_c (conj _ (conj lock_free pad_ok))))).
  split; [exists b, jj, w1, w2, w3, a2; exact sorted|].
  split; [eexists; split; [|exact bylog']; rewrite upd_length; exact bl_len|].
  eexists _, _; exact gstat.
Qed.

Lemma sa_p4 : forall (ra t0 t1 t2 a1 a2 a4 a5 a6 a7 s4 s6 s7 t3 t4 t5 t6 sp gp tp s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (rac s0c s1c s2c s3c s4c s5c s6c s7c s8c s9c : word) (j : list byte)
    (m : mem) (P SZ PAB nres n k lo : Z) (ws : list word),
  (0 < SZ /\ SZ + 16384 <= 2^47)%Z -> (P mod 4096 = 0)%Z -> (0 <= k < 64)%Z ->
  gobj P (sa_msz SZ) lo -> gobj PAB (8 * Z.of_nat (length ws)) lo -> sapart P (sa_msz SZ) PAB (8 * Z.of_nat (length ws)) ->
  (0 <= n < Z.of_nat (length ws))%Z ->
  rw_cells ctasegs m (bv_unsigned sp) [CB 8 j; C8 s9c; C8 s8c; C8 s7c; C8 s6c; C8 s5c; C8 s4c; C8 s3c; C8 s2c; C8 s1c; C8 s0c; C8 rac] ->
  stk ctasegs m lo (bv_unsigned sp) -> (kHighShadowEnd + 8 <= lo)%Z -> (lo <= bv_unsigned sp)%Z -> (bv_unsigned sp + 96 <= 2^47)%Z ->
  rw_cells ctasegs m i_sec_chunks [C8 (Z_to_bv 64 PAB)] ->
  rw_cells ctasegs m i_sec_nres [C8 (Z_to_bv 64 nres); C8 (Z_to_bv 64 n)] ->
  sec_junk m ->
  rw_cells ctasegs m i_sec_mutex [C4 (Z_to_bv 64 1)] ->
  u64arr ctasegs m PAB ws ->
  rw_cells ctasegs m (P + 24) [C8 (Z_to_bv 64 0)] ->
  mem_inv ctasegs m ->
  evt ctasegs (secalloc_post rac (Z_to_bv 64 (bv_unsigned sp + 96)) gp tp s0c s1c s2c s3c s4c s5c s6c s7c s8c s9c s10 s11 F fc
               (sa_W4 PAB n P) (P + 4096) lo m (sa_K4 PAB nres n P ws))
    (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 GSTAT) (Z_to_bv 64 SEC) (Z_to_bv 64 (P + 4096)) a1 a2 (Z_to_bv 64 n) a4 a5 a6 a7
             (Z_to_bv 64 (sa_msz SZ)) (Z_to_bv 64 (63 - k)) s4 (Z_to_bv 64 P) s6 s7 (Z_to_bv 64 7) (Z_to_bv 64 (P + 4096))
             s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1a0ab8) fc None m (seg_rom ctasegs)).
Proof.
  intros ra t0 t1 t2 a1 a2 a4 a5 a6 a7 s4 s6 s7 t3 t4 t5 t6 sp gp tp s10 s11 F fc
    rac s0c s1c s2c s3c s4c s5c s6c s7c s8c s9c j m P SZ PAB nres n k lo ws
    sz_ok p_page k_ok obj_p obj_pab apart n_ok frame stack lo_hi lo_sp sp_top chunks nres_c junk mutex arr hidx inv.
  destruct junk as ((b & jb & w1 & w2 & w3 & w4 & sorted) & (bl & bl_len & bylog) & (ga & gm & gstat)).
  pose proof (munch_refl (sa_W4 PAB n P) m) as foot. pose proof (wmono_refl ctasegs m) as mono.
  pose proof obj_p as geo_p. pose proof obj_pab as geo_pab. pose proof lo_hi as lo_lit.
  unfold gobj, img_hull_lo, img_hull_hi in geo_p, geo_pab. unfold kHighShadowEnd in lo_lit. unfold sapart in apart.
  pose proof (sa_msz_facts SZ ltac:(lia)) as msz_ok.
  change SEC with 6744600%Z. change GSTAT with 6745224%Z.
  change i_sec_chunks with 6744608%Z in chunks. change i_sec_nres with 6744648%Z in nres_c.
  change i_sec_sorted with 6744664%Z in sorted. change i_sec_bylog with 6744704%Z in bylog.
  change i_gstat_alloc with 6745240%Z in gstat. change i_sec_mutex with 6745216%Z in mutex.
  unfold sa_W4, i_sec_nres, i_sec_sorted, i_sec_bylog, i_gstat_alloc, i_sec_mutex, INST, g_instance in foot.
  zstep. zstep. rewrite lxor63_k by lia. zstep. zstep. zstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
    assert (slot_ok : store_ok ctasegs mc (Z_to_bv 64 (PAB + Z.shiftl n 3)%Z) 8 = true)
      by (apply (u64arr_store_ok ctasegs mc PAB ws n _ arr); [lia|];
          rewrite Z.shiftl_mul_pow2 by lia; unfold wa; f_equal; lia) end.
  zstep.
  replace (Z_to_bv 64 (PAB + Z.shiftl n 3)%Z) with (wa (PAB + 8 * n)%Z) in *
    by (rewrite Z.shiftl_mul_pow2 by lia; unfold wa; f_equal; lia).
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mc _ _) _) =>
    pose proof (u64arr_write ctasegs mc PAB ws n (Z_to_bv 64 P) arr ltac:(lia)) as arr' end.
  clear arr. store_done.
  do 7 zstep. zstep. fix_lit_store. zstep. zstep. zstep.
  if_cases wrap_lt; cbv iota; [| zstep].
  all: change (Z_to_bv 64 6745224) with (Z_to_bv 64 GSTAT); change (Z_to_bv 64 6744600) with (Z_to_bv 64 SEC).
  all: eapply sa_p4b; eassumption.
Qed.

