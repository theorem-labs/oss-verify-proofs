(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Lib Require Import Tac ImageA Arr Walk StoreFast.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Malloc Require Import MallocKit_AB.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.B Require Import Layout R_small R_m2s R_thread R_cache_defs R_prim_defs R_glue_defs R_sec_defs R_mmapordie R_secalloc.
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
Local Ltac zidle_end MUz WMz :=
  lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch type of MUz with munch _ ?m _ =>
      try unfold zidle in *; transport_after_call segs m mm MUz WMz; clear MUz WMz end end.

Local Ltac zidle_end_m m :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch goal with MU : munch _ m mm, WM : wmono _ m mm |- _ =>
      unfold zidle in *; transport_after_call bsegs m mm MU WM end end.
Open Scope bv_scope.
Notation mem := (word -> option byte).
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

Definition secalloc_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (W : list (Z * Z)) (res lo : Z) (m : mem) (K : mem -> Prop) : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 res) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                  t3' t4' t5' t6') F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch W m m' /\ wmono bsegs m m' /\ mem_inv bsegs m' /\ stk bsegs m' lo (bv_unsigned sp) /\ K m'.

Definition sa_W4 (PAB n P : Z) : list (Z * Z) :=
  [(P + 24, P + 32); (PAB + 8 * n, PAB + 8 * n + 8); (i_sec_nres + 8, i_sec_nres + 16); (i_sec_sorted, i_sec_sorted + 40);
   (i_sec_bylog, i_sec_bylog + 512); (i_gstat_alloc, i_gstat_alloc + 16); (i_sec_mutex, i_sec_mutex + 4)]%Z.

Definition sa_K4 (PAB nres n P : Z) (ws : list word) (m : mem) : Prop :=
  rw_cells bsegs m (P + 24) [C8 (Z_to_bv 64 n)] /\ u64arr bsegs m PAB (upd ws (Z.to_nat n) (Z_to_bv 64 P))
  /\ rw_cells bsegs m i_sec_nres [C8 (Z_to_bv 64 nres); C8 (Z_to_bv 64 (n + 1))] /\ sec_junk m
  /\ rw_cells bsegs m i_sec_mutex [C1 (Z_to_bv 8 0)] /\ sec_pad m.

Lemma sa_p4b : forall (ra t0 t1 t2 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 t3 t4 t5 t6 sp gp tp s10 s11 : word)
    (F : bvmap 5 word) (fc : bv 32) (rac s0c s1c s2c s3c s4c s5c s6c s7c s8c s9c : word) (j : list byte)
    (m m1 : mem) (P SZ PAB nres n k lo : Z) (ws : list word) (b : byte) (jj : list byte) (w1 w2 w3 w4 ga gm : word)
    (bl : list word),
  (0 < SZ /\ SZ + 16384 <= 2^47)%Z -> (0 <= k < 64)%Z ->
  gobj P (sa_msz SZ) lo -> gobj PAB (8 * Z.of_nat (length ws)) lo ->
  (0 <= n < Z.of_nat (length ws))%Z ->
  rw_cells bsegs m1 (bv_unsigned sp) [CB 8 j; C8 s9c; C8 s8c; C8 s7c; C8 s6c; C8 s5c; C8 s4c; C8 s3c; C8 s2c; C8 s1c; C8 s0c; C8 rac] ->
  stk bsegs m1 lo (bv_unsigned sp) -> (kHighShadowEnd + 8 <= lo)%Z -> (lo <= bv_unsigned sp)%Z -> (bv_unsigned sp + 96 <= 2^47)%Z ->
  rw_cells bsegs m1 i_sec_chunks [C8 (Z_to_bv 64 PAB)] ->
  rw_cells bsegs m1 i_sec_nres [C8 (Z_to_bv 64 nres); C8 (Z_to_bv 64 (n + 1))] ->
  rw_cells bsegs m1 i_sec_sorted [C1 b; CB 7 jj; C8 w1; C8 w2; C8 w3; C8 w4] ->
  length bl = 64%nat -> u64arr bsegs m1 i_sec_bylog bl ->
  rw_cells bsegs m1 i_gstat_alloc [C8 ga; C8 gm] ->
  rw_cells bsegs m1 i_sec_mutex [C4 (Z_to_bv 64 1)] ->
  u64arr bsegs m1 PAB (upd ws (Z.to_nat n) (Z_to_bv 64 P)) ->
  rw_cells bsegs m1 (P + 24) [C8 (Z_to_bv 64 n)] ->
  munch (sa_W4 PAB n P) m m1 -> wmono bsegs m m1 ->
  mem_inv bsegs m1 ->
  evt bsegs (secalloc_post rac (Z_to_bv 64 (bv_unsigned sp + 96)) gp tp s0c s1c s2c s3c s4c s5c s6c s7c s8c s9c s10 s11 F fc
               (sa_W4 PAB n P) (P + 4096) lo m (sa_K4 PAB nres n P ws))
    (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 GSTAT) (Z_to_bv 64 SEC) (Z_to_bv 64 (P + 4096)) (Z_to_bv 64 k) a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 (sa_msz SZ)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x5e2fc) fc None m1 (seg_rom bsegs)).
Proof.
  intros until bl. intros HSZ Hk GP GA Hn FR ST HLOH HLO HSP CH NR SJ1 Hbl SJ2 SJ3 LW ARR HI MU WM MI.
  pose proof (sa_msz_facts SZ ltac:(lia)) as [MS1 MS2].
  destruct GP as (GP1 & GP2 & GP3 & GP4). destruct GA as (GA1 & GA2 & GA3 & GA4).
  unfold img_hull_lo, img_hull_hi, kHighShadowEnd in *.
  change i_sec_chunks with 1525152%Z in CH. change i_sec_nres with 1525192%Z in NR. change i_sec_mutex with 1525760%Z in LW.
  change i_sec_sorted with 1525208%Z in SJ1. change i_sec_bylog with 1525248%Z in SJ2. change i_gstat_alloc with 1525784%Z in SJ3.
  change SEC with 1525144%Z. change GSTAT with 1525768%Z.
  unfold sa_W4 in MU.
  change i_sec_nres with 1525192%Z in MU. change i_sec_sorted with 1525208%Z in MU. change i_sec_bylog with 1525248%Z in MU.
  change i_gstat_alloc with 1525784%Z in MU. change i_sec_mutex with 1525760%Z in MU.
  hide_disj.
  zhide.
  zstep. zstep.
  replace (1525144 + k ≪ 3)%Z with (1525144 + 8 * k)%Z by (rewrite Z.shiftl_mul_pow2 by lia; lia).
  destruct (nth_error bl (Z.to_nat k)) as [wb|] eqn:Hwb; [| apply nth_error_None in Hwb; lia].
  pose proof (u64arr_read bsegs m1 1525248 bl k wb (Z_to_bv 64 (1525144 + 8 * k + 104)) SJ2 Hwb ltac:(lia)
                ltac:(unfold wa; f_equal; lia)) as RD.
  zstep. clear RD.
  zstep.
  unfold hide in GA4, GP4.
  zstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    match goal with SJ2' : u64arr bsegs mm 1525248 _ |- _ =>
      pose proof (u64arr_store_ok bsegs mm 1525248 _ k (Z_to_bv 64 (1525144 + 8 * k + 104)) SJ2' ltac:(lia)
                    ltac:(unfold wa; f_equal; lia)) as SO;
      zstep;
      replace (1525144 + 8 * k + 104)%Z with (1525248 + 8 * k)%Z in * by lia;
      pose proof (u64arr_write bsegs mm 1525248 _ k (Z_to_bv 64 (bv_unsigned wb + 1)) SJ2' ltac:(lia)) as SJ2n; clear SJ2' end end.
  store_done.
  zstep.
  assert (AMO1 : amo_aligned AD (Z_to_bv 64 1525784) = true) by (vm_compute; reflexivity).
  amo_step AMO1.
  zstep.
  assert (AMO2 : amo_aligned AD (Z_to_bv 64 1525792) = true) by (vm_compute; reflexivity).
  amo_step AMO2.
  zstep.
  apply lockw_to1 in LW. change i_sec_mutex with 1525760%Z in LW.
  zstep; fix_lit_store.
  do 12 zstep.
  zstep.
  release_frame FR ST (bv_unsigned sp + 96)%Z.
  change 1525760%Z with i_sec_mutex in LW. apply lockw_split in LW. destruct LW as [MX PAD].
  apply evt_done. unfold secalloc_post. do 15 eexists.
  split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption|].
  split; [rewrite unsigned_lit by (pose proof (bv_unsigned_in_range 64 sp); unfold bv_modulus in *; cbn [Z.of_N] in *; lia);
          exact ST|].
  unfold sa_K4. split; [exact HI|]. split; [exact ARR|]. split; [exact NR|].
  split; [|split; [exact MX| exact PAD]].
  unfold sec_junk. split; [do 6 eexists; exact SJ1|]. split; [eexists; split; [| exact SJ2n]; rewrite upd_length; exact Hbl|].
  do 2 eexists. exact SJ3.
Qed.

Lemma sa_p4 : forall (ra t0 t1 t2 a1 a2 a4 a5 a6 a7 s4 s6 s7 t3 t4 t5 t6 sp gp tp s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (rac s0c s1c s2c s3c s4c s5c s6c s7c s8c s9c : word) (j : list byte)
    (m : mem) (P SZ PAB nres n k lo : Z) (ws : list word),
  (0 < SZ /\ SZ + 16384 <= 2^47)%Z -> (P mod 4096 = 0)%Z -> (0 <= k < 64)%Z ->
  gobj P (sa_msz SZ) lo -> gobj PAB (8 * Z.of_nat (length ws)) lo -> sapart P (sa_msz SZ) PAB (8 * Z.of_nat (length ws)) ->
  (0 <= n < Z.of_nat (length ws))%Z ->
  rw_cells bsegs m (bv_unsigned sp) [CB 8 j; C8 s9c; C8 s8c; C8 s7c; C8 s6c; C8 s5c; C8 s4c; C8 s3c; C8 s2c; C8 s1c; C8 s0c; C8 rac] ->
  stk bsegs m lo (bv_unsigned sp) -> (kHighShadowEnd + 8 <= lo)%Z -> (lo <= bv_unsigned sp)%Z -> (bv_unsigned sp + 96 <= 2^47)%Z ->
  rw_cells bsegs m i_sec_chunks [C8 (Z_to_bv 64 PAB)] ->
  rw_cells bsegs m i_sec_nres [C8 (Z_to_bv 64 nres); C8 (Z_to_bv 64 n)] ->
  sec_junk m ->
  rw_cells bsegs m i_sec_mutex [C4 (Z_to_bv 64 1)] ->
  u64arr bsegs m PAB ws ->
  rw_cells bsegs m (P + 24) [C8 (Z_to_bv 64 0)] ->
  mem_inv bsegs m ->
  evt bsegs (secalloc_post rac (Z_to_bv 64 (bv_unsigned sp + 96)) gp tp s0c s1c s2c s3c s4c s5c s6c s7c s8c s9c s10 s11 F fc
               (sa_W4 PAB n P) (P + 4096) lo m (sa_K4 PAB nres n P ws))
    (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 GSTAT) (Z_to_bv 64 SEC) (Z_to_bv 64 (P + 4096)) a1 a2 (Z_to_bv 64 n) a4 a5 a6 a7
             (Z_to_bv 64 (sa_msz SZ)) (Z_to_bv 64 (63 - k)) s4 (Z_to_bv 64 P) s6 s7 (Z_to_bv 64 7) (Z_to_bv 64 (P + 4096))
             s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x5e2b4) fc None m (seg_rom bsegs)).
Proof.
  intros until ws. intros HSZ HP Hk GP GA APA Hn FR ST HLOH HLO HSP CH NR SJ LW ARR HI MI.
  pose proof (sa_msz_facts SZ ltac:(lia)) as [MS1 MS2].
  pose proof GP as GP0. pose proof GA as GA0. apply box in GP0, GA0.
  destruct GP as (GP1 & GP2 & GP3 & GP4). destruct GA as (GA1 & GA2 & GA3 & GA4).
  unfold sapart, img_hull_lo, img_hull_hi, kHighShadowEnd in *.
  destruct SJ as ((b & jj & w1 & w2 & w3 & w4 & SJ1) & (bl & Hbl & SJ2) & (ga & gm & SJ3)).
  change i_sec_chunks with 1525152%Z in CH. change i_sec_nres with 1525192%Z in NR. change i_sec_mutex with 1525760%Z in LW.
  change i_sec_sorted with 1525208%Z in SJ1. change i_sec_bylog with 1525248%Z in SJ2. change i_gstat_alloc with 1525784%Z in SJ3.
  change SEC with 1525144%Z. change GSTAT with 1525768%Z.
  pose proof (munch_refl (sa_W4 PAB n P) m) as MU. unfold sa_W4 in MU.
  change i_sec_nres with 1525192%Z in MU. change i_sec_sorted with 1525208%Z in MU. change i_sec_bylog with 1525248%Z in MU.
  change i_gstat_alloc with 1525784%Z in MU. change i_sec_mutex with 1525760%Z in MU.
  pose proof (wmono_refl bsegs m) as WM.
  hide_disj.
  zhide.
  zstep.
  zstep.
  rewrite (lxor63_k k Hk).
  unfold hide in GP4, APA.
  zstep.
  hide_disj.
  zstep. zstep.
  replace (PAB + n ≪ 3)%Z with (PAB + 8 * n)%Z by (rewrite Z.shiftl_mul_pow2 by lia; lia).
  unfold hide in APA, GA4.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (u64arr_store_ok bsegs mm PAB ws n (Z_to_bv 64 (PAB + 8 * n)) ARR ltac:(lia) ltac:(unfold wa; f_equal; lia)) as SO;
    zstep;
    pose proof (u64arr_write bsegs mm PAB ws n (Z_to_bv 64 P) ARR ltac:(lia)) as ARR'; clear ARR end.
  store_done.
  hide_disj.
  do 6 zstep.
  unfold hide in GA4, GP4.
  zstep.
  zstep; fix_lit_store.
  zstep. zstep.
  hide_disj.
  zstep.
  apply unbox in GP0, GA0.
  if_cases C.
  - eapply sa_p4b; try eassumption.
  - zstep. eapply sa_p4b; try eassumption.
Qed.

