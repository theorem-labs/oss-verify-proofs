(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Lib Require Import Tac ImageA Arr Walk SysStep ITree StoreFast.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Malloc Require Import MallocKit_AB.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.A Require Import Shadow R_secalloc_math.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.B Require Import Layout R_small R_m2s R_thread R_cache_defs R_prim_defs R_glue_defs R_sec_defs F_memset R_setshadow R_poison R_secalloc_ps0 R_mmapordie R_secalloc R_secalloc_p2 R_secalloc_p3 R_secalloc_p4 R_secalloc_B0 R_flushshadow.
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
Local Ltac lia ::= lia3.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac hide_disj := repeat match goal with
  | H : (?A \/ ?B) |- _ => change (hide (A \/ B)) in H
  end.

Ltac lia_p := zify_prune_plain; Zify.zify; xlia zchecker.
Ltac disj_one :=
  first [ lia_p
        | match goal with H : hide (_ \/ _) |- _ =>
            let H' := fresh "Hd" in pose proof H as H'; unfold hide in H'; decompose [or] H'; lia_p
          end ].
Ltac my_disj := repeat match goal with |- _ /\ _ => split end; try exact I; disj_one.
Local Ltac tslia ::= first [ exact I | my_disj ].

Local Ltac disj_try H := let H' := fresh "Hd" in pose proof H as H'; unfold hide in H'; decompose [or] H'; lia_p.
Module RS.
  Import Ltac2.
  Ltac2 is_hdisj (t : constr) : bool := lazy_match! t with hide (_ \/ _) => true | _ => false end.
  Ltac2 rsearch () : unit :=
    let gv := SF2.vars_of [] (Control.goal ()) in
    let ids := List.map_filter (fun h => let (id, body, ty) := h in
                 match body with
                 | Some _ => None
                 | None => if is_hdisj ty then (if SF2.meets (SF2.vars_of [] ty) gv then Some id else None) else None
                 end) (Control.hyps ()) in
    let rec go l := match l with
      | [] => Control.zero (Tactic_failure None)
      | id :: l' => Control.plus (fun () => ltac1:(h |- disj_try h) (Ltac1.of_constr (Control.hyp id))) (fun _ => go l')
      end in
    go ids.
  Ltac2 rsearch1 () : unit := Control.enter rsearch.
End RS.
Local Ltac disj_rel := ltac2:(RS.rsearch1 ()).
Local Ltac disj_one ::=
  first [ lia_p
        | disj_rel
        | match goal with H : hide (_ \/ _) |- _ =>
            let H' := fresh "Hd" in pose proof H as H'; unfold hide in H'; decompose [or] H'; lia_p
          end ].

Definition sd_W1 (sp PAB IDX LMB : Z) : list (Z * Z) :=
  [(sp - 32, sp); (i_sec_mutex, i_sec_mutex + 4); (i_sec_nres + 8, i_sec_nres + 16); (i_sec_sorted, i_sec_sorted + 40);
   (PAB + 8 * IDX, PAB + 8 * IDX + 8); (LMB + 24, LMB + 32); (i_gstat_alloc, i_gstat_alloc + 16)]%Z.

Section P1.
Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (m : mem) (MB MSZ SZ IDX PAB nres n LMB LIDX lo : Z) (ws : list word) (Q : machine_state -> Prop).
Hypothesis HMB : (MB mod 4096 = 0 /\ 65536 < MSZ /\ MSZ mod 4096 = 0)%Z.
Hypothesis GM : gobj MB MSZ lo.
Hypothesis GA : gobj PAB 0x800000 lo.
Hypothesis GL : (7135232 <= LMB /\ LMB + 32 <= lo)%Z.
Hypothesis AMA : sapart MB MSZ PAB 0x800000.
Hypothesis ALA : sapart LMB 32 PAB 0x800000.
Hypothesis ALM : (LMB = MB \/ LMB + 32 <= MB \/ MB + MSZ <= LMB)%Z.
Hypothesis Hidx : (0 <= IDX < n /\ n <= nres /\ Z.of_nat (length ws) = nres /\ nres <= 2^20)%Z.
Hypothesis HWI : nth_error ws (Z.to_nat IDX) = Some (Z_to_bv 64 MB).
Hypothesis HWL : nth_error ws (Z.to_nat (n - 1)) = Some (Z_to_bv 64 LMB).
Hypothesis PG : sec_page m.
Hypothesis SC : sec_core m PAB nres n.
Hypothesis PAD : sec_pad m.
Hypothesis SJ : sec_junk m.
Hypothesis ARR : u64arr bsegs m PAB ws.
Hypothesis HD : rw_cells bsegs m MB [C8 (Z_to_bv 64 MB); C8 (Z_to_bv 64 MSZ); C8 (Z_to_bv 64 SZ)].
Hypothesis HDI : rw_cells bsegs m (MB + 24) [C8 (Z_to_bv 64 IDX)].
Hypothesis WLI : rw_cells bsegs m (LMB + 24) [C8 (Z_to_bv 64 LIDX)].
Hypothesis ST : stk bsegs m lo (bv_unsigned sp).
Hypothesis HLOH : (kHighShadowEnd + 8 <= lo)%Z.
Hypothesis HLO : (lo <= bv_unsigned sp - 32)%Z.
Hypothesis HSP : (bv_unsigned sp <= 2^47)%Z.
Hypothesis MI : mem_inv bsegs m.
Hypothesis K : forall (m' : mem) (t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
  munch (sd_W1 (bv_unsigned sp) PAB IDX LMB) m m' -> wmono bsegs m m' -> mem_inv bsegs m' ->
  rw_cells bsegs m' (bv_unsigned sp - 32) [C8 s2; C8 s1; C8 s0; C8 ra] -> stk bsegs m' lo (bv_unsigned sp - 32) ->
  sec_page m' -> sec_core m' PAB nres (n - 1) -> sec_pad m' -> sec_junk m' ->
  u64arr bsegs m' PAB (upd ws (Z.to_nat IDX) (Z_to_bv 64 LMB)) ->
  rw_cells bsegs m' MB [C8 (Z_to_bv 64 MB); C8 (Z_to_bv 64 MSZ); C8 (Z_to_bv 64 SZ)] ->
  rw_cells bsegs m' (LMB + 24) [C8 (Z_to_bv 64 IDX)] ->
  evt bsegs Q
    (MS (mkR (Z_to_bv 64 0x5bff0) (Z_to_bv 64 (bv_unsigned sp - 32)) gp tp t0 t1 t2 (Z_to_bv 64 MB) (Z_to_bv 64 MB)
             (Z_to_bv 64 MB) (Z_to_bv 64 MSZ) (Z_to_bv 64 0) a3 a4 a5 a6 a7 (Z_to_bv 64 MSZ) s3 s4 s5 s6 s7 s8 s9 s10 s11
             t3 t4 t5 t6)
        F (Z_to_bv 64 0x81d40) fc None m' (seg_rom bsegs)).

Lemma sd_p1 : forall (t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
  evt bsegs Q
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 SEC) (Z_to_bv 64 GSTAT) (Z_to_bv 64 (MB + 4096)) a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x5befc) fc None m (seg_rom bsegs)).
Proof using HMB GM GA GL AMA ALA ALM Hidx HWI HWL PG SC PAD SJ ARR HD HDI WLI ST HLOH HLO HSP MI K.
  intros.
  destruct HMB as (HMB1 & HMB2 & HMB3). destruct Hidx as (HI1 & HI2 & Hlen & HI4).
  pose proof GM as (GM1 & GM2 & GM3 & GM4). pose proof GA as (GA1 & GA2 & GA3 & GA4). destruct GL as (GL1 & GL2).
  unfold sapart, img_hull_lo, img_hull_hi, kHighShadowEnd in *.
  assert (GM4' : (7135232 <= MB)%Z) by (destruct GM4; lia).
  assert (GA4' : (7135232 <= PAB)%Z) by (destruct GA4; lia).
  pose proof SC as (CH & NR & MX). pose proof SJ as ((b & jj & w1 & w2 & w3 & w4 & SJ1) & (bl & Hbl & SJ2) & (ga & gm & SJ3)).
  unfold sec_page, i_sec_page in PG. change (INST + 0x40)%Z with 1525144%Z in PG.
  change i_sec_chunks with 1525152%Z in CH. change i_sec_nres with 1525192%Z in NR. change i_sec_mutex with 1525760%Z in MX.
  unfold sec_pad in PAD. change (i_sec_mutex + 1)%Z with 1525761%Z in PAD.
  change i_sec_sorted with 1525208%Z in SJ1. change i_sec_bylog with 1525248%Z in SJ2. change i_gstat_alloc with 1525784%Z in SJ3.
  change SEC with 1525144%Z. change GSTAT with 1525768%Z.
  pose proof (munch_refl (sd_W1 (bv_unsigned sp) PAB IDX LMB) m) as MU. unfold sd_W1 in MU.
  change i_sec_nres with 1525192%Z in MU. change i_sec_sorted with 1525208%Z in MU.
  change i_gstat_alloc with 1525784%Z in MU. change i_sec_mutex with 1525760%Z in MU.
  pose proof (wmono_refl bsegs m) as WM.
  apply box in HMB1, HMB3.
  clear GM GA SC SJ.
  hide_disj.
  carve_frame 32%nat ST.
  zhide.
  do 5 zstep.
  do 3 zstep.
  rewrite (land4095_al (MB + 4096)) by (pose proof (unbox _ HMB1); Z.div_mod_to_equations; lia).
  zstep. ifF.
  do 4 zstep.
  pose proof (lockw_of _ MX PAD) as LW. clear MX PAD. change i_sec_mutex with 1525760%Z in LW.
  assert (AMO : amo_aligned AW (Z_to_bv 64 1525760) = true) by (vm_compute; reflexivity).
  amo_step AMO.
  replace (sx32 (Z_to_bv 64 0)) with (Z_to_bv 64 0) by (vm_compute; reflexivity).
  do 4 zstep.
  amo_step AMO; try fix_lit_store.
  zstep. ifF.
  do 3 zstep. ifF.
  replace (MB + 4096 + - (4096))%Z with MB by lia.
  do 4 zstep.
  replace (PAB + IDX ≪ 3)%Z with (PAB + 8 * IDX)%Z by (rewrite Z.shiftl_mul_pow2 by lia; lia).
  pose proof (u64arr_read bsegs _ PAB ws IDX (Z_to_bv 64 MB) (Z_to_bv 64 (PAB + 8 * IDX)) ARR HWI ltac:(lia) ltac:(reflexivity)) as RD1.
  zstep. clear RD1.
  zstep. ifF.
  zstep. zstep. ifF.
  do 3 zstep.
  replace (n ≪ 3 + PAB)%Z with (PAB + 8 * n)%Z by (rewrite Z.shiftl_mul_pow2 by lia; lia).
  do 3 zstep.
  pose proof (u64arr_read bsegs _ PAB ws (n - 1) (Z_to_bv 64 LMB) (Z_to_bv 64 (PAB + 8 * n + -8)) ARR HWL ltac:(lia)
                ltac:(unfold wa; f_equal; lia)) as RD2.
  zstep. clear RD2.
  do 2 zstep.
  zstep.
  zstep; fix_lit_store.
  zstep. zstep.
  zstep. zstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    match goal with A' : u64arr bsegs mm PAB _ |- _ =>
      pose proof (u64arr_store_ok bsegs mm PAB _ IDX (Z_to_bv 64 (PAB + 8 * IDX)) A' ltac:(lia) ltac:(reflexivity)) as SO;
      zstep;
      pose proof (u64arr_write bsegs mm PAB _ IDX (Z_to_bv 64 LMB) A' ltac:(lia)) as ARR'; clear A' end end.
  store_done.
  zstep.
  assert (AMO1 : amo_aligned AD (Z_to_bv 64 1525784) = true) by (vm_compute; reflexivity).
  amo_step AMO1.
  do 3 zstep.
  assert (AMO2 : amo_aligned AD (Z_to_bv 64 1525792) = true) by (vm_compute; reflexivity).
  amo_step AMO2.
  zstep.
  apply lockw_to1 in LW. change i_sec_mutex with 1525760%Z in LW.
  zstep; fix_lit_store.
  do 6 zstep.
  change 1525760%Z with i_sec_mutex in LW. apply lockw_split in LW. destruct LW as [MX PAD].
  replace (bv_unsigned sp + -32)%Z with (bv_unsigned sp - 32)%Z in * by lia.
  unfold hide in *.
  apply (K _ _ _ _ _ _ _ _ _ _ _ _ _ MU WM); try assumption.
  all: first [ (unfold sec_page, i_sec_page; exact PG)
             | (split; [exact CH| split; [exact NR| exact MX]])
             | (unfold sec_junk; split; [do 6 eexists; exact SJ1|]; split; [eexists; split; [exact Hbl| exact SJ2]|];
                do 2 eexists; exact SJ3) ].
Qed.
End P1.
