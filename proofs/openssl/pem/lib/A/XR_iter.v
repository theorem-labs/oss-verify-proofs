(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac ImageA Arr Walk Image SysStep.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import StoreFast.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Str_tac Startup_glue.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import MallocKit_AB.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Start Require Import AsanRehashModel AsanRegModel.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require R_memiszero R_prim_defs.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow R_arrkit.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface R_small R_cache_defs F_memset X_atexit X_gdefs X_unregi XR_rehash XR_kit XR_probe.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

(* [comment removed for export] *)
Lemma seg_rom_above : forall x, img_hull_hi <= x < 2 ^ 64 -> seg_rom asegs (wa x) = None.
Proof.
  intros x Hx. unfold seg_rom, memory_read. rewrite wa_unsigned by (unfold img_hull_hi in Hx; lia).
  rewrite R_prim_defs.find_segment_above; [reflexivity| unfold img_hull_hi in Hx; lia|].
  apply (R_prim_defs.forallb_mono_top asegs img_hull_hi); [lia| exact R_prim_defs.asegs_top].
Qed.

Lemma mrd_above : forall (m : mem) x v, img_hull_hi <= x < 2 ^ 64 -> mrd asegs m (wa x) = Some v -> m (wa x) = Some v.
Proof. intros m x v Hx H. unfold mrd in H. destruct (m (wa x)) as [b|]; [exact H|]. rewrite (seg_rom_above x Hx) in H. discriminate H. Qed.

(* [comment removed for export] *)
Definition sh_pt (m : mem) (lo hi : Z) (f : Z -> byte) : Prop := forall x, lo <= x < hi -> m (Z_to_bv 64 x) = Some (f x).

Lemma sh_pt_of_cells : forall (m : mem) A cs (n : nat) (f : Z -> byte), rw_cells asegs m A cs -> img_hull_hi <= A ->
  length (cells_bytes cs) = n -> (forall i, (i < n)%nat -> nth_error (cells_bytes cs) i = Some (f (A + Z.of_nat i))) ->
  sh_pt m A (A + Z.of_nat n) f.
Proof.
  intros m A cs n f RW HA HL HF x Hx.
  pose proof (rw_cells_bytes_at asegs m A _ RW) as (B0 & B1 & BY). rewrite HL in B1.
  assert (Hi : (Z.to_nat (x - A) < length (cells_bytes cs))%nat) by lia.
  pose proof (BY _ Hi) as E. rewrite (HF (Z.to_nat (x - A)) ltac:(lia)) in E.
  replace (A + Z.of_nat (Z.to_nat (x - A))) with x in E by lia.
  apply (mrd_above m x _ ltac:(lia) E).
Qed.

Lemma sh_pt_of_CB : forall (m : mem) A n (v : byte), rw_cells asegs m A [CB n (repeat v n)] -> img_hull_hi <= A ->
  sh_pt m A (A + Z.of_nat n) (fun _ => v).
Proof.
  intros m A n v RW HA. apply (sh_pt_of_cells m A _ n (fun _ => v) RW HA); cbn [cells_bytes cbytes]; rewrite app_nil_r.
  - apply repeat_length.
  - intros i Hi. apply nth_error_repeat. exact Hi.
Qed.

Lemma sh_pt_of_C1 : forall (m : mem) A (v : byte), rw_cells asegs m A [C1 v] -> img_hull_hi <= A -> sh_pt m A (A + 1) (fun _ => v).
Proof.
  intros m A v RW HA. apply (sh_pt_of_cells m A _ 1 (fun _ => v) RW HA); [reflexivity|].
  intros i Hi. destruct i; [reflexivity| lia].
Qed.

Lemma sh_pt_write_other : forall (m : mem) a bs (n : Z) lo hi f, Z.of_nat (length bs) = n -> 0 <= a -> a + n <= 2 ^ 64 ->
  sh_pt m lo hi f -> 0 <= lo -> hi <= 2 ^ 64 -> (hi <= a \/ a + n <= lo) -> sh_pt (write_to_mem m (wa a) bs) lo hi f.
Proof.
  intros m a bs n lo hi f Hn Ha Hl H L0 H1 D x Hx. rewrite (write_to_mem_spec bs m a (Z_to_bv 64 x) Ha ltac:(lia)).
  rewrite unsigned_lit by lia.
  replace ((a <=? x) && (x <? a + Z.of_nat (length bs))) with false by (symmetry; apply andb_false_iff; rewrite Z.leb_gt, Z.ltb_ge; lia).
  apply H. exact Hx.
Qed.

(* [comment removed for export] *)
Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::=
  repeat match goal with
  | H : sh_pt m ?lo ?hi ?f |- _ =>
      apply (sh_pt_write_other m a bs n lo hi f Hn Ha Hl) in H; [ | tlia | tlia | tlia ]
  end.

Notation TABA := 0x5aaa60%Z (only parsing).

Section Iter.
Variables (fp n : Z) (gp tp s3 s10 : word) (F : bvmap 5 word) (fc : bv 32).

(* [comment removed for export] *)
Definition st_entry (i : Z) (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s6 s7 t3 t4 t5 t6 : word) (pc : Z) (m : mem) : machine_state :=
  MS (mkR ra (Z_to_bv 64 (fp - 0x10f0)) gp tp t0 t1 t2 (Z_to_bv 64 fp) (Z_to_bv 64 TABA) a0 a1 a2 a3 a4 a5 a6 a7
          s2 s3 (Z_to_bv 64 0x66cb38) (Z_to_bv 64 1) s6 s7 (Z_to_bv 64 0x66a338) (Z_to_bv 64 0x66a3b0) s10 (Z_to_bv 64 i) t3 t4 t5 t6)
     F (Z_to_bv 64 pc) fc None m (seg_rom asegs).

Lemma reg_head : forall (i g beg size swr odr : Z) (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s6 s7 t3 t4 t5 t6 : word) (m : mem),
  0 <= i < 2 ^ 24 -> g = TABA + 64 * i ->
  ro_cells asegs m g [C8 (Z_to_bv 64 beg); C8 (Z_to_bv 64 size); C8 (Z_to_bv 64 swr)] ->
  ro_cells asegs m (g + 56) [C8 (Z_to_bv 64 odr)] ->
  0x10000 <= beg -> beg mod 8 = 0 -> 0 <= swr -> swr mod 8 = 0 -> beg + swr <= 0xbc6000 -> 0 <= odr < 2 ^ 64 ->
  rw_cells asegs m 0x66d818 [C1 (Z_to_bv 8 1)] ->
  ro_cells asegs m 0x66a350 [C4 (Z_to_bv 64 1)] -> ro_cells asegs m 0x66a39c [C4 (Z_to_bv 64 2)] ->
  ro_cells asegs m 0x66cb38 [C8 (Z_to_bv 64 0x7fff8000)] ->
  mem_inv asegs m ->
  evt asegs (fun ms' => exists (t0' t1' t2' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
      ms' = st_entry i (Z_to_bv 64 0x1a94f0) t0' t1' t2' (Z_to_bv 64 beg) (Z_to_bv 64 swr) (Z_to_bv 64 odr) (Z_to_bv 64 (-1)) a4' a5' a6' a7'
                     s2 (Z_to_bv 64 g) s7 t3' t4' t5' t6' (if odr =? RGM.ODR_NONE then 0x1a9904 else 0x1a9770) m'
      /\ munch [] m m' /\ wmono asegs m m' /\ mem_inv asegs m')
    (st_entry i ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s6 s7 t3 t4 t5 t6 0x1a94ec m).
Proof.
  intros until m. intros Hi Hg REC RODR B0 B8 S0 S8 BT HO AI RG DO SHC MI. unfold st_entry in *.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
  xstep.
  call asan_inited_spec; [exact AI| exact MI|].
  xsteps_to 0x1a9500%Z.
  rewrite (Z.shiftl_mul_pow2 i 6) by lia.
  lazymatch goal with |- context [Z_to_bv 64 (?tb + i * 2 ^ 6)] => replace (tb + i * 2 ^ 6) with g by lia end.
  xsteps_to 0x1a953c%Z.
  xstep. fold_closed_regs. ifT.
  xstep. rewrite (land_7 beg ltac:(lia)), B8. xstep.
  xstep. xstep. rewrite (land_7 swr S0), S8. xstep.
  xsteps_to 0x1a976c%Z.
  xstep.
  rewrite bv_eqb_Z, (unsigned_lit odr) by lia. change (bv_unsigned (Z_to_bv 64 (-1))) with RGM.ODR_NONE.
  apply evt_done. do 12 eexists. split; [| split; [exact MU| split; [exact WM| assumption]]].
  destruct (odr =? RGM.ODR_NONE); reflexivity.
Qed.

(* [comment removed for export] *)
Lemma reg_poison : forall (i g beg size swr : Z)
    (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s7 t3 t4 t5 t6 : word) (m : mem),
  TABA <= g -> g + 64 <= 0x669460 -> 0x80170c00 <= fp + -4304 -> fp < 2 ^ 47 ->
  ro_cells asegs m g [C8 (Z_to_bv 64 beg); C8 (Z_to_bv 64 size); C8 (Z_to_bv 64 swr)] ->
  0x10000 <= beg -> beg mod 8 = 0 -> swr mod 8 = 0 -> 1 <= size -> RGM.rup8 size <= swr -> swr < 0x80000 -> beg + swr <= 0xbc6000 ->
  ro_cells asegs m 0x66cb38 [C8 (Z_to_bv 64 0x7fff8000)] ->
  ro_cells asegs m 0x66a38d [C1 (Z_to_bv 8 1)] ->
  ro_cells asegs m 0x5a77f0 [C8 (Z_to_bv 64 0x526914)] ->
  ro_cells asegs m (fp + -4304) [C8 (Z_to_bv 64 0x5a77f0)] ->
  stk asegs m SHW_LO SHW_HI ->
  mem_inv asegs m ->
  evt asegs (fun ms' => exists (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s2' t3' t4' t5' t6' : word) (m' : mem),
      ms' = st_entry i ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s2' (Z_to_bv 64 g) s7 t3' t4' t5' t6' 0x1a9a90 m'
      /\ munch [(0x7fff8000 + beg / 8 + size / 8, 0x7fff8000 + beg / 8 + swr / 8)] m m'
      /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ stk asegs m' SHW_LO SHW_HI
      (* [comment removed for export] *)
      /\ sh_pt m' (0x7fff8000 + beg / 8 + size / 8) (0x7fff8000 + beg / 8 + swr / 8)
               (fun x => Z_to_bv 8 (if (x =? 0x7fff8000 + beg / 8 + size / 8) && negb (size mod 8 =? 0) then size mod 8 else 0xf9)))
    (st_entry i ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 g) s7 t3 t4 t5 t6 0x1a990c m).
Proof.
  intros until m. intros G0 G1 FP0 FP1 REC B0 B8 S8 Z1 RU SW BT SHC PP MSC MP SCW MI.
  unfold st_entry in *.
  pose proof (munch_refl [(0x7fff8000 + beg / 8 + size / 8, 0x7fff8000 + beg / 8 + swr / 8)] m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  xsteps_to 0x1a9924%Z. change (- (4096)) with (-4096).
  xsteps_to 0x1a995c%Z.
  assert (E64 : forall x, 0 <= x < 2 ^ 64 -> Z.land x 18446744073709551615 = x)
    by (intros x Hx; change 18446744073709551615 with (Z.ones 64); rewrite Z.land_ones by lia; apply Z.mod_small; exact Hx).
  set (al := RGM.rup8 size) in *.
  assert (ALF : al mod 8 = 0 /\ size <= al < size + 8) by (unfold al, RGM.rup8; Z.div_mod_to_equations; lia).
  assert (EA : Z.land (Z.land (size + 7) 18446744073709551615) 18446744073709551608 = al)
    by (rewrite (E64 (size + 7)) by lia; rewrite R_memiszero.land_m8 by lia; reflexivity).
  rewrite !EA.
  assert (ED : Z.land (al + beg) 18446744073709551615 ≫ 3 + 2147450880 = 2147450880 + (beg + al) / 8)
    by (rewrite (E64 (al + beg)) by lia; rewrite Z.shiftr_div_pow2 by lia; change (2 ^ 3) with 8; replace (al + beg) with (beg + al) by lia; lia).
  rewrite !ED.
  assert (EN : 2147450880 + Z.land (beg + swr + -8) 18446744073709551615 ≫ 3 + - Z.land (2147450880 + (beg + al) / 8) 18446744073709551615 + 1 = (swr - al) / 8).
  { rewrite (E64 (beg + swr + -8)) by lia. rewrite (E64 (2147450880 + (beg + al) / 8)) by (Z.div_mod_to_equations; lia).
    rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. Z.div_mod_to_equations. lia. }
  rewrite EN.
  xstep.
  assert (N0 : 0 <= (swr - al) / 8) by (Z.div_mod_to_equations; lia).
  assert (SL0 : 0x7fffa000 <= 2147450880 + (beg + al) / 8) by (Z.div_mod_to_equations; lia).
  assert (SH0 : 2147450880 + (beg + al) / 8 + (swr - al) / 8 <= 0x80170c00) by (Z.div_mod_to_equations; lia).
  destruct (stk_window _ _ _ (2147450880 + (beg + al) / 8) ((swr - al) / 8) SCW SL0 SH0 N0) as (SA & (junk & DST) & SB). clear SCW.
  call memset_callZ; [exact DST| assumption| lia| Z.div_mod_to_equations; lia| Z.div_mod_to_equations; lia| lia|].
  pose proof (sh_pt_of_CB _ _ _ _ POST ltac:(unfold img_hull_hi; lia)) as PW.
  rewrite Z2Nat.id in PW by lia.
  pose proof (stk_unwindow _ _ _ _ ((swr - al) / 8) _ SA POST ltac:(cbn [cells_size csize]; rewrite Nat.add_0_r, Z2Nat.id by lia; reflexivity)
                SB SL0 SH0) as SCW.
  clear SA SB POST.
  xstep. xstep.
  assert (EUs : bv_unsigned (Z_to_bv 64 size) = size) by (apply unsigned_lit; lia).
  assert (EUa : bv_unsigned (Z_to_bv 64 al) = al) by (apply unsigned_lit; lia).
  rewrite bv_eqb_Z, EUs, EUa.
  destruct (Z.eqb_spec size al) as [EQ|NE].
  - (* [comment removed for export] *)
    apply evt_done. do 18 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact SCW|].
    intros xx Hxx. assert (SM0 : size mod 8 = 0) by (clear -EQ ALF; lia).
    rewrite SM0. change (0 =? 0) with true. cbn [negb]. rewrite andb_false_r.
    apply PW. clear -Hxx EQ ALF B8 S8 RU Z1. lia.
  - xstep. rewrite (land_7 size ltac:(lia)).
    assert (SM : size mod 8 <> 0) by (unfold al, RGM.rup8 in *; Z.div_mod_to_equations; lia).
    xstep.
    assert (EUm : bv_unsigned (Z_to_bv 64 (size mod 8)) = size mod 8) by (apply unsigned_lit; Z.div_mod_to_equations; lia).
    rewrite bv_eqb_Z, EUm. change (bv_unsigned z64) with 0. rewrite (proj2 (Z.eqb_neq _ _) SM). cbn [negb].
    xsteps_to 0x1a9a8c%Z.
    assert (EP : Z.land (beg + Z.land size 18446744073709551608) 18446744073709551615 ≫ 3 + 2147450880 = 2147450880 + (beg + size / 8 * 8) / 8).
    { rewrite R_memiszero.land_m8 by lia. rewrite (E64 (beg + size / 8 * 8)) by (Z.div_mod_to_equations; lia).
      rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. lia. }
    rewrite EP.
    assert (PL0 : 0x7fffa000 <= 2147450880 + (beg + size / 8 * 8) / 8) by (Z.div_mod_to_equations; lia).
    assert (PH0 : 2147450880 + (beg + size / 8 * 8) / 8 + 1 <= 0x80170c00) by (Z.div_mod_to_equations; lia).
    destruct (stk_window _ _ _ (2147450880 + (beg + size / 8 * 8) / 8) 1 SCW PL0 PH0 ltac:(lia)) as (SA & (junk1 & DST1) & SB). clear SCW.
    change (Z.to_nat 1) with 1%nat in DST1.
    remember (2147450880 + (beg + size / 8 * 8) / 8) as PB eqn:EPB.
    assert (EUpb : bv_unsigned (Z_to_bv 64 PB) = PB) by (apply unsigned_lit; lia).
    assert (EUpb1 : bv_unsigned (Z_to_bv 64 (PB + 1)) = PB + 1) by (apply unsigned_lit; lia).
    assert (EV : Z_to_bv 64 (Z.land (Z.land (0 + - (1)) 18446744073709551615) (size mod 8)) = zxb (Z_to_bv 8 (size mod 8))).
    { change (Z.land (0 + - (1)) 18446744073709551615) with (Z.ones 64). rewrite Z.land_comm, Z.land_ones by lia.
      rewrite (Z.mod_small (size mod 8)) by (Z.div_mod_to_equations; lia).
      unfold zxb. f_equal. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. cbn [Z.of_N]. symmetry. apply Z.mod_small. Z.div_mod_to_equations. lia. }
    rewrite EV.
    zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mm ?aa (le1 (?f ?b))) _) =>
      change (le1 (f b)) with (le1 (zxb b)) end.
    rewrite le1_zxb.
    mem_after_store.
    lazymatch goal with DST' : rw_cells asegs ?mm PB ?cs |- _ =>
      pose proof (sh_pt_of_C1 mm PB _ DST' ltac:(unfold img_hull_hi; lia)) as PW1;
      pose proof (stk_unwindow mm _ _ PB 1 cs SA DST' ltac:(reflexivity) SB ltac:(lia) ltac:(lia)) as SCW end.
    apply evt_done. do 18 eexists. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact SCW|].
    intros xx Hxx.
    assert (EWL : 0x7fff8000 + beg / 8 + size / 8 = PB) by (clear -EPB B8; lia).
    rewrite EWL in Hxx |- *.
    destruct (Z.eqb_spec xx PB) as [->|NEx].
    + cbn [negb andb]. apply PW1. lia.
    + cbn [andb]. apply PW. clear -Hxx NEx EPB ALF B8 S8 RU Z1 SM. lia.
Qed.

(* [comment removed for export] *)
Lemma reg_addlist : forall (i g lend cur CEND lsize first : Z)
    (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s7 t3 t4 t5 t6 : word) (m : mem),
  0 <= i -> i + 1 < n -> TABA + 64 * n <= 0x669460 -> g = TABA + 64 * i ->
  ro_cells asegs m (g + 40) [C8 (Z_to_bv 64 0)] ->
  ro_cells asegs m 0x5a7830 [C8 (Z_to_bv 64 8)] ->
  ro_cells asegs m (fp + -4272) [C8 (Z_to_bv 64 n)] ->
  stk asegs m (fp - 0x10f0 - 32) (fp - 0x10f0) -> 0x80170c00 <= fp - 0x10f0 - 32 -> fp < 2 ^ 47 ->
  rw_cells asegs m LLA [C8 (Z_to_bv 64 lend); C8 (Z_to_bv 64 cur)] -> 0 < cur -> cur + 16 <= CEND -> CEND <= lend -> lend < 2 ^ 47 ->
  stk asegs m cur CEND -> (CEND <= 0x10000 \/ 0xbc6000 <= cur) ->
  (CEND <= fp - 0x10f0 - 32 \/ fp <= cur) ->
  rw_cells asegs m 0x66a3b8 [C8 (Z_to_bv 64 lsize); C8 (Z_to_bv 64 first)] -> 1 <= lsize -> lsize + 1 < 2 ^ 63 ->
  mem_inv asegs m ->
  evt asegs (fun ms' => exists (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
      ms' = st_entry (i + 1) ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s2 (Z_to_bv 64 g) s7 t3' t4' t5' t6' 0x1a94ec m'
      /\ munch [(fp - 0x10f0 - 32, fp - 0x10f0); (0x66a3b8, 0x66a3c8); (LLA + 8, LLA + 16); (cur, cur + 16)] m m'
      /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ stk asegs m' (fp - 0x10f0 - 32) (fp - 0x10f0)
      /\ rw_cells asegs m' LLA [C8 (Z_to_bv 64 lend); C8 (Z_to_bv 64 (cur + 16))]
      /\ stk asegs m' (cur + 16) CEND
      /\ rw_cells asegs m' 0x66a3b8 [C8 (Z_to_bv 64 (lsize + 1)); C8 (Z_to_bv 64 cur)])
    (st_entry i ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 g) s7 t3 t4 t5 t6 0x1a9a90 m).
Proof.
  intros until m. intros Hi Hin Hn Hg RDYN AL NS FRS SPlo FPhi LLC C0 CR CE LE AST AI AFR HDR LS1 LS2 MI.
  unfold st_entry in *.
  pose proof (munch_refl [(fp - 0x10f0 - 32, fp - 0x10f0); (0x66a3b8, 0x66a3c8); (0x6eed88 + 8, 0x6eed88 + 16); (cur, cur + 16)] m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  xstep. xstep. xstep. xstep. xstep. xstep.
  assert (SPR : fp - 0x10f0 < 2 ^ 63) by lia.
  call (lla_alloc16_spec (fp - 0x10f0)); [reflexivity| reflexivity| exact FRS| lia| unfold SEGTOP_A; lia| exact SPR| exact AL| exact LLC| lia| lia| lia| assumption|].
  destruct (stk_window _ _ _ cur 16 AST ltac:(lia) ltac:(lia) ltac:(lia)) as (SA & (junkn & NODE) & SB). clear AST SA.
  change (Z.to_nat 16) with 16%nat in NODE.
  assert (EUc : bv_unsigned (Z_to_bv 64 cur) = cur) by (apply unsigned_lit; lia).
  assert (EUl : bv_unsigned (Z_to_bv 64 lsize) = lsize) by (apply unsigned_lit; lia).
  xsteps_to 0x1a9ac0%Z. xstep.
  xstep. xstep. xstep. xstep. change (- (4096)) with (-4096). xstep.
  assert (EUi : bv_unsigned (Z_to_bv 64 (i + 1)) = i + 1) by (apply unsigned_lit; lia).
  assert (EUn : bv_unsigned (Z_to_bv 64 n) = n) by (apply unsigned_lit; lia).
  xstep.
  apply evt_done. do 17 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption|].
  split; [assumption|]. split; [assumption|]. split; [exact SB| exact HDR].
Qed.

(* [comment removed for export] *)
Lemma reg_addlist_fr : forall (P : mem -> Prop) (i g lend cur CEND lsize first : Z)
    (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s7 t3 t4 t5 t6 : word) (m : mem),
  0 <= i -> i + 1 < n -> TABA + 64 * n <= 0x669460 -> g = TABA + 64 * i ->
  ro_cells asegs m (g + 40) [C8 (Z_to_bv 64 0)] ->
  ro_cells asegs m 0x5a7830 [C8 (Z_to_bv 64 8)] ->
  ro_cells asegs m (fp + -4272) [C8 (Z_to_bv 64 n)] ->
  stk asegs m (fp - 0x10f0 - 32) (fp - 0x10f0) -> 0x80170c00 <= fp - 0x10f0 - 32 -> fp < 2 ^ 47 ->
  rw_cells asegs m LLA [C8 (Z_to_bv 64 lend); C8 (Z_to_bv 64 cur)] -> 0 < cur -> cur + 16 <= CEND -> CEND <= lend -> lend < 2 ^ 47 ->
  stk asegs m cur CEND -> (CEND <= 0x10000 \/ 0xbc6000 <= cur) ->
  (CEND <= fp - 0x10f0 - 32 \/ fp <= cur) ->
  rw_cells asegs m 0x66a3b8 [C8 (Z_to_bv 64 lsize); C8 (Z_to_bv 64 first)] -> 1 <= lsize -> lsize + 1 < 2 ^ 63 ->
  mem_inv asegs m ->
  (forall m', munch [(fp - 0x10f0 - 32, fp - 0x10f0); (0x66a3b8, 0x66a3c8); (LLA + 8, LLA + 16); (cur, cur + 16)] m m' -> P m') ->
  evt asegs (fun ms' => exists (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
      ms' = st_entry (i + 1) ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s2 (Z_to_bv 64 g) s7 t3' t4' t5' t6' 0x1a94ec m'
      /\ munch [(fp - 0x10f0 - 32, fp - 0x10f0); (0x66a3b8, 0x66a3c8); (LLA + 8, LLA + 16); (cur, cur + 16)] m m'
      /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ stk asegs m' (fp - 0x10f0 - 32) (fp - 0x10f0)
      /\ rw_cells asegs m' LLA [C8 (Z_to_bv 64 lend); C8 (Z_to_bv 64 (cur + 16))]
      /\ stk asegs m' (cur + 16) CEND
      /\ rw_cells asegs m' 0x66a3b8 [C8 (Z_to_bv 64 (lsize + 1)); C8 (Z_to_bv 64 cur)]
      /\ P m')
    (st_entry i ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 g) s7 t3 t4 t5 t6 0x1a9a90 m).
Proof.
  intros until m. intros Hi Hin Hn Hg RDYN AL NS FRS SPlo FPhi LLC C0 CR CE LE AST AI AFR HDR LS1 LS2 MI HP.
  eapply evt_mono.
  { exact (reg_addlist i g lend cur CEND lsize first ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s7 t3 t4 t5 t6 m
             Hi Hin Hn Hg RDYN AL NS FRS SPlo FPhi LLC C0 CR CE LE AST AI AFR HDR LS1 LS2 MI). }
  intros ms' (ra' & t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & E & MU & Q1 & Q2 & Q3 & Q4 & Q5 & Q6).
  exists ra', t0', t1', t2', a0', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'.
  split; [exact E|]. split; [exact MU|]. split; [exact Q1|]. split; [exact Q2|]. split; [exact Q3|]. split; [exact Q4|]. split; [exact Q5|].
  split; [exact Q6| exact (HP m' MU)].
Qed.

(* [comment removed for export] *)
Lemma reg_ind : forall (i g odr B N ne p lend cur CEND : Z) (ks : list Z) (nws : list word)
    (ra t0 t1 t2 a0 a1 a3 a4 a5 a6 a7 s2 s7 t3 t4 t5 t6 : word) (m : mem),
  TABA <= g -> g + 64 <= 0x669460 ->
  ro_cells asegs m (g + 56) [C8 (Z_to_bv 64 odr)] -> 0xb9faa0 <= odr < 0xba356d ->
  RGM.probe_ins N ks odr (RGM.hash0 N odr) 1 (Z.to_nat N) = Some p ->
  RGM.no_grow N ne = true ->
  8 <= N <= 2 ^ 20 -> 0 <= ne -> Forall (fun k => 0 <= k < 2 ^ 64) ks ->
  rw_cells asegs m 0x66a3e8 [C8 (Z_to_bv 64 MAPA)] ->
  rw_cells asegs m MAPA [C8 (Z_to_bv 64 B); C4 (Z_to_bv 64 ne); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 N)] ->
  u64arr asegs m B nws -> keys_rep (Z.to_nat N) nws ks ->
  0 < B -> B + 32 * N <= 2 ^ 47 -> (B + 32 * N <= 0x10000 \/ 0xbc6000 <= B) ->
  (B + 32 * N <= cur \/ CEND <= B) -> (B + 32 * N <= fp - 0x10f0 - 32 \/ fp <= B) ->
  rw_cells asegs m odr [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 0x66c39c [C1 (Z_to_bv 8 1)] ->
  ro_cells asegs m 0x5a7830 [C8 (Z_to_bv 64 8)] ->
  stk asegs m (fp + -4264) (fp + -4256) ->
  stk asegs m (fp - 0x10f0 - 32) (fp - 0x10f0) -> 0x80170c00 <= fp - 0x10f0 - 32 -> fp < 2 ^ 47 ->
  rw_cells asegs m LLA [C8 (Z_to_bv 64 lend); C8 (Z_to_bv 64 cur)] -> 0 < cur -> cur + 16 <= CEND -> CEND <= lend -> lend < 2 ^ 47 ->
  stk asegs m cur CEND -> (CEND <= 0x10000 \/ 0xbc6000 <= cur) ->
  (CEND <= fp - 0x10f0 - 32 \/ fp <= cur) ->
  mem_inv asegs m ->
  evt asegs (fun ms' => exists (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (nws' : list word) (m' : mem),
      ms' = st_entry i ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s2 (Z_to_bv 64 g) (Z_to_bv 64 (B + 32 * p)) t3' t4' t5' t6' 0x1a990c m'
      /\ munch [(fp + -4264, fp + -4256); (fp - 0x10f0 - 32, fp - 0x10f0); (MAPA + 8, MAPA + 12); (B + 32 * p, B + 32 * p + 32);
                (odr, odr + 1); (LLA + 8, LLA + 16); (cur, cur + 16)] m m'
      /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ stk asegs m' (fp + -4264) (fp + -4256)
      /\ stk asegs m' (fp - 0x10f0 - 32) (fp - 0x10f0)
      /\ rw_cells asegs m' MAPA [C8 (Z_to_bv 64 B); C4 (Z_to_bv 64 (ne + 1)); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 N)]
      /\ u64arr asegs m' B nws' /\ keys_rep (Z.to_nat N) nws' (RGM.upd ks (Z.to_nat p) odr)
      /\ rw_cells asegs m' odr [C1 (Z_to_bv 8 1)]
      /\ rw_cells asegs m' LLA [C8 (Z_to_bv 64 lend); C8 (Z_to_bv 64 (cur + 16))]
      /\ stk asegs m' (cur + 16) CEND)
    (st_entry i ra t0 t1 t2 a0 a1 (Z_to_bv 64 odr) a3 a4 a5 a6 a7 s2 (Z_to_bv 64 g) s7 t3 t4 t5 t6 0x1a9770 m).
Proof.
  intros until m. intros G0 G1 RODR HO PI NG HN Hne KF MPC MAP NA KR B0 BT BI BC BF IND CP AL KSS FRS SPlo FPhi LLC C0 CR CE LE AST AI AFR MI.
  unfold st_entry in *.
  pose proof (munch_refl [(fp + -4264, fp + -4256); (fp - 0x10f0 - 32, fp - 0x10f0); (0x66a418 + 8, 0x66a418 + 12); (B + 32 * p, B + 32 * p + 32);
                          (odr, odr + 1); (0x6eed88 + 8, 0x6eed88 + 16); (cur, cur + 16)] m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  assert (HLn : length nws = (4 * Z.to_nat N)%nat) by (destruct KR as (L & _); exact L).
  assert (EUo : bv_unsigned (Z_to_bv 64 odr) = odr) by (apply unsigned_lit; lia).
  xstep. xstep. xstep. xstep. xstep. change (- (4264)) with (-4264).
  destruct (stk_window _ _ _ (fp + -4264) 8 KSS ltac:(lia) ltac:(lia) ltac:(lia)) as (_ & (junkk & KS) & _). clear KSS.
  change (Z.to_nat 8) with 8%nat in KS.
  xstep. xstep.
  xstep. xstep. xstep. change (- (4264)) with (-4264). xstep.
  call (fac_spec B N ne odr p (fp + -4264) (fp - 0x10f0) 0x1a98c0 ks nws);
    [exact PI| exact NG| exact HN| exact Hne| exact KF| lia| exact KS| exact MAP| exact NA| exact KR| exact FRS| exact B0| exact BT
    | unfold SEGTOP_A; lia| unfold SEGTOP_A; lia| lia| lia| lia| lia| reflexivity| assumption|].
  rename PC0 into NA1, PC1 into KR1, PC2 into V1, PC3 into FRS1, PC4 into Hp0, POST into Hp1, PC into MAP1.
  lazymatch type of KR1 with keys_rep _ ?w _ => set (nws1 := w) in * end.
  assert (HLn1 : length nws1 = (4 * Z.to_nat N)%nat) by (destruct KR1 as (L & _); exact L).
  xstep. xstep. xstep. xstep.
  xstep.
  xstep. xstep. xstep. xstep. xstep. xstep.
  assert (SPR : fp - 0x10f0 < 2 ^ 63) by lia.
  call (lla_alloc16_spec (fp - 0x10f0)); [reflexivity| reflexivity| exact FRS1| lia| unfold SEGTOP_A; lia| exact SPR| exact AL| exact LLC| lia| lia| lia| assumption|].
  rename PC into FRS2, POST into LLC2.
  destruct (stk_window _ _ _ cur 16 AST ltac:(lia) ltac:(lia) ltac:(lia)) as (SA & (junkn & NODE) & SB). clear AST SA.
  change (Z.to_nat 16) with 16%nat in NODE.
  assert (EUc : bv_unsigned (Z_to_bv 64 cur) = cur) by (apply unsigned_lit; lia).
  xstep.
  (* [comment removed for export] *)
  lazymatch goal with NAx : u64arr asegs ?mm B nws1 |- _ =>
    pose proof (u64arr_read asegs mm B nws1 (4 * p + 1) _ (Z_to_bv 64 (B + 32 * p + 8)) NAx V1 ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD end.
  xstep. clear RD.
  xstep. xstep.
  (* [comment removed for export] *)
  lazymatch goal with NAx : u64arr asegs ?mm B ?xs |- _ =>
    pose proof (u64arr_store_ok asegs mm B _ (4 * p + 1) (wa (B + 8 * (4 * p + 1))) NAx ltac:(rewrite ?upd_length, HLn1; lia) eq_refl) as SOK;
    pose proof (u64arr_write asegs mm B _ (4 * p + 1) (Z_to_bv 64 1) NAx ltac:(rewrite ?upd_length, HLn1; lia)) as NA2 end.
  replace (B + 8 * (4 * p + 1)) with (B + 32 * p + 8) in SOK, NA2 by lia.
  zstep. lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ ?bs) _) => change bs with (le8 (Z_to_bv 64 1)) end. clear NA1. store_done.
  lazymatch goal with NAx : u64arr asegs ?mm B ?xs |- _ =>
    pose proof (u64arr_store_ok asegs mm B _ (4 * p + 2) (wa (B + 8 * (4 * p + 2))) NAx ltac:(rewrite ?upd_length, HLn1; lia) eq_refl) as SOK;
    pose proof (u64arr_write asegs mm B _ (4 * p + 2) (Z_to_bv 64 cur) NAx ltac:(rewrite ?upd_length, HLn1; lia)) as NA3 end.
  replace (B + 8 * (4 * p + 2)) with (B + 32 * p + 16) in SOK, NA3 by lia.
  zstep. clear NA2. store_done.
  lazymatch goal with NAx : u64arr asegs ?mm B ?xs |- _ =>
    pose proof (u64arr_store_ok asegs mm B _ (4 * p + 3) (wa (B + 8 * (4 * p + 3))) NAx ltac:(rewrite ?upd_length, HLn1; lia) eq_refl) as SOK;
    pose proof (u64arr_write asegs mm B _ (4 * p + 3) (Z_to_bv 64 cur) NAx ltac:(rewrite ?upd_length, HLn1; lia)) as NA4 end.
  replace (B + 8 * (4 * p + 3)) with (B + 32 * p + 24) in SOK, NA4 by lia.
  zstep. clear NA3. store_done.
  xstep.
  call can_poison_spec; [exact CP| assumption|].
  xstep. xstep.
  lazymatch goal with KSx : rw_cells asegs ?mm (fp + -4264) [C8 _] |- _ =>
    pose proof (stk_of_rw_cells asegs mm (fp + -4264) _ KSx) as KSS; cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in KSS end.
  replace (fp + -4264 + 8) with (fp + -4256) in KSS by lia.
  apply evt_done. do 16 eexists.
  eexists (upd (upd (upd nws1 (Z.to_nat (4 * p + 1)) (Z_to_bv 64 1)) (Z.to_nat (4 * p + 2)) (Z_to_bv 64 cur)) (Z.to_nat (4 * p + 3)) (Z_to_bv 64 cur)).
  eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption|].
  split; [exact KSS|]. split; [assumption|]. split; [assumption|]. split; [assumption|].
  split; [do 3 (apply keys_rep_set_val; [| apply mod4_ne; lia]); exact KR1|].
  split; [assumption|]. split; [assumption| exact SB].
Qed.

End Iter.
