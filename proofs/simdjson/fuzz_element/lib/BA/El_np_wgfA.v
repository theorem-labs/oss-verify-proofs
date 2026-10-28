(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Arr Bytes ITree Nodes Decode SysStep RegsEquiv Image ZBridge.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Export FX_lib.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import Str_tac Startup_glue Pj_steps Pj_loc_kit Pj_os_kit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import El_os_defsA El_os_xsputnA El_np_wgiA.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import I_qck. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import F_imemmove.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Import ListNotations.
Open Scope bv_scope.
Ltac show_pc := lazymatch goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac "pc =" pc end.
Ltac show_reg k :=
  lazymatch goal with |- evt _ _ (MS ?R _ ?pc _ _ _ _) =>
    let p := eval vm_compute in (bv_key (Z_to_bv 5 k)) in
    let v := eval cbv beta iota delta [tget] in (tget p R) in
    idtac "x" k "=" v
  end.
Ltac lit_words := repeat match goal with |- context [zext 64 ?x] =>
  let v := eval vm_compute in (bv_unsigned (zext 64 x)) in
  replace (zext 64 x) with (Z_to_bv 64 v) by (apply bv_eq; vm_compute; reflexivity) end.

Definition gchb (b : byte) : Prop := Z.lor (bv_unsigned b) 32 <> 120%Z.
Definition is_digb (b : byte) : bool := ((48 <=? bv_unsigned b) && (bv_unsigned b <=? 57))%Z.

Definition wgf_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo NB NP NE OB CAP POP POE : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 junk' m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 176, bv_unsigned sp); (OB, OB + CAP); (POP, POP + 8); (POE, POE + 8)]%Z m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' OB [CB (Z.to_nat CAP) junk']
    /\ rw_cells asegs m' POP [C8 (Z_to_bv 64 (OB + (NP - NB)))]
    /\ rw_cells asegs m' POE [C8 (Z_to_bv 64 (OB + (NE - NB)))]
    /\ LOCBA m'.

Definition wgf_stmt : Prop :=
  forall ra sp gp tp t0 t1 t2 s0 s1 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo NB NP NE OB CAP POP POE PLOC : Z) (src junk jp je : list byte),
  stk asegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 176)%Z -> (0x6ca000 <= lo)%Z ->
  rw_cells asegs m NB [CB (Z.to_nat (NE - NB)) src] -> Forall gchb src -> (NB < NE)%Z -> (NB <= NP <= NE)%Z -> (NE - NB <= CAP)%Z ->
  rw_cells asegs m OB [CB (Z.to_nat CAP) junk] ->
  rw_cells asegs m POP [CB 8 jp] -> rw_cells asegs m POE [CB 8 je] -> rw_cells asegs m PLOC [C8 (Z_to_bv 64 EL_IMP)] ->
  (bv_unsigned sp <= NB)%Z -> (NE < 2^62)%Z -> (bv_unsigned sp <= OB)%Z -> (OB + CAP < 2^62)%Z ->
  (bv_unsigned sp <= POP)%Z -> (POP + 8 < 2^62)%Z -> (bv_unsigned sp <= POE)%Z -> (POE + 8 < 2^62)%Z -> (bv_unsigned sp <= PLOC)%Z -> (PLOC + 8 < 2^62)%Z ->
  (NE <= OB \/ OB + CAP <= NB)%Z -> (POP + 8 <= OB \/ OB + CAP <= POP)%Z -> (POE + 8 <= OB \/ OB + CAP <= POE)%Z -> (POE + 8 <= POP \/ POP + 8 <= POE)%Z ->
  (NE <= POP \/ POP + 8 <= NB)%Z -> (NE <= POE \/ POE + 8 <= NB)%Z ->
  LOCBA m -> el_dccA m -> mem_inv asegs m ->
  evt asegs (wgf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo NB NP NE OB CAP POP POE m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 NB) (Z_to_bv 64 NP) (Z_to_bv 64 NE) (Z_to_bv 64 OB) (Z_to_bv 64 POP) (Z_to_bv 64 POE) (Z_to_bv 64 PLOC) a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 EL_WGF) fc None m (seg_rom asegs)).

Lemma isdig_val : forall b : byte,
  Z.b2z (bv_swrap 32 (bv_unsigned b + -48) mod 18446744073709551616 <? 10)%Z = (if is_digb b then 1 else 0)%Z.
Proof.
  intros b. pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. cbn in R.
  unfold is_digb, bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  set (c := bv_unsigned b) in *. clearbody c.
  change (2^Z.of_N 32)%Z with 4294967296%Z. change (4294967296 / 2)%Z with 2147483648%Z.
  rewrite (Z.mod_small (c + -48 + _)) by lia. replace (c + -48 + 2147483648 - 2147483648)%Z with (c - 48)%Z by lia.
  destruct (Z.leb_spec 48 c) as [H1|H1].
  - rewrite Z.mod_small by lia. destruct (Z.leb_spec c 57); destruct (Z.ltb_spec (c - 48) 10); cbn; lia.
  - replace ((c - 48) mod 18446744073709551616)%Z with (18446744073709551616 + (c - 48))%Z by (apply Z.mod_unique with (q := (-1)%Z); lia).
    destruct (Z.ltb_spec (18446744073709551616 + (c - 48)) 10); cbn; lia.
Qed.

Lemma isdig_val2 : forall b : byte,
  Z.b2z (Z.land (bv_swrap 32 (bv_unsigned b + -48)) 18446744073709551615 <? 10)%Z = (if is_digb b then 1 else 0)%Z.
Proof. intros b. change 18446744073709551615%Z with (Z.ones 64). rewrite Z.land_ones by lia. apply isdig_val. Qed.

Section Wgf.
Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (lo NB NP NE OB CAP POP POE PLOC : Z) (src : list byte) (m0 : word -> option byte).
Variables (l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 : list byte).
Hypothesis LO : (lo <= bv_unsigned sp - 176)%Z.
Hypothesis LOLO : (0x6ca000 <= lo)%Z.
Hypothesis GCH : Forall gchb src.
Hypothesis LEN : length src = Z.to_nat (NE - NB).
Hypothesis RNB : (NB < NE)%Z.
Hypothesis RNP : (NB <= NP <= NE)%Z.
Hypothesis RCAP : (NE - NB <= CAP)%Z.
Hypothesis R1 : (bv_unsigned sp <= NB)%Z.
Hypothesis R2 : (NE < 2^62)%Z.
Hypothesis R3 : (bv_unsigned sp <= OB)%Z.
Hypothesis R4 : (OB + CAP < 2^62)%Z.
Hypothesis R5 : (bv_unsigned sp <= POP)%Z.
Hypothesis R6 : (POP + 8 < 2^62)%Z.
Hypothesis R7 : (bv_unsigned sp <= POE)%Z.
Hypothesis R8 : (POE + 8 < 2^62)%Z.
Hypothesis D1 : (NE <= OB \/ OB + CAP <= NB)%Z.
Hypothesis D2 : (POP + 8 <= OB \/ OB + CAP <= POP)%Z.
Hypothesis D3 : (POE + 8 <= OB \/ OB + CAP <= POE)%Z.
Hypothesis D4 : (POE + 8 <= POP \/ POP + 8 <= POE)%Z.
Hypothesis D5 : (NE <= POP \/ POP + 8 <= NB)%Z.
Hypothesis D6 : (NE <= POE \/ POE + 8 <= NB)%Z.

Definition loop1_post (m : word -> option byte) (xsp x9 x18 x19 x20 x21 x22 x23 x25 x26 x27 : word) (S : Z) : machine_state -> Prop :=
  fun ms' => exists (x1 x8 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (ns : Z),
    ms' = MS (mkR x1 xsp gp tp t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 (Z_to_bv 64 ns) x25 x26 x27 t3 t4 t5 t6)
             F (Z_to_bv 64 0x11c22c) fc None m (seg_rom asegs)
    /\ (S <= ns <= NE)%Z.

Lemma wgf_loop1 : forall (k : nat) (cur : Z) (xsp x1 x8 a0 a1 a2 a3 a4 a5 a6 a7 t0 t1 t2 t3 t4 t5 t6 x18 x19 x22 x23 x26 x27 : word) (S : Z) (m : word -> option byte),
  (NE - cur <= Z.of_nat k)%Z -> (NB <= S)%Z -> (S <= cur < NE)%Z ->
  mem_inv asegs m -> bytes_at asegs m NB src -> rw_cells asegs m 0x6a66a8 (locb_cellsA l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15) ->
  evt asegs (loop1_post m xsp (Z_to_bv 64 NE) x18 x19 (Z_to_bv 64 S) (Z_to_bv 64 NE) x22 x23 (Z_to_bv 64 0x6a6870) x26 x27 S)
    (MS (mkR x1 xsp gp tp t0 t1 t2 x8 (Z_to_bv 64 NE) a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 (Z_to_bv 64 S) (Z_to_bv 64 NE) x22 x23 (Z_to_bv 64 cur) (Z_to_bv 64 0x6a6870) x26 x27 t3 t4 t5 t6)
        F (Z_to_bv 64 0x11c1b4) fc None m (seg_rom asegs)).
Proof using LEN RNB R1 R2.
  clear GCH LO LOLO RNP RCAP R3 R4 R5 R6 R7 R8 D1 D2 D3 D4 D5 D6.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  induction k as [|k IH]; intros cur xsp x1 x8 a0 a1 a2 a3 a4 a5 a6 a7 t0 t1 t2 t3 t4 t5 t6 x18 x19 x22 x23 x26 x27 S m HK HS HC MI SRC LBC; [lia|].
  unfold locb_cellsA, PJ_LOC_LO_A in LBC.
  pose proof (I_qck.ro_C1_of_bytes m (NB + (cur - NB)) _ (F_imemmove.bytes_at_nth m NB src (cur - NB) SRC ltac:(rewrite LEN; lia))) as SB.
  replace (NB + (cur - NB))%Z with cur in SB by lia.
  set (b := nth (Z.to_nat (cur - NB)) src (Z_to_bv 8 0)) in SB.
  lstep.
  cbv beta.
  do 3 lstep.
  if_false.
  do 5 lstep.
  rewrite ?isdig_val, ?isdig_val2.
  do 2 lstep.
  destruct (is_digb b).
  -
    if_false. do 2 lstep.
    destruct (Z_lt_dec (cur + 1) NE) as [MORE|LAST].
    + bru true. eapply IH; try eassumption; lia.
    + bru false. replace (cur + 1)%Z with NE by lia.
      do 2 lstep.
      unfold loop1_post. sys_finish; lia.
  -
    if_true. unfold loop1_post. sys_finish; lia.
Qed.

Definition loop2_post (m1 : word -> option byte) (xsp x9 x18 x20 x25 : word) : machine_state -> Prop :=
  fun ms' => exists (x1 x8 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (cur' : Z) (junk' : list byte) (m' : word -> option byte),
    ms' = MS (mkR x1 xsp gp tp t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 (Z_to_bv 64 POE) x20 (Z_to_bv 64 NE) (Z_to_bv 64 EL_CTYPE_F) (Z_to_bv 64 EL_NPUNCT_F)
                  (Z_to_bv 64 cur') x25 (Z_to_bv 64 OB) (Z_to_bv 64 NB) t3 t4 t5 t6)
             F (Z_to_bv 64 0x11c450) fc None m' (seg_rom asegs)
    /\ (NB <= cur' <= NE)%Z
    /\ munch [(OB, OB + CAP); (POE, POE + 8)]%Z m1 m' /\ wmono asegs m1 m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' OB [CB (Z.to_nat CAP) junk']
    /\ rw_cells asegs m' POE [C8 (Z_to_bv 64 (OB + (cur' - NB)))].

Lemma wgf_loop2 : forall (k : nat) (cur : Z) (xsp x1 x9 x18 x20 x25 a0 a1 a2 a3 a4 a5 a6 a7 t0 t1 t2 t3 t4 t5 t6 : word) (junk : list byte) (m1 m : word -> option byte),
  (NE - cur <= Z.of_nat k)%Z -> (NB <= cur < NE)%Z ->
  munch [(OB, OB + CAP); (POE, POE + 8)]%Z m1 m -> wmono asegs m1 m -> mem_inv asegs m ->
  bytes_at asegs m NB src -> rw_cells asegs m 0x6a66a8 (locb_cellsA l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15) ->
  ro_cells asegs m 0x168050 [C8 (Z_to_bv 64 0x133c98)] -> ro_cells asegs m 0x168058 [C8 (Z_to_bv 64 0x133ca0)] ->
  ro_cells asegs m 0x1681e8 [C8 (Z_to_bv 64 0x136e84); C8 (Z_to_bv 64 0x136e94); C8 (Z_to_bv 64 0x136ea4)] ->
  rw_cells asegs m OB [CB (Z.to_nat CAP) junk] -> rw_cells asegs m POE [C8 (Z_to_bv 64 (OB + (cur - NB)))] ->
  evt asegs (loop2_post m1 xsp x9 x18 x20 x25)
    (MS (mkR x1 xsp gp tp t0 t1 t2 (Z_to_bv 64 46) x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 (Z_to_bv 64 POE) x20 (Z_to_bv 64 NE) (Z_to_bv 64 EL_CTYPE_F) (Z_to_bv 64 EL_NPUNCT_F)
             (Z_to_bv 64 cur) x25 (Z_to_bv 64 OB) (Z_to_bv 64 NB) t3 t4 t5 t6)
        F (Z_to_bv 64 0x11c3f8) fc None m (seg_rom asegs)).
Proof using LEN LO LOLO RNB RCAP R1 R2 R3 R4 R7 R8 D1 D3 D6.
  clear GCH RNP R5 R6 D2 D4 D5.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  induction k as [|k IH]; intros cur xsp x1 x9 x18 x20 x25 a0 a1 a2 a3 a4 a5 a6 a7 t0 t1 t2 t3 t4 t5 t6 junk m1 m HK HC MU WM MI SRC LBC WS WS2 NPV DST HOE; [lia|].
  unfold locb_cellsA, PJ_LOC_LO_A in LBC.
  pose proof (I_qck.ro_C1_of_bytes m (NB + (cur - NB)) _ (F_imemmove.bytes_at_nth m NB src (cur - NB) SRC ltac:(rewrite LEN; lia))) as SB.
  replace (NB + (cur - NB))%Z with cur in SB by lia.
  set (b := nth (Z.to_nat (cur - NB)) src (Z_to_bv 8 0)) in SB.
  pose proof (bv_unsigned_in_range 8 b) as RB. unfold bv_modulus in RB. cbn in RB.
  destruct (rw_cells_CB_cut3 m OB (Z.to_nat CAP) junk (cur - NB) 1 ltac:(lia) ltac:(lia) ltac:(rewrite Z2Nat.id by lia; lia) DST) as (d1 & d2 & d3 & DP1 & DP2 & DP3).
  change (Z.to_nat 1) with 1%nat in DP2. clear DST.
  set (cd := (OB + (cur - NB))%Z) in *.
  lstep.
  cbv beta.
  lstep.
  destruct (Z.eq_dec (bv_unsigned b) 46) as [DOT|NDOT].
  -
    bru true.
    do 4 lstep.
    retype_at LBC 23%nat 1%nat [C1 (Z_to_bv 8 46); C1 (Z_to_bv 8 44)].
    do 2 lstep.
    do 5 lstep.
    apply rw_cells_C1_CB1 in DP2.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      destruct (rw_cells_CB_join3 mm OB (Z.to_nat (cur - NB)) 1 (Z.to_nat CAP - Z.to_nat (cur - NB) - 1) (Z.to_nat CAP) d1 _ d3 cd (cd + 1)%Z DP1 DP2 DP3
                  ltac:(lia) ltac:(lia) ltac:(lia)) as [junk2 DST] end.
    clear DP1 DP2 DP3 SB. subst cd. replace (OB + (cur - NB) + 1)%Z with (OB + (cur + 1 - NB))%Z in HOE by lia.
    unfold loop2_post. sys_finish; first [lia | exact DST | exact HOE].
  -
    bru false.
    do 4 lstep.
    do 2 lstep.
    do 4 lstep.
    lstep.
    sbZ.
    apply rw_cells_C1_CB1 in DP2.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      destruct (rw_cells_CB_join3 mm OB (Z.to_nat (cur - NB)) 1 (Z.to_nat CAP - Z.to_nat (cur - NB) - 1) (Z.to_nat CAP) d1 _ d3 cd (cd + 1)%Z DP1 DP2 DP3
                  ltac:(lia) ltac:(lia) ltac:(lia)) as [junk2 DST] end.
    clear DP1 DP2 DP3 SB. subst cd. replace (OB + (cur - NB) + 1)%Z with (OB + (cur + 1 - NB))%Z in HOE by lia.
    lstep.
    destruct (Z_lt_dec (cur + 1) NE) as [MORE|LAST].
    + bru true. eapply (IH (cur + 1)%Z); try eassumption; lia.
    + bru false. replace (cur + 1)%Z with NE in * by lia.
      lstep.
      unfold loop2_post. sys_finish; first [lia | exact DST | exact HOE].
Qed.

Definition wgf_frame (j0 j56 : list byte) : list cell :=
  [CB 16 j0; C8 (Z_to_bv 64 NP); C8 (Z_to_bv 64 POP); CB 8 (repeat (Z_to_bv 8 0) 8); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); CB 16 j56;
   C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Notation W4 := [(bv_unsigned sp - 176, bv_unsigned sp); (OB, OB + CAP); (POP, POP + 8); (POE, POE + 8)]%Z.

Lemma wgf_fin : forall (cur : Z) (x1 x8 x9 x18 x20 x23 x25 a0 a1 a2 a3 a4 a5 a6 a7 t0 t1 t2 t3 t4 t5 t6 : word) (junk j0 j56 jp : list byte) (m : word -> option byte),
  (NB <= cur <= NE)%Z ->
  munch W4 m0 m -> wmono asegs m0 m -> mem_inv asegs m -> stk asegs m lo (bv_unsigned sp + -176) ->
  bytes_at asegs m NB src -> rw_cells asegs m 0x6a66a8 (locb_cellsA l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15) ->
  ro_cells asegs m 0x168050 [C8 (Z_to_bv 64 0x133c98)] -> ro_cells asegs m 0x168058 [C8 (Z_to_bv 64 0x133ca0)] ->
  rw_cells asegs m (bv_unsigned sp + -176) (wgf_frame j0 j56) ->
  rw_cells asegs m OB [CB (Z.to_nat CAP) junk] -> rw_cells asegs m POE [C8 (Z_to_bv 64 (OB + (cur - NB)))] -> rw_cells asegs m POP [CB 8 jp] ->
  evt asegs (wgf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo NB NP NE OB CAP POP POE m0)
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -176)) gp tp t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 (Z_to_bv 64 POE) x20 (Z_to_bv 64 NE) (Z_to_bv 64 EL_CTYPE_F) x23
             (Z_to_bv 64 cur) x25 (Z_to_bv 64 OB) (Z_to_bv 64 NB) t3 t4 t5 t6)
        F (Z_to_bv 64 0x11c450) fc None m (seg_rom asegs)).
Proof using LEN LO LOLO RNB RNP RCAP R1 R2 R3 R4 R5 R6 R7 R8 D1 D2 D3 D4 D5 D6.
  clear GCH.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  intros until m. intros HC MU WM MI ST SRC LBC WS WS2 FR DST HOE HOP.
  unfold locb_cellsA, PJ_LOC_LO_A in LBC. unfold wgf_frame in FR.
  do 6 lstep.
  lstep.
  pose proof (bytes_at_sub m NB src (cur - NB) (NE - cur) SRC ltac:(lia) ltac:(lia) ltac:(rewrite LEN; lia)) as SRB.
  replace (NB + (cur - NB))%Z with cur in SRB by lia.
  destruct (rw_cells_CB_cut3 m OB (Z.to_nat CAP) junk (cur - NB) (NE - cur) ltac:(lia) ltac:(lia) ltac:(rewrite Z2Nat.id by lia; lia) DST) as (e1 & e2 & e3 & DP1 & DP2 & DP3).
  clear DST.
  replace (Z_to_bv 64 NE) with (Z_to_bv 64 (cur + (NE - cur))) by (f_equal; lia).
  call_sp (widen_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc cur (OB + (cur - NB))%Z (NE - cur)%Z (firstn (Z.to_nat (NE - cur)) (skipn (Z.to_nat (cur - NB)) src)) _);
    [lia | lia | lia | lia | lia | rewrite firstn_length_le by (rewrite length_skipn, LEN; lia); reflexivity | lia | assumption | exact SRB | exact DP2 |].
  rename POST into DP2.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    destruct (rw_cells_CB_join3 mm OB (Z.to_nat (cur - NB)) (Z.to_nat (NE - cur)) (Z.to_nat CAP - Z.to_nat (cur - NB) - Z.to_nat (NE - cur)) (Z.to_nat CAP)
                e1 _ e3 (OB + (cur - NB))%Z (OB + (cur - NB) + (NE - cur))%Z DP1 DP2 DP3 ltac:(lia) ltac:(lia) ltac:(lia)) as [junk2 DST] end.
  clear DP1 DP2 DP3.
  do 4 lstep.
  replace (OB + (cur - NB) + (cur + (NE - cur) - cur))%Z with (OB + (NE - NB))%Z in HOE by lia.
  do 2 lstep.
  replace (cur + (NE - cur))%Z with NE by lia.
  destruct (Z.eq_dec NP NE) as [PE|PNE].
  - bru true.
    do 4 lstep.
    lstep.
    lit_words. change (Z.land (bv_unsigned z64) 1) with 0%Z. if_true.
    do 15 lstep.
    release_frame FR ST (bv_unsigned sp).
    replace (OB + (cur - NB) + (NE - cur))%Z with (OB + (NP - NB))%Z in HOP by lia.
    unfold wgf_post. sys_finish; first [exact DST | do 15 eexists; exact LBC].
  - bru false.
    do 6 lstep.
    lstep.
    lit_words. change (Z.land (bv_unsigned z64) 1) with 0%Z. if_true.
    do 15 lstep.
    release_frame FR ST (bv_unsigned sp).
    unfold wgf_post. sys_finish; first [exact DST | do 15 eexists; exact LBC].
Qed.

Lemma wgf_tail : forall (nf ns : Z) (x1 x9 x18 x20 x25 a0 a1 a2 a3 a4 a5 a6 a7 t0 t1 t2 t3 t4 t5 t6 : word) (junk j0 j56 jp : list byte) (m : word -> option byte),
  (NB <= nf <= ns)%Z -> (ns <= NE)%Z ->
  munch W4 m0 m -> wmono asegs m0 m -> mem_inv asegs m -> stk asegs m lo (bv_unsigned sp + -176) ->
  bytes_at asegs m NB src -> rw_cells asegs m 0x6a66a8 (locb_cellsA l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15) ->
  ro_cells asegs m 0x168050 [C8 (Z_to_bv 64 0x133c98)] -> ro_cells asegs m 0x168058 [C8 (Z_to_bv 64 0x133ca0)] ->
  ro_cells asegs m 0x1681e8 [C8 (Z_to_bv 64 0x136e84); C8 (Z_to_bv 64 0x136e94); C8 (Z_to_bv 64 0x136ea4)] ->
  rw_cells asegs m (bv_unsigned sp + -176) (wgf_frame j0 j56) ->
  rw_cells asegs m OB [CB (Z.to_nat CAP) junk] -> rw_cells asegs m POE [C8 (Z_to_bv 64 (OB + (nf - NB)))] -> rw_cells asegs m POP [CB 8 jp] ->
  evt asegs (wgf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo NB NP NE OB CAP POP POE m0)
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -176)) gp tp t0 t1 t2 (Z_to_bv 64 nf) x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 (Z_to_bv 64 POE) x20 (Z_to_bv 64 NE)
             (Z_to_bv 64 EL_CTYPE_F) (Z_to_bv 64 EL_NPUNCT_F) (Z_to_bv 64 ns) x25 (Z_to_bv 64 OB) (Z_to_bv 64 NB) t3 t4 t5 t6)
        F (Z_to_bv 64 0x11c3c4) fc None m (seg_rom asegs)).
Proof using LEN LO LOLO RNB RNP RCAP R1 R2 R3 R4 R5 R6 R7 R8 D1 D2 D3 D4 D5 D6.
  clear GCH.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  intros until m. intros HNF HNS MU WM MI ST SRC LBC WS WS2 NPV FR DST HOE HOP.
  unfold locb_cellsA, PJ_LOC_LO_A in LBC. unfold wgf_frame in FR.
  do 6 lstep.
  lstep.
  pose proof (bytes_at_sub m NB src (nf - NB) (ns - nf) SRC ltac:(lia) ltac:(lia) ltac:(rewrite LEN; lia)) as SRB.
  replace (NB + (nf - NB))%Z with nf in SRB by lia.
  destruct (rw_cells_CB_cut3 m OB (Z.to_nat CAP) junk (nf - NB) (ns - nf) ltac:(lia) ltac:(lia) ltac:(rewrite Z2Nat.id by lia; lia) DST) as (e1 & e2 & e3 & DP1 & DP2 & DP3).
  clear DST.
  replace (Z_to_bv 64 ns) with (Z_to_bv 64 (nf + (ns - nf))) by (f_equal; lia).
  call_sp (widen_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc nf (OB + (nf - NB))%Z (ns - nf)%Z (firstn (Z.to_nat (ns - nf)) (skipn (Z.to_nat (nf - NB)) src)) _);
    [lia | lia | lia | lia | lia | rewrite firstn_length_le by (rewrite length_skipn, LEN; lia); reflexivity | lia | assumption | exact SRB | exact DP2 |].
  rename POST into DP2.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    destruct (rw_cells_CB_join3 mm OB (Z.to_nat (nf - NB)) (Z.to_nat (ns - nf)) (Z.to_nat CAP - Z.to_nat (nf - NB) - Z.to_nat (ns - nf)) (Z.to_nat CAP)
                e1 _ e3 (OB + (nf - NB))%Z (OB + (nf - NB) + (ns - nf))%Z DP1 DP2 DP3 ltac:(lia) ltac:(lia) ltac:(lia)) as [junk2 DST] end.
  clear DP1 DP2 DP3.
  do 4 lstep.
  replace (OB + (nf - NB) + (nf + (ns - nf) - nf))%Z with (OB + (ns - NB))%Z in HOE by lia.
  replace (nf + (ns - nf))%Z with ns by lia.
  lstep.
  destruct (Z.eq_dec ns NE) as [NSE|NSL].
  - bru true. subst ns.
    eapply wgf_fin; try eassumption; lia.
  - bru false.
    lstep.
    eapply evt_cut.
    { eapply (wgf_loop2 (Z.to_nat (NE - ns)) ns) with (m1 := m); try eassumption; try lia. apply munch_refl. apply wmono_refl. }
    cbv beta. intros ms_ P. unfold loop2_post in P.
    destruct P as (y1 & y8 & u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & cur2 & junk3 & m2 & -> & HC2 & MUc & WMc & MI2 & DST2 & HOE2).
    clear DST HOE.
    lazymatch type of MUc with munch _ ?mm _ => transport_after_call asegs mm m2 MUc WMc; clear MUc WMc; try clear MI end.
    eapply wgf_fin; try eassumption; lia.
Qed.

Lemma rw_cells_forget2_at : forall m A (c1 c2 : cell) (pre post : list cell),
  csize c1 = 8%nat -> csize c2 = 8%nat ->
  rw_cells asegs m A (pre ++ c1 :: c2 :: post) -> exists j, rw_cells asegs m A (pre ++ CB 16 j :: post).
Proof.
  intros m A c1 c2 pre post S1 S2 H.
  apply Startup_glue.rw_cells_app in H. destruct H as [H1 H2].
  change (c1 :: c2 :: post) with ([c1; c2] ++ post) in H2. apply Startup_glue.rw_cells_app in H2. destruct H2 as [H2 H3].
  destruct (rw_cells_forget asegs m _ _ H2) as [j Hj]. cbn [cells_size] in Hj. rewrite S1, S2 in Hj. cbn in Hj.
  exists j. apply Startup_glue.rw_cells_app. split; [exact H1|].
  change (CB 16 j :: post) with ([CB 16 j] ++ post). apply Startup_glue.rw_cells_app. split; [exact Hj|].
  cbn [cells_size csize Nat.add] in H3 |- *. rewrite S1, S2 in H3. exact H3.
Qed.

Lemma wgf_scan : forall (nf : Z) (x1 x8 x24 a0 a1 a2 a3 a4 a5 a6 a7 t0 t1 t2 t3 t4 t5 t6 : word) (junk jk jk0 jp : list byte) (m : word -> option byte),
  (NB <= nf <= NE)%Z ->
  munch W4 m0 m -> wmono asegs m0 m -> mem_inv asegs m -> stk asegs m lo (bv_unsigned sp + -176) ->
  bytes_at asegs m NB src -> rw_cells asegs m 0x6a66a8 (locb_cellsA l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15) ->
  ro_cells asegs m 0x168050 [C8 (Z_to_bv 64 0x133c98)] -> ro_cells asegs m 0x168058 [C8 (Z_to_bv 64 0x133ca0)] ->
  ro_cells asegs m 0x1681e8 [C8 (Z_to_bv 64 0x136e84); C8 (Z_to_bv 64 0x136e94); C8 (Z_to_bv 64 0x136ea4)] ->
  rw_cells asegs m (bv_unsigned sp + -176)
     [CB 16 jk; C8 (Z_to_bv 64 NP); C8 (Z_to_bv 64 POP); CB 8 (repeat (Z_to_bv 8 0) 8); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 6973808); CB 8 jk0;
      C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  rw_cells asegs m OB [CB (Z.to_nat CAP) junk] -> rw_cells asegs m POE [C8 (Z_to_bv 64 (OB + (nf - NB)))] -> rw_cells asegs m POP [CB 8 jp] ->
  evt asegs (wgf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo NB NP NE OB CAP POP POE m0)
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -176)) gp tp t0 t1 t2 x8 (Z_to_bv 64 (NE - nf)) a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 NP) (Z_to_bv 64 POE) (Z_to_bv 64 nf) (Z_to_bv 64 NE)
             (Z_to_bv 64 EL_CTYPE_F) (Z_to_bv 64 EL_NPUNCT_F) x24 (Z_to_bv 64 0x6a6870) (Z_to_bv 64 OB) (Z_to_bv 64 NB) t3 t4 t5 t6)
        F (Z_to_bv 64 0x11c188) fc None m (seg_rom asegs)).
Proof using LEN LO LOLO RNB RNP RCAP R1 R2 R3 R4 R5 R6 R7 R8 D1 D2 D3 D4 D5 D6.
  clear GCH.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  intros until m. intros HNF MU WM MI ST SRC LBC WS WS2 NPV FR DST HOE HOP.
  unfold locb_cellsA, PJ_LOC_LO_A in LBC.
  lstep.
  destruct (Z.eq_dec nf NE) as [NFE|NFL].
  -
    bru true. subst nf.
    do 4 lstep.
    lit_words. change (Z.land (bv_unsigned z64) 1) with 0%Z.
    lstep.
    if_false.
    do 2 lstep.
    lstep.
    if_false.
    lazymatch type of FR with rw_cells _ ?mm ?A (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?c7 :: ?post) =>
      destruct (rw_cells_forget2_at mm A c6 c7 [c0;c1;c2;c3;c4;c5] post eq_refl eq_refl FR) as [j56 FR2]; clear FR; cbn [app] in FR2 end.
    eapply wgf_tail; try eassumption; lia.
  - bru false.
    do 10 lstep.
    replace (nf + (NE - nf))%Z with NE by lia.
    eapply evt_cut.
    { eapply (wgf_loop1 (Z.to_nat (NE - nf)) nf); try eassumption; lia. }
    cbv beta. intros ms_ P. unfold loop1_post in P.
    destruct P as (y1 & y8 & u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & ns & -> & HNS).
    do 5 lstep.
    lit_words. change (Z.land (bv_unsigned z64) 1) with 0%Z.
    lstep.
    if_true.
    lstep.
    lstep.
    if_false.
    lazymatch type of FR with rw_cells _ ?mm ?A (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?c7 :: ?c8 :: ?post) =>
      destruct (rw_cells_forget2_at mm A c7 c8 [c0;c1;c2;c3;c4;c5;c6] post eq_refl eq_refl FR) as [j56 FR2]; clear FR; cbn [app] in FR2;
      destruct (rw_cells_forget2_at mm A c0 c1 [] (c2 :: c3 :: c4 :: c5 :: c6 :: CB 16 j56 :: post) eq_refl eq_refl FR2) as [j0 FR3]; clear FR2; cbn [app] in FR3 end.
    eapply wgf_tail; try eassumption; lia.
Qed.

Lemma wgf_mid : forall (nf : Z) (x1 x8 x24 a0 a1 a2 a3 a4 a5 a6 a7 t0 t1 t2 t3 t4 t5 t6 : word) (junk jk jk0 jp : list byte) (m : word -> option byte),
  (NB <= nf <= NB + 1)%Z -> (nf <= NE)%Z ->
  munch W4 m0 m -> wmono asegs m0 m -> mem_inv asegs m -> stk asegs m lo (bv_unsigned sp + -176) ->
  bytes_at asegs m NB src -> rw_cells asegs m 0x6a66a8 (locb_cellsA l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15) ->
  ro_cells asegs m 0x168050 [C8 (Z_to_bv 64 0x133c98)] -> ro_cells asegs m 0x168058 [C8 (Z_to_bv 64 0x133ca0)] ->
  ro_cells asegs m 0x1681e8 [C8 (Z_to_bv 64 0x136e84); C8 (Z_to_bv 64 0x136e94); C8 (Z_to_bv 64 0x136ea4)] ->
  rw_cells asegs m (bv_unsigned sp + -176)
     [CB 32 jk; C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 6973808); CB 8 jk0;
      C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  rw_cells asegs m OB [CB (Z.to_nat CAP) junk] -> rw_cells asegs m POE [C8 (Z_to_bv 64 (OB + (nf - NB)))] -> rw_cells asegs m POP [CB 8 jp] ->
  evt asegs (wgf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo NB NP NE OB CAP POP POE m0)
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -176)) gp tp t0 t1 t2 x8 (Z_to_bv 64 POP) a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 NP) (Z_to_bv 64 POE) (Z_to_bv 64 nf) (Z_to_bv 64 NE)
             (Z_to_bv 64 EL_CTYPE_F) (Z_to_bv 64 EL_NPUNCT_F) x24 (Z_to_bv 64 0x6a6870) (Z_to_bv 64 OB) (Z_to_bv 64 NB) t3 t4 t5 t6)
        F (Z_to_bv 64 0x11c084) fc None m (seg_rom asegs)).
Proof using LEN LO LOLO GCH RNB RNP RCAP R1 R2 R3 R4 R5 R6 R7 R8 D1 D2 D3 D4 D5 D6.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  intros until m. intros HNF HNE MU WM MI ST SRC LBC WS WS2 NPV FR DST HOE HOP.
  unfold locb_cellsA, PJ_LOC_LO_A in LBC.
  do 4 lstep.
  retype_at FR 3%nat 1%nat [CB 8 (repeat (Z_to_bv 8 0) 8)].
  lstep.
  rewrite lts_small by lia.
  destruct (Z.ltb_spec (NE - nf) 2) as [SHORT|LONG].
  -
    eapply wgf_scan; try eassumption; lia.
  -
    pose proof (I_qck.ro_C1_of_bytes m (NB + (nf - NB)) _ (F_imemmove.bytes_at_nth m NB src (nf - NB) SRC ltac:(rewrite LEN; lia))) as SB.
    replace (NB + (nf - NB))%Z with nf in SB by lia.
    set (b := nth (Z.to_nat (nf - NB)) src (Z_to_bv 8 0)) in SB.
    pose proof (bv_unsigned_in_range 8 b) as RB. unfold bv_modulus in RB. cbn in RB.
    do 3 lstep.
    cbv beta.
    destruct (Z.eq_dec (bv_unsigned b) 48) as [Z0|NZ0].
    + bru false.
      pose proof (I_qck.ro_C1_of_bytes m (NB + (nf + 1 - NB)) _ (F_imemmove.bytes_at_nth m NB src (nf + 1 - NB) SRC ltac:(rewrite LEN; lia))) as SB1.
      replace (NB + (nf + 1 - NB))%Z with (nf + 1)%Z in SB1 by lia.
      assert (G1 : gchb (nth (Z.to_nat (nf + 1 - NB)) src (Z_to_bv 8 0))) by (apply (Forall_nth_d GCH) || (eapply Forall_forall; [exact GCH | apply nth_In; rewrite LEN; lia])).
      set (b1 := nth (Z.to_nat (nf + 1 - NB)) src (Z_to_bv 8 0)) in SB1, G1.
      pose proof (bv_unsigned_in_range 8 b1) as RB1. unfold bv_modulus in RB1. cbn in RB1.
      pose proof G1 as NX. unfold gchb in NX.
      do 3 lstep.
      cbv beta.
      lstep.
      assert (RL : (0 <= Z.lor (bv_unsigned b1) 32 < 256)%Z).
      { split; [apply Z.lor_nonneg; lia|]. change 256%Z with (2^8)%Z. apply Z_lor_lt_pow2; lia. }
      bru true.
      eapply wgf_scan; try eassumption; lia.
    + bru true.
      eapply wgf_scan; try eassumption; lia.
Qed.

Lemma wgf_main : forall (t0 t1 t2 a7 t3 t4 t5 t6 : word) (junk jp je : list byte),
  stk asegs m0 lo (bv_unsigned sp) -> mem_inv asegs m0 ->
  rw_cells asegs m0 NB [CB (Z.to_nat (NE - NB)) src] -> rw_cells asegs m0 OB [CB (Z.to_nat CAP) junk] ->
  rw_cells asegs m0 POP [CB 8 jp] -> rw_cells asegs m0 POE [CB 8 je] -> rw_cells asegs m0 PLOC [C8 (Z_to_bv 64 EL_IMP)] ->
  (bv_unsigned sp <= PLOC)%Z -> (PLOC + 8 < 2^62)%Z ->
  rw_cells asegs m0 0x6a66a8 (locb_cellsA l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15) -> el_dccA m0 ->
  evt asegs (wgf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo NB NP NE OB CAP POP POE m0)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 NB) (Z_to_bv 64 NP) (Z_to_bv 64 NE) (Z_to_bv 64 OB) (Z_to_bv 64 POP) (Z_to_bv 64 POE) (Z_to_bv 64 PLOC) a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 EL_WGF) fc None m0 (seg_rom asegs)).
Proof using LEN LO LOLO GCH RNB RNP RCAP R1 R2 R3 R4 R5 R6 R7 R8 D1 D2 D3 D4 D5 D6.
  intros until je. intros ST MI SRC DST HOP HOE HLOC R9 R10 LBC DCC.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
  pose proof (munch_refl W4 m0) as MU. pose proof (wmono_refl asegs m0) as WM.
  destruct DCC as (_ & WS & WS2 & _ & NPV & _ & _).
  unfold locb_cellsA, PJ_LOC_LO_A in LBC.
  carve_frame 176%nat ST.
  do 22 lstep.
  do 7 lstep.
  lstep.
  if_true.
  lstep.
  replace (sx32 (Z_to_bv 64 3)) with (Z_to_bv 64 3) by (vm_compute; reflexivity).
  do 6 lstep.
  if_false.
  do 3 lstep.
  lstep.
  if_false.
  do 7 lstep.
  if_true.
  lstep.
  replace (sx32 (Z_to_bv 64 11)) with (Z_to_bv 64 11) by (vm_compute; reflexivity).
  do 6 lstep.
  if_false.
  do 3 lstep.
  lstep.
  if_false.
  do 4 lstep.
  lstep.
  retype_at LBC 25%nat 1%nat [CB 8 (repeat (Z_to_bv 8 0) 8)].
  do 2 lstep.
  lstep.
  if_false.
  retype_at LBC 25%nat 1%nat [C8 (Z_to_bv 64 0)].
  do 7 lstep.
  forget_junk FR.
  lstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (SRB : bytes_at asegs mm NB src) by (destruct SRC as [[_ B] _]; cbn [cells_bytes cbytes app] in B; rewrite app_nil_r in B; exact B) end.
  clear SRC.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (I_qck.ro_C1_of_bytes mm (NB + 0) _ (F_imemmove.bytes_at_nth mm NB src 0 SRB ltac:(rewrite LEN; lia))) as SB0 end.
  replace (NB + 0)%Z with NB in SB0 by lia. change (Z.to_nat 0) with 0%nat in SB0.
  set (b0 := nth 0 src (Z_to_bv 8 0)) in SB0.
  pose proof (bv_unsigned_in_range 8 b0) as RB0. unfold bv_modulus in RB0. cbn in RB0.
  lstep.
  cbv beta.
  do 2 lstep.
  destruct (Z.eq_dec (bv_unsigned b0) 45) as [NEG|NNEG].
  - bru true.
    do 4 lstep.
    do 2 lstep.
    do 4 lstep.
    destruct (rw_cells_CB_cut3 _ OB (Z.to_nat CAP) junk 0 1 ltac:(lia) ltac:(lia) ltac:(rewrite Z2Nat.id by lia; lia) DST) as (d1 & d2 & d3 & _ & DP2 & DP3).
    replace (OB + 0)%Z with OB in DP2, DP3 by lia. change (Z.to_nat 1) with 1%nat in DP2. clear DST.
    lstep.
    sbZ.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      destruct (rw_cells_forget asegs mm OB _ (rw_cells_glue asegs mm OB _ _ (OB + 1)%Z DP2 DP3 ltac:(cbn; lia))) as [junk1 DST] end.
    cbn [cells_size csize Nat.add app] in DST. replace (S (Z.to_nat CAP - Z.to_nat 0 - Z.to_nat 1 + 0))%nat with (Z.to_nat CAP) in DST by lia. clear DP2 DP3.
    replace (OB + 1)%Z with (OB + (NB + 1 - NB))%Z in HOE by lia.
    eapply wgf_mid; try eassumption; lia.
  - bru false.
    do 3 lstep.
    destruct (Z.eq_dec (bv_unsigned b0) 43) as [POS|NPOS].
    + bru false.
      do 4 lstep.
      do 2 lstep.
      do 4 lstep.
      destruct (rw_cells_CB_cut3 _ OB (Z.to_nat CAP) junk 0 1 ltac:(lia) ltac:(lia) ltac:(rewrite Z2Nat.id by lia; lia) DST) as (d1 & d2 & d3 & _ & DP2 & DP3).
      replace (OB + 0)%Z with OB in DP2, DP3 by lia. change (Z.to_nat 1) with 1%nat in DP2. clear DST.
      lstep.
      sbZ.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        destruct (rw_cells_forget asegs mm OB _ (rw_cells_glue asegs mm OB _ _ (OB + 1)%Z DP2 DP3 ltac:(cbn; lia))) as [junk1 DST] end.
      cbn [cells_size csize Nat.add app] in DST. replace (S (Z.to_nat CAP - Z.to_nat 0 - Z.to_nat 1 + 0))%nat with (Z.to_nat CAP) in DST by lia. clear DP2 DP3.
      replace (OB + 1)%Z with (OB + (NB + 1 - NB))%Z in HOE by lia.
      eapply wgf_mid; try eassumption; lia.
    + bru true.
      replace (Z_to_bv 64 OB) with (Z_to_bv 64 (OB + (NB - NB))) in HOE by (f_equal; lia).
      eapply wgf_mid; try eassumption; lia.
Qed.
End Wgf.

Theorem wgf_proof : wgf_stmt.
Proof.
  unfold wgf_stmt. intros until je. intros ST LO LOLO SRC GCH RNB RNP RCAP DST HOP HOE HLOC R1 R2 R3 R4 R5 R6 R7 R8 R9 R10 D1 D2 D3 D4 D5 D6 LB DCC MI.
  destruct LB as (l1 & l2 & l3 & l4 & l5 & l6 & l7 & l8 & l9 & l10 & l11 & l12 & l13 & l14 & l15 & LBC).
  assert (LEN : length src = Z.to_nat (NE - NB)) by (destruct SRC as [[[L _] _] _]; exact L).
  eapply wgf_main; eassumption.
Qed.
