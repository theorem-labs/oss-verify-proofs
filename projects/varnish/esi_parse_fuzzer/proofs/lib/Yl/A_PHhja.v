(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr RzBridge Image.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import V_Kit V_Stgw7 V_Vct V_Ma6xg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw Require Import CellsX.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Hull.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIface LayoutPA AClient ATac AIcpm9j AIcpghc AIcpya4 AIcp3q7.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpnnp.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpii0 AIcpnnp.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIface OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.LayoutPA OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AClient OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpm9j OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpghc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpya4 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcp3q7 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpnnp.AIcpnl3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpii0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpnnp.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_App A_Vsb A_World A_Img A_La0bg A_Cocsh A_Tac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_Cocsh.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_vez59.

Module A_veh4q.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import V_Ma6xg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface ATac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpm9j.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcp0e6 AIcpnnp AIcpii0.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpm9j OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpghc.AIcpxbj OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpghc.AIcp6d9 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcp0e6 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpnnp OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpii0.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require Import A_App.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_prune; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid; Stdlib.omega.PreOmega.Z.euclidean_division_equations_cleanup; xlia Stdlib.micromega.Lia.zchecker | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_prune; Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Kit.vk_lia_prune; Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker | Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker ].
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require JunkName.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.split_for_access H segs m A cs kn n ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.JunkName.split_for_access_jn H segs m A cs kn n.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.transport_chunks segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_chunks segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.footprint_after_store segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_footprint_after_store segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_mem_after_store.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_after_call segs m m' MU WM.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.addr_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_addr_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_zmlia.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.RL.sec := Ltac2.Init.true.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_mlia.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require StepFast.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.step_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.zstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_zstep.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require MliaFast DietLia2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.mlia ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.MliaFast.mlia_fast | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_mlia ].
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require ShdFast.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.shadow_dead ::=
  exfalso;
  match goal with SOK : OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.shadow_val_ok ?b ?a ?k |- _ =>
    (let BR := fresh "SBR" in pose proof (OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.byte_range b) as BR;
     let MB := fresh "SMB" in first [ pose proof (Z.mod_pos_bound a 8 (@eq_refl comparison Lt)) as MB | idtac ]);   (* [comment removed for export] *)
    let Z0 := fresh "SZ" in let R1 := fresh "SR" in let R2 := fresh "SR" in
    destruct SOK as [Z0 | [R1 R2]]; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.sb_norm b a; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ShdFast.shd_mlia0
  end.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Destzna.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_exs PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_exs PO.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_ands PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_ands PO.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require WeqG3qt TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= first [ exact eq_refl | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.WeqG3qt.weq_guard; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac ].
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Stor0fe.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stor0fe.sb_mem_after_store.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Dieta54.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dieta54.dlia.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require LiaMunch.
Local Ltac hot_lia_prev := OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dieta54.dlia.
Local Ltac lia ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaMunch.munch_tier ltac:(hot_lia_prev) | hot_lia_prev ].
(* [comment removed for export] *)

Definition vep_match_entry := 0x8ff70%Z.
Definition VM_FRAME := 64%Z.

(* [comment removed for export] *)
Definition VM_STACK : Z := (VM_FRAME + STRLEN_ICPT_STACK)%Z.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition mtab_shadows (m : word -> option byte) (es : list mentry) : Prop :=
  forall i e, nth_error es i = Some e -> me_ptr e <> 0%Z ->
    exists n, bytes_at rsegs m (sh (me_ptr e)) (shpat n)
      /\ (Z.of_nat (length (me_str e)) + 1 <= n)%Z /\ (me_ptr e mod 8 = 0)%Z
      /\ (me_ptr e + n + 16 <= kLowMemEnd)%Z
      /\ mapped m (sh (me_ptr e) - sh (me_ptr e) mod 8) 8
      /\ mapped m (sh (me_ptr e + Z.of_nat (length (me_str e))) - sh (me_ptr e + Z.of_nat (length (me_str e))) mod 8) 8.

Lemma shadow_ok_of_shpat : forall m p n a k,
  bytes_at rsegs m (sh p) (shpat n) -> (p mod 8 = 0)%Z -> (0 <= p)%Z ->
  (p <= a)%Z -> (a + k <= p + n)%Z -> (1 <= k)%Z ->
  shadow_ok m a k.
Proof.
  intros m p n a k SH AL P0 LO HI K.
  assert (N0 : (0 <= n)%Z) by lia.
  (first [ dand3 SH as S0 S1 S2 | destruct SH as (S0 & S1 & S2) ]). rewrite (shpat_length n N0) in S1.
  assert (LEN : Z.of_nat (length (shpat n)) = ((n + 7) / 8)%Z) by (apply shpat_length; lia).
  set (i0 := (a / 8 - p / 8)%Z). set (i1 := ((a + k - 1) / 8 - p / 8)%Z).
  assert (R : (0 <= i0 <= i1)%Z /\ (i1 <= (n - 1) / 8)%Z /\ ((n - 1) / 8 < (n + 7) / 8)%Z /\ ((n - 1) / 8 <= n / 8)%Z
              /\ (sh p + i0 = a / 8 + shadow_off)%Z).
  { unfold i0, i1, sh, kShadowOffset, shadow_off. Z.div_mod_to_equations. lia. }
  (first [ dand5 R as R0 R1 R1' R1'' R2 | destruct R as (R0 & R1 & R1' & R1'' & R2) ]).
  assert (CASE : (i1 < n / 8)%Z \/ (i1 = n / 8 /\ n mod 8 <> 0 /\ (a + k - 1) mod 8 < n mod 8 <= 7)%Z).
  { unfold i0, i1 in *. Z.div_mod_to_equations. lia. }
  exists (Z.to_nat (i1 - i0)), (if Z_lt_le_dec i1 (n / 8) then 0%Z else (n mod 8)%Z).
  split; [lia|]. split.
  - split; [unfold shadow_off; lia|]. split.
    { rewrite length_app, zeros_length. cbn [length]. lia. }
    intros j Hj. rewrite length_app, zeros_length in Hj. cbn [length] in Hj.
    rewrite <- R2.
    replace (sh p + i0 + Z.of_nat j)%Z with (sh p + Z.of_nat (Z.to_nat (i0 + Z.of_nat j)))%Z by lia.
    rewrite (S2 (Z.to_nat (i0 + Z.of_nat j))) by (apply Nat2Z.inj_lt; rewrite LEN; lia).
    destruct (Nat.eq_dec j (Z.to_nat (i1 - i0))) as [Ej | Nj].
    + (* [comment removed for export] *)
      rewrite nth_error_app2 by (rewrite zeros_length; lia). rewrite zeros_length.
      replace (j - Z.to_nat (i1 - i0))%nat with 0%nat by lia. cbn [nth_error].
      destruct (Z_lt_le_dec i1 (n / 8)) as [LT | GE].
      * rewrite shpat_nth_full; [reflexivity | lia | lia].
      * destruct CASE as [LT | (E1 & M & _)]; [lia|].
        replace (Z.to_nat (i0 + Z.of_nat j)) with (Z.to_nat (n / 8)) by lia.
        rewrite shpat_nth_tail; [reflexivity | lia | exact M].
    + rewrite nth_error_app1 by (rewrite zeros_length; lia). rewrite zeros_nth by lia.
      rewrite shpat_nth_full; [reflexivity | lia | lia].
  - destruct (Z_lt_le_dec i1 (n / 8)) as [LT | GE]; [left; reflexivity | right].
    destruct CASE as [LT | (E1 & M & B)]; [lia | exact B].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Notation mtab_strings := (mtab_strings rsegs).

Definition vep_match_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (T : Z) (es : list mentry) (inp : list byte) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (vm_result T es inp) a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [(bv_unsigned sp - VM_STACK, bv_unsigned sp)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ stk rsegs m' lo (bv_unsigned sp).

(* [comment removed for export] *)
Lemma strlen_icpt_cells_transport : forall (wlo whi : Z) mA mB,
  munch [(wlo, whi)] mA mB -> (0x200000 <= wlo)%Z ->
  strlen_icpt_cells mA -> strlen_icpt_cells mB.
Proof.
  (intros wlo whi mA mB MU Hw; (first [ intro dR_11; dand5 dR_11 as C1 C2 C3 C4 MC | intros (C1 & C2 & C3 & C4 & MC) ])).
  unfold asan_inited_cell in *. unfold map_cells in *.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  unfold strlen_icpt_cells, asan_inited_cell, map_cells.
  OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits;
  match goal with H : ro_cells rsegs mA ?A ?cs |- ro_cells rsegs mB ?A2 ?cs2 => constr_eq A A2;
    apply (ro_cells_transport rsegs [(wlo, whi)] mA mB A cs H MU); cbn [disjoint_from cells_size csize Nat.add]; lia end.
Qed.

Ltac icall_consts_in H ::= unfold STRLEN_ICPT_STACK in H.

Section Proof.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
            (VEP T : Z) (es : list mentry) (inp : list byte) (lo : Z)
            (NV NT P NP : Z).

  (* [comment removed for export] *)
  Hypothesis MI : mem_inv rsegs m.
  Hypothesis ST : stk rsegs m lo (bv_unsigned sp).
  Hypothesis LO : (lo + VM_STACK <= bv_unsigned sp)%Z.
  Hypothesis CEIL : (alloc_ceiling <= lo)%Z.
  Hypothesis A0 : a0 = Z_to_bv 64 VEP.
  Hypothesis MATCH : ro_cells rsegs m (VEP + 240) [C8 (Z_to_bv 64 T)].
  Hypothesis T0 : (0 < T)%Z.
  Hypothesis TAB : ro_cells rsegs m T (mtab_cells es).
  Hypothesis WF : mtab_wf es.
  Hypothesis STRS : mtab_strings m es.
  Hypothesis INP : bytes_at rsegs m (bv_unsigned a1) inp.
  Hypothesis A2 : a2 = Z_to_bv 64 (bv_unsigned a1 + Z.of_nat (length inp)).
  (* [comment removed for export] *)
  Hypothesis VEP_LO : (0 <= VEP /\ VEP + 248 <= alloc_ceiling)%Z.
  Hypothesis TAB_LO : (T + 16 * Z.of_nat (length es) <= alloc_ceiling)%Z.
  Hypothesis STR_LO : forall i e, nth_error es i = Some e -> me_ptr e <> 0%Z -> (me_ptr e + 16 <= alloc_ceiling)%Z.
  (* [comment removed for export] *)
  Hypothesis CELLS : strlen_icpt_cells m.
  Hypothesis SHV : bytes_at rsegs m (sh VEP) (shpat NV).
  Hypothesis SHV' : (VEP mod 8 = 0 /\ 248 <= NV /\ VEP + NV <= alloc_ceiling)%Z.
  Hypothesis SHT : bytes_at rsegs m (sh T) (shpat NT).
  Hypothesis SHT' : (T mod 8 = 0 /\ 16 * Z.of_nat (length es) <= NT /\ T + NT <= alloc_ceiling)%Z.
  Hypothesis SHS : mtab_shadows m es.
  Hypothesis SHI : bytes_at rsegs m (sh P) (shpat NP).
  Hypothesis SHI' : (P mod 8 = 0 /\ 0 <= P /\ P <= bv_unsigned a1 /\ bv_unsigned a1 + Z.of_nat (length inp) <= P + NP
                     /\ P + NP <= alloc_ceiling)%Z.

  Notation POST := (vep_match_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc T es inp lo m).
  Notation B := (bv_unsigned a1).
  Notation E := (bv_unsigned a1 + Z.of_nat (length inp))%Z.
  Notation SOFF := (Z_to_bv 64 2147450880).

  (* [comment removed for export] *)
  Section AfterPrologue.
    Variable m1 : word -> option byte.
    Hypothesis MU1 : munch [(bv_unsigned sp - VM_STACK, bv_unsigned sp)]%Z m m1.
    Hypothesis WM1 : wmono rsegs m m1.
    Hypothesis MI1 : mem_inv rsegs m1.
    Hypothesis ST1 : stk rsegs m1 lo (bv_unsigned sp - VM_FRAME).
    Variable junk : list byte.
    Hypothesis FR1 : rw_cells rsegs m1 (bv_unsigned sp - VM_FRAME) [CB 8 junk; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
    Hypothesis TAB1 : ro_cells rsegs m1 T (mtab_cells es).
    Hypothesis INP1 : bytes_at rsegs m1 B inp.
    Hypothesis SHT1 : bytes_at rsegs m1 (sh T) (shpat NT).
    Hypothesis SHI1 : bytes_at rsegs m1 (sh P) (shpat NP).
    Hypothesis CELLS1 : strlen_icpt_cells m1.
    Hypothesis TB : (0 <= T /\ T + 16 * Z.of_nat (length es) <= 2^64)%Z.
    Hypothesis IB : (0 <= B /\ E < 2^64)%Z.

    (* [comment removed for export] *)
    Notation AT pc xra x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x19 x28 x29 x30 x31 :=
      (MS (mkR xra (Z_to_bv 64 (bv_unsigned sp - 64)) gp tp x5 x6 x7
              (Z_to_bv 64 E) x9 x10 x11 x12 x13 x14 x15 x16 x17
              a1 x19 SOFF (Z_to_bv 64 8) s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 pc) fc None m1 (seg_rom rsegs)).

    Ltac prep :=
      unfold VM_STACK, STRLEN_ICPT_STACK, VM_FRAME in *;
      pose proof MU1 as MU; pose proof WM1 as WM; pose proof FR1 as FR; pose proof ST1 as STK;
      clear MI; pose proof MI1 as MI; pose proof alloc_ceiling_num as ACV.

    (* [comment removed for export] *)
    #[using="FR1 junk ST1 MI1 WM1 MU1 LO P VEP Clg"] Lemma epilogue : forall xra x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x28 x29 x30 x31,
      evt rsegs POST (AT 0x900b4 xra x5 x6 x7 (vm_result T es inp) x10 x11 x12 x13 x14 x15 x16 x17 x19 x28 x29 x30 x31).
    Proof.
      intros. prep.
      do 9 zstep. zstep.
      replace (bv_unsigned sp - 64 + 64)%Z with (bv_unsigned sp) by lia. rewrite (Z_to_bv_bv_unsigned sp).
      release_frame FR STK (bv_unsigned sp). finish.
    Qed.

    (* [comment removed for export] *)
    #[using="MU1 SHI' SHS STR_LO VEP_LO STRS WF T0 CEIL LO NP P lo inp T VEP m a1 sp Clg"] Lemma str1 : forall i e, nth_error es i = Some e -> me_ptr e <> 0%Z ->
      exists slack n,
        bytes_at rsegs m1 (me_ptr e) (me_str e ++ Z_to_bv 8 0 :: slack)
        /\ ((- (me_ptr e + Z.of_nat (length (me_str e)) + 1)) mod 8 <= Z.of_nat (length slack))%Z
        /\ (length (me_str e) + 1 + length slack <= 16)%nat
        /\ bytes_at rsegs m1 (sh (me_ptr e)) (shpat n)
        /\ (Z.of_nat (length (me_str e)) + 1 <= n)%Z /\ (me_ptr e mod 8 = 0)%Z /\ (me_ptr e + n + 16 <= kLowMemEnd)%Z
        /\ (0 <= sh (me_ptr e) /\ sh (me_ptr e) + Z.of_nat (length (shpat n)) <= SHMAX)%Z
        /\ mapped m1 (sh (me_ptr e) - sh (me_ptr e) mod 8) 8
        /\ mapped m1 (sh (me_ptr e + Z.of_nat (length (me_str e))) - sh (me_ptr e + Z.of_nat (length (me_str e))) mod 8) 8.
    Proof.
      intros i e Hn Hp. unfold VM_STACK, STRLEN_ICPT_STACK, VM_FRAME in *. pose proof alloc_ceiling_num as ACV.
      (first [ pose proof ((STRS i e Hn Hp)) as dR_3; dex1 dR_3 as slack; dand3 dR_3 as Hb Hpad Hlen | pose proof ((STRS i e Hn Hp)) as dR_3; dand4 dR_3 as slack Hb Hpad Hlen | destruct (STRS i e Hn Hp) as (slack & Hb & Hpad & Hlen) ]).
      (first [ pose proof ((SHS i e Hn Hp)) as dR_4; dex1 dR_4 as n; dand6 dR_4 as SHb Hn1 Hal Hlow Q1 Q2 | pose proof ((SHS i e Hn Hp)) as dR_4; dand7 dR_4 as n SHb Hn1 Hal Hlow Q1 Q2 | destruct (SHS i e Hn Hp) as (n & SHb & Hn1 & Hal & Hlow & Q1 & Q2) ]).
      pose proof (STR_LO i e Hn Hp) as HS. pose proof (wf_ptr_nonneg es i e WF Hn) as Hp0.
      unfold kLowMemEnd in Hlow.
      (first [ pose proof ((shpat_sh_boundL (Clg:=Clg) (me_ptr e) n ltac:(lia) ltac:(lia) ltac:(lia))) as dR_5; dand3 dR_5 as B0 B1 B2 | pose proof (shpat_sh_boundL (Clg:=Clg) (me_ptr e) n ltac:(lia) ltac:(lia) ltac:(lia)) as (B0 & B1 & B2) ]).
      pose proof (sh_word_bound (Clg:=Clg) (me_ptr e) ltac:(lia) ltac:(lia)) as W1.
      pose proof (sh_word_bound (Clg:=Clg) (me_ptr e + Z.of_nat (length (me_str e))) ltac:(lia) ltac:(lia)) as W2.
      exists slack, n. split; [|split; [exact Hpad|split; [exact Hlen|split; [|split; [lia|split; [lia|split; [unfold kLowMemEnd; lia|split; [lia|split]]]]]]]].
      - eapply bytes_at_transport; [exact Hb | exact MU1 |].
        cbn [disjoint_from]. split; [|exact I]. rewrite app_length. cbn [length]. lia.
      - eapply bytes_at_transport; [exact SHb | exact MU1 |]. cbn [disjoint_from]. split; [lia|exact I].
      - eapply mapped_munch; [exact MU1 | lia | lia | | exact Q1]. intros j Hj. cbn [outside]. split; [lia|exact I].
      - eapply mapped_munch; [exact MU1 | lia | lia | | exact Q2]. intros j Hj. cbn [outside]. split; [lia|exact I].
    Qed.

    Ltac klia K := first [rewrite Z.mod_small in K by lia | idtac]; lia.

    (* [comment removed for export] *)
    (* [comment removed for export] *)
    #[using="FR1 junk ST1 MI1 WM1 MU1 LO P VEP Clg"] Lemma ret_vm : forall i xra x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x28 x29 x30 x31,
      vm_find es inp = Some i ->
      evt rsegs POST (AT 0x900b4 xra x5 x6 x7 (Z_to_bv 64 (T + 16 * Z.of_nat i)) x10 x11 x12 x13 x14 x15 x16 x17 x19 x28 x29 x30 x31).
    Proof.
      intros.
      replace (Z_to_bv 64 (T + 16 * Z.of_nat i)) with (vm_result T es inp) by (unfold vm_result; rewrite H; reflexivity).
      apply epilogue.
    Qed.

    (* [comment removed for export] *)
    #[using="FR1 junk ST1 MI1 WM1 MU1 LO P VEP Clg"] Lemma ret_null : forall xra x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x19 x28 x29 x30 x31,
      vm_find es inp = None ->
      evt rsegs POST (AT 0x900b0 xra x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x19 x28 x29 x30 x31).
    Proof.
      intros. prep.
      zstep.
      replace (Z_to_bv 64 0) with (vm_result T es inp) by (unfold vm_result; rewrite H; reflexivity).
      apply epilogue.
    Qed.

    (* [comment removed for export] *)
    Definition OUTER (i : nat) : Prop :=
      forall (e : mentry) xra x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31,
      nth_error es i = Some e -> me_ptr e <> 0%Z -> searched inp es i ->
      evt rsegs POST (AT 0x8ffdc xra x5 x6 x7 (Z_to_bv 64 (T + 16 * Z.of_nat i)) x10 x11 x12 x13 x14 x15 x16 x17
                         (Z_to_bv 64 (me_ptr e)) x28 x29 x30 x31).

    (* [comment removed for export] *)
    #[using="TB SHT1 TAB1 FR1 junk ST1 MI1 WM1 MU1 SHI' SHT' TAB_LO VEP_LO WF T0 LO NP P NT VEP Clg"] Lemma next_entry : forall i e xra x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x28 x29 x30 x31,
      nth_error es i = Some e -> me_ptr e <> 0%Z -> searched inp es i ->
      is_prefixb (me_str e) inp = false -> runs_outb (me_str e) inp = false ->
      OUTER (S i) ->
      evt rsegs POST (AT 0x90080 xra x5 x6 x7 (Z_to_bv 64 (T + 16 * Z.of_nat i)) x10 x11 x12 x13 x14 x15 x16 x17 x19 x28 x29 x30 x31).
    Proof.
      intros i e xra x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x28 x29 x30 x31 Hn Hp Hs H1 H2 IH.
      prep. pose proof TB as TB'. pose proof SHT' as (TAL & TNT & TCE).
      (first [ pose proof ((wf_entry es i e WF Hn Hp)) as dR_6; dand3 dR_6 as _ _ Hlen | destruct (wf_entry es i e WF Hn Hp) as (_ & _ & Hlen) ]).
      destruct (nth_error es (S i)) as [e2|] eqn:He2. 2:{ apply nth_error_None in He2. lia. }
      pose proof (wf_ptr_nonneg es (S i) e2 WF He2) as Hp2.
      pose proof (nth_error_lt _ _ _ He2) as Hi2.
      pose proof (mtab_read_ptr rsegs m1 T es (S i) e2 _ TAB1 He2 eq_refl) as RD2.
      pose proof (searched_next inp es i e Hs Hn Hp H1 H2) as Hs2.
      (* [comment removed for export] *)
      zstep.
      shadow_chk0 SHT1 8%Z.
      (* [comment removed for export] *)
      replace (T + 16 * Z.of_nat i + 16)%Z with (T + 16 * Z.of_nat (S i))%Z by lia.
      zstep.
      (* [comment removed for export] *)
      zstep. if_cases K; zify_cond K.
      - (* [comment removed for export] *)
        apply (IH e2); auto; klia K.
      - (* [comment removed for export] *)
        zstep.
        replace (Z_to_bv 64 (T + 16 * Z.of_nat (S i))) with (vm_result T es inp).
        2:{ unfold vm_result. rewrite (vm_sentinel inp es (S i) e2 Hs2 He2) by klia K. reflexivity. }
        apply epilogue.
    Qed.

    (* [comment removed for export] *)
    #[using="IB TB SHI1 SHT1 INP1 TAB1 FR1 junk ST1 MI1 WM1 MU1 SHI' SHT' TAB_LO VEP_LO WF T0 LO NP P NT VEP Clg"] Lemma inner : forall (k : nat) (i j : nat) (e : mentry) (c : byte) (slack : list byte) (n : Z)
                         xra x5 x6 x7 x11 x12 x14 x15 x16 x17 x28 x29 x30 x31,
      (k = length inp - j)%nat ->
      nth_error es i = Some e -> me_ptr e <> 0%Z -> searched inp es i -> OUTER (S i) ->
      bytes_at rsegs m1 (me_ptr e) (me_str e ++ Z_to_bv 8 0 :: slack) ->
      bytes_at rsegs m1 (sh (me_ptr e)) (shpat n) ->
      (Z.of_nat (length (me_str e)) + 1 <= n)%Z -> (me_ptr e mod 8 = 0)%Z ->
      nth_error (me_str e) j = Some c -> (j < length inp)%nat ->
      agree_upto inp (me_str e) j ->
      x11 = Z_to_bv 64 (B + Z.of_nat j) -> x12 = Z_to_bv 64 (B + Z.of_nat j) ->
      evt rsegs POST (AT 0x90014 xra x5 x6 x7 (Z_to_bv 64 (T + 16 * Z.of_nat i))
                         (Z_to_bv 64 (me_ptr e + Z.of_nat j + 1)) x11 x12 (Z_to_bv 64 (bv_unsigned c)) x14 x15 x16 x17
                         (Z_to_bv 64 (me_ptr e + Z.of_nat j + 1)) x28 x29 x30 x31).
    Proof.
      induction k as [|k IH]; intros i j e c slack n xra x5 x6 x7 x11 x12 x14 x15 x16 x17 x28 x29 x30 x31
        Hk Hn Hp Hs HO SB SSH Hn1 Hal Hc Hj Hag -> ->.
      { exfalso. lia. }
      prep. pose proof SHI' as (PAL & P0 & PB & PE & PCE).
      pose proof (nth_error_lt _ _ _ Hc) as Hjs.
      pose proof (bv_unsigned_in_range _ c) as Hcr. pose proof TB as TB'. pose proof IB as IB'.
      (first [ pose proof ((wf_entry es i e WF Hn Hp)) as dR_7; dand3 dR_7 as Hslen Hnonul Hlen | destruct (wf_entry es i e WF Hn Hp) as (Hslen & Hnonul & Hlen) ]).
      pose proof (wf_ptr_nonneg es i e WF Hn) as Hpr.
      assert (Hc0 : bv_unsigned c <> 0%Z).
      { intros Z0. apply Hnonul. replace (Z_to_bv 8 0) with c by (apply bv_eq; rewrite Z0; reflexivity). eapply nth_error_In; eauto. }
      destruct (nth_error inp j) as [d|] eqn:Hd. 2:{ apply nth_error_None in Hd. lia. }
      pose proof (bv_unsigned_in_range _ d) as Hdr.
      pose proof (u8ro_read rsegs m1 B inp (Z.of_nat j) d _ INP1 ltac:(rewrite Nat2Z.id; exact Hd) ltac:(lia) eq_refl) as RD.
      pose proof (bytes_at_bound _ _ _ _ SB) as SBB. rewrite app_length in SBB. cbn [length] in SBB.
      (* [comment removed for export] *)
      shadow_chk SHI1 1%Z 15%Z.
      (* [comment removed for export] *)
      zstep. cbv beta.
      (* [comment removed for export] *)
      zstep. if_cases K; zify_cond K.
      - (* [comment removed for export] *)
        assert (Hcd : c <> d) by (intros ->; apply K; reflexivity).
        destruct (mismatch_at inp (me_str e) j c d Hag Hc Hd Hcd) as [M1 M2].
        zstep. if_cases K2; zify_cond K2. { exfalso. klia K2. }
        eapply next_entry; eauto.
      - (* [comment removed for export] *)
        assert (Ecd : c = d) by (apply bv_eq; klia K).
        subst d.
        pose proof (agree_step inp (me_str e) j c Hag Hc Hd) as Hag'.
        shadow_chk SSH 1%Z 14%Z.
        destruct (Nat.eq_dec (S j) (length (me_str e))) as [Hend|Hmore].
        + (* [comment removed for export] *)
          pose proof (u8ro_read rsegs m1 (me_ptr e) (me_str e ++ Z_to_bv 8 0 :: slack) (Z.of_nat (S j)) (Z_to_bv 8 0) _ SB
                        ltac:(rewrite Nat2Z.id, nth_error_app2, Hend, Nat.sub_diag by lia; reflexivity) ltac:(lia) eq_refl) as RD2.
          zstep. cbv beta. zstep. zstep. if_cases K2; zify_cond K2. 2:{ exfalso. apply K2. reflexivity. }
          (* [comment removed for export] *)
          zstep. if_cases K3; zify_cond K3. 2:{ exfalso. apply K3. reflexivity. }
          apply ret_vm. eapply (vm_found inp es); eauto. eapply prefix_at_end; eauto.
        + (* [comment removed for export] *)
          destruct (nth_error (me_str e) (S j)) as [c2|] eqn:Hc2. 2:{ apply nth_error_None in Hc2. lia. }
          pose proof (bv_unsigned_in_range _ c2) as Hc2r.
          assert (Hc20 : bv_unsigned c2 <> 0%Z).
          { intros Z0. apply Hnonul. replace (Z_to_bv 8 0) with c2 by (apply bv_eq; rewrite Z0; reflexivity). eapply nth_error_In; eauto. }
          pose proof (u8ro_read rsegs m1 (me_ptr e) (me_str e ++ Z_to_bv 8 0 :: slack) (Z.of_nat (S j)) c2 _ SB
                        ltac:(rewrite Nat2Z.id, nth_error_app1 by lia; exact Hc2) ltac:(lia) eq_refl) as RD2.
          zstep. cbv beta. zstep. zstep. if_cases K2; zify_cond K2. { exfalso. klia K2. }
          (* [comment removed for export] *)
          zstep. zstep. zstep. zstep. if_cases K3; zify_cond K3.
          * (* [comment removed for export] *)
            replace (B + Z.of_nat j + 1)%Z with (B + Z.of_nat (S j))%Z by lia.
            replace (me_ptr e + Z.of_nat j + 2)%Z with (me_ptr e + Z.of_nat (S j) + 1)%Z by lia.
            apply (IH i (S j) e c2 slack n xra); auto; try lia; try klia K3.
          * (* [comment removed for export] *)
            assert (Hje : (S j = length inp)%nat) by klia K3.
            destruct (runs_out_at inp (me_str e) (S j) Hag' ltac:(lia) Hje) as [M1 M2].
            zstep. zstep. if_cases K4; zify_cond K4. { exfalso. klia K4. }
            zstep. if_cases K5; zify_cond K5. 2:{ exfalso. klia K5. }
            apply ret_null. eapply (vm_ranout inp es); eauto.
    Qed.
  End AfterPrologue.

  Ltac klia' K := first [rewrite Z.mod_small in K by lia | idtac]; lia.

  (* [comment removed for export] *)
  #[using="SHI' SHS SHT' CELLS STR_LO TAB_LO VEP_LO A2 INP STRS WF T0 CEIL LO VEP a2 Clg"] Lemma outer : forall k i (m1 : word -> option byte) (junk : list byte),
    munch [(bv_unsigned sp - VM_STACK, bv_unsigned sp)]%Z m m1 ->
    wmono rsegs m m1 -> mem_inv rsegs m1 ->
    stk rsegs m1 lo (bv_unsigned sp - VM_FRAME) ->
    rw_cells rsegs m1 (bv_unsigned sp - VM_FRAME) [CB 8 junk; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    ro_cells rsegs m1 T (mtab_cells es) ->
    bytes_at rsegs m1 B inp ->
    bytes_at rsegs m1 (sh T) (shpat NT) ->
    bytes_at rsegs m1 (sh P) (shpat NP) ->
    strlen_icpt_cells m1 ->
    (0 <= T /\ T + 16 * Z.of_nat (length es) <= 2^64)%Z ->
    (0 <= B /\ E < 2^64)%Z ->
    (k = length es - i)%nat -> OUTER m1 i.
  Proof.
    induction k as [|k IH]; intros i m1 junk MU WM MI1 STK FR TAB1 INP1 SHT1 SHI1 CELLS1 TB IB Hk
      e xra x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 Hn Hp Hs.
    { exfalso. pose proof (nth_error_lt _ _ _ Hn). lia. }
    unfold VM_STACK, STRLEN_ICPT_STACK, VM_FRAME in *. clear MI. pose proof MI1 as MI. clear MI1.
    pose proof alloc_ceiling_num as ACV.
    pose proof TB as TB'. pose proof IB as IB'. pose proof SHT' as (TAL & TNT & TCE). pose proof SHI' as (PAL & P0 & PB & PE & PCE).
    pose proof (mtab_cells_size es) as TSZ.
    pose proof (shpat_sh_boundL (Clg:=Clg) T NT ltac:(lia) ltac:(lia) ltac:(lia)) as SHTB.
    pose proof (shpat_sh_boundL (Clg:=Clg) P NP ltac:(lia) ltac:(lia) ltac:(lia)) as SHIB.
    (first [ pose proof ((wf_entry es i e WF Hn Hp)) as dR_8; dand3 dR_8 as Hslen Hnonul Hlen | destruct (wf_entry es i e WF Hn Hp) as (Hslen & Hnonul & Hlen) ]).
    pose proof (wf_ptr_nonneg es i e WF Hn) as Hpr. pose proof (STR_LO i e Hn Hp) as HSL.
    (first [ pose proof ((str1 m1 MU i e Hn Hp)) as dR_9; dex2 dR_9 as slack n; dand10 dR_9 as SB PAD SLK SSH Hn1 Hal Hlow SHB Q1 Q2 | pose proof ((str1 m1 MU i e Hn Hp)) as dR_9; dand12 dR_9 as slack n SB PAD SLK SSH Hn1 Hal Hlow SHB Q1 Q2 | destruct (str1 m1 MU i e Hn Hp) as (slack & n & SB & PAD & SLK & SSH & Hn1 & Hal & Hlow & SHB & Q1 & Q2) ]).
    pose proof (bytes_at_bound _ _ _ _ SB) as SBB. rewrite app_length in SBB. cbn [length] in SBB.
    pose proof (zr_word sp) as SPR; unfold inr64 in SPR. assert (LO0 : (0 <= lo)%Z) by (destruct STK as [? _]; assumption).
    (* [comment removed for export] *)
    zstep. zstep.
    icall (strlen_icpt_spec) by
      (rewrite ?unsigned_lit by lia;
       first [ exact SB | exact Hnonul | exact PAD | exact MI | exact CELLS1 | exact STK | exact CEIL
             | exact Q1 | exact Q2
             | apply (shadow_ok_of_shpat m1 (me_ptr e) n); [exact SSH | lia | lia | lia | lia | lia]
             | unfold inmem_range, kLowMemEnd in *; lia
             | rewrite ?app_length; cbn [length]; unfold STRLEN_ICPT_STACK; lia ]).
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      assert (CELLSx : strlen_icpt_cells mx) by (eapply strlen_icpt_cells_transport; [exact MU | lia | exact CELLS]);
      assert (HO : OUTER mx (S i)) by (apply (IH (S i) mx junk); try assumption; lia) end.
    (* [comment removed for export] *)
    zstep. if_cases K; zify_cond K. { exfalso. klia' K. }
    (* [comment removed for export] *)
    shadow_chk SSH 1%Z 11%Z.
    (* [comment removed for export] *)
    destruct (me_str e) as [|c str'] eqn:Estr. { cbn in Hslen. lia. }
    assert (Hc0 : nth_error (me_str e) 0 = Some c) by (rewrite Estr; reflexivity).
    rewrite <- Estr in *.
    pose proof (bv_unsigned_in_range _ c) as Hcr.
    assert (Hcnz : bv_unsigned c <> 0%Z).
    { intros Z0. apply Hnonul. replace (Z_to_bv 8 0) with c by (apply bv_eq; rewrite Z0; reflexivity). eapply nth_error_In; eauto. }
    lazymatch goal with SBx : bytes_at rsegs ?mx (me_ptr e) _ |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      pose proof (u8ro_read rsegs mx (me_ptr e) (me_str e ++ Z_to_bv 8 0 :: slack) 0 c _ SBx
                    ltac:(cbn [Z.to_nat]; rewrite nth_error_app1 by lia; exact Hc0) ltac:(lia) ltac:(rewrite Z.add_0_r; reflexivity)) as RD0 end.
    zstep. cbv beta.
    (* [comment removed for export] *)
    zstep. if_cases K2; zify_cond K2. { exfalso. klia' K2. }
    (* [comment removed for export] *)
    zstep. if_cases K3; zify_cond K3.
    - (* [comment removed for export] *)
      assert (Hinp : inp = []) by (destruct inp; [reflexivity| cbn [length] in K3; exfalso; klia' K3]).
      destruct (runs_out_at inp (me_str e) 0 (agree_upto_0 inp (me_str e)) ltac:(lia) ltac:(rewrite Hinp; reflexivity)) as [M1 M2].
      zstep. zstep. if_cases K4; zify_cond K4. { exfalso. klia' K4. }
      zstep. if_cases K5; zify_cond K5. 2:{ exfalso. rewrite Hinp in K5. cbn [length] in K5. klia' K5. }
      unshelve (eapply ret_null; eauto); try assumption. eapply (vm_ranout inp es); eauto.
    - (* [comment removed for export] *)
      zstep. zstep. zstep. zstep.
      replace (me_ptr e + 1)%Z with (me_ptr e + Z.of_nat 0 + 1)%Z by lia.
      lazymatch goal with SBx : bytes_at rsegs ?mx (me_ptr e) _, SSHx : bytes_at rsegs ?mx (sh (me_ptr e)) _ |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
        unshelve (eapply (inner mx) with (k := (length inp - 0)%nat) (j := 0%nat) (c := c) (slack := slack) (n := n); eauto; try lia);
          try assumption end.
      + apply agree_upto_0.
      + rewrite Z.add_0_r. symmetry. apply Z_to_bv_bv_unsigned.
      + rewrite Z.add_0_r. symmetry. apply Z_to_bv_bv_unsigned.
  Qed.
End Proof.


(* [comment removed for export] *)
Section CEIL.
Context {Clg : Ceiling}.  (* [comment removed for export] *)

Theorem vep_match_spec :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (VEP T : Z) (es : list mentry) (inp : list byte) (lo : Z) (NV NT P NP : Z),
  mem_inv rsegs m ->
  stk rsegs m lo (bv_unsigned sp) -> (lo + VM_STACK <= bv_unsigned sp)%Z -> (alloc_ceiling <= lo)%Z ->
  a0 = Z_to_bv 64 VEP ->
  ro_cells rsegs m (VEP + 240) [C8 (Z_to_bv 64 T)] -> (0 < T)%Z ->
  ro_cells rsegs m T (mtab_cells es) -> mtab_wf es -> mtab_strings m es ->
  bytes_at rsegs m (bv_unsigned a1) inp ->
  a2 = Z_to_bv 64 (bv_unsigned a1 + Z.of_nat (length inp)) ->
  (0 <= VEP /\ VEP + 248 <= alloc_ceiling)%Z ->
  (T + 16 * Z.of_nat (length es) <= alloc_ceiling)%Z ->
  (forall i e, nth_error es i = Some e -> me_ptr e <> 0%Z -> (me_ptr e + 16 <= alloc_ceiling)%Z) ->
  strlen_icpt_cells m ->
  bytes_at rsegs m (sh VEP) (shpat NV) -> (VEP mod 8 = 0 /\ 248 <= NV /\ VEP + NV <= alloc_ceiling)%Z ->
  bytes_at rsegs m (sh T) (shpat NT) -> (T mod 8 = 0 /\ 16 * Z.of_nat (length es) <= NT /\ T + NT <= alloc_ceiling)%Z ->
  mtab_shadows m es ->
  bytes_at rsegs m (sh P) (shpat NP) ->
  (P mod 8 = 0 /\ 0 <= P /\ P <= bv_unsigned a1 /\ bv_unsigned a1 + Z.of_nat (length inp) <= P + NP /\ P + NP <= alloc_ceiling)%Z ->
  evt rsegs (vep_match_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc T es inp lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 vep_match_entry) fc None m (seg_rom rsegs)).
Proof.
  intros until NP. intros MI ST LO CEIL A0 MATCH T0 TAB WF STRS INP A2 VEP_LO TAB_LO STR_LO CELLS SHV SHV' SHT SHT' SHS SHI SHI'.
  rewrite A0, A2.
  pose proof (munch_refl [(bv_unsigned sp - VM_STACK, bv_unsigned sp)]%Z m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (bytes_at_bound _ _ _ _ INP) as IB.
  pose proof (bytes_at_bound _ _ _ _ (proj2 TAB)) as TB. rewrite cells_bytes_length in TB by exact (proj1 TAB).
  pose proof (mtab_cells_size es) as TSZ.
  destruct es as [|e0 es'] eqn:Ees. { cbn in WF. contradiction. }
  rewrite <- Ees in *.
  assert (LEN : length es = S (length es')) by (rewrite Ees; reflexivity).
  assert (He0 : nth_error es 0 = Some e0) by (rewrite Ees; reflexivity).
  pose proof (wf_ptr_nonneg es 0 e0 WF He0) as Hp0.
  (* [comment removed for export] *)
  pose proof (conj INP I) as INP0. pose proof (conj TAB I) as TAB0. pose proof (conj ST I) as ST0.
  pose proof (conj SHT I) as SHT0. pose proof (conj SHI I) as SHI0.
  unfold VM_STACK, STRLEN_ICPT_STACK, VM_FRAME in *. unfold vep_match_entry.
  pose proof alloc_ceiling_num as ACV.
  pose proof SHV' as (VAL & VNV & VCE). pose proof SHT' as (TAL & TNT & TCE). pose proof SHI' as (PAL & P0 & PB & PE & PCE).
  pose proof (shpat_sh_boundL (Clg:=Clg) VEP NV ltac:(lia) ltac:(lia) ltac:(lia)) as SHVB.
  pose proof (shpat_sh_boundL (Clg:=Clg) T NT ltac:(lia) ltac:(lia) ltac:(lia)) as SHTB.
  pose proof (shpat_sh_boundL (Clg:=Clg) P NP ltac:(lia) ltac:(lia) ltac:(lia)) as SHIB.
  pose proof (zr_word sp) as SPR; unfold inr64 in SPR. assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
  carve_frame 64%nat ST.
  do 8 zstep.
  (* [comment removed for export] *)
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
    assert (CELLS0 : strlen_icpt_cells mx) by (eapply strlen_icpt_cells_transport; [exact MU | lia | exact CELLS]) end.
  pose proof CELLS0 as CC. (first [ dand5 CC as _ _ _ _ MC | destruct CC as (_ & _ & _ & _ & MC) ]). open_map_cells MC.
  (* [comment removed for export] *)
  zstep. zstep. zstep. zstep.
  (* [comment removed for export] *)
  zstep. shadow_chk0 SHV 8%Z.
  (* [comment removed for export] *)
  zstep. zstep. if_cases K; zify_cond K. { exfalso. first [rewrite Z.mod_small in K by lia | idtac]; lia. }
  clear K.
  (* [comment removed for export] *)
  shadow_chk0 SHT 8%Z.
  (* [comment removed for export] *)
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
    pose proof (mtab_read_ptr rsegs mx T es 0 e0 _ TAB He0 eq_refl) as RD0 end.
  replace (T + 16 * Z.of_nat 0)%Z with T in RD0 by lia.
  zstep.
  (* [comment removed for export] *)
  zstep. if_cases K; zify_cond K.
  - (* [comment removed for export] *)
    assert (Hvm : vm_find es inp = Some 0%nat).
    { apply (vm_sentinel inp es 0 e0); [unfold searched; intros i' e' Hi'; lia | exact He0 | first [rewrite Z.mod_small in K by lia | idtac]; lia]. }
    do 10 zstep.
    replace (Z_to_bv 64 T) with (vm_result T es inp) by (unfold vm_result; rewrite Hvm; f_equal; lia).
    release_frame FR ST (bv_unsigned sp). finish.
  - (* [comment removed for export] *)
    zstep. zstep.
    replace (Z_to_bv 64 T) with (Z_to_bv 64 (T + 16 * Z.of_nat 0)) by (f_equal; lia).
    replace (bv_unsigned sp + -64)%Z with (bv_unsigned sp - 64)%Z in * by lia.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      unshelve (eapply (outer) with (k := (length es - 0)%nat) (i := 0%nat) (m1 := mx);
        eauto); try assumption; try lia end;
      try exact (proj1 INP0); try exact (proj1 TAB0); try exact (proj1 ST0); try exact (proj1 SHT0); try exact (proj1 SHI0).
    all: unfold searched; intros i' e' Hi'; lia.
Qed.

End CEIL.
End A_veh4q.

From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_PDefs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_PKit2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_PKit2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_PKit2.

Module A_PMmab.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import V_Stgw7 V_Ma6xg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface LayoutPA AClient ATac AIcpm9j.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_App A_World A_Img A_La0bg.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_App OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_World OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Img OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_La0bg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_PHhja.A_veh4q.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require Import A_AI16.   (* [comment removed for export] *)
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_prune; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid; Stdlib.omega.PreOmega.Z.euclidean_division_equations_cleanup; xlia Stdlib.micromega.Lia.zchecker | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_prune; Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Kit.vk_lia_prune; Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker | Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker ].
Open Scope Z_scope.

(* [comment removed for export] *)
Definition tgt_ok (es : list mentry) (ts : list vstate) : Prop :=
  forall i e, nth_error es i = Some e ->
    exists S', nth_error ts i = Some S' /\ me_svar e = stvarA S' /\ stvarA S' <> 0 /\ me_sval e = stA S'.

Definition tgts_bom : list vstate := [S_Start; S_BOM].
Definition tgts_attr_include : list vstate := [S_AttrGetValue; S_AttrGetValue; S_SkipAttribute].
Definition tgts_esi : list vstate := [S_ESI_Include; S_ESI_Remove; S_ESI_Comment; S_ESI_Bogon].
Definition tgts_starttag : list vstate := [S_CommentESI; S_NxtTag; S_Comment; S_end_ESITag; S_ESITag; S_CDATA; S_NotMyTag].

Ltac tgt_ok_tac :=
  intros [|[|[|[|[|[|[|[|i]]]]]]]] e H; cbn in H; try discriminate; injection H as <-;
  eexists; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; first [reflexivity | cbv; discriminate].

Lemma tgt_bom : tgt_ok tbl_bom tgts_bom. Proof. tgt_ok_tac. Qed.
Lemma tgt_attr_include : tgt_ok tbl_attr_include tgts_attr_include. Proof. tgt_ok_tac. Qed.
Lemma tgt_esi : tgt_ok tbl_esi tgts_esi. Proof. tgt_ok_tac. Qed.
Lemma tgt_starttag : tgt_ok tbl_starttag tgts_starttag. Proof. tgt_ok_tac. Qed.

(* [comment removed for export] *)
Definition tab4 (Tb : Z) (es : list mentry) (ts : list vstate) (NT : Z) : Prop :=
     (Tb = TBL_bom /\ es = tbl_bom /\ ts = tgts_bom /\ NT = 32)
  \/ (Tb = TBL_attr_include /\ es = tbl_attr_include /\ ts = tgts_attr_include /\ NT = 48)
  \/ (Tb = TBL_esi /\ es = tbl_esi /\ ts = tgts_esi /\ NT = 64)
  \/ (Tb = TBL_starttag /\ es = tbl_starttag /\ ts = tgts_starttag /\ NT = 112).

Lemma tab4_geom : forall Tb es ts NT, tab4 Tb es ts NT ->
  Tb mod 8 = 0 /\ 16 * Z.of_nat (length es) = NT /\ 0xad760 <= Tb /\ Tb + NT <= 0xad900 /\ tgt_ok es ts /\ mtab_wf es
  /\ (forall i e, nth_error es i = Some e -> me_ptr e <> 0 -> 0x23b60 <= me_ptr e /\ me_ptr e + 16 <= 0x23d40).
Proof.
  intros Tb es ts NT [(-> & -> & -> & ->)|[(-> & -> & -> & ->)|[(-> & -> & -> & ->)|(-> & -> & -> & ->)]]];
    unfold TBL_bom, TBL_attr_include, TBL_esi, TBL_starttag; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ];
    (split; [reflexivity|]); (split; [reflexivity|]); (split; [lia|]); (split; [lia|]);
    (split; [first [exact tgt_bom | exact tgt_attr_include | exact tgt_esi | exact tgt_starttag]|]);
    (split; [first [exact tbl_bom_wf | exact tbl_attr_include_wf | exact tbl_esi_wf | exact tbl_starttag_wf]|]);
    (intros [|[|[|[|[|[|[|[|i]]]]]]]] e H; cbn in H; try discriminate; injection H as <-; cbn; intros; lia).
Qed.

Lemma tab4_strings : forall m Tb es ts NT, mem_inv rsegs m -> tab4 Tb es ts NT -> mtab_strings m es.
Proof.
  intros m Tb es ts NT MI [(_ & -> & _)|[(_ & -> & _)|[(_ & -> & _)|(_ & -> & _)]]];
    [apply tbl_bom_strings| apply tbl_attr_include_strings| apply tbl_esi_strings| apply tbl_starttag_strings]; exact MI.
Qed.

Lemma tab4_cells : forall v Tb es ts NT, img_tabs v -> tab4 Tb es ts NT -> ro_cells rsegs v Tb (mtab_cells es).
Proof.
  (intros v Tb es ts NT; (first [ intro dR_2; dand5 dR_2 as T1 T2 T3 T4 _ | intros (T1 & T2 & T3 & T4 & _) ]); intros [(-> & -> & _)|[(-> & -> & _)|[(-> & -> & _)|(-> & -> & _)]]]); assumption.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section CEIL.
Context {Clg : Ceiling}.  (* [comment removed for export] *)

Lemma tab4_shadow : forall v Tb es ts NT, consts_hold LPA v -> tab4 Tb es ts NT -> bytes_at rsegs v (sh Tb) (shpat NT).
Proof.
  intros v Tb es ts NT CH [(-> & _ & _ & ->)|[(-> & _ & _ & ->)|[(-> & _ & _ & ->)|(-> & _ & _ & ->)]]];
    unfold TBL_bom, TBL_attr_include, TBL_esi, TBL_starttag.
  - apply (global_shadow_pat v 0xad760 32 64 CH). gdesc_in.
  - apply (global_shadow_pat v 0xad8a0 48 96 CH). gdesc_in.
  - apply (global_shadow_pat v 0xad840 64 96 CH). gdesc_in.
  - apply (global_shadow_pat v 0xad7a0 112 160 CH). gdesc_in.
Qed.

(* [comment removed for export] *)
Lemma svar_shadow : forall v S, consts_hold LPA v -> stvarA S <> 0 -> bytes_at rsegs v (sh (stvarA S)) (shpat 8).
Proof.
  intros v S CH NZ. destruct S; cbn [stvarA] in *; try (exfalso; apply NZ; reflexivity);
  match goal with |- bytes_at _ _ (sh ?b) _ => apply (global_shadow_pat v b 8 32 CH); gdesc_in end.
Qed.

End CEIL.

Section Sh.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {AI : AsanAlloc LPA}.
  Context {AI16 : AsanAlloc16}.   (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma mstr_shadow : forall A m md b s (str : list byte),
    ainv A m md -> In (b, s, 32) pa_gdescs -> Z.of_nat (length str) + 1 = s -> b mod 32 = 0 -> 0x23b60 <= b -> b + 32 <= 0x23d40 ->
    exists n, bytes_at rsegs (aview A m) (sh b) (shpat n)
      /\ Z.of_nat (length str) + 1 <= n /\ b mod 8 = 0 /\ b + n + 16 <= kLowMemEnd
      /\ mapped (aview A m) (sh b - sh b mod 8) 8
      /\ mapped (aview A m) (sh (b + Z.of_nat (length str)) - sh (b + Z.of_nat (length str)) mod 8) 8.
  Proof.
    intros A m md b s str AI0 HIn LEN AL LO HI. exists s.
    (first [ pose proof ((gdesc_facts b s 32 HIn)) as dR_1; dand3 dR_1 as _ SZ _ | pose proof (gdesc_facts b s 32 HIn) as (_ & SZ & _) ]).
    split; [exact (global_shadow_pat _ b s 32 (consts_hold_ainv LPA A m md AI0) HIn)|].
    split; [lia|]. split; [try (generalize alloc_ceiling_val); clear - AL; try pose proof alloc_ceiling_val; Z.div_mod_to_equations; lia|]. split; [unfold kLowMemEnd; lia|].
    split.
    - eapply (global_shadow_word_visible A m md b s 32 b AI0 HIn); [lia|]. unfold pa_static. lia.
    - eapply (global_shadow_word_visible A m md b s 32 _ AI0 HIn); [lia|]. unfold pa_static. lia.
  Qed.

  Lemma tab4_mtab_shadows : forall A m md Tb es ts NT, ainv A m md -> tab4 Tb es ts NT -> mtab_shadows (aview A m) es.
  Proof.
    intros A m md Tb es ts NT AI0 T4 i e Hn NZ.
    destruct T4 as [(_ & -> & _)|[(_ & -> & _)|[(_ & -> & _)|(_ & -> & _)]]];
      destruct i as [|[|[|[|[|[|[|[|i]]]]]]]]; cbn in Hn; try discriminate; injection Hn as <-; cbn [me_ptr me_str] in *;
      try (exfalso; apply NZ; reflexivity);
      (eapply (mstr_shadow A m md _ _ _ AI0); [| reflexivity| reflexivity| lia| lia]; gdesc_in).
  Qed.
End Sh.
End A_PMmab.

Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_App OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Vsb OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_World OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Img OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_La0bg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Cocsh OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Tac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Cocsh.A_Henv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_vez59 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_PHhja.A_veh4q OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_PDefs OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_PKit2.A_PKit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_PKit2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_PKit2.A_PMark OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_PHhja.A_PMmab.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require Import A_AI16.   (* [comment removed for export] *)
Import ListNotations.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.DL.projn := Ltac2.Init.true.   (* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Ltac icall_consts_in H ::= unfold vep_match_post, strlen_icpt_post, asan_memcpy_post, VM_STACK, VM_FRAME, STRLEN_ICPT_STACK, ASAN_MEMCPY_STACK in H.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.transport_chunks segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_chunks segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.footprint_after_store segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_footprint_after_store segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_mem_after_store.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_after_call segs m m' MU WM.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.addr_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_addr_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_zmlia.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_mlia.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require StepFast.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.step_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.zstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_zstep.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require MliaFast DietLia2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.mlia ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.MliaFast.mlia_fast | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_mlia ].
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require ShdFast.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.shadow_dead ::=
  exfalso;
  match goal with SOK : OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.shadow_val_ok ?b ?a ?k |- _ =>
    (let BR := fresh "SBR" in pose proof (OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.byte_range b) as BR;
     let MB := fresh "SMB" in first [ pose proof (Z.mod_pos_bound a 8 (@eq_refl comparison Lt)) as MB | idtac ]);   (* [comment removed for export] *)
    let Z0 := fresh "SZ" in let R1 := fresh "SR" in let R2 := fresh "SR" in
    destruct SOK as [Z0 | [R1 R2]]; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.sb_norm b a; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ShdFast.shd_mlia0
  end.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Destzna.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_exs PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_exs PO.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_ands PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_ands PO.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require WeqGuard TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= first [ exact eq_refl | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.WeqGuard.weq_guard; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac ].
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Stor0fe.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stor0fe.sb_mem_after_store.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Dietvxh.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dietvxh.dlia_vk.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require MliaFast DietLia2 DietDL3.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.mlia ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.MliaFast.mlia_fast | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.dl_solve0 | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_mlia ].
(* [comment removed for export] *)
Ltac show_left := match goal with |- ?G => idtac "LEFTOVER:" G end.
Local Tactic Notation "klia" ne_hyp_list(hs) := try (generalize alloc_ceiling_val); clear - hs; try pose proof alloc_ceiling_val; lia.
(* [comment removed for export] *)
Ltac chk_branch2 :=
  let K := fresh "KS" in
  zstep; if_cases K; zify_cond K;
  [ first [ shadow_fast K; clear K; shadow_cleanup | shadow_dead ]
  | first [ shadow_fast K; clear K; shadow_cleanup | shadow_dead ] ].

(* [comment removed for export] *)
Lemma vm_find_some : forall es inp i, mtab_wf es -> vm_find es inp = Some i ->
  exists e, nth_error es i = Some e /\
            ((me_ptr e = 0 /\ me_str e = []) \/ (me_ptr e <> 0 /\ is_prefixb (me_str e) inp = true /\ (1 <= length (me_str e) <= 8)%nat)).
Proof.
  induction es as [|e es IH]; intros inp i WF H; cbn in H; [cbn in WF; contradiction|].
  destruct es as [|e2 es2].
  - destruct WF as [E0 Es]. rewrite E0 in H. cbn in H. injection H as <-. exists e. split; [reflexivity| left; auto].
  - destruct WF as (Hp & Hl & Hn & WF').
    destruct (me_ptr e =? 0) eqn:E0; [apply Z.eqb_eq in E0; lia|]. apply Z.eqb_neq in E0.
    destruct (is_prefixb (me_str e) inp) eqn:EP.
    + injection H as <-. exists e. split; [reflexivity| right; auto].
    + destruct (runs_outb (me_str e) inp); [discriminate|].
      destruct (vm_find (e2 :: es2) inp) as [j|] eqn:EJ; [|discriminate]. cbn in H. injection H as <-.
      destruct (IH inp j WF' EJ) as (e' & Hn' & F). exists e'. split; [exact Hn'| exact F].
Qed.

Lemma vm_find_none : forall es inp, mtab_wf es -> vm_find es inp = None -> (length inp <= 7)%nat.
Proof.
  induction es as [|e es IH]; intros inp WF H; cbn in H; [discriminate|].
  destruct es as [|e2 es2].
  - destruct WF as [E0 _]. rewrite E0 in H. cbn in H. discriminate.
  - destruct WF as (Hp & Hl & Hn & WF').
    destruct (me_ptr e =? 0); [discriminate|]. destruct (is_prefixb (me_str e) inp); [discriminate|].
    destruct (runs_outb (me_str e) inp) eqn:ER.
    + apply runs_outb_length in ER. lia.
    + destruct (vm_find (e2 :: es2) inp) eqn:EJ; [discriminate|]. eapply IH; eauto.
Qed.

Lemma vm_find_lt : forall es inp i, mtab_wf es -> vm_find es inp = Some i -> (i < length es)%nat.
Proof. intros. eapply vm_find_bound; eauto. Qed.

(* [comment removed for export] *)
Lemma vep_cells_split_match : forall v tag q,
  vep_cells v tag q = firstn 39 (vep_cells v tag q) ++ [C8 (Z_to_bv 64 (v Fmatch))] ++ skipn 40 (vep_cells v tag q).
Proof. intros; reflexivity. Qed.
Lemma vep_cells_pre39_size : forall v tag q, cells_size (firstn 39 (vep_cells v tag q)) = 240%nat.
Proof. intros; reflexivity. Qed.
Lemma vep_cells_split_tag : forall v tag q,
  vep_cells v tag q = firstn 41 (vep_cells v tag q) ++ [CB 8 tag] ++ skipn 42 (vep_cells v tag q).
Proof. intros; reflexivity. Qed.
Lemma vep_cells_pre41_size : forall v tag q, cells_size (firstn 41 (vep_cells v tag q)) = 256%nat.
Proof. intros; reflexivity. Qed.
Lemma vep_cells_tag_indep : forall v tag tag' q, firstn 41 (vep_cells v tag q) = firstn 41 (vep_cells v tag' q) /\ skipn 42 (vep_cells v tag q) = skipn 42 (vep_cells v tag' q).
Proof. intros; split; reflexivity. Qed.

Section S.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {AI : AsanAlloc LPA}.
  Context {AI16 : AsanAlloc16}.   (* [comment removed for export] *)

  Lemma PH_Match : handler_stmt S_Match.
  Proof.
    intros E x A m md T. intros until t6. intros PE PI AINV MDF ST PLT KL KX.
    pose proof PI as PI0.
    handler_prologue PE PI AINV ST.
    pose proof (munch_refl [(pe_sp E - 304 - 2288, pe_sp E - 304); (pe_VEP E, pe_VEP E + 312)] (aview A m)) as MU.
    pose proof (wmono_refl rsegs (aview A m)) as WM.
    assert (WZ : wzone E A [pe_S E; vb_buf (x_vv x); pe_DATA E; x_v x Fattr_vsb; oabuf x; x_v x Finclude_src; oibuf x]
                         [(pe_sp E - 304 - 2288, pe_sp E - 304); (pe_VEP E, pe_VEP E + 312)]) by wzone_tac.
    assert (CFP : client_fp LPA A (aview A m) [(pe_sp E - 304 - 2288, pe_sp E - 304); (pe_VEP E, pe_VEP E + 312)])
      by (eapply wzone_client_fp; [exact PE| exact HFR| exact STK| unfold pframe; cbv zeta; exact FR| exact WZ]).
    destruct (data_shadow A m md _ _ AINV DATA) as [SHD D16]. fold_cl_segs. fold_aview.
    pose proof (shpat_sh_boundL (Clg:=Clg) (pe_DATA E) (Z.of_nat (length (pe_inp E))) ltac:(lia) ltac:(lia) Dhi) as SHDB. rewrite SHMAX_val in SHDB.
    assert (PHI : phi E x = 16 * (pe_e E - x_p x) + rank E x) by reflexivity.
    (* [comment removed for export] *)
    assert (TBL : exists Tb es ts NT, x_v x Fmatch = Tb /\ tab4 Tb es ts NT).
    { destruct (MTCH eq_refl) as [TM|[TM|[TM|TM]]]; rewrite TM; cbn [vi_tbl_bom vi_tbl_starttag vi_tbl_esi vi_tbl_attr_include VIA].
      - exists TBL_bom, tbl_bom, tgts_bom, 32. split; [reflexivity| left; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; reflexivity].
      - exists TBL_starttag, tbl_starttag, tgts_starttag, 112. split; [reflexivity| right; right; right; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; reflexivity].
      - exists TBL_esi, tbl_esi, tgts_esi, 64. split; [reflexivity| right; right; left; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; reflexivity].
      - exists TBL_attr_include, tbl_attr_include, tgts_attr_include, 48. split; [reflexivity| right; left; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; reflexivity]. }
    destruct TBL as (Tb & es & ts & NT & TM & TAB4).
    pose proof (tab4_geom _ _ _ _ TAB4) as (T8 & NTE & TLO & THI & TGT & WF & STRB).
    pose proof (tab4_strings _ _ _ _ _ MI TAB4) as STRS.
    pose proof (tab4_cells _ _ _ _ _ (img_tabs_ainv A m md AINV) TAB4) as ITB.
    pose proof (tab4_shadow _ _ _ _ _ (consts_hold_ainv LPA A m md AINV) TAB4) as SHT.
    pose proof (tab4_mtab_shadows A m md _ _ _ _ AINV TAB4) as SHS.
    pose proof (strlen_icpt_cells_of_consts _ (consts_hold_ainv LPA A m md AINV)) as SLC.
    fold_cl_segs. fold_aview.
    assert (SHTB : 0 <= sh Tb /\ sh Tb + Z.of_nat (length (shpat NT)) <= 17594064011264).
    { rewrite shpat_length by (try (generalize alloc_ceiling_val); clear - NTE; try pose proof alloc_ceiling_val; lia). unfold sh. rewrite kShadowOffset_val. clear - TLO THI NTE; try pose proof alloc_ceiling_val. Z.div_mod_to_equations. lia. }
    pose proof (mtab_cells_size es) as TSZ.
    (* [comment removed for export] *)
    assert (VPM : ro_cells rsegs (aview A m) (pe_VEP E + 240) [C8 (Z_to_bv 64 Tb)]).
    { pose proof (pi_vep _ _ _ _ PI0) as (_ & VC & _). rewrite vep_cells_split_match in VC.
      apply (proj1 (rw_cells_app rsegs _ _ _ _)) in VC. destruct VC as [_ VC]. rewrite vep_cells_pre39_size in VC.
      apply (proj1 (rw_cells_app rsegs _ _ _ _)) in VC. destruct VC as [VC _]. change (Z.of_nat 240) with 240 in VC. rewrite TM in VC. exact (proj1 VC). }
    set (inp' := pslice E (x_p x) (pe_e E)).
    assert (LINP : Z.of_nat (length inp') = pe_e E - x_p x) by (subst inp'; apply pslice_length; [try (generalize alloc_ceiling_val); clear - VERP; try pose proof alloc_ceiling_val; lia| exact PLE| clear; unfold pe_e, pe_N; lia]).
    assert (PINP : bytes_at rsegs (aview A m) (x_p x) inp') by (subst inp'; apply pslice_bytes; [exact DBY| try (generalize alloc_ceiling_val); clear - VERP; try pose proof alloc_ceiling_val; lia| exact PLE| clear; unfold pe_e, pe_N; lia]).
    hide_neqs.
    ago AINV. fold_cl_segs.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.
    icall (vep_match_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                          (pe_VEP E) Tb es inp' (pe_lo E) 312 NT (pe_DATA E) (Z.of_nat (length (pe_inp E)))) by
      (rewrite ?unsigned_lit by (try (generalize alloc_ceiling_val); clear - FRB VERP Dlo Dhi PLE ACV; try pose proof alloc_ceiling_val; unfold pe_e, pe_N in *; lia);
       first [ exact MI | exact CEIL | exact VPM | exact ITB | exact WF | exact STRS | exact SLC | exact SHT | exact SHS | exact SHD | exact STK | exact PINP
             | reflexivity
             | lazymatch goal with |- _ = Z_to_bv 64 _ => rewrite LINP; f_equal; clear; lia end
             | lazymatch goal with |- _ + VM_STACK <= _ => unfold VM_STACK, VM_FRAME, STRLEN_ICPT_STACK; try (generalize alloc_ceiling_val); clear - LOP; try pose proof alloc_ceiling_val; lia end
             | lazymatch goal with |- 0 < _ => try (generalize alloc_ceiling_val); clear - TLO; try pose proof alloc_ceiling_val; lia end
             | lazymatch goal with |- bytes_at _ _ (sh (pe_VEP E)) _ => pose proof SHV0 as T_; rewrite EzsV in T_; exact T_ end
             | lazymatch goal with |- forall i e, _ => intros i_ e_ Hn_ Hp_; pose proof (STRB i_ e_ Hn_ Hp_) as X_; try (generalize alloc_ceiling_val); clear - X_ ACV; try pose proof alloc_ceiling_val; lia end
             | lazymatch goal with |- 0 <= pe_VEP E /\ _ => try (generalize alloc_ceiling_val); clear - VEPlo VEPhi; try pose proof alloc_ceiling_val; lia end
             | lazymatch goal with |- _ + 16 * _ <= _ => try (generalize alloc_ceiling_val); clear - THI NTE ACV; try pose proof alloc_ceiling_val; lia end
             | lazymatch goal with |- pe_VEP E mod 8 = 0 /\ _ => split; [try (generalize alloc_ceiling_val); clear - VEP16; try pose proof alloc_ceiling_val; Z.div_mod_to_equations; lia| try (generalize alloc_ceiling_val); clear - VEPhi; try pose proof alloc_ceiling_val; lia] end
             | lazymatch goal with |- Tb mod 8 = 0 /\ _ => refine (conj T8 (conj _ _)); try (generalize alloc_ceiling_val); clear - NTE THI ACV; try pose proof alloc_ceiling_val; lia end
             | lazymatch goal with |- pe_DATA E mod 8 = 0 /\ _ => rewrite LINP; try (generalize alloc_ceiling_val); clear - D16 Dlo Dhi VERP PLE EE ACV; try pose proof alloc_ceiling_val; unfold pe_e, pe_N in *; Z.div_mod_to_equations; lia end ]).
    lazymatch goal with X : stk _ ?mx _ _ |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename X into STK1 end.
    (* [comment removed for export] *)
    zstep. vchk SHV0 EzsV 8 0. zstep.
    destruct (vm_find es inp') as [i|] eqn:VF; unfold vm_result; rewrite VF.
    - (* [comment removed for export] *)
      destruct (vm_find_some es inp' i WF VF) as (e & Hnth & CASES).
      destruct (TGT i e Hnth) as (S' & Hts & Esv & SVNZ & Esval).
      pose proof (vm_find_lt es inp' i WF VF) as IL.
      assert (IR : 0 <= Tb + 16 * Z.of_nat i /\ Tb + 16 * Z.of_nat i + 16 <= Tb + NT) by (try (generalize alloc_ceiling_val); clear - IL TLO NTE; try pose proof alloc_ceiling_val; lia).
      pose proof (wf_ptr_nonneg _ _ _ WF Hnth) as PR.
      zstep. zstep. if_cases K1; zify_cond K1. { exfalso. try (generalize alloc_ceiling_val); clear - K1 TLO IR; try pose proof alloc_ceiling_val. rewrite ?unsigned_lit in K1 by lia. lia. } clear K1.
      (* [comment removed for export] *)
      lazymatch goal with |- evt _ ?P _ =>
      assert (P44 : forall (p' : Z) (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (mc : mem),
        munch [(pe_sp E - 304 - 2288, pe_sp E - 304); (pe_VEP E, pe_VEP E + 312)] (aview A m) mc -> wmono rsegs (aview A m) mc -> mem_inv rsegs mc ->
        rw_cells rsegs mc (pe_VEP E) (vep_cells (fupd (fupd (x_v x) Fstate (stA (x_st x))) Fmatch_hit (Tb + 16 * Z.of_nat i)) (x_tag x) (x_q x)) ->
        rw_cells rsegs mc (pe_sp E - 304) (pframe E j0 j8) ->
        bytes_at rsegs mc (pe_DATA E) (pe_inp E) -> stk rsegs mc (pe_lo E) (pe_sp E - 304) ->
        bytes_at rsegs mc (sh (pe_VEP E)) zsV -> bytes_at rsegs mc (sh Tb) (shpat NT) ->
        ((me_ptr e = 0 /\ me_str e = [] /\ p' = x_p x) \/
         (me_ptr e <> 0 /\ is_prefixb (me_str e) inp' = true /\ p' = x_p x + Z.of_nat (length (me_str e)) /\ (1 <= length (me_str e) <= 8)%nat)) ->
        evt rsegs P (call_ms E 0x8cfb8 p' ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 (Tb + 16 * Z.of_nat i))
                              (Z_to_bv 64 143872) (Z_to_bv 64 144000) t3' t4' t5' t6' mc))
      end.
      { intros until mc. intros MUc WMc MIc VEPCc FRc DBYc STKc SHVc SHTc HP. unfold call_ms, S8. cbv zeta. rewrite EFP.
        clear VEPC FR DBY SHV0 SHD SHT. try clear STK1. try clear MI.
        unfold vep_cells in VEPCc. psimp_in VEPCc. unfold pframe in FRc. cbv zeta in FRc.
        assert (LP : x_p x <= p' <= pe_e E).
        { destruct HP as [(_ & _ & ->)|(_ & PF & -> & _)]; [try (generalize alloc_ceiling_val); clear - PLE; try pose proof alloc_ceiling_val; unfold pe_e, pe_N; lia|].
          apply is_prefixb_length in PF. revert PF LINP PLE. clear. unfold pe_e, pe_N. intros. lia. }
        assert (PR' : 0 <= p' < 2^64) by (try (generalize alloc_ceiling_val); clear - LP VERP Dlo Dhi PLE ACV EE; try pose proof alloc_ceiling_val; unfold pe_e, pe_N in *; lia).
        (* [comment removed for export] *)
        pose proof (consts_hold_munch _ _ mc (consts_hold_ainv LPA A m md AINV) MUc
                      ltac:(apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]]; unfold const_free_ivl, CONSTS_TOP; cbn [fst snd]; left; try (generalize alloc_ceiling_val); clear - VEPlo LOP CEIL ACV; try pose proof alloc_ceiling_val; lia)) as CHc.
        pose proof (tab4_cells _ _ _ _ _ (img_tabs_of_consts _ CHc) TAB4) as ITBc.
        pose proof (vepvars_of_consts _ CHc S' SVNZ) as VVc.
        pose proof (svar_shadow _ S' CHc SVNZ) as SVSH. fold_cl_segs.
        assert (SVB : 0xa8e20 <= stvarA S' <= 0xa8fe0) by (try (generalize alloc_ceiling_val); clear - SVNZ; try pose proof alloc_ceiling_val; destruct S'; cbn in *; first [lia | exfalso; apply SVNZ; reflexivity]).
        assert (SVSB : 0 <= sh (stvarA S') /\ sh (stvarA S') + Z.of_nat (length (shpat 8)) <= 17594064011264).
        { change (Z.of_nat (length (shpat 8))) with 1. unfold sh. rewrite kShadowOffset_val. clear - SVB; try pose proof alloc_ceiling_val. Z.div_mod_to_equations. lia. }
        assert (SV8 : stvarA S' mod 8 = 0) by (clear - SVNZ; try pose proof alloc_ceiling_val; destruct S'; cbn; first [reflexivity | exfalso; apply SVNZ; reflexivity]).
        (* [comment removed for export] *)
        zstep. zstep. zstep. shadow_addr SHTc 8. zstep. do 5 zstep. chk_branch2.
        (* [comment removed for export] *)
        pose proof (mtab_read_svar rsegs _ Tb es i e _ ITBc Hnth eq_refl) as RD2. unfold wa in RD2.
        replace (Tb + 16 * Z.of_nat i + 8) with (Tb + 16 * Z.of_nat i + 8) in RD2 by reflexivity.
        zstep. clear RD2. cbv beta. rewrite Esv.
        (* [comment removed for export] *)
        shadow_chk0 SVSH 8.
        vrechk SHVc EzsV (pe_VEP E + 64) 8 0.
        (* [comment removed for export] *)
        pose proof (cells_at_read rsegs _ _ _ 0%nat _ VVc eq_refl) as RD3. cbn [csize cbytes Z.of_nat] in RD3. rewrite Z.add_0_r in RD3. unfold wa in RD3.
        zstep. clear RD3. cbv beta. zstep.
        (* [comment removed for export] *)
        zstep. vchk SHVc EzsV 8 1. zstep. vchk SHVc EzsV 4 0. zstep. zstep.
        astop AINV MUc WMc CFP. fold_cl_segs.
        (* [comment removed for export] *)
        assert (LKM : Tb = TBL_attr_include -> vct_xmlname (look E x) = true).
        { intros ETB. destruct (look_read rsegs E x _ DBYc ltac:(try (generalize alloc_ceiling_val); clear - VERP; try pose proof alloc_ceiling_val; lia) PLT) as (b & Hb & Hlk & _).
          pose proof (bv_unsigned_in_range _ b) as BR. change (bv_modulus 8) with 256 in BR. rewrite <- Hlk.
          apply (proj1 (vct_namestart_facts _ BR ltac:(rewrite Hlk; apply (LOOKM eq_refl); [rewrite TM, ETB; reflexivity| exact PLT]))). }
        eapply (KL (PST p' S' (fupd (fupd (fupd (fupd (x_v x) Fmatch_hit (Tb + 16 * Z.of_nat i)) Fstate (stA S')) Fmatch 0) Ftag_i 0)
                        (x_tag x) (x_q x) (x_vv x) (x_va x) (x_vi x)) A _ _).
        2:{ assumption. }
        2:{ eapply amd_frame_sbm_r; [exact MDF | exact SBM]. }
        1: apply Build_pinv; psimp; pinv_close PE0 AINV HFR MUc WMc WZ.
        (* [comment removed for export] *)
        (* [comment removed for export] *)
        all: try clear VEPCc; try clear ITBc; try clear ITB; try clear VPM; try clear SHTc; try clear CASES.
        all: destruct TAB4 as [(ETb & Ees & Ets & ENT)|[(ETb & Ees & Ets & ENT)|[(ETb & Ees & Ets & ENT)|(ETb & Ees & Ets & ENT)]]]; subst ts es;
          (destruct i as [|[|[|[|[|[|[|[|i]]]]]]]]; cbn in Hts; try discriminate Hts);
          injection Hts as ES'; subst S'; cbn in Hnth; injection Hnth as Ee; subst e; cbn [me_ptr me_str length] in HP; rewrite ETb in TM; subst Tb.
        (* [comment removed for export] *)
        all: try (psimp; intros _; split; [| discriminate]; rewrite PHI; unfold phi, rank; psimp; rewrite ST, TM;
                  cbn [vi_tbl_attr_include vi_tbl_esi VIA]; unfold TBL_bom, TBL_starttag, TBL_esi, TBL_attr_include; cbn [Z.eqb Pos.eqb];
                  destruct HP as [(Z0 & _ & EP)|(NZ & PF & EP & LEN)]; subst p'; try (exfalso; try (generalize alloc_ceiling_val); clear - Z0; try pose proof alloc_ceiling_val; lia); try (exfalso; try (generalize alloc_ceiling_val); clear - NZ; try pose proof alloc_ceiling_val; lia);
                  try (unfold look; cbn [x_p]; unfold look in LKM; rewrite (LKM eq_refl)); try (generalize alloc_ceiling_val); clear - PLT; try pose proof alloc_ceiling_val; lia).
        (* [comment removed for export] *)
        all: psimp; pinv_close PE0 AINV HFR MUc WMc WZ.
        all: try lazymatch goal with
          | |- _ <= _ Fver_p <= _ => try (generalize alloc_ceiling_val); clear - VERP LP; try pose proof alloc_ceiling_val; lia
          | |- _ <= pe_e _ => try (generalize alloc_ceiling_val); clear - LP; try pose proof alloc_ceiling_val; lia
          | |- 0 <= 0 <= 7 => clear; lia
          | |- _ = 0 \/ _ =>
              destruct ATTR as [A0|(A1 & A2 & A3)]; [left; exact A0| exfalso; destruct A3 as [A3|[A3|[A3|A3]]];
                [rewrite TM in A3; revert A3; clear; cbn; unfold TBL_bom, TBL_starttag, TBL_esi, TBL_attr_include; intros; lia
                | discriminate A3| discriminate A3| discriminate A3]]
          | |- _ + _ + _ + _ <= _ => revert OUT LP HP; unfold oacost, oicost; cbn [x_va x_vi x_st x_p x_vv]; clear; intros; lia
          | |- True -> _ <> 0 => intros _; apply ARMED; rewrite TM; reflexivity
          | |- True -> _ -> _ /\ _ => intros _ _; split; [apply (MATTR eq_refl); rewrite TM; reflexivity| cbn [Z.of_nat Pos.of_succ_nat Pos.succ Z.mul Pos.mul vi_tbl_attr_include VIA]; unfold TBL_attr_include; first [left; reflexivity | right; reflexivity | left; clear; lia | right; clear; lia]]
          | |- match x_va _ with _ => _ end => world_close PE0 AINV HFR MUc WMc WZ
          | |- match x_vi _ with _ => _ end => world_close PE0 AINV HFR MUc WMc WZ
          | |- cframe _ _ _ _ _ _ _ _ _ => cf_stores CF MUc PE0 STKc FRc; left; left; unfold blk; lia
          end.
        all: show_left. }
      (* [comment removed for export] *)
      shadow_chk0 SHT 8.
      pose proof (mtab_read_ptr rsegs _ Tb es i e _ ITB Hnth eq_refl) as RD1. unfold wa in RD1.
      replace (Tb + 16 * Z.of_nat i) with (Tb + 16 * Z.of_nat i) in RD1 by reflexivity.
      zstep. clear RD1. cbv beta.
      zstep. if_cases K2; zify_cond K2.
      { (* [comment removed for export] *)
        destruct CASES as [[Z0 ZS]|(NZ & _)]; [| exfalso; apply NZ; try (generalize alloc_ceiling_val); clear - K2 PR; try pose proof alloc_ceiling_val; rewrite ?unsigned_lit in K2 by lia; lia].
        lazymatch goal with MIx : mem_inv _ ?mr, VX : rw_cells _ ?mr (pe_VEP E) _, FX : rw_cells _ ?mr (pe_sp E - 304) _, DX : bytes_at _ ?mr (pe_DATA E) _,
                             SX : stk _ ?mr _ _, H1 : bytes_at _ ?mr (sh (pe_VEP E)) _, H2 : bytes_at _ ?mr (sh Tb) _ |- evt _ _ (MS _ _ _ _ _ ?mr _) =>
          eapply (P44 (x_p x) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mr MU WM MIx ltac:(unfold vep_cells; psimp; exact VX) ltac:(unfold pframe; cbv zeta; exact FX) DX SX H1 H2) end.
        left. split; [exact Z0|]. split; [exact ZS| reflexivity]. }
      destruct CASES as [[Z0 _]|(NZ & PF & LEN)]; [exfalso; apply K2; rewrite Z0; reflexivity|].
      pose proof (wf_entry _ _ _ WF Hnth NZ) as (_ & NONUL & _).
      (* [comment removed for export] *)
      zstep.
      destruct (STRS i e Hnth NZ) as (slack & SB & SPAD & SLEN).
      destruct (SHS i e Hnth NZ) as (n & SSH & Hn1 & Hal & Hlow & Q1 & Q2). fold_cl_segs. fold_aview.
      pose proof (STRB i e Hnth NZ) as HS. unfold kLowMemEnd in Hlow.
      assert (SSHB : 0 <= sh (me_ptr e) /\ sh (me_ptr e) + Z.of_nat (length (shpat n)) <= 17594064011264).
      { rewrite shpat_length by (try (generalize alloc_ceiling_val); clear - Hn1; try pose proof alloc_ceiling_val; lia). unfold sh. rewrite kShadowOffset_val. clear - HS Hlow Hn1; try pose proof alloc_ceiling_val. Z.div_mod_to_equations. lia. }
      (* [comment removed for export] *)
      lazymatch goal with MUx : munch _ (aview A m) ?mr |- evt _ _ (MS _ _ _ _ _ ?mr _) =>
        pose proof (bytes_at_transport rsegs _ (aview A m) mr _ _ SB MUx ltac:(cbn [disjoint_from]; rewrite length_app; cbn [length]; try (generalize alloc_ceiling_val); clear - HS LOP CEIL ACV VEPlo SLEN; try pose proof alloc_ceiling_val; lia)) as SB1;
        pose proof (bytes_at_transport rsegs _ (aview A m) mr _ _ SSH MUx ltac:(cbn [disjoint_from]; try (generalize alloc_ceiling_val); clear - SSHB LOP CEIL ACV VEPlo; try pose proof alloc_ceiling_val; lia)) as SSH1;
        pose proof (mapped_munch _ (aview A m) mr (sh (me_ptr e) - sh (me_ptr e) mod 8) 8 MUx ltac:(unfold sh; pose proof kShadowOffset_val as KV_; try (generalize alloc_ceiling_val); clear - HS KV_; try pose proof alloc_ceiling_val; Z.div_mod_to_equations; lia)
                      ltac:(unfold sh; pose proof kShadowOffset_val as KV_; try (generalize alloc_ceiling_val); clear - HS KV_; try pose proof alloc_ceiling_val; Z.div_mod_to_equations; lia)
                      ltac:(intros j_ Hj_; cbn [outside]; unfold sh in Hj_ |- *; pose proof kShadowOffset_val as KV_; try (generalize alloc_ceiling_val); clear - Hj_ HS LOP CEIL ACV VEPlo KV_; try pose proof alloc_ceiling_val; Z.div_mod_to_equations; lia) Q1) as Q1';
        pose proof (mapped_munch _ (aview A m) mr (sh (me_ptr e + Z.of_nat (length (me_str e))) - sh (me_ptr e + Z.of_nat (length (me_str e))) mod 8) 8 MUx ltac:(unfold sh; pose proof kShadowOffset_val as KV_; try (generalize alloc_ceiling_val); clear - HS LEN KV_; try pose proof alloc_ceiling_val; Z.div_mod_to_equations; lia)
                      ltac:(unfold sh; pose proof kShadowOffset_val as KV_; try (generalize alloc_ceiling_val); clear - HS LEN KV_; try pose proof alloc_ceiling_val; Z.div_mod_to_equations; lia)
                      ltac:(intros j_ Hj_; cbn [outside]; unfold sh in Hj_ |- *; pose proof kShadowOffset_val as KV_; try (generalize alloc_ceiling_val); clear - Hj_ HS LEN LOP CEIL ACV VEPlo KV_; try pose proof alloc_ceiling_val; Z.div_mod_to_equations; lia) Q2) as Q2';
        clear SB SSH Q1 Q2; rename SB1 into SB; rename SSH1 into SSH; rename Q1' into Q1; rename Q2' into Q2;
        pose proof (strlen_icpt_cells_of_consts _ (consts_hold_munch _ _ mr (consts_hold_ainv LPA A m md AINV) MUx
                      ltac:(apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]]; unfold const_free_ivl, CONSTS_TOP; cbn [fst snd]; left; try (generalize alloc_ceiling_val); clear - VEPlo LOP CEIL ACV; try pose proof alloc_ceiling_val; lia))) as SLCc
      end.
      icall (strlen_icpt_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (me_str e) slack (pe_lo E)) by
        (rewrite ?unsigned_lit by (try (generalize alloc_ceiling_val); clear - PR FRB; try pose proof alloc_ceiling_val; lia);
         first [ exact SB | exact NONUL | exact SPAD | exact SLCc | exact CEIL | exact Q1 | exact Q2
               | lazymatch goal with |- mem_inv _ _ => assumption | |- stk _ _ _ _ => assumption end
               | apply (shadow_ok_of_shpat _ (me_ptr e) n); [exact SSH | exact Hal | try (generalize alloc_ceiling_val); clear - PR; try pose proof alloc_ceiling_val; lia | clear; lia | try (generalize alloc_ceiling_val); clear - Hn1; try pose proof alloc_ceiling_val; lia | clear; lia]
               | unfold OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpghc.AIcp6d9.inmem_range; rewrite ?unsigned_lit by (try (generalize alloc_ceiling_val); clear - PR; try pose proof alloc_ceiling_val; lia); left; try (generalize alloc_ceiling_val); clear - PR Hlow Hn1 HS; try pose proof alloc_ceiling_val; lia
               | rewrite ?length_app; cbn [length]; unfold STRLEN_ICPT_STACK; try (generalize alloc_ceiling_val); clear - LOP CEIL ACV HS SLEN LEN; try pose proof alloc_ceiling_val; lia ]).
      (* [comment removed for export] *)
      zstep.
      lazymatch goal with MIx : mem_inv _ ?mr, MUx : munch _ (aview A m) ?mr, WMx : wmono _ (aview A m) ?mr, VX : rw_cells _ ?mr (pe_VEP E) _,
                           FX : rw_cells _ ?mr (pe_sp E - 304) _, DX : bytes_at _ ?mr (pe_DATA E) _,
                           SX : stk _ ?mr _ _, H1 : bytes_at _ ?mr (sh (pe_VEP E)) _, H2 : bytes_at _ ?mr (sh Tb) _ |- evt _ _ (MS _ _ _ _ _ ?mr _) =>
        eapply (P44 (x_p x + Z.of_nat (length (me_str e))) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mr MUx WMx MIx ltac:(unfold vep_cells; psimp; exact VX) ltac:(unfold pframe; cbv zeta; exact FX) DX SX H1 H2) end.
      right. split; [exact NZ|]. split; [exact PF|]. split; [reflexivity| exact LEN].
    - (* [comment removed for export] *)
      pose proof (vm_find_none es inp' WF VF) as LIN.
      assert (NR : 0 <= pe_e E - x_p x <= 7) by (revert LIN LINP PLT; clear; intros; lia).
      zstep. zstep. if_cases K1; zify_cond K1. 2:{ exfalso. apply K1. reflexivity. } clear K1.
      (* [comment removed for export] *)
      zstep. zstep. if_cases K3; zify_cond K3.
      { exfalso. unsign K3. revert K3 NR VERP Dlo PLT Dhi ACV EE. clear. unfold pe_e, pe_N. intros. rewrite ?unsigned_lit in K3 by lia. lia. }
      clear K3.
      zstep. zstep. zstep. zstep. zstep.
      (* [comment removed for export] *)
      set (nb := Z.to_nat (pe_e E - x_p x)).
      assert (LN : length inp' = nb) by (subst nb; revert LINP; clear; intros; lia).
      assert (LT8 : (nb <= 8)%nat) by (subst nb; revert NR; clear; intros; lia).
      lazymatch goal with VX : rw_cells _ ?mr (pe_VEP E) _ |- evt _ _ (MS _ _ _ _ _ ?mr _) =>
        assert (VC : rw_cells rsegs mr (pe_VEP E) (vep_cells (fupd (fupd (x_v x) Fstate (stA (x_st x))) Fmatch_hit 0) (x_tag x) (x_q x))) by exact VX; clear VX end.
      rewrite vep_cells_split_tag in VC.
      apply (proj1 (rw_cells_app rsegs _ _ _ _)) in VC. destruct VC as [VXA VC]. rewrite vep_cells_pre41_size in VC.
      apply (proj1 (rw_cells_app rsegs _ _ _ _)) in VC. destruct VC as [VXT VXB]. change (Z.of_nat 256) with 256 in VXT, VXB.
      cbn [cells_size csize Nat.add] in VXB. change (Z.of_nat 8) with 8 in VXB. replace (pe_VEP E + 256 + 8) with (pe_VEP E + 264) in VXB by (clear; lia).
      apply (rw_cells_recast rsegs _ (pe_VEP E + 256) _ [CB nb (firstn nb (x_tag x)); CB (8 - nb) (skipn nb (x_tag x))]) in VXT;
        [| cbn; rewrite firstn_length, skipn_length; revert TAG LT8; clear; intros; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; lia
         | cbn [cells_bytes cbytes]; rewrite !app_nil_r; rewrite firstn_skipn; reflexivity].
      apply (proj1 (rw_cells_app rsegs _ _ [CB nb (firstn nb (x_tag x))] [CB (8 - nb) (skipn nb (x_tag x))])) in VXT.
      destruct VXT as [VXT1 VXT2]. cbn [cells_size csize Nat.add] in VXT2.
      unfold vep_cells in VXA, VXB. cbn [firstn] in VXA. cbn [skipn] in VXB. psimp_in VXA. psimp_in VXB.
      lazymatch goal with MUx : munch _ (aview A m) ?mr, DX : bytes_at _ ?mr (pe_DATA E) _ |- evt _ _ (MS _ _ _ _ _ ?mr _) =>
        pose proof (asan_memcpy_cells_of_consts _ (consts_hold_munch _ _ mr (consts_hold_ainv LPA A m md AINV) MUx
                      ltac:(apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]]; unfold const_free_ivl, CONSTS_TOP; cbn [fst snd]; left; try (generalize alloc_ceiling_val); clear - VEPlo LOP CEIL ACV; try pose proof alloc_ceiling_val; lia))) as AMCc;
        assert (PINPc : bytes_at rsegs mr (x_p x) inp') by (subst inp'; apply pslice_bytes; [exact DX| try (generalize alloc_ceiling_val); clear - VERP; try pose proof alloc_ceiling_val; lia| exact PLE| clear; unfold pe_e, pe_N; lia]);
        pose proof (live_range_ok A m md (pe_VEP E) 312 (pe_VEP E + 256) (pe_e E - x_p x) AINV LVEP ltac:(clear; lia) ltac:(try (generalize alloc_ceiling_val); clear - NR; try pose proof alloc_ceiling_val; lia)) as RNGd;
        pose proof (live_range_ok A m md (pe_DATA E) (Z.of_nat (length (pe_inp E))) (x_p x) (pe_e E - x_p x) AINV LDATA ltac:(try (generalize alloc_ceiling_val); clear - VERP; try pose proof alloc_ceiling_val; lia) ltac:(clear; unfold pe_e, pe_N; lia)) as RNGs
      end.
      assert (N0 : pe_e E - x_p x = 0 \/ 1 <= pe_e E - x_p x) by (try (generalize alloc_ceiling_val); clear - NR; try pose proof alloc_ceiling_val; lia).
      lazymatch goal with MUx : munch _ (aview A m) ?mr |- evt _ _ (MS _ _ _ _ _ ?mr _) =>
        assert (RNGc : pe_e E - x_p x = 0 \/ (range_ok mr (x_p x) (pe_e E - x_p x) /\ range_ok mr (pe_VEP E + 256) (pe_e E - x_p x)))
          by (destruct N0 as [Z0|P1]; [left; exact Z0| right; split;
                [ eapply (range_ok_high_munch _ _ mr _ _); [exact (RNGs P1)| exact MUx| try (generalize alloc_ceiling_val); clear - VERP Dlo; try pose proof alloc_ceiling_val; lia| exact P1| try (generalize alloc_ceiling_val); clear - Dhi PLE EE; try pose proof alloc_ceiling_val; unfold pe_e, pe_N in *; lia
                   | apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]]; cbn [fst]; rewrite SHMAX_val; try (generalize alloc_ceiling_val); clear - VEPlo LOP CEIL ACV; try pose proof alloc_ceiling_val; lia]
                | eapply (range_ok_high_munch _ _ mr _ _); [exact (RNGd P1)| exact MUx| try (generalize alloc_ceiling_val); clear - VEPlo; try pose proof alloc_ceiling_val; lia| exact P1| try (generalize alloc_ceiling_val); clear - VEPhi NR; try pose proof alloc_ceiling_val; lia
                   | apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]]; cbn [fst]; rewrite SHMAX_val; try (generalize alloc_ceiling_val); clear - VEPlo LOP CEIL ACV; try pose proof alloc_ceiling_val; lia] ]])
      end.
      clear RNGd RNGs.
      icall (asan_memcpy_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ inp' (firstn nb (x_tag x)) (pe_lo E)) by
        (rewrite ?unsigned_lit by (try (generalize alloc_ceiling_val); clear - FRB VERP Dlo Dhi PLE ACV VEPlo VEPhi NR EE; try pose proof alloc_ceiling_val; unfold pe_e, pe_N in *; lia);
         first [ exact PINPc | exact AMCc | exact CEIL | exact RNGc
               | lazymatch goal with |- mem_inv _ _ => assumption | |- stk _ _ _ _ => assumption end
               | lazymatch goal with |- length _ = _ => rewrite LN; subst nb; reflexivity end
               | lazymatch goal with |- rw_cells _ _ _ _ => subst nb; exact VXT1 end
               | unfold ASAN_MEMCPY_STACK; revert DJ_VD VERP PLE NR VEPhi Dhi LOP CEIL ACV EE; clear; unfold pe_e, pe_N; intros; lia ]).
      lazymatch goal with H : rw_cells rsegs ?mc (pe_VEP E + 256) _ |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename H into DST end.
      (* [comment removed for export] *)
      set (tag' := inp' ++ skipn nb (x_tag x)).
      assert (TAG' : length tag' = 8%nat) by (subst tag'; rewrite length_app, skipn_length, LN; revert TAG LT8; clear; intros; lia).
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mf _) =>
        assert (VEPC2 : rw_cells rsegs mf (pe_VEP E) (vep_cells (fupd (fupd (x_v x) Fstate (stA (x_st x))) Fmatch_hit 0) tag' (x_q x))) end.
      { rewrite (vep_cells_split_tag _ tag').
        destruct (vep_cells_tag_indep (fupd (fupd (x_v x) Fstate (stA (x_st x))) Fmatch_hit 0) (x_tag x) tag' (x_q x)) as [E41 E42].
        rewrite <- E41, <- E42.
        apply (proj2 (rw_cells_app rsegs _ _ _ _)). split; [exact VXA|]. rewrite vep_cells_pre41_size. change (Z.of_nat 256) with 256.
        apply (proj2 (rw_cells_app rsegs _ _ _ _)). split.
        - subst tag'. apply (rw_cells_recast rsegs _ (pe_VEP E + 256) [CB nb inp'; CB (8 - nb) (skipn nb (x_tag x))]).
          + apply (proj2 (rw_cells_app rsegs _ _ [CB nb inp'] [CB (8 - nb) (skipn nb (x_tag x))])).
            split; [rewrite <- LN; replace (length inp') with (Z.to_nat (pe_e E - x_p x)) by (rewrite LN; reflexivity); exact DST|].
            cbn [cells_size csize Nat.add]. exact VXT2.
          + cbn. rewrite length_app, skipn_length, LN. revert TAG LT8. clear. intros. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; lia.
          + cbn [cells_bytes cbytes]. rewrite !app_nil_r. reflexivity.
        - cbn [cells_size csize Nat.add length]. change (Z.of_nat 8) with 8.
          replace (pe_VEP E + 256 + 8) with (pe_VEP E + 264) by (clear; lia). exact VXB. }
      clear VXA VXB VXT2 DST. unfold vep_cells in VEPC2. psimp_in VEPC2.
      assert (NR64 : 0 <= pe_e E - x_p x < 2^64) by (revert NR; clear; intros; lia).
      assert (NR32 : 0 <= pe_e E - x_p x < 2^32) by (revert NR; clear; intros; lia).
      (* [comment removed for export] *)
      lazymatch goal with H1 : bytes_at _ ?mr (sh (pe_VEP E)) _ |- evt _ _ (MS _ _ _ _ _ ?mr _) => rename H1 into SHVc end.
      zstep. vchk SHVc EzsV 4 0. zstep. zstep.
      vrechk SHVc EzsV (pe_VEP E + 64) 8 0. zstep. zstep. zstep. zstep. zstep.
      lazymatch goal with MUx : munch _ (aview A m) ?mr, WMx : wmono _ (aview A m) ?mr |- evt _ _ (MS _ _ _ _ _ ?mr _) =>
        astop AINV MUx WMx CFP end.
      fold_cl_segs.
      set (v' := fupd (fupd (fupd (x_v x) Fmatch_hit 0) Ftag_i (pe_e E - x_p x)) Fstate (stA S_MatchBuf)).
      eapply (KX (PST (pe_e E) S_MatchBuf v' tag' (x_q x) (x_vv x) (x_va x) (x_vi x)) A _ _).
      2:{ assumption. }
      2:{ eapply amd_frame_sbm_r; [exact MDF | exact SBM]. }
      2:{ reflexivity. }
      subst v'. lazymatch goal with MUx : munch _ (aview A m) ?mr, WMx : wmono _ (aview A m) ?mr |- pinv _ _ _ ?mr =>
        apply Build_pinv; psimp; pinv_close PE0 AINV HFR MUx WMx WZ;
        try lazymatch goal with
          | |- _ <= _ Fver_p <= _ => try (generalize alloc_ceiling_val); clear - VERP PLE; try pose proof alloc_ceiling_val; unfold pe_e, pe_N; lia
          | |- _ + _ + _ + _ <= _ => revert OUT PLE; unfold oacost, oicost; cbn [x_va x_vi x_st x_p x_vv]; clear; unfold pe_e, pe_N; intros; lia
          | |- 0 <= _ <= 7 => try (generalize alloc_ceiling_val); clear - NR; try pose proof alloc_ceiling_val; lia
          | |- match x_va _ with _ => _ end => world_close PE0 AINV HFR MUx WMx WZ
          | |- match x_vi _ with _ => _ end => world_close PE0 AINV HFR MUx WMx WZ
          | |- cframe _ _ _ _ _ _ _ _ _ => lazymatch goal with SX : stk _ mr _ _, FX : rw_cells _ mr (pe_sp E - 304) _ |- _ => cf_stores CF MUx PE0 SX FX; left; left; unfold blk; lia end
          end end.
      all: show_left.
  Qed.
End S.
