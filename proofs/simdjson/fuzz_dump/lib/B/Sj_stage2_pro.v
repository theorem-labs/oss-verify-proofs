(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Lib Require Import Tac Arr Bytes StoreFast ImageA.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Sj Require Import SjS1Out SjStage2 SjLeaves.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.P Require Import Sj_h_arith.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.B Require Import Layout Sj_akit Sj_stage2_defs Sj_stage2_traps Sj_stage2_guard.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Local Ltac addr_near k ::= let inb := eval vm_compute in (andb (Z.leb 0 k) (Z.ltb k 16384))%Z in lazymatch inb with true => idtac end.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Ltac pro_store_shadow :=
  match goal with
  | |- context [store_ok ?segs ?m ?a ?n] =>
      rewrite ?store_bytes_1';
      let Ea := addr_expr a in
      lazymatch Ea with
      | (Z.shiftr ?f 3 + ?c)%Z =>
          match goal with
          | H : wr_at segs m (Z.shiftr f 3 + 2147450880)%Z ?N |- _ =>
              let idx := eval vm_compute in (c - 2147450880)%Z in
              rewrite (wr_store_ok_at m (Z.shiftr f 3 + 2147450880)%Z N idx n a H ltac:(lia) ltac:(cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia) ltac:(unfold wa; f_equal; lia));
              cbv beta iota
          end
      end
  end.
Ltac pro_store_done :=
  lazymatch goal with
  | |- evt ?segs _ (MS _ _ _ _ _ (write_to_mem ?m ?a ?bs) _) =>
      let Ea := addr_expr a in
      lazymatch Ea with
      | (Z.shiftr ?f 3 + ?c)%Z =>
          (match goal with
           | H : wr_at segs m (Z.shiftr f 3 + 2147450880)%Z ?N |- _ =>
               let idx := eval vm_compute in (c - 2147450880)%Z in
               let HS := fresh "HSOK" in
               assert (HS : store_ok segs m a 1 = true)
                 by (apply (wr_store_ok_at m (Z.shiftr f 3 + 2147450880)%Z N idx 1%nat a H); [lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | unfold wa; f_equal; lia])
           end);
          store_done
      end
  | _ => idtac
  end.
Local Ltac solve_store ::= first [ solve_store0 | s2_store_wr | pro_store_shadow ].

Lemma land_m32 : forall x, (0 <= x < 2^64)%Z -> Z.land x 18446744073709551584 = (x - x mod 32)%Z.
Proof. intros x H. apply (land_align x 64 5); [reflexivity| lia| exact H]. Qed.

Definition s2_mid1 (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo THIS DOC : Z)
    : machine_state -> Prop :=
  fun ms' => exists (spa : Z) x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x18 x19 x22 x23 x25 x26 x27 x28 x29 x30 x31 (m1 : mem) (jf : list byte),
    ms' = MS (mkR (wz 0xb68dc) (wz spa) gp tp x5 x6 x7 sp (wz spa) (wz 1312) x11 x12 x13 x14 x15 x16 x17
                  x18 x19 (wz 2147450880) (wz DOC) x22 x23 (wz THIS) x25 x26 x27 x28 x29 x30 x31)
             F (wz 0x64cc0) fc None m1 (seg_rom bsegs)
    /\ (bv_unsigned sp - 432 <= spa <= bv_unsigned sp - 416)%Z /\ (spa mod 32 = 0)%Z
    /\ rw_cells bsegs m1 spa [CB 312 jf]
    /\ rw_cells bsegs m1 (bv_unsigned sp + -104) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ stk bsegs m1 (spa + 312) (bv_unsigned sp + -104)
    /\ stk bsegs m1 lo spa
    /\ munch [(lo, bv_unsigned sp)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1.

Section Pro.
  Lemma s2_pro1 : forall (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo THIS DOC : Z),
    stk bsegs m lo (bv_unsigned sp) -> (lo + 448 <= bv_unsigned sp)%Z -> (bv_unsigned sp mod 16 = 0)%Z -> (0x6cd000 <= lo)%Z ->
    mem_inv bsegs m ->
    ro_cells bsegs m g_GOT_shadow_offset_cell [C8 (Z_to_bv 64 g_shadow_memory_dynamic_address)] ->
    ro_cells bsegs m g_shadow_memory_dynamic_address [C8 (Z_to_bv 64 SHB)] ->
    ro_cells bsegs m g_GOT_detect_uar [C8 (Z_to_bv 64 g_detect_stack_use_after_return)] ->
    ro_cells bsegs m g_detect_stack_use_after_return [C4 (Z_to_bv 64 1)] ->
    evt bsegs (s2_mid1 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo THIS DOC)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz THIS) (wz DOC) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz 0xb6868) fc None m (seg_rom bsegs)).
  Proof.
    intros until DOC. intros ST ROOM AL GLO MI G1 G2 G3 G4.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    unfold g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return, SHB in *.
    pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
    assert (CASES : (bv_unsigned sp mod 32 = 0 \/ bv_unsigned sp mod 32 = 16)%Z).
    { pose proof (Z.mod_pos_bound (bv_unsigned sp) 32 ltac:(lia)). pose proof (Z.div_mod (bv_unsigned sp) 32 ltac:(lia)).
      pose proof (Z.div_mod (bv_unsigned sp) 16 ltac:(lia)). lia. }
    destruct CASES as [C0 | C16].
    -
      zstep. carve_frame 104%nat ST. rename FR into SAV. carve_frame 312%nat ST.
      lazymatch type of FR with rw_cells _ _ _ [CB 312 ?jk] => apply (rw_cells_split_CB bsegs m _ [] 312 jk [] [8;304]%nat) in FR; [|reflexivity] end.
      cbn [mk_CB_cells app] in FR.
      repeat match type of FR with context [CB ?n ?t] => lazymatch t with firstn _ _ => idtac | skipn _ _ => idtac end; let j := fresh "jq" in set (j := t) in FR; clearbody j end.
      do 16 gstep.
      rewrite (land_m32 (bv_unsigned sp + -416)) by lia.
      replace ((bv_unsigned sp + -416) mod 32)%Z with 0%Z
        by (pose proof (Z.div_mod (bv_unsigned sp) 32 ltac:(lia)); pose proof (Z.div_mod (bv_unsigned sp + -416) 32 ltac:(lia));
            pose proof (Z.mod_pos_bound (bv_unsigned sp + -416) 32 ltac:(lia)); lia).
      replace (bv_unsigned sp + -416 - 0)%Z with (bv_unsigned sp + -416)%Z by lia.
      do 7 gstep. clear G3 G4.
      grun_to 0xb68d0%Z.
      zstep. if_false.
      grun_to 0x64cc0%Z.
      apply evt_done. unfold s2_mid1.
      exists (bv_unsigned sp + -416)%Z. do 23 eexists. split; [reflexivity|].
      split; [lia|]. split; [pose proof (Z.div_mod (bv_unsigned sp) 32 ltac:(lia)); pose proof (Z.div_mod (bv_unsigned sp + -416) 32 ltac:(lia));
            pose proof (Z.mod_pos_bound (bv_unsigned sp + -416) 32 ltac:(lia)); lia|].
      lazymatch type of FR with rw_cells _ _ ?A ?l => pose proof (rw_cells_merge bsegs m1 A [] l []) as M end.
      cbn [app cells_size cells_bytes csize Nat.add] in M. rewrite app_nil_r in M. specialize (M FR).
      split; [exact M|]. split; [exact SAV|].
      split; [replace (bv_unsigned sp + -416 + 312)%Z with (bv_unsigned sp + -104)%Z by lia; apply stk_empty; lia|].
      split; [exact ST|]. split; [exact MU|]. split; [exact WM| exact MI].
    -
      zstep. carve_frame 104%nat ST. rename FR into SAV. carve_frame 16%nat ST. rename FR into GAPC. carve_frame 312%nat ST.
      lazymatch type of FR with rw_cells _ _ _ [CB 312 ?jk] => apply (rw_cells_split_CB bsegs m _ [] 312 jk [] [16;8;288]%nat) in FR; [|reflexivity] end.
      cbn [mk_CB_cells app] in FR.
      repeat match type of FR with context [CB ?n ?t] => lazymatch t with firstn _ _ => idtac | skipn _ _ => idtac end; let j := fresh "jq" in set (j := t) in FR; clearbody j end.
      do 16 gstep.
      rewrite (land_m32 (bv_unsigned sp + -416)) by lia.
      replace ((bv_unsigned sp + -416) mod 32)%Z with 16%Z
        by (pose proof (Z.div_mod (bv_unsigned sp) 32 ltac:(lia)); pose proof (Z.div_mod (bv_unsigned sp + -416) 32 ltac:(lia));
            pose proof (Z.mod_pos_bound (bv_unsigned sp + -416) 32 ltac:(lia)); lia).
      replace (bv_unsigned sp + -416 - 16)%Z with (bv_unsigned sp + -432)%Z by lia.
      do 7 gstep. clear G3 G4.
      grun_to 0xb68d0%Z.
      zstep. if_false.
      grun_to 0x64cc0%Z.
      apply evt_done. unfold s2_mid1.
      exists (bv_unsigned sp + -432)%Z. do 23 eexists. split; [reflexivity|].
      split; [lia|]. split; [pose proof (Z.div_mod (bv_unsigned sp) 32 ltac:(lia)); pose proof (Z.div_mod (bv_unsigned sp + -432) 32 ltac:(lia));
            pose proof (Z.mod_pos_bound (bv_unsigned sp + -432) 32 ltac:(lia)); lia|].
      lazymatch type of FR with rw_cells _ _ ?A ?l => pose proof (rw_cells_merge bsegs m1 A [] l []) as M end.
      cbn [app cells_size cells_bytes csize Nat.add] in M. rewrite app_nil_r in M. specialize (M FR).
      split; [exact M|]. split; [exact SAV|].
      split; [apply stk_of_rw_cells in GAPC; cbn [cells_size csize Nat.add] in GAPC;
              replace (bv_unsigned sp + -432 + 312)%Z with (bv_unsigned sp + -120)%Z by lia;
              replace (bv_unsigned sp + -104)%Z with (bv_unsigned sp + -120 + Z.of_nat 16)%Z by lia; exact GAPC|].
      split; [exact ST|]. split; [exact MU|]. split; [exact WM| exact MI].
  Qed.

  Definition s2_mid2 (sp gp tp : word) (spa f THIS DOC : Z) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
    fun ms' => exists x1 x5 x6 x7 x11 x12 x13 x16 x17 x18 x22 x23 x25 x27 x28 x29 x30 x31 (m1 : mem),
      ms' = MS (mkR x1 (wz spa) gp tp x5 x6 x7 sp (wz spa) (wz (Z.shiftr (THIS + 88)%Z 3)) x11 x12 x13 (wz (THIS + 88)%Z) (wz f) x16 x17
                    x18 (wz (SHA f)) (wz 2147450880) (wz DOC) x22 x23 (wz THIS) x25 (wz f) x27 x28 x29 x30 x31)
               F (wz 0xb6be8) fc None m1 (seg_rom bsegs)
      /\ munch [(f, f + 24); (SHA f, SHA f + 164)]%Z m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1.

  Lemma s2_pro2 : forall (sp gp tp x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x18 x19 x22 x23 x25 x26 x27 x28 x29 x30 x31 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (spa f THIS DOC : Z),
    (0 < f)%Z -> (f + 2048 < 2^47)%Z -> (0 <= THIS < 2^47)%Z ->
    wr_at bsegs m f 2040 -> wr_at bsegs m (SHA f) 256 -> mem_inv bsegs m ->
    evt bsegs (s2_mid2 sp gp tp spa f THIS DOC F fc m)
      (MS (mkR x1 (wz spa) gp tp x5 x6 x7 sp (wz spa) (wz f) x11 x12 x13 x14 x15 x16 x17
               x18 x19 (wz 2147450880) (wz DOC) x22 x23 (wz THIS) x25 x26 x27 x28 x29 x30 x31)
          F (wz 0xb68dc) fc None m (seg_rom bsegs)).
  Proof.
    intros until DOC. intros F0 F1 T0 FW SW MI.
    pose proof (munch_refl [(f, f + 24); (SHA f, SHA f + 164)]%Z m) as MU. pose proof (wmono_refl bsegs m) as WM.
    assert (SHR : (0 <= Z.shiftr f 3 < 2^44)%Z).
    { rewrite Z.shiftr_div_pow2 by lia. split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]. }
    grun_to 0xb68e4%Z.
    zstep. if_cases KF; zify_cond KF; [|exfalso; lia].
    grun_to 0xb6938%Z.
    repeat (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) => lazymatch pc with 0xb6be8%Z => fail | _ => idtac end end;
            zstep; first [ pro_store_done | g_store_done ]).
    apply evt_done. unfold s2_mid2. do 19 eexists. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM| exact MI].
  Qed.
End Pro.
