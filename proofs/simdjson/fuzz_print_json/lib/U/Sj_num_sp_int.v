(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Lib Require Import Tac Arr Bytes StoreFast FP.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Sj Require Import SjNumber SjNumSwar SjNumU.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.P Require Import Sj_num_kit Sj_num_walk.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.U Require Import Sj_num_kitu Sj_num_kitn Sj_num_kitw Sj_num_sp_defs Sj_num_sp_dc Sj_num_sp_pdefs Sj_num_sp_pns Sj_num_sp_frac2.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac solve_load ::= first [ solve_load_base | num_load_hook | solve_load_image ].
Local Ltac solve_store ::= first [ num_solve_store0 | num_store_hook ].
Local Ltac nnorm ::= nnorm_w.

Section SPUINT.
  Variable E : spuenv.
  Hypothesis OK : spu_ok E.
  Hypothesis HSET : spu_memset_stmt.
  Hypothesis HPM : spu_pm_stmt.
  Hypothesis HPDC : spu_pdc_stmt.
  Hypothesis HNDC : spu_ndc_stmt.
  Notation A := (q_A E).
  Notation LAST := (q_LAST E).
  Notation OUT := (q_OUT E).

  Notation IS pc IP c0 xra xt0 xt1 xt2 xs0 xs1 xa0 xa2 xa4 xs2 xs3 xs4 xs5 xs6 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm :=
    (SPS E pc xra xt0 xt1 xt2 xs0 xs1 xa0 (Z_to_bv 64 LAST) xa2 (Z_to_bv 64 53) xa4 c0 (Z_to_bv 64 IP) (Z_to_bv 64 46)
         xs2 xs3 xs4 xs5 xs6 (Z_to_bv 64 OUT) xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm).

  Lemma spu_c40 : forall (IP IL : Z) (c0 spl : word) xra xt2 xs0 xs1 xa0 xa2 xa4 xs2 xs3 xs4 xs5 xs6 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm,
    SPUINV0 E mm spl -> frm0 xfc -> (A <= IP)%Z -> (1 <= IL)%Z -> (IP + IL <= LAST)%Z -> sp_ge48 E IP (IP + IL) ->
    evt usegs (spu_post E) (IS 0x5bc9c IP c0 xra (Z_to_bv 64 (IP + IL)) (Z_to_bv 64 IL) xt2 xs0 xs1 xa0 xa2 xa4 xs2 xs3 xs4 xs5 xs6 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm).
  Proof using OK HSET HPM HPDC HNDC.
    intros until mm. intros INV FRM H1 H2 H3 G1.
    pose proof INV as INV0. spu_open0 INV0. spu_env OK.
    kwalk ltac:(fun pc => lazymatch pc with
      | 0x5d1bc%Z => u_trap_b pc
      | 0x5bcac%Z => first [ eapply evt_eq; [| eapply (spu_c50 E OK HSET HPM HPDC HNDC spl)]; [num_st_eq | exact INV | assumption] | fail 100 "cut" pc ]
      | 0x5bcf4%Z => first [ eapply evt_eq; [| eapply (spu_c98 E OK HSET HPM HPDC HNDC IP IL c0 spl)]; [num_st_eq | exact INV | assumption | lia | lia | lia | exact G1]
                           | fail 100 "cut" pc ]
      end).
  Qed.

  Ltac int_cuts INV spl IP c0 :=
    fun pc => lazymatch pc with
      | 0x5d1bc%Z => u_trap_b pc
      | 0x5b900%Z => first [ eapply evt_eq; [| eapply (spu_8a4 E OK HSET HPM HPDC HNDC spl)]; [num_st_eq | exact INV | assumption] | fail 100 "cut" pc ]
      | 0x5bc9c%Z => first [ eapply evt_eq; [| eapply (spu_c40 IP _ c0 spl)]; [num_st_eq | exact INV | assumption | lia | lia | lia |];
                             first [ assumption
                                   | lazymatch goal with G : sp_ge48 E IP ?pe |- sp_ge48 E IP ?pe' => replace pe' with pe by lia; exact G end ]
                           | fail 100 "cut" pc ]
      end.

  Lemma spu_c38 : forall (IP pe : Z) (c0 spl : word) xra xt1 xt2 xs0 xs1 xa0 xa2 xa4 xs2 xs3 xs4 xs5 xs6 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm,
    SPUINV0 E mm spl -> frm0 xfc -> (A <= IP <= pe)%Z -> (pe <= LAST)%Z -> sp_ge48 E IP pe ->
    evt usegs (spu_post E) (IS 0x5bc94 IP c0 xra (Z_to_bv 64 pe) xt1 xt2 xs0 xs1 xa0 xa2 xa4 xs2 xs3 xs4 xs5 xs6 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm).
  Proof using OK HSET HPM HPDC HNDC.
    intros until mm. intros INV FRM H1 H2 G1.
    pose proof INV as INV0. spu_open0 INV0. spu_env OK.
    kwalk ltac:(int_cuts INV spl IP c0).
  Qed.

  Lemma spu_L1 : forall (f : nat) (IP pe : Z) (c0 spl : word) xra xt2 xs0 xs1 xa2 xa4 xs2 xs3 xs4 xs5 xs6 xs8 xs9 xs10 xs11 xt5 xt6 xF xfc mm,
    SPUINV0 E mm spl -> frm0 xfc -> (A <= IP < pe)%Z -> (pe <= LAST)%Z -> sp_ge48 E IP pe -> (LAST - pe <= Z.of_nat f)%Z ->
    evt usegs (spu_post E) (IS 0x5bac0 IP c0 xra (Z_to_bv 64 pe) (Z_to_bv 64 10) xt2 xs0 xs1 (Z_to_bv 64 2) xa2 xa4 xs2 xs3 xs4 xs5 xs6 xs8 xs9 xs10 xs11 (Z_to_bv 64 pe) (Z_to_bv 64 9) xt5 xt6 xF xfc mm).
  Proof using OK HSET HPM HPDC HNDC.
    intros f. induction f as [|f IH]; intros until mm; intros INV FRM H1 H2 G1 Hf.
    {   assert (pe = LAST) by lia. subst pe.
      pose proof INV as INV0. spu_open0 INV0. spu_env OK.
      kwalk ltac:(int_cuts INV spl IP c0). }
    pose proof INV as INV0. spu_open0 INV0. spu_env OK.
    pose proof (sp_tb_range E pe) as Rp. unfold sp_tb in Rp.
    kstep.
    kwalk ltac:(fun pc => lazymatch pc with
      | 0x5d1bc%Z => u_trap_b pc
      | 0x5b900%Z => first [ exfalso; lia | fail 100 "cut" pc ]
      | 0x5bc9c%Z => first [ eapply evt_eq; [| eapply (spu_c40 IP _ c0 spl)]; [num_st_eq | exact INV | assumption | lia | lia | lia |];
                             lazymatch goal with G : sp_ge48 E IP ?pe0 |- sp_ge48 E IP ?pe' => replace pe' with pe0 by lia; exact G end
                           | fail 100 "cut" pc ]
      | 0x5bc94%Z => first [ eapply evt_eq; [| eapply (spu_c38 IP pe c0 spl)]; [num_st_eq | exact INV | assumption | lia | lia | exact G1] | fail 100 "cut" pc ]
      | 0x5bac0%Z => first [ eapply evt_eq; [| eapply (IH IP (pe + 1)%Z c0 spl)]; [num_st_eq | exact INV | assumption | lia | lia | | lia];
                             apply sp_ge48_snoc; [exact G1 | unfold sp_tb; lia]
                           | fail 100 "cut" pc ]
      end).
  Qed.

  Ltac ge48_peel IP :=
    let i := fresh "i" in let Hi := fresh "Hi" in intros i Hi;
    assert (C : (i = IP \/ i = IP + 1 \/ i = IP + 2 \/ i = IP + 3 \/ i = IP + 4)%Z) by lia;
    destruct C as [-> | [-> | [-> | [-> | ->]]]]; unfold sp_tb; lia.

  Lemma spu_95c : forall (IP : Z) (c0 spl : word) xra xt0 xt1 xs0 xs1 xa0 xa2 xa4 xs2 xs3 xs4 xs5 xs6 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm,
    SPUINV0 E mm spl -> frm0 xfc -> (A <= IP < LAST)%Z ->
    evt usegs (spu_post E) (IS 0x5b9b8 IP c0 xra xt0 xt1 (Z_to_bv 64 (sp_tb E IP)) xs0 xs1 xa0 xa2 xa4 xs2 xs3 xs4 xs5 xs6 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm).
  Proof using OK HSET HPM HPDC HNDC.
    intros until mm. intros INV FRM H1.
    pose proof INV as INV0. spu_open0 INV0. spu_env OK.
    pose proof (sp_tb_range E IP) as R0. pose proof (sp_tb_range E (IP + 1)) as R1. pose proof (sp_tb_range E (IP + 2)) as R2.
    pose proof (sp_tb_range E (IP + 3)) as R3. pose proof (sp_tb_range E (IP + 4)) as R4.
    unfold sp_tb in R0, R1, R2, R3, R4 |- *.
    kwalk ltac:(fun pc => lazymatch pc with
      | 0x5d1bc%Z => u_trap_b pc
      | 0x5bc94%Z => first [ eapply evt_eq; [| eapply (spu_c38 IP _ c0 spl)]; [num_st_eq | exact INV | assumption | lia | lia | ge48_peel IP] | fail 100 "cut" pc ]
      | 0x5bac0%Z => first [ eapply evt_eq; [| eapply (spu_L1 (Z.to_nat LAST) IP (IP + 5)%Z c0 spl)]; [num_st_eq | exact INV | assumption | lia | lia | ge48_peel IP | lia]
                           | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma spu_854 : forall (spl : word) xra xt0 xt1 xt2 xs0 xs1 xa0 xa2 xa4 xs2 xs3 xs4 xs5 xs6 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm,
    SPUINV0 E mm spl -> frm0 xfc ->
    evt usegs (spu_post E) (IS 0x5b8b0 (q_FIRST E) (Z_to_bv 64 1) xra xt0 xt1 xt2 xs0 xs1 xa0 xa2 xa4 xs2 xs3 xs4 xs5 xs6 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm).
  Proof using OK HSET HPM HPDC HNDC.
    intros until mm. intros INV FRM.
    pose proof INV as INV0. spu_open0 INV0. spu_env OK.
    kwalk ltac:(fun pc => lazymatch pc with
      | 0x5d1bc%Z => u_trap_b pc
      | 0x5baec%Z => first [ eapply evt_eq; [| eapply (spu_a90 E OK HSET HPM HPDC HNDC spl)]; [num_st_eq | exact INV | assumption] | fail 100 "cut" pc ]
      | 0x5bf90%Z => first [ eapply evt_eq; [| eapply (spu_f34 E OK HSET HPM HPDC HNDC spl)]; [num_st_eq | exact INV | assumption] | fail 100 "cut" pc ]
      | 0x5b8f4%Z => first [ exfalso; lia | fail 100 "cut" pc ]
      | 0x5b9b8%Z => first [ eapply evt_eq; [| eapply (spu_95c _ _ spl)]; [unfold sp_tb; num_st_eq | exact INV | assumption | lia] | fail 100 "cut" pc ]
      end).
  Qed.

  Ltac peel_cell FR H :=
    lazymatch type of FR with
    | rw_cells ?s ?m ?A0 (?c :: ?rest) =>
        change (c :: rest) with ([c] ++ rest) in FR; apply num_rw_cells_app in FR; destruct FR as [H FR];
        cbn [cells_size csize Nat.add] in FR;
        lazymatch type of FR with
        | rw_cells _ _ (?b + ?k + Z.of_nat ?n)%Z _ =>
            let v := eval vm_compute in (k + Z.of_nat n)%Z in replace (b + k + Z.of_nat n)%Z with (b + v)%Z in FR by lia
        end
    end.

  Theorem spu_body_spec : forall t0 t1 t2 a6 a7 t3 t4 t5 t6 F fc v0,
    mem_inv usegs (q_m0 E) -> frm0 fc -> stk usegs (q_m0 E) (q_lo E) (q_SP E) -> bytes_at usegs (q_m0 E) A (q_txt E) ->
    rw_cells usegs (q_m0 E) OUT [C8 v0] ->
    evt usegs (spu_post E)
      (MS (mkR (q_ra E) (q_sp E) (q_gp E) (q_tp E) t0 t1 t2 (q_s0 E) (q_s1 E) (Z_to_bv 64 (q_FIRST E)) (Z_to_bv 64 LAST) (Z_to_bv 64 OUT)
               (Z_to_bv 64 53) (Z_to_bv 64 SPATH_A4) (Z_to_bv 64 1) a6 a7
               (q_s2 E) (q_s3 E) (q_s4 E) (q_s5 E) (q_s6 E) (q_s7 E) (q_s8 E) (q_s9 E) (q_s10 E) (q_s11 E) t3 t4 t5 t6)
          F (Z_to_bv 64 SPATHU_ENTRY) fc None (q_m0 E) (seg_rom usegs)).
  Proof using OK HSET HPM HPDC HNDC.
    intros t0 t1 t2 a6 a7 t3 t4 t5 t6 F fc v0 MI FRM ST TXT OUTC.
    unfold SPATHU_ENTRY.
    pose proof (munch_refl (spu_W E) (q_m0 E)) as MU. pose proof (wmono_refl usegs (q_m0 E)) as WM. unfold spu_W in MU.
    pose proof OK as OK0. spu_env OK0.
    assert (LO0 : (0 <= q_lo E)%Z) by (destruct ST as [? _]; assumption).
    set (m := q_m0 E) in MI, ST, TXT, OUTC, MU at 2, WM at 2 |- * at 2. clearbody m.
    step.
    carve_frame 704%nat ST.
    apply (rw_cells_split_CB usegs m _ [] 704 junk [] [8;8;24;8;32;8;504;8;8;8;8;8;8;8;8;8;8;8;8;8;8]%nat) in FR; [|reflexivity].
    cbn [mk_CB_cells app] in FR.
    repeat match type of FR with context [CB ?n ?t] => lazymatch t with firstn _ _ => idtac end; let j := fresh "j" in set (j := t) in FR; clearbody j end.
    do 13 step.
    peel_cell FR PADa. peel_cell FR PADb. peel_cell FR PNS. peel_cell FR NEGB. peel_cell FR SPANS. peel_cell FR PERR. peel_cell FR BG. peel_cell FR DGC.
    apply (num_cb8_c8 usegs _ _ [] []) in PADb. cbn [app] in PADb.
    assert (PAD0 : rw_cells usegs _ (q_SP E + -704) ([CB 8 _] ++ [C8 _])) by (apply num_rw_cells_app; split; [exact PADa | cbn [cells_size csize Nat.add]; replace (q_SP E + -704 + Z.of_nat 8)%Z with (q_SP E + -696)%Z by lia; exact PADb]).
    cbn [app] in PAD0. clear PADa PADb.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
      lazymatch type of PAD0 with rw_cells _ _ _ [_; C8 ?spl] =>
        assert (INV : SPUINV0 E m1 spl) by (unfold spu_W, SPATHU_STACK, NDCU_STACK, P5U_STACK, LMU_STACK, LAFU_STACK; spu_close0) end end.
    unfold SPATH_A4.
    kwalk ltac:(fun pc => lazymatch pc with
      | 0x5d1bc%Z => u_trap_b pc
      | 0x5b8b0%Z => first [ eapply evt_eq; [| eapply spu_854]; [num_st_eq | exact INV | exact FRM] | fail 100 "cut" pc ]
      end).
  Qed.
End SPUINT.

Theorem spathu_spec : spu_memset_stmt -> spu_pm_stmt -> spu_pdc_stmt -> spu_ndc_stmt -> spathu_stmt_g usegs SPATHU_ENTRY NUMU_GTOP.
Proof.
  intros HSET HPM HPDC HNDC. unfold spathu_stmt_g. intros until v0. intros MI FRM ST ROOM GTOP SP16 TXT TLO TMAX A0 HF HL OUTC HOUT HOUT8.
  set (E := mkSpuEnv ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 A FIRST LAST OUT lo txt m).
  assert (OK : spu_ok E) by (constructor; cbn; assumption).
  exact (spu_body_spec E OK HSET HPM HPDC HNDC t0 t1 t2 a6 a7 t3 t4 t5 t6 F fc v0 MI FRM ST TXT OUTC).
Qed.
