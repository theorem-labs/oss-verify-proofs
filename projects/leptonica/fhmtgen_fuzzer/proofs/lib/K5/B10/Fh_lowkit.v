(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.B10 Require Import ImageA.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.Lib Require Import RzCPS NodesA SysStep Arr.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.Lib Require Import StoreFast.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.PG Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.B10 Require Import Layout.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.B10 Require Import RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit Lept_iface Lept_env LeptC_kit LeptL_kit Lept_deserkit D_iface D_defs Gm_iface Fh_iface LeptB_guard LeptB_guard2.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Definition FHL_EXIT : Z := 0xb3fac.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition fhl_case (RT : rt_sig) (k : Z) : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (rd rs w h wpl : Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 (rd + 4 * (32 * wpl + 1)) -> a1 = Z_to_bv 64 w -> a2 = Z_to_bv 64 h -> a3 = Z_to_bv 64 wpl ->
  a4 = Z_to_bv 64 (rs + 4 * (32 * wpl + 1)) -> a5 = Z_to_bv 64 wpl -> a6 = Z_to_bv 64 k ->
  0 < w -> 0 < h -> w + 64 <= 20000 -> h + 64 <= 20000 -> wpl = (w + 64 + 31) / 32 ->
  chunk (rt_live RT Σ) rd (4 * (wpl * (h + 64))) -> chunk (rt_live RT Σ) rs (4 * (wpl * (h + 64))) -> rd <> rs ->
  lenv RT Σ m sp lo (LSTK 1) ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_fhmtgen_low_1 m)))
    (fun c => exists (Σ' : rts RT) (rv : word),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 rv m' ms
          /\ lpost RT Σ Σ' m m' sp lo /\ keeps RT Σ Σ' sp [(rd, rd + 4 * (wpl * (h + 64)))] m m') c
       /\ rt_live RT Σ' = rt_live RT Σ
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ <= rt_credit RT Σ').

Lemma fhmtgen_low_1_of_cases : forall RT : rt_sig,
  fhl_case RT 0 -> fhl_case RT 1 -> fhl_case RT 2 -> fhl_case RT 3 -> fhl_case RT 4 ->
  fhl_case RT 5 -> fhl_case RT 6 -> fhl_case RT 7 -> fhl_case RT 8 -> fhl_case RT 9 -> fhmtgen_low_1_cps RT.
Proof.
  intros RT C0 C1 C2 C3 C4 C5 C6 C7 C8 C9.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
    rd rs w h wpl index FDO MST TP A0 A1 A2 A3 A4 A5 A6 IDX.
  assert (CS : index = 0 \/ index = 1 \/ index = 2 \/ index = 3 \/ index = 4 \/ index = 5 \/ index = 6 \/ index = 7 \/ index = 8 \/ index = 9) by lia.
  destruct CS as [->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]];
    [ eapply C0 | eapply C1 | eapply C2 | eapply C3 | eapply C4 | eapply C5 | eapply C6 | eapply C7 | eapply C8 | eapply C9 ]; eassumption.
Qed.

(* [comment removed for export] *)
Lemma fhl_geom : forall w h wpl, 0 < w -> 0 < h -> w + 64 <= 20000 -> h + 64 <= 20000 -> wpl = (w + 64 + 31) / 32 ->
  1 <= (w + 31) / 32 <= 623 /\ wpl = (w + 31) / 32 + 2 /\ 32 <= w + 31 < 2^31 /\ 0 < wpl * (h + 64) <= 12520000.
Proof.
  intros w h wpl W H WC HC ->.
  assert (E : (w + 64 + 31) / 32 = (w + 31) / 32 + 2) by (Z.div_mod_to_equations; lia).
  assert (P : 1 <= (w + 31) / 32 <= 623) by (Z.div_mod_to_equations; lia).
  rewrite E. repeat split; try lia. nia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition fhl_exit (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (W : list (Z * Z)) (rd rs ld sb : Z) (ns : nat)
    (wss : list word) : machine_state -> Prop :=
  fun ms' => exists (ra' t0' t1' t2' s0' s1' a0' a1' a2' a3' a4' a5' a6' a7' s2' s3' s4' s5' s6' s7' s8' s9' s10' s11' t3' t4' t5' t6' : word)
                    (m' : mem) (wsd' slots : list word),
    ms' = MS (mkR ra' sp gp tp t0' t1' t2' s0' s1' a0' a1' a2' a3' a4' a5' a6' a7' s2' s3' s4' s5' s6' s7' s8' s9' s10' s11' t3' t4' t5' t6')
             F (Z_to_bv 64 FHL_EXIT) fc None m' (seg_rom asegs)
    /\ munch W m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ u32arr asegs m' rd wsd' /\ Z.of_nat (length wsd') = ld /\ u32arr asegs m' rs wss
    /\ length slots = ns /\ rw_cells asegs m' sb (map C8 slots).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac idx_of A E :=
  lazymatch E with
  | A => constr:(0%Z)
  | (A + 4 * ?t)%Z => constr:(t)
  | (?E' + 4 * ?t)%Z => let i := idx_of A E' in constr:((i + t)%Z)
  | (?E' - 4 * ?t)%Z => let i := idx_of A E' in constr:((i - t)%Z)
  | (?E' + ?t * 4)%Z => let i := idx_of A E' in constr:((i + t)%Z)
  | (?E' - ?t * 4)%Z => let i := idx_of A E' in constr:((i - t)%Z)
  | (?E' + Zpos ?p)%Z => let c := eval vm_compute in (Zpos p / 4)%Z in let i := idx_of A E' in constr:((i + c)%Z)
  | (?E' + Zneg ?p)%Z => let c := eval vm_compute in (Zneg p / 4)%Z in let i := idx_of A E' in constr:((i + c)%Z)
  | (?E' - Zpos ?p)%Z => let c := eval vm_compute in (Zpos p / 4)%Z in let i := idx_of A E' in constr:((i - c)%Z)
  end.

(* [comment removed for export] *)
Ltac rd4 A :=
  next_instr ltac:(fun i => lazymatch i with
    | Load SZ4 _ _ ?rs ?imm => reg_val rs ltac:(fun v => lazymatch v with
        | Z_to_bv 64 ?E =>
            let k := eval vm_compute in (bv_signed imm) in
            let EA := lazymatch k with 0%Z => constr:(E) | _ => constr:((E + k)%Z) end in
            let idx := idx_of A EA in
            lazymatch goal with UA : u32arr asegs ?m A ?ws |- evt _ _ (MS _ _ _ _ _ ?m _) =>
              let wv := fresh "wv" in let NTH := fresh "NTH" in let R := fresh "RD" in
              destruct (u32arr_nth ws idx ltac:(lia)) as (wv & NTH);
              pose proof (u32arr_read asegs m A ws idx wv (wa EA) UA NTH ltac:(lia) ltac:(f_equal; lia)) as R;
              lstep; clear R NTH
            end
        end)
    end).

(* [comment removed for export] *)
Ltac wr4 A :=
  next_instr ltac:(fun i => lazymatch i with
    | Store SZ4 ?rs1 _ ?imm => reg_val rs1 ltac:(fun v => lazymatch v with
        | Z_to_bv 64 ?E =>
            let k := eval vm_compute in (bv_signed imm) in
            let EA := lazymatch k with 0%Z => constr:(E) | _ => constr:((E + k)%Z) end in
            let idx := idx_of A EA in
            arr_sw A idx EA
        end)
    end).

(* [comment removed for export] *)
Ltac abs_store_val := next_instr ltac:(fun i => lazymatch i with
  | Store _ _ ?rs2 _ => reg_val rs2 ltac:(fun v => lazymatch v with
      | Z_to_bv 64 ?e => let x := fresh "sv" in set (x := v) in *; clearbody x
      | _ => idtac end) end).

(* [comment removed for export] *)
Ltac hide_disj := repeat match goal with H : _ \/ _ |- _ => hide H end.

(* [comment removed for export] *)
Ltac is_store := next_instr ltac:(fun i => lazymatch i with Store _ _ _ _ => idtac end).
Ltac fwalk1 As Ad :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) => first [ shbr | shbr0 | shbr_inv | shbr_x3 | br | progress guard_fix; try br ]
  | |- evt _ _ (MS _ _ (Z_to_bv 64 _) _ _ _ _) =>
      first [ shload; lstep; clear_shl | rd4 As | abs_store_val; unhide_all; wr4 Ad; hide_disj | is_store; unhide_all; lstep; hide_disj
            | lstep; try sb_fix; try fix_land32; shnorm ]
  end.
Ltac fwalk As Ad stops := repeat (tryif at_stop stops then fail else fwalk1 As Ad).

(* [comment removed for export] *)
Ltac regtree_eq slv :=
  lazymatch goal with
  | |- Z_to_bv 64 _ = Z_to_bv 64 _ => first [ reflexivity | apply (f_equal (Z_to_bv 64)); slv ]
  | |- _ => first [ reflexivity | f_equal; regtree_eq slv ]
  end.
Ltac canon_reg_with n C slv :=
  reg_val (Z_to_bv 5 n) ltac:(fun v => lazymatch v with
    | Z_to_bv 64 C => idtac
    | Z_to_bv 64 ?E =>
        lazymatch goal with |- evt _ _ (MS ?R _ _ _ _ _ _) =>
          replace R with (@bvmap_set 5 word (Z_to_bv 5 n) (Z_to_bv 64 C) R) by (norm_regset; regtree_eq slv);
          norm_regset
        end
    end).
Ltac canon_reg n C := canon_reg_with n C ltac:(clear; lia).
(* [comment removed for export] *)
Ltac join_cells H1 H2 :=
  lazymatch type of H1 with rw_cells _ ?m ?A ?cs1 =>
  lazymatch type of H2 with rw_cells _ m ?A2 ?cs2 =>
    let v := eval vm_compute in (Z.of_nat (cells_size cs1)) in
    let N := fresh "JN" in
    assert (N : rw_cells asegs m A (cs1 ++ cs2))
      by (apply (proj2 (rw_cells_app m A cs1 cs2)); split; [exact H1|];
          change (Z.of_nat (cells_size cs1)) with v; replace (A + v) with A2 by lia; exact H2);
    cbn [app] in N; clear H1 H2; rename N into H1
  end end.

(* [comment removed for export] *)
Ltac slots_c8 H :=
  repeat (lazymatch type of H with rw_cells _ ?m ?A ?cs =>
    let rec go pre rest :=
      lazymatch rest with
      | CB 8 ?b :: ?post => apply (cb8_c8_in m A pre post b) in H; cbn [app] in H
      | ?c :: ?post => let pre' := eval cbn [app] in (pre ++ [c]) in go pre' post
      end in
    go (@nil cell) cs end).

(* [comment removed for export] *)
Ltac show_rr n := reg_val (Z_to_bv 5 n) ltac:(fun v => idtac "REG" n "=" v).
Ltac rregs := show_rr 1; show_rr 2; show_rr 5; show_rr 6; show_rr 7; show_rr 8; show_rr 9;
  show_rr 10; show_rr 11; show_rr 12; show_rr 13; show_rr 14; show_rr 15; show_rr 16; show_rr 17;
  show_rr 18; show_rr 19; show_rr 20; show_rr 21; show_rr 22; show_rr 23; show_rr 24; show_rr 25; show_rr 26; show_rr 27;
  show_rr 28; show_rr 29; show_rr 30; show_rr 31.
