(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep FP StoreFast.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Sj Require Import SjNumber SjNumU.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.P Require Import Rnd Sj_num_kit Sj_num_walk.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.B Require Import Layout RT_iface D_defs D_kit D_clx Sj_akit Sj_acps Sj_hkit Sj_rtf
  Sj_num_akit Sj_num_amem Sj_num_iface Sj_num_bkit Sj_num_bdefs Sj_num_lm_kit Sj_num_nd_defs Sj_num_nd_b3.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac solve_load ::= first [ solve_load_base | asan_load_hook | asan_ptr_hook | asan_zr_hook | asan_zc_hook | asan_zcp_hook | num_load_hook | solve_load_image ].
Local Ltac solve_store ::= first [ num_solve_store0 | num_store_hook ].
Ltac nnorm_ndc :=
  repeat match goal with
  | |- context [bv_swrap 32 (?p mod 4294967296 + ?k)] => rewrite (swrap32_zext_add p k) by lia
  | |- context [bv_swrap 32 (?p mod 4294967296)] => rewrite (swrap32_zext p) by lia
  end;
  nnorm_u.
Local Ltac nnorm ::= nnorm_ndc.
Local Ltac num_abstract_data ::= num_abstract_data_u.

Section NDB.
  Variables (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (X p2 e lo d spq f : Z) (m0 : mem).
  Notation SP := (bv_unsigned sp).
  Notation S := (f / 8 + 2147450880)%Z.
  Hypothesis SPQ : (0 <= d <= 16 /\ spq = SP - 160 - d)%Z.
  Hypothesis ROOM : (lo + NDCB_STACK <= SP)%Z.
  Hypothesis TOP : (SP + 16 <= USTACK_TOP)%Z.
  Hypothesis F64 : (f mod 64 = 0)%Z.
  Hypothesis FLO : (0x6cd000 <= f /\ f + 1016 <= lo)%Z.
  Hypothesis FSH : (f + 1016 <= S \/ S + 127 <= f)%Z.
  Hypothesis FS0 : (0 <= S /\ S + 127 <= lo)%Z.
  Hypothesis X8 : (X mod 8 = 0)%Z.
  Hypothesis XR : (0x6cd000 <= X /\ X + 504 <= lo)%Z.
  Hypothesis XSH : (X + 504 <= X / 8 + 2147450880 \/ X / 8 + 2147450880 + 63 <= X)%Z.
  Hypothesis XS0 : (0 <= X / 8 + 2147450880 /\ X / 8 + 2147450880 + 63 <= lo)%Z.
  Hypothesis SEP : ((X + 504 <= f \/ f + 1024 <= X) /\ (X + 504 <= S \/ S + 128 <= X)
       /\ (X / 8 + 2147450880 + 63 <= f \/ f + 1024 <= X / 8 + 2147450880)
       /\ (X / 8 + 2147450880 + 63 <= S \/ S + 128 <= X / 8 + 2147450880))%Z.
  Hypothesis PR : (- NDCB_RANGE <= p2 <= NDCB_RANGE)%Z.
  Hypothesis ER : (0 <= e <= NDCB_RANGE)%Z.
  Variable Q : machine_state -> Prop.
  Collection NDH := SPQ ROOM TOP F64 FLO FSH FS0 X8 XR XSH XS0 SEP PR ER.
  Notation NDINV := (nd_inv X spq f m0).

  Notation NDS pc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs5 xt3 xt4 xt5 xt6 mm :=
    (MS (mkR xra (Z_to_bv 64 spq) gp tp xt0 xt1 xt2 sp (Z_to_bv 64 spq) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
             xs2 (Z_to_bv 64 S) (Z_to_bv 64 (p2 mod 4294967296)) xs5 (Z_to_bv 64 X) (Z_to_bv 64 (- e)) (Z_to_bv 64 (f + 32)) (Z_to_bv 64 f) (Z_to_bv 64 2147450880)
             (Z_to_bv 64 (0 - p2)) xt3 xt4 xt5 xt6)
        F (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).

  Ltac nd_env :=
    destruct SPQ as [Hd Hspq]; pose proof ROOM as ROOM'; pose proof TOP as TOP'; unfold NDCB_STACK, P5B_STACK, LMB_STACK, RT_STACK, USTACK_TOP in ROOM', TOP';
    pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR; cbn in SPR;
    pose proof PR as PR'; pose proof ER as ER'; unfold NDCB_RANGE in PR', ER';
    pose proof F64 as F64'; pose proof FLO as FLO'; pose proof FSH as FSH'; pose proof FS0 as FS0'; pose proof X8 as X8'; pose proof XR as XR';
    pose proof XSH as XSH'; pose proof XS0 as XS0'; pose proof SEP as SEP';
    pose proof (repeat_length (Z_to_bv 8 0) 63) as RL; pose proof (f64_8 f F64) as F8.

  Hypothesis KP5 : nd_p5_k sp gp tp F fc X p2 e spq f m0 Q.
  Hypothesis KSHT : nd_shlt_k sp gp tp F fc X p2 e spq f m0 Q.
  Hypothesis KSHX : nd_shlx_k sp gp tp F fc X p2 e spq f m0 Q.
  Hypothesis K55C : nd_55c_k sp gp tp F fc X p2 e spq f m0 Q.
  Notation nd_2d4 := (nd_2d4 sp gp tp F fc X p2 e lo d spq f m0 SPQ ROOM TOP F64 FLO FSH FS0 X8 XR XSH XS0 SEP PR ER Q K55C).

  Lemma nd_2b8 : forall (q2 : Z) xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs5 xt3 xt4 xt5 xt6 (mm : mem) xlen tlen,
    NDINV (repeat (Z_to_bv 8 0) 63) mm xlen tlen -> (-2412352 <= q2 <= 2412352)%Z ->
    evt bsegs Q (NDS 0xec338 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 q2) xs5 xt3 xt4 xt5 xt6 mm).
  Proof using NDH KSHT KSHX K55C.
    intros until tlen. intros INV HQ. pose proof INV as INV0. nd_open INV0. nd_env.
    bwalk ltac:(fun pc => lazymatch pc with
      | 0xec688%Z => u_trap pc
      | 0xec354%Z => first [ eapply evt_eq; [| eapply nd_2d4]; [num_st_eq | exact INV] | fail 100 "cut" pc ]
      | 0xedef8%Z => first [ rewrite (Z.mod_small q2 4294967296) by lia; eapply evt_eq; [| eapply (KSHT q2)]; [num_st_eq | exact INV | lia]
                           | rewrite (Z.mod_small (0 - q2) 4294967296) by lia; eapply evt_eq; [| eapply (KSHX (0 - q2)%Z)]; [num_st_eq | exact INV | lia]
                           | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma nd_288 : forall (t7 : Z) xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 w xt3 xt4 xt5 xt6 c0 c8 c16 c32 c40 xbs tbs jl (mm : mem) xlen,
    rw_cells bsegs mm spq (nd_spill f c0 c8 c16 c32 c40) ->
    u8arr bsegs mm X xbs -> length xbs = 496%nat -> rw_cells bsegs mm (X + 496) [C2 (Z_to_bv 64 xlen)] -> (0 <= xlen <= 62)%Z ->
    bytes_at bsegs mm (X / 8 + 2147450880) (repeat (Z_to_bv 8 0) 63) ->
    u8arr bsegs mm (f + 32) tbs -> length tbs = 496%nat -> rw_cells bsegs mm (f + 528) [CB 2 jl] ->
    rw_cells bsegs mm (f / 8 + 2147450884) [CB 63 (repeat (Z_to_bv 8 0) 63)] ->
    mem_inv bsegs mm -> munch (nd_W X spq f) m0 mm -> wmono bsegs m0 mm -> (-1076 <= t7 <= 3020)%Z ->
    evt bsegs Q (NDS 0xec308 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 w (Z_to_bv 64 t7) xt3 xt4 xt5 xt6 mm).
  Proof using NDH KP5 KSHT KSHX K55C.
    intros until xlen. intros SPILL XA XL XN LEN ZR TA TL TN TSH MI MU WM H7. unfold nd_spill in SPILL. unfold nd_W in MU. nd_env.
    assert (DW : IsData w) by exact I.
    bwalk ltac:(fun pc => lazymatch pc with
      | 0xec688%Z => u_trap pc
      | 0xec338%Z => first [ num_cur_mem ltac:(fun m1 => assert (INV1 : NDINV (repeat (Z_to_bv 8 0) 63) m1 xlen 1) by nd_close);
                             eapply evt_eq; [| eapply (nd_2b8 (t7 - - e)%Z)]; [num_st_eq | exact INV1 | lia] | fail 100 "cut" pc ]
      | 0xeca28%Z => first [ num_cur_mem ltac:(fun m1 => assert (INV1 : NDINV (repeat (Z_to_bv 8 0) 63) m1 xlen 1) by nd_close);
                             eapply evt_eq; [| eapply (KP5 (t7 - - e)%Z)]; [num_st_eq | exact INV1 | lia | lia] | fail 100 "cut" pc ]
      end).
  Qed.
End NDB.
