(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr Frame Image.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yd Require Import DA_Tac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo Asan12c Asanqj4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIface AState AIcpm9j ARtStmts ARtSscs ARtSeg3 ARtS4t2 AMTac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require ARt3o73.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require ARt3o73.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AMallocA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpm9j.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AFreeH AFreeH0 AFreeC AFreeH4w AFreeH4r.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIface OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AState OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpm9j OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARtStmts OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARtSscs OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARtSeg3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARtS4t2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AMTac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARt3o73.ARt3dl2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARt3o73.ARt3_gfa OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AMallocA OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpm9j.AFreeLib OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeH OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeH0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeC OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeH4w OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeH4r.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import ExN ExW.   (* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.DL.projn := Ltac2.Init.true.   (* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Destzna.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_exs PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_exs PO.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_ands PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_ands PO.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Diet8z6.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Diet8z6.dlia_nc.
(* [comment removed for export] *)

Notation wz z := (Z_to_bv 64 z) (only parsing).

(* [comment removed for export] *)
Ltac slia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits;
  first [ exact I | lia
        | lazymatch goal with
          | |- ?x + _ <= ?y \/ _ <= _ => apart_guided x y
          | |- ?x <= ?y \/ _ <= _ => apart_guided x y
          end ].

(* [comment removed for export] *)
Local Ltac fside_asm := first
  [ lazymatch goal with
    | |- rw_cells ?s ?m ?a _ => match goal with H : rw_cells s m a _ |- _ => exact H end
    | |- ro_cells ?s ?m ?a _ => match goal with H : ro_cells s m a _ |- _ => exact H end
    end
  | eassumption ].
Local Ltac fside_tail E := lazymatch goal with |- ?g => tryif has_evar g then first [ fside_asm | eqrefl ]
             else first [ fside_asm | eqrefl | lia | unfold QINST, AINST; kung; lia | rewrite <- E; fside_asm
                        | match goal with S : sh _ = _ |- _ => rewrite S; fside_asm end | left; kung; lia
                        | rewrite ?unsigned_lit by lia; first [fside_asm | lia | kung; lia]
                        | kung; slia
                        | apply mod_add_lit; [lia | assumption | reflexivity]
                        | lazymatch goal with |- _ \/ _ => unfold boxed in *; kung; lia end ]
 end.
Local Ltac fside E ::=
  lazymatch goal with
  | |- apart _ _ _ _ => fail
  | |- forall _ : word, _ => fail
  | |- forall _ : machine_state, _ => fail
  | |- poison_consts _ => unfold poison_consts; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits; fside_asm
  | |- aobj _ _ => lazymatch goal with |- ?g => tryif has_evar g then try fside_asm else faobj end
  | |- aobjK _ _ => apply aobjK_i; faobj
  | |- pz_in _ _ => lazymatch goal with |- ?g => tryif has_evar g then try fside_asm else fpz end
  | |- pz0_in _ _ => lazymatch goal with |- ?g => tryif has_evar g then try fside_asm else plia end
  | |- fl_in _ _ => lazymatch goal with |- ?g => tryif has_evar g then try fside_asm else plia end
  | |- m2s_in _ => lazymatch goal with |- ?g => tryif has_evar g then try fside_asm else plia end
  | |- _ mod _ = _ => first [ zmod | fside_tail E ]
  | |- _ => fside_tail E
  end.
(* [comment removed for export] *)
Section EnqPop.
Context {Clg : Ceiling}.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte).
  Variables (lo thr sto mch size fb lb qb nx bsz sb ri : Z) (ks : list word).

  #[warnings="-notation-for-abbreviation"] Local Notation usp := (bv_unsigned sp).
  #[warnings="-notation-for-abbreviation"] Local Notation q := (thr + 80).
  #[warnings="-notation-for-abbreviation"] Local Notation C := (thr + 208).
  #[warnings="-notation-for-abbreviation"] Local Notation E := (thr + 208 + 80 * 24).
  #[warnings="-notation-for-abbreviation"] Local Notation R := (ri + 128 * 24).
  #[warnings="-notation-for-abbreviation"] Local Notation fa := (free_array_of sb 24).
  (* [comment removed for export] *)
  #[warnings="-notation-for-abbreviation"] Local Notation uG := (bv_unsigned sp + 112 + -128 + -48 + -32 + -128).

  (* [comment removed for export] *)
  Hypothesis MI : mem_inv rsegs m.
  Hypothesis ST : stk rsegs m lo usp.
  Hypothesis LO : alloc_ceiling <= lo /\ lo <= usp + 112 - 1024.     (* [comment removed for export] *)
  Hypothesis SPA : usp mod 16 = 0.
  Hypothesis SPH : usp <= 2^47.
  Hypothesis RA2 : bv_unsigned ra mod 2 = 0.
  (* [comment removed for export] *)
  Hypothesis THR : aobj thr 4096 /\ thr + 4096 <= alloc_ceiling.
  Hypothesis THRA : thr mod 16 = 0.
  Hypothesis SBLO : kHighMemBeg <= sb.
  Hypothesis SBHI : sb + 2^37 <= alloc_ceiling.
  Hypothesis SBAL : sb mod 4096 = 0.
  Hypothesis RILO : kHighMemBeg <= ri.
  Hypothesis RIHI : ri + 4096 <= alloc_ceiling.
  Hypothesis RIAL : ri mod 128 = 0.
  Hypothesis SEP_tr : apart thr 4096 ri 4096.
  Hypothesis SEP_ts : apart thr 4096 sb (2^37).
  Hypothesis SEP_rs : apart ri 4096 sb (2^37).
  (* [comment removed for export] *)
  Hypothesis SZ : 0 <= size < 2^64.
  Hypothesis MCH : 0 <= mch < 2^64.
  Hypothesis STO : 0 <= sto < 2^64.
  Hypothesis LKS : length ks = 16%nat.

  (* [comment removed for export] *)
  Local Ltac pop_lin CV :=
    free_lin;
    assert (SEP_TR : thr + 4096 <= ri \/ ri + 4096 <= thr) by (revert SEP_tr; unfold apart; clear; intros; lia);
    assert (SEP_TS : thr + 4096 <= sb \/ sb + 2^37 <= thr) by (revert SEP_ts; unfold apart; clear; intros; lia);
    assert (SEP_RS : ri + 4096 <= sb \/ sb + 2^37 <= ri) by (revert SEP_rs; unfold apart; clear; intros; lia);
    pose proof (zr_word sp) as SPR; unfold inr64 in SPR.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition enq_pop_head_post : machine_state -> Prop := fun st =>
    exists (t0' t1' t2' a0' a5' a6' a7' t3' t4' t5' t6' : word) (scr pad rpad : list byte) (m' : word -> option byte),
      st = MS (mkR (wz refill_ret) (wz uG) gp tp t0' t1' t2' (wz R) (wz 0xb1d58) a0' (wz (thr + 208 + 2560)) (wz 24) (wz (E + 16)) (wz (Z.shiftr 2 1)) a5' a6' a7'
                   (wz mch) (wz 2305843009213693952) (wz fa) (wz 1099511627776) (wz 1152921504607895551)
                   (wz kMutexWriter) (wz 1500) (wz 16140901064495857663) s10 s11 t3' t4' t5' t6')
              F (wz gfa_locked) fc None m' (seg_rom rsegs)
      /\ munch [(usp - 224, usp); (R, R + 8)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
      /\ stk rsegs m' lo (usp + 112 + -128 + -48 + -32 - 128)
      /\ rw_cells rsegs m' (usp + -64) (enqueue_frame pad s5 s4 s3 s2 s1 s0 ra)
      /\ rw_cells rsegs m' (usp + -64 + -32) (refill_frame rpad (wz C) (wz E) (wz enqueue_ret))
      /\ rw_cells rsegs m' uG (gfa_frame scr s11 s10 s9 s8 s7 s6 (wz size) (wz sto) (wz q) (wz mch) (wz 1) (wz E) (wz refill_ret))
      /\ rw_cells rsegs m' R [C8 (wz kMutexWriter)].

  (* [comment removed for export] *)
  #[using="LKS STO MCH SZ SEP_rs SEP_ts SEP_tr RIAL RIHI RILO SBHI SBLO THRA THR SPH LO ST MI"] Lemma enq_pop_head : forall (nb0 : Z),
    ro_cells rsegs m 0xb1d78 [C8 (wz sb)] -> ro_cells rsegs m 0xb1d88 [C8 (wz ri)] ->
    rw_cells rsegs m E [C4 (wz 0); C4 (wz 2); C8 (wz 8192); CB 64 (u32s ks)] ->
    rw_cells rsegs m R [C8 (wz 0)] ->
    0 <= nb0 < 2^63 ->
    rw_cells rsegs m q [C8 (wz nb0); C8 (wz fb); C8 (wz lb); C8 (wz qb)] ->
    (nb0 <> 0 -> kHighMemBeg <= lb /\ lb + 8192 <= alloc_ceiling /\ (q + 32 <= lb \/ lb + 24 <= q) /\ (lb + 24 <= C + 1920 \/ C + 2584 <= lb)) ->
    (nb0 <> 0 -> rw_cells rsegs m lb [C8 (wz nx); C8 (wz bsz); C8 (wz 1021)]) ->
    evt rsegs enq_pop_head_post
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz q) (wz C) (wz sto) (wz mch) (wz size) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (wz enqueue_entry) fc None m (seg_rom rsegs)).
  Proof.
    intros nb0 CSB CRI PC MX NBR0 QC LBF LBC0.
    pose proof alloc_ceiling_val as CV. pop_lin CV.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    unfold kHighMemBeg in *.
    change (80 * 24) with 1920 in *. change (128 * 24) with 3072 in *.
    (* [comment removed for export] *)
    eapply (enq_to_gfa ra sp gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
              lo q C sto mch size fb lb qb nx bsz sb ri ks (wz 0)); [> try (fside CV) .. | idtac].
    all: try (first [ fside CV
                    | lazymatch goal with |- apart _ _ _ _ => revert SEP_tr SEP_ts SEP_rs; clear; unfold apart; intros; rewrite ?unsigned_lit by lia; lia end ]).
    intros a6' a7' pad rpad m1 MI1 ST1 EF1 RF1 MU1 WM1.
    rewrite ?unsigned_lit in ST1, MU1 by lia.
    xfer CSB MU1 WM1. xfer CRI MU1 WM1. xfer MX MU1 WM1.
    (* [comment removed for export] *)
    eapply (gfa_lock_ok _ _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s10 s11 _ _ _ _ F fc m1 lo ri sb 24);
      [> try (fside CV) .. | idtac].
    all: try (first [fside CV | rewrite ?unsigned_lit by lia; kcellz]).
    intros t0b t1b t2b a0b a5b a6b a7b t3b t4b t5b t6b scr m2 MX2 GF2 MU2 WM2 MI2 ST2.
    rewrite ?unsigned_lit in GF2, MU2, ST2 by lia. rewrite ?unsigned_lit by lia.
    xfer EF1 MU2 WM2. xfer RF1 MU2 WM2.
    apply evt_done. unfold enq_pop_head_post.
    first [ hotw_ex15 t0b t1b t2b a0b a5b a6b a7b t3b t4b t5b t6b scr pad rpad m2 | exists t0b, t1b, t2b, a0b, a5b, a6b, a7b, t3b, t4b, t5b, t6b, scr, pad, rpad, m2 ].
    split. { replace (usp + -64 + -32 + -128) with (usp + 112 + -128 + -48 + -32 + -128) by lia.
             change (80 * 24) with 1920. change (128 * 24) with 3072. change (Z.shiftr 2 1) with 1. reflexivity. }
    change (80 * 24) with 1920. change (128 * 24) with 3072.
    split. { eapply munch_trans; [eapply munch_weaken; [| exact MU1] | eapply munch_weaken; [| exact MU2]]; unfold sub_fp; cbn [outside]; intros y Hy; clear - Hy; lia. }
    split; [exact (wmono_trans _ _ _ _ WM1 WM2)|]. split; [exact MI2|].
    OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits; first [kcellz | eassumption].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition enq_pop_head0_post (cnt : Z -> Z) (ksf : Z -> list word) : machine_state -> Prop := fun st =>
    exists (t0' t1' t2' a0' a5' a6' a7' t3' t4' t5' t6' : word) (scr pad rpad : list byte) (m' : word -> option byte),
      st = MS (mkR (wz refill_ret) (wz uG) gp tp t0' t1' t2' (wz R) (wz 0xb1d58) a0' (wz (thr + 208 + 2560)) (wz 24) (wz (E + 16)) (wz (Z.shiftr 2 1)) a5' a6' a7'
                   (wz mch) (wz 2305843009213693952) (wz fa) (wz 1099511627776) (wz 1152921504607895551)
                   (wz kMutexWriter) (wz 1500) (wz 16140901064495857663) s10 s11 t3' t4' t5' t6')
              F (wz gfa_locked) fc None m' (seg_rom rsegs)
      /\ munch [(usp - 224, usp); (C + 80, C + 2560); (R, R + 8)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
      /\ stk rsegs m' lo (usp + 112 + -128 + -48 + -32 - 128)
      /\ rw_cells rsegs m' (usp + -64) (enqueue_frame pad s5 s4 s3 s2 s1 s0 ra)
      /\ rw_cells rsegs m' (usp + -64 + -32) (refill_frame rpad (wz C) (wz E) (wz enqueue_ret))
      /\ rw_cells rsegs m' uG (gfa_frame scr s11 s10 s9 s8 s7 s6 (wz size) (wz sto) (wz q) (wz mch) (wz 1) (wz E) (wz refill_ret))
      /\ rw_cells rsegs m' R [C8 (wz kMutexWriter)]
      /\ (forall i, 1 <= i <= 31 ->
            rw_cells rsegs m' (C + 80 * i) [C4 (wz (cnt i)); C4 (wz (max_count i)); C8 (wz (class_size i)); CB 64 (u32s (ksf i))]).

  #[using="LKS STO MCH SZ SEP_rs SEP_ts SEP_tr RIAL RIHI RILO SBHI SBLO THRA THR SPH LO ST MI ks"] Lemma enq_pop_head0 : forall (nb0 : Z) (cnt mc0 cs0 : Z -> Z) (ksf : Z -> list word),
    ro_cells rsegs m 0xb1d78 [C8 (wz sb)] -> ro_cells rsegs m 0xb1d88 [C8 (wz ri)] ->
    (forall i, 1 <= i <= 31 -> 0 <= cnt i < 2^32 /\ 0 <= mc0 i < 2^32 /\ 0 <= cs0 i < 2^64 /\ length (ksf i) = 16%nat /\
       rw_cells rsegs m (C + 80 * i) [C4 (wz (cnt i)); C4 (wz (mc0 i)); C8 (wz (cs0 i)); CB 64 (u32s (ksf i))]) ->
    cnt 24 = 0 -> mc0 24 = 0 ->
    rw_cells rsegs m R [C8 (wz 0)] ->
    0 <= nb0 < 2^63 ->
    rw_cells rsegs m q [C8 (wz nb0); C8 (wz fb); C8 (wz lb); C8 (wz qb)] ->
    (nb0 <> 0 -> kHighMemBeg <= lb /\ lb + 8192 <= alloc_ceiling /\ (q + 32 <= lb \/ lb + 24 <= q) /\ (lb + 24 <= C + 1920 \/ C + 2584 <= lb)) ->
    (nb0 <> 0 -> rw_cells rsegs m lb [C8 (wz nx); C8 (wz bsz); C8 (wz 1021)]) ->
    evt rsegs (enq_pop_head0_post cnt ksf)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz q) (wz C) (wz sto) (wz mch) (wz size) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (wz enqueue_entry) fc None m (seg_rom rsegs)).
  Proof.
    intros nb0 cnt mc0 cs0 ksf CSB CRI LINES CNT0 MC0 MX NBR0 QC LBF LBC0.
    pose proof alloc_ceiling_val as CV. pop_lin CV.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    unfold kHighMemBeg in *.
    change (80 * 24) with 1920 in *. change (128 * 24) with 3072 in *.
    (first [ pose proof ((LINES 24 ltac:(lia))) as dR_1; dand5 dR_1 as _ _ CS24 LK24 PC | pose proof (LINES 24 ltac:(lia)) as (_ & _ & CS24 & LK24 & PC) ]). rewrite CNT0, MC0 in PC. change (80 * 24) with 1920 in PC.
    pose proof (munch_refl [(usp - 224, usp)] m) as MUS. pose proof (wmono_refl rsegs m) as WM0.
    (* [comment removed for export] *)
    eapply (enqueue_miss_pre_ok _ _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m
              q C sto mch size nb0 fb lb qb nx bsz 0 (cs0 24) lo (ksf 24)); [> try (fside CV) .. | idtac].
    all: try (first [ fside CV | kcellz | zmod ]).
    intros a6' a7' pad m0 EF0 QC0 PC0 MU0 WM0' MI0 ST0. rewrite ?unsigned_lit in EF0, MU0, ST0 by lia.
    assert (LINES0 : forall i, 1 <= i <= 31 -> 0 <= cnt i < 2^32 /\ 0 <= mc0 i < 2^32 /\ 0 <= cs0 i < 2^64 /\ length (ksf i) = 16%nat /\
              rw_cells rsegs m0 (C + 80 * i) [C4 (wz (cnt i)); C4 (wz (mc0 i)); C8 (wz (cs0 i)); CB 64 (u32s (ksf i))]).
    { intros i Hi; (first [ pose proof ((LINES i Hi)) as dR_2; dand5 dR_2 as X1 X2 X3 X4 X5 | destruct (LINES i Hi) as (X1 & X2 & X3 & X4 & X5) ]); refine (conj X1 (conj X2 (conj X3 (conj X4 _)))).
      eapply (rw_cells_transport rsegs _ m m0); [exact X5 | exact MU0 | exact WM0'
                                               | cbn [disjoint_from]; simpl_sizes; clear - Hi ATHR THR CV LO SPR LO0; lia]. }
    xfer CSB MU0 WM0'. xfer CRI MU0 WM0'. xfer MX MU0 WM0'. clear QC PC LINES. rewrite ?unsigned_lit by lia.
    (* [comment removed for export] *)
    replace (Z_to_bv 64 (C + 1920) : word) with (Z_to_bv 64 (C + 80 * 24) : word) by (f_equal; lia).
    eapply (refill_pre0_ok _ _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s10 s11 _ _ _ _ F fc m0 lo C 24 cnt mc0 cs0 ksf);
      [> try (fside CV) .. | idtac].
    all: try (first [ fside CV | rewrite ?unsigned_lit by lia; kcellz | zmod ]).
    intros a5r a6r a7r t0e t1e t2e t3e t4e t5e rpad m1 RF1 LINES1 MU1 WM1 MI1 ST1. rewrite ?unsigned_lit in RF1, MU1, ST1 by lia.
    change (refill_count 24) with 1. change (80 * 24) with 1920 in *.
    xfer CSB MU1 WM1. xfer CRI MU1 WM1. xfer MX MU1 WM1. xfer EF0 MU1 WM1. clear LINES0. rewrite ?unsigned_lit by lia.
    (* [comment removed for export] *)
    eapply (gfa_lock_ok _ _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s10 s11 _ _ _ _ F fc m1 lo ri sb 24);
      [> try (fside CV) .. | idtac].
    all: try (first [fside CV | rewrite ?unsigned_lit by lia; kcellz]).
    intros t0b t1b t2b a0b a5b a6b a7b t3b t4b t5b t6b scr m2 MX2 GF2 MU2 WM2 MI2 ST2.
    rewrite ?unsigned_lit in GF2, MU2, ST2 by lia. rewrite ?unsigned_lit by lia.
    xfer EF0 MU2 WM2. xfer RF1 MU2 WM2.
    assert (LINES2 : forall i, 1 <= i <= 31 ->
              rw_cells rsegs m2 (C + 80 * i) [C4 (wz (cnt i)); C4 (wz (max_count i)); C8 (wz (class_size i)); CB 64 (u32s (ksf i))]).
    { intros i Hi. eapply (rw_cells_transport rsegs _ m1 m2); [exact (LINES1 i Hi) | exact MU2 | exact WM2
                                                             | cbn [disjoint_from]; simpl_sizes; clear - Hi ATHR THR CV LO SPR LO0 SEP_TR RILO RIHI; lia]. }
    apply evt_done. unfold enq_pop_head0_post.
    first [ hotw_ex15 t0b t1b t2b a0b a5b a6b a7b t3b t4b t5b t6b scr pad rpad m2 | exists t0b, t1b, t2b, a0b, a5b, a6b, a7b, t3b, t4b, t5b, t6b, scr, pad, rpad, m2 ].
    split. { replace (usp + -64 + -32 + -128) with (usp + 112 + -128 + -48 + -32 + -128) by lia.
             change (80 * 24) with 1920. change (128 * 24) with 3072. change (Z.shiftr 2 1) with 1. reflexivity. }
    change (80 * 24) with 1920. change (128 * 24) with 3072.
    split. { eapply munch_trans; [eapply munch_weaken; [| exact MU0] | eapply munch_trans; [eapply munch_weaken; [| exact MU1] | eapply munch_weaken; [| exact MU2]]];
             unfold sub_fp; cbn [outside]; intros y Hy; clear - Hy; lia. }
    split; [exact (wmono_trans _ _ _ _ WM0' (wmono_trans _ _ _ _ WM1 WM2))|]. split; [exact MI2|].
    OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits; first [kcellz | eassumption].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Section Tail.
  Variables (a0g t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (scr pad rpad : list byte) (statv0 na w bj0 bj1 bj2 bj3 : word)
            (nf' : Z) (mg : word -> option byte).
  #[warnings="-notation-for-abbreviation"] Local Notation b := (sb + 24 * 2^32 + 16 * bv_unsigned w).
  Hypothesis MIg : mem_inv rsegs mg.
  Hypothesis STg : stk rsegs mg lo uG.
  Hypothesis NFR : 1 <= nf' < 2^27.
  Hypothesis WR : bv_unsigned w < 2^32.
  Hypothesis BLO : kHighMemBeg <= b.
  Hypothesis BHI : b + 8192 <= alloc_ceiling.
  Hypothesis BFA : b + 8192 <= fa.
  Hypothesis Abt : apart b 8192 thr 4096.
  Hypothesis Abr : apart b 8192 ri 4096.
  Hypothesis EFg : rw_cells rsegs mg (usp + -64) (enqueue_frame pad s5 s4 s3 s2 s1 s0 ra).
  Hypothesis RFg : rw_cells rsegs mg (usp + -64 + -32) (refill_frame rpad (wz C) (wz E) (wz enqueue_ret)).
  Hypothesis GFg : rw_cells rsegs mg uG (gfa_frame scr s11 s10 s9 s8 s7 s6 (wz size) (wz sto) (wz q) (wz mch) (wz 1) (wz E) (wz refill_ret)).
  Hypothesis CSBg : ro_cells rsegs mg 0xb1d78 [C8 (wz sb)].
  Hypothesis MXg : rw_cells rsegs mg R [C8 (wz kMutexWriter)].
  Hypothesis NFCg : rw_cells rsegs mg (R + 16) [C8 (wz nf')].
  Hypothesis NALg : rw_cells rsegs mg (R + 72) [C8 na].
  Hypothesis FARRg : u32arr rsegs mg (fa + 4 * (nf' - 1)) [w].
  Hypothesis PCg : rw_cells rsegs mg E [C4 (wz 0); C4 (wz 2); C8 (wz 8192); CB 64 (u32s ks)].
  Hypothesis STAg : rw_cells rsegs mg (C + 2576) [C8 statv0].
  Hypothesis BCg : rw_cells rsegs mg b [C8 bj0; C8 bj1; C8 bj2; C8 bj3].

  Local Ltac tail_lin CV :=
    pop_lin CV;
    assert (DJbt : b + 8192 <= thr \/ thr + 4096 <= b) by (revert Abt; unfold apart; clear; intros; lia);
    assert (DJbr : b + 8192 <= ri \/ ri + 4096 <= b) by (revert Abr; unfold apart; clear; intros; lia);
    pose proof (zr_word w) as W0; unfold inr64 in W0.

  (* [comment removed for export] *)
  #[using="BCg STAg PCg FARRg NALg NFCg MXg CSBg GFg RFg EFg Abr Abt BFA BHI BLO WR NFR STg MIg bj3 bj2 bj1 bj0 statv0 rpad pad scr LKS STO MCH SZ SEP_rs SEP_ts SEP_tr RIAL RIHI RILO SBAL SBHI SBLO THRA THR RA2 SPH SPA LO sto Clg"] Lemma enq_pop_tail0 :
    rw_cells rsegs mg q [C8 (wz 0); C8 (wz fb); C8 (wz lb); C8 (wz qb)] ->
    evt rsegs (enq_refill_post0 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc q C mch size qb sb ri nf' ks w na lo mg)
        (MS (mkR (wz gfa_popret) (wz uG) gp tp t0' t1' t2' (wz R) (wz 0xb1d58) (wz 1) a1' a2' a3' a4' a5' a6' a7'
                 a0g (wz 2305843009213693952) (wz fa) (wz (E + 16)) (wz (Z.shiftr 2 1)) (wz kMutexWriter) (wz 1500) (wz 16140901064495857663) s10 s11 t3' t4' t5' t6')
            F (ret_pc (wz gfa_popret)) fc None mg (seg_rom rsegs)).
  Proof.
    intros QCg.
    pose proof alloc_ceiling_val as CV. tail_lin CV.
    assert (LO0 : 0 <= lo) by (destruct STg as [? _]; assumption).
    unfold kHighMemBeg in *.
    change (80 * 24) with 1920 in *. change (128 * 24) with 3072 in *. change (Z.shiftr 2 1) with 1.
    replace (ret_pc (wz gfa_popret)) with (wz gfa_popret : word) by (symmetry; apply ret_pc_even; [unfold gfa_popret; lia| reflexivity]).
    (* [comment removed for export] *)
    eapply evt_cut; [eapply (gfa_popok_ok _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ s10 s11 _ _ _ _ F fc mg
                               (usp + 112 + -128 + -48 + -32) lo (ri + 3072) sb 24 nf' 1 (C + 1920) 0 2 8192 1 na [w] ks scr)|];
      [> try (fside CV) .. | idtac].
    all: try (first [ fside CV | rewrite ?unsigned_lit by lia; kcellz | zmod
                    | lazymatch goal with |- apart _ _ _ _ => revert SEP_tr SEP_ts SEP_rs Abt Abr; clear; unfold apart; intros; lia end ]).
    (* [comment removed for export] *)
    intros ms' PO. replace (usp + 112 + -128 + -48 + -32) with (usp + -64 + -32) in PO by lia. revert PO.
    refine (enq_gfa_tail0 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo q C sto mch size fb lb qb sb ri ks w na bj0 bj1 bj2 bj3
              _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (nf' - 1) pad rpad statv0 mg _ _ _ _ _ _ _ _ _ ms'); [> try (fside CV) .. | idtac].
    all: try (first [ fside CV | rewrite ?unsigned_lit by lia; kcellz | zmod
                    | lazymatch goal with |- apart _ _ _ _ => revert SEP_tr SEP_ts SEP_rs Abt Abr; clear; unfold apart; intros; lia end ]).
    (* [comment removed for export] *)
    intros. apply evt_done. unfold enq_refill_post0, enq_refill_W0. cbv zeta.
    hot_eexists_all. split; [reflexivity|].
    OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits; first [eassumption | kcellz].
  Qed.

  (* [comment removed for export] *)
  #[using="BCg STAg PCg FARRg NALg NFCg MXg CSBg GFg RFg EFg Abr Abt BFA BHI BLO WR NFR STg MIg bj3 bj2 bj1 bj0 statv0 rpad pad scr LKS STO MCH SZ SEP_rs SEP_ts SEP_tr RIAL RIHI RILO SBAL SBHI SBLO THRA THR RA2 SPH SPA LO sto"] Lemma enq_pop_tailF : forall nb : Z,
    nb <> 0 -> 0 <= nb < 2^63 ->
    kHighMemBeg <= lb -> lb + 8192 <= alloc_ceiling -> apart lb 8192 thr 4096 -> apart lb 8192 ri 4096 -> apart lb 8192 b 8192 -> lb + 8192 <= fa ->
    rw_cells rsegs mg q [C8 (wz nb); C8 (wz fb); C8 (wz lb); C8 (wz qb)] ->
    rw_cells rsegs mg lb [C8 (wz nx); C8 (wz bsz); C8 (wz 1021)] ->
    evt rsegs (enq_refill_postF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc q C mch size nb fb lb qb bsz sb ri nf' ks w na lo mg)
        (MS (mkR (wz gfa_popret) (wz uG) gp tp t0' t1' t2' (wz R) (wz 0xb1d58) (wz 1) a1' a2' a3' a4' a5' a6' a7'
                 a0g (wz 2305843009213693952) (wz fa) (wz (E + 16)) (wz (Z.shiftr 2 1)) (wz kMutexWriter) (wz 1500) (wz 16140901064495857663) s10 s11 t3' t4' t5' t6')
            F (ret_pc (wz gfa_popret)) fc None mg (seg_rom rsegs)).
  Proof.
    intros nb NB NBR LBLO LBHI Albt Albr Albb LBFA QCg LBCg.
    pose proof alloc_ceiling_val as CV. tail_lin CV.
    assert (DJlt : lb + 8192 <= thr \/ thr + 4096 <= lb) by (revert Albt; unfold apart; clear; intros; lia).
    assert (DJlr : lb + 8192 <= ri \/ ri + 4096 <= lb) by (revert Albr; unfold apart; clear; intros; lia).
    assert (DJlb : lb + 8192 <= b \/ b + 8192 <= lb) by (revert Albb; unfold apart; clear; intros; lia).
    assert (LO0 : 0 <= lo) by (destruct STg as [? _]; assumption).
    unfold kHighMemBeg in *.
    change (80 * 24) with 1920 in *. change (128 * 24) with 3072 in *. change (Z.shiftr 2 1) with 1.
    replace (ret_pc (wz gfa_popret)) with (wz gfa_popret : word) by (symmetry; apply ret_pc_even; [unfold gfa_popret; lia| reflexivity]).
    eapply evt_cut; [eapply (gfa_popok_ok _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ s10 s11 _ _ _ _ F fc mg
                               (usp + 112 + -128 + -48 + -32) lo (ri + 3072) sb 24 nf' 1 (C + 1920) 0 2 8192 1 na [w] ks scr)|];
      [> try (fside CV) .. | idtac].
    all: try (first [ fside CV | rewrite ?unsigned_lit by lia; kcellz | zmod
                    | lazymatch goal with |- apart _ _ _ _ => revert SEP_tr SEP_ts SEP_rs Abt Abr Albt Albr Albb; clear; unfold apart; intros; lia end ]).
    intros ms' PO. replace (usp + 112 + -128 + -48 + -32) with (usp + -64 + -32) in PO by lia. revert PO.
    refine (enq_gfa_tailF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo q C sto mch size fb lb qb nx bsz sb ri ks w na bj0 bj1 bj2 bj3
              _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ nb _ _ _ _ _ _ _ _ _ _ (nf' - 1) pad rpad statv0 mg _ _ _ _ _ _ _ _ _ _ ms'); [> try (fside CV) .. | idtac].
    all: try (first [ fside CV | rewrite ?unsigned_lit by lia; kcellz | zmod
                    | lazymatch goal with |- apart _ _ _ _ => revert SEP_tr SEP_ts SEP_rs Abt Abr Albt Albr Albb; clear; unfold apart; intros; lia end ]).
    intros. apply evt_done. unfold enq_refill_postF, enq_refill_WF. cbv zeta.
    hot_eexists_all. split; [reflexivity|].
    OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits; first [eassumption | kcellz].
  Qed.
  End Tail.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Section Null.
  Variables (a0g t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (scr pad rpad : list byte) (sealed : Z) (mg : word -> option byte).
  Hypothesis MIg : mem_inv rsegs mg.
  Hypothesis STg : stk rsegs mg lo uG.
  Hypothesis EFg : rw_cells rsegs mg (usp + -64) (enqueue_frame pad s5 s4 s3 s2 s1 s0 ra).
  Hypothesis RFg : rw_cells rsegs mg (usp + -64 + -32) (refill_frame rpad (wz C) (wz E) (wz enqueue_ret)).
  Hypothesis GFg : rw_cells rsegs mg uG (gfa_frame scr s11 s10 s9 s8 s7 s6 (wz size) (wz sto) (wz q) (wz mch) (wz 1) (wz E) (wz refill_ret)).
  Hypothesis MXg : rw_cells rsegs mg R [C8 (wz kMutexWriter)].
  Hypothesis PCg : rw_cells rsegs mg E [C4 (wz 0); C4 (wz 2); C8 (wz 8192); CB 64 (u32s ks)].
  (* [comment removed for export] *)
  Hypothesis SNZ : sealed <> 0.
  Hypothesis SR : 0 <= sealed < 2^64.
  Hypothesis CSEAL : ro_cells rsegs mg 0xa91d0 [C8 (wz sealed)].
  Hypothesis CDYG : ro_cells rsegs mg 0xa91d8 [C8 (wz 0x146edc)].
  Hypothesis CDY : ro_cells rsegs mg 0x146edc [C4 (wz 0)].

  Definition enq_pop_null_post : machine_state -> Prop := fun st =>
    exists (t0'' t1'' t2'' a0'' a1'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' : word) (m' : word -> option byte),
      st = MS (mkR (wz enqueue_ret) (wz (usp + -64)) gp tp t0'' t1'' t2'' (wz E) (wz C) a0'' a1'' (wz sto) a3'' a4'' a5'' a6'' a7''
                   (wz mch) (wz q) (wz sto) (wz size) s6 s7 s8 s9 s10 s11 t3'' t4'' t5'' t6'')
              F (wz enqueue_spin) fc None m' (seg_rom rsegs)
      /\ munch [(usp - 224, usp + -64); (R, R + 8); (E, E + 4)] mg m' /\ wmono rsegs mg m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (usp + -64)
      /\ rw_cells rsegs m' R [C8 (wz 0)]
      /\ rw_cells rsegs m' E [C4 (wz 0); C4 (wz 2); C8 (wz 8192); CB 64 (u32s ks)]
      /\ rw_cells rsegs m' (usp + -64) (enqueue_frame pad s5 s4 s3 s2 s1 s0 ra).

  (* [comment removed for export] *)
  End Null.
End EnqPop.
Ltac slia ::= first [ exact I | lia | split; [lia|exact I] ].
