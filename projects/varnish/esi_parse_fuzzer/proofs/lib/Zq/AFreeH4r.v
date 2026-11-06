(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr Frame Image.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd Require Import DA_Tac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo Asan12c Asanqj4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface AState.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpm9j ARtStmts ARtSscs ARtSeg3 ARtS4t2 AMTac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require ARt3o73.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require ARt3o73.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AMallocA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpm9j.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AFreeH AFreeH0 AFreeC AFreeH4w.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpm9j OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtStmts OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtSscs OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtSeg3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtS4t2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMTac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt3o73.ARt3dl2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt3o73.ARt3_gfa OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMallocA OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpm9j.AFreeLib OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeH OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeH0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeC OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeH4w.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tran6di.
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
From Ltac2 Require Ltac2.
Ltac2 hot_lia_keep_existing names :=
  let hs := Ltac2.List.map (fun h => let (id, _, _) := h in id) (Ltac2.Control.hyps ()) in
  Ltac2.Std.keep (Ltac2.List.filter (fun n => Ltac2.List.exist (fun h => Ltac2.Ident.equal h n) hs) names).
Ltac hot_lia_cut := ltac2:(Ltac2.Control.enter (fun () => hot_lia_keep_existing [@LO; @NFR; @SPR; @SEP_ES; @SEP_RS; @LO0; @ACLO; @SBHI; @RIHI; @LKS; @NF1; @SEP_ER; @SBLO; @NF0; @RILO; @SEP_cr; @SEP_cs; @SEP_rs; @SEP_qC; @Abq; @AbC; @SEP_qs; @BFA; @NB; @NBR; @SPH; @CV; @Albq; @AlbC; @Albb; @LBFA])).
Ltac hot_lia_full := OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Diet8z6.dlia_nc.
Local Ltac lia ::= hot_lia_cut; hot_lia_full.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Dietcz7.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tran6di.tf_cfree_lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dietcz7.dl_tf_cfree_lia.
(* [comment removed for export] *)

Notation wz z := (Z_to_bv 64 z) (only parsing).

(* [comment removed for export] *)
Ltac slia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits;
  first [ exact I | lia
        | lazymatch goal with
          | |- ?x + _ <= ?y \/ _ <= _ => apart_guided x y
          | |- ?x <= ?y \/ _ <= _ => apart_guided x y
          end ].

Ltac kcellz :=
  lazymatch goal with
  | |- rw_cells _ ?mm ?A ?cs => match goal with H : rw_cells _ mm ?B cs |- _ => replace A with B by lia; exact H end
  | |- ro_cells _ ?mm ?A ?cs => match goal with H : ro_cells _ mm ?B cs |- _ => replace A with B by lia; exact H end
  | |- u32arr _ ?mm ?A ?ws => match goal with H : u32arr _ mm ?B ws |- _ => replace A with B by lia; exact H end
  | |- bytes_at _ ?mm ?A ?bs => match goal with H : bytes_at _ mm ?B bs |- _ => replace A with B by lia; exact H end
  | |- stk _ ?mm ?lo ?A => match goal with H : stk _ mm lo ?B |- _ => replace A with B by lia; exact H end
  end.

(* [comment removed for export] *)
Definition enq_refill_W0 (sp : word) (q C ri b : Z) : list (Z * Z) :=
  let E := C + 1920 in let R := ri + 3072 in
  [(bv_unsigned sp - 224, bv_unsigned sp); (q, q + 32); (E, E + 80); (C + 2576, C + 2584); (b, b + 32); (R, R + 8); (R + 16, R + 24); (R + 72, R + 80)].
Definition enq_refill_WF (sp : word) (q C ri b lb : Z) : list (Z * Z) :=
  let E := C + 1920 in let R := ri + 3072 in
  [(bv_unsigned sp - 224, bv_unsigned sp); (q, q + 32); (lb, lb + 8); (E, E + 80); (C + 2576, C + 2584); (b, b + 32); (R, R + 8); (R + 16, R + 24); (R + 72, R + 80)].

(* [comment removed for export] *)
Definition enq_refill_post0 (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (q C mch size qb sb ri nf : Z) (ks : list word) (w na : word) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 statv' m',
    let E := C + 1920 in let R := ri + 3072 in let b := sb + 24 * 2^32 + 16 * bv_unsigned w in
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch (enq_refill_W0 sp q C ri b) m m'
    /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp)
    /\ rw_cells rsegs m' q [C8 (wz 1); C8 (wz b); C8 (wz b); C8 (wz (qb + (size + 8192)))]
    /\ rw_cells rsegs m' E [C4 (wz 0); C4 (wz 2); C8 (wz 8192); CB 64 (u32s ([w] ++ skipn 1 ks))]
    /\ rw_cells rsegs m' (C + 2576) [C8 statv']
    /\ rw_cells rsegs m' b [C8 (wz 0); C8 (wz (size + 8192)); C8 (wz 1); C8 (wz mch)]
    /\ rw_cells rsegs m' R [C8 (wz 0)]
    /\ rw_cells rsegs m' (R + 16) [C8 (wz (nf - 1))]
    /\ rw_cells rsegs m' (R + 72) [C8 (wz (bv_unsigned na + 1))]
    /\ u32arr rsegs m' (free_array_of sb 24 + 4 * (nf - 1)) [w].
Definition enq_refill_postF (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (q C mch size nb fb lb qb bsz sb ri nf : Z) (ks : list word) (w na : word) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 statv' m',
    let E := C + 1920 in let R := ri + 3072 in let b := sb + 24 * 2^32 + 16 * bv_unsigned w in
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch (enq_refill_WF sp q C ri b lb) m m'
    /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp)
    /\ rw_cells rsegs m' q [C8 (wz (nb + 1)); C8 (wz fb); C8 (wz b); C8 (wz (qb + (size + 8192)))]
    /\ rw_cells rsegs m' lb [C8 (wz b); C8 (wz bsz); C8 (wz 1021)]
    /\ rw_cells rsegs m' E [C4 (wz 0); C4 (wz 2); C8 (wz 8192); CB 64 (u32s ([w] ++ skipn 1 ks))]
    /\ rw_cells rsegs m' (C + 2576) [C8 statv']
    /\ rw_cells rsegs m' b [C8 (wz 0); C8 (wz (size + 8192)); C8 (wz 1); C8 (wz mch)]
    /\ rw_cells rsegs m' R [C8 (wz 0)]
    /\ rw_cells rsegs m' (R + 16) [C8 (wz (nf - 1))]
    /\ rw_cells rsegs m' (R + 72) [C8 (wz (bv_unsigned na + 1))]
    /\ u32arr rsegs m' (free_array_of sb 24 + 4 * (nf - 1)) [w].

(* [comment removed for export] *)
Local Ltac tf_region_find a n ::=
  let ba := tf_base a in
  match goal with
  | R : regn ?key ?B ?S |- _ => let bk := tf_base key in constr_eq ba bk; tf_with_region B S a n
  | R : regn_lit ?B ?S |- _ => tf_is_lit a; tf_with_region B S a n
  end.
Local Ltac tf_region_used segs m key ::=
  let bk := tf_base key in
  match goal with
  | H : rw_cells segs m ?a _ |- _ => let ba := tf_base a in constr_eq ba bk
  | H : ro_cells segs m ?a _ |- _ => let ba := tf_base a in constr_eq ba bk
  | H : bytes_at segs m ?a _ |- _ => let ba := tf_base a in constr_eq ba bk
  | H : stk segs m ?a _ |- _ => let ba := tf_base a in constr_eq ba bk
  end.
Local Ltac tf_apart B lo ::=
  let bB := tf_base B in let bl := tf_base lo in
  multimatch goal with
  | H : apart ?a _ ?c _ |- _ => let ba := tf_base a in let bc := tf_base c in constr_eq ba bB; constr_eq bc bl; eapply (apart_gl _ _ _ _ H)
  | H : apart ?a _ ?c _ |- _ => let ba := tf_base a in let bc := tf_base c in constr_eq bc bB; constr_eq ba bl; eapply (apart_gr _ _ _ _ H)
  end.
Local Ltac tf_same ::= first [ tf_cfree_lia | tf_lia ].
Local Ltac tf_regions ::=
  repeat match goal with K : aobjK ?X ?S |- _ => lazymatch goal with _ : regn X X S |- _ => fail | _ => pose proof (I : regn X X S) end end;
  try match goal with LO : alloc_ceiling <= ?lo /\ ?lo <= bv_unsigned ?sp - _ |- _ =>
        pose proof (I : regn (bv_unsigned sp) lo (bv_unsigned sp - lo)); pose proof (I : regn lo lo (bv_unsigned sp - lo)) end;
  try match goal with TSDL : ?L <= ?tsd /\ ?tsd + 8 <= _ |- _ => tf_closed L; pose proof (I : regn tsd 65536 6266880) end;
  pose proof (I : regn_lit 65536 6266880).
Local Ltac transport_after_call segs m m' MU WM ::= tf_transport segs m m' MU WM.

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
(* [comment removed for export] *)
From Ltac2 Require Ltac2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require LiaTwx2.
Ltac2 hot_tf_keep_existing names :=
  let hs := Ltac2.List.map (fun h => let (id, _, _) := h in id) (Ltac2.Control.hyps ()) in
  Ltac2.Std.keep (Ltac2.List.filter (fun n => Ltac2.List.exist (fun h => Ltac2.Ident.equal h n) hs) names).
Ltac hot_tf_cut := ltac2:(Ltac2.Control.enter (fun () => hot_tf_keep_existing [@ACLO; @W0; @AQLO])).
Ltac hot_tf_lia0 :=
  first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_prune; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
        | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_prune; Zify.zify; xlia zchecker
        | Zify.zify; xlia zchecker ].
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tran6di.tf_lia ::= hot_tf_cut; hot_tf_lia0.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require TfIncl.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tran6di.tf_with_region B S a n ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TfIncl.tf_with_region_fast B S a n.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.simpl_arr_sizes ::= rewrite ?OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Arr.u32s_length, ?OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Arr.u64s_length, ?OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Arr.upd_length.
(* [comment removed for export] *)
Section EnqRefill.
Context {Clg : Ceiling}.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte).
  Variables (lo q C sto mch size fb lb qb nx bsz sb ri nf : Z) (ks : list word) (w statv na bj0 bj1 bj2 bj3 : word).

  #[warnings="-notation-for-abbreviation"] Local Notation usp := (bv_unsigned sp).
  #[warnings="-notation-for-abbreviation"] Local Notation E := (C + 1920).
  #[warnings="-notation-for-abbreviation"] Local Notation R := (ri + 3072).
  #[warnings="-notation-for-abbreviation"] Local Notation fa := (free_array_of sb 24).
  #[warnings="-notation-for-abbreviation"] Local Notation b := (sb + 24 * 2^32 + 16 * bv_unsigned w).

  Hypothesis MI : mem_inv rsegs m.
  Hypothesis ST : stk rsegs m lo usp.
  Hypothesis LO : alloc_ceiling <= lo /\ lo <= usp - 224.
  Hypothesis SPA : usp mod 16 = 0.
  Hypothesis SPH : usp <= 2^47.
  Hypothesis RA2 : bv_unsigned ra mod 2 = 0.
  (* [comment removed for export] *)
  Hypothesis QLO : aobj q 32.
  Hypothesis QHI : q + 32 <= alloc_ceiling.
  Hypothesis CLO : aobj C 3888.
  Hypothesis CHI : C + 3888 <= alloc_ceiling.
  Hypothesis CAL : C mod 16 = 0.
  Hypothesis SEP_qC : apart q 32 C 3888.        (* [comment removed for export] *)
  (* [comment removed for export] *)
  Hypothesis SBLO : kHighMemBeg <= sb.
  Hypothesis SBHI : sb + 2^37 <= alloc_ceiling.
  Hypothesis SBAL : sb mod 4096 = 0.
  Hypothesis RILO : kHighMemBeg <= ri.
  Hypothesis RIHI : ri + 4096 <= alloc_ceiling.
  Hypothesis RIAL : ri mod 128 = 0.
  Hypothesis SEP_cr : apart C 3888 ri 4096.
  Hypothesis SEP_cs : apart C 3888 sb (2^37).
  Hypothesis SEP_rs : apart ri 4096 sb (2^37).
  Hypothesis SEP_qr : apart q 32 ri 4096.
  Hypothesis SEP_qs : apart q 32 sb (2^37).
  (* [comment removed for export] *)
  Hypothesis SZ : 0 <= size < 2^64.
  Hypothesis MCH : 0 <= mch < 2^64.
  Hypothesis STO : 0 <= sto < 2^64.
  (* [comment removed for export] *)
  Hypothesis LKS : length ks = 16%nat.
  Hypothesis WR : bv_unsigned w < 2^32.
  Hypothesis NFR : 1 <= nf < 2^27.
  (* [comment removed for export] *)
  Hypothesis BLO : kHighMemBeg <= b.
  Hypothesis BHI : b + 8192 <= alloc_ceiling.
  Hypothesis Abq : apart b 8192 q 32.
  Hypothesis AbC : apart b 8192 C 3888.
  Hypothesis Abr : apart b 8192 ri 4096.
  Hypothesis BFA : b + 8192 <= fa.            (* [comment removed for export] *)
  (* [comment removed for export] *)
  Hypothesis CSB : ro_cells rsegs m 0xb1578 [C8 (wz sb)].
  Hypothesis CRI : ro_cells rsegs m 0xb1588 [C8 (wz ri)].
  Hypothesis PC : rw_cells rsegs m E [C4 (wz 0); C4 (wz 2); C8 (wz 8192); CB 64 (u32s ks)].
  Hypothesis STA : rw_cells rsegs m (C + 2576) [C8 statv].
  Hypothesis MX : rw_cells rsegs m R [C8 (wz 0)].
  Hypothesis NFC : rw_cells rsegs m (R + 16) [C8 (wz nf)].
  Hypothesis NAL : rw_cells rsegs m (R + 72) [C8 na].
  Hypothesis FARR : u32arr rsegs m (fa + 4 * (nf - 1)) [w].
  Hypothesis BC : rw_cells rsegs m b [C8 bj0; C8 bj1; C8 bj2; C8 bj3].
  (* [comment removed for export] *)
  Variable nb : Z.
  Hypothesis NB : nb <> 0.
  Hypothesis NBR : 0 <= nb < 2^63.
  Hypothesis LBLO : kHighMemBeg <= lb.
  Hypothesis LBHI : lb + 8192 <= alloc_ceiling.
  Hypothesis Albq : apart lb 8192 q 32.
  Hypothesis AlbC : apart lb 8192 C 3888.
  Hypothesis Albr : apart lb 8192 ri 4096.
  Hypothesis Albb : apart lb 8192 b 8192.
  Hypothesis LBFA : lb + 8192 <= fa.
  Hypothesis LBC : rw_cells rsegs m lb [C8 (wz nx); C8 (wz bsz); C8 (wz 1021)].

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac enq_lin CV :=
    pose proof CLO as ACLO; aobj_lin1 ACLO; pose proof QLO as AQLO; aobj_lin1 AQLO;
    assert (SEP_ER : E + 80 <= R \/ R + 128 <= E) by (revert SEP_cr; unfold apart; clear; intros; lia);
    assert (SEP_ES : E + 80 <= sb \/ sb + 2^37 <= E) by (revert SEP_cs; unfold apart; clear; intros; lia);
    assert (SEP_RS : R + 128 <= sb \/ sb + 2^37 <= R) by (revert SEP_rs; unfold apart; clear; intros; lia);
    assert (DJ0 : q + 32 <= C + 1920 \/ C + 2584 <= q) by (revert SEP_qC; unfold apart; clear; intros; lia); box DJ0;
    assert (DJ1 : b + 32 <= q \/ q + 32 <= b) by (revert Abq; unfold apart; clear; intros; lia); box DJ1;
    assert (DJ2 : b + 32 <= C + 1920 \/ C + 2584 <= b) by (revert AbC; unfold apart; clear; intros; lia); box DJ2;
    pose proof (zr_word w) as W0; unfold inr64 in W0.

  Local Ltac enq_linF CV :=
    enq_lin CV;
    assert (DJ4 : q + 32 <= lb \/ lb + 24 <= q) by (revert Albq; unfold apart; clear; intros; lia); box DJ4;
    assert (DJ5 : lb + 24 <= C + 1920 \/ C + 2584 <= lb) by (revert AlbC; unfold apart; clear; intros; lia); box DJ5;
    assert (DJ6 : b + 32 <= lb \/ lb + 24 <= b) by (revert Albb; unfold apart; clear; intros; lia); box DJ6.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="BFA AbC Abq BHI BLO WR LKS STO MCH SZ SEP_qs SEP_qr SEP_rs SEP_cs SEP_cr RIHI RILO SBHI SBLO SEP_qC CAL CHI CLO QHI QLO RA2 SPH SPA LO Clg"] Lemma enq_gfa_tail0 : forall (Q : machine_state -> Prop) (nf0 : Z) (pad rpad : list byte) (statv0 : word) (mg : word -> option byte),
    rw_cells rsegs mg (usp + -64) (enqueue_frame pad s5 s4 s3 s2 s1 s0 ra) ->
    rw_cells rsegs mg (usp + -64 + -32) (refill_frame rpad (wz C) (wz E) (wz enqueue_ret)) ->
    ro_cells rsegs mg 0xb1578 [C8 (wz sb)] ->
    rw_cells rsegs mg (C + 2576) [C8 statv0] ->
    rw_cells rsegs mg q [C8 (wz 0); C8 (wz fb); C8 (wz lb); C8 (wz qb)] ->
    rw_cells rsegs mg b [C8 bj0; C8 bj1; C8 bj2; C8 bj3] ->
    0 <= nf0 -> nf0 + 1 < 2^27 ->
    (forall (t0'' t1'' t2'' a0'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' statv' : word) (m' : word -> option byte),
        rw_cells rsegs m' q [C8 (wz 1); C8 (wz b); C8 (wz b); C8 (wz (qb + (size + 8192)))] ->
        rw_cells rsegs m' E [C4 (wz 0); C4 (wz 2); C8 (wz 8192); CB 64 (u32s ([w] ++ skipn 1 ks))] ->
        rw_cells rsegs m' (C + 2576) [C8 statv'] ->
        rw_cells rsegs m' b [C8 (wz 0); C8 (wz (size + 8192)); C8 (wz 1); C8 (wz mch)] ->
        rw_cells rsegs m' R [C8 (wz 0)] -> rw_cells rsegs m' (R + 16) [C8 (wz nf0)] ->
        rw_cells rsegs m' (R + 72) [C8 (wz (bv_unsigned na + 1))] ->
        u32arr rsegs m' (fa + 4 * nf0) [w] ->
        munch (enq_refill_W0 sp q C ri b) mg m' -> wmono rsegs mg m' -> mem_inv rsegs m' -> stk rsegs m' lo usp ->
        evt rsegs Q (MS (mkR ra sp gp tp t0'' t1'' t2'' s0 s1 a0'' a1'' a2'' a3'' a4'' a5'' a6'' a7''
                            s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3'' t4'' t5'' t6'')
                        F (ret_pc ra) fc None m' (seg_rom rsegs))) ->
    forall ms', gfa_post gp tp F fc (usp + -64 + -32) lo R fa nf0 1 E 0 2 8192 na [w] ks
                         s11 s10 s9 s8 s7 s6 (wz size) (wz sto) (wz q) (wz mch) (wz 1) (wz E) (wz refill_ret) mg ms' ->
    evt rsegs Q ms'.
  Proof. try clear SBAL. try clear RIAL. try clear NFR. try clear Abr. try clear CRI.   (* [comment removed for export] *)
    clear MI ST CSB PC STA MX NFC NAL FARR BC NB NBR LBLO LBHI Albq AlbC Albr Albb LBFA LBC.
    intros Q nf0 pad rpad statv0 mg EF1 RF1 CSB1 STA1 QC1 BC1 NF0 NF1 K ms' PO.
    pose proof alloc_ceiling_val as CV. enq_lin CV. pose proof (zr_word sp) as SPR; unfold inr64 in SPR.
    unfold enq_refill_W0, kHighMemBeg, free_array_of, refill_frame, enqueue_frame in *.
    unfold gfa_post in PO. destruct_exs PO.
    (first [ dand10 PO as E3 MUc WMc MI3 ST3 MX3 NFC3 NAL3 FARR3 PC3 | destruct PO as (E3 & MUc & WMc & MI3 & ST3 & MX3 & NFC3 & NAL3 & FARR3 & PC3) ]). subst ms'.
    assert (LO0 : 0 <= lo) by (destruct ST3 as [? _]; assumption).
    rewrite ?unsigned_lit in MUc, ST3 by lia.
    pose proof (munch_refl [(usp - 224, usp); (q, q + 32); (E, E + 80); (C + 2576, C + 2584); (b, b + 32); (R, R + 8); (R + 16, R + 24); (R + 72, R + 80)] mg) as MU.
    pose proof (wmono_refl rsegs mg) as WM.
    kpost MUc WMc.
    replace (ret_pc (Z_to_bv 64 refill_ret)) with (Z_to_bv 64 refill_ret) by (symmetry; apply ret_pc_even; [unfold refill_ret; lia|reflexivity]).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename mc into m3 end.
    (* [comment removed for export] *)
    eapply (refill_epi_ok _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s10 s11 _ _ _ _ F fc m3 (usp + -64) lo E 1 1 0 2 8192
              ([w] ++ skipn 1 ks) rpad); [> try (fside CV) .. | idtac].
    all: try (first [fside CV | kcellz | zmod | f_equal; lia | cbn [length app]; rewrite length_skipn, LKS; reflexivity ]).
    intros m4 PC4 MU4 WM4 MI4 ST4. rewrite ?unsigned_lit in MU4, ST4 by lia. cbn [Z.eqb Pos.eqb] in PC4.
    clear PC3 RF1. kpost MU4 WM4.
    replace (ret_pc (Z_to_bv 64 enqueue_ret)) with (Z_to_bv 64 enqueue_ret) by (symmetry; apply ret_pc_even; [unfold enqueue_ret; lia|reflexivity]).
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename mc into m5 end.
    eapply evt_cut; [eapply (enqueue_miss_tail0_ok gp tp _ _ _ _ _ _ _ _ _ _ s6 s7 s8 s9 s10 s11 _ _ _ _ F fc m5
                               usp q C sto mch size fb lb qb 1 1 2 sb lo ([w] ++ skipn 1 ks) w _ bj0 bj1 bj2 bj3 pad s5 s4 s3 s2 s1 s0 ra)
                    | ]; [> try (fside CV) .. | idtac].
    all: try (first [fside CV | kcellz | zmod | cbn [length app]; rewrite length_skipn, LKS; reflexivity ]).
    intros ms' PO. destruct_exs PO. (first [ dand9 PO as E6 MU6 WM6 MI6 ST6 QC6 PC6 STA6 BC6 | destruct PO as (E6 & MU6 & WM6 & MI6 & ST6 & QC6 & PC6 & STA6 & BC6) ]). subst ms'.
    rewrite ?unsigned_lit in MU6, ST6 by lia. try clear EF1. kpost MU6 WM6.
    replace (1 - 1) with 0 in PC6 by lia. rewrite (Z_to_bv_bv_unsigned sp).
    eapply K; first [kcellz | eassumption].
  Qed.

  (* [comment removed for export] *)
  #[using="BFA AbC Abq BHI BLO NFR WR LKS STO MCH SZ SEP_qs SEP_qr SEP_rs SEP_cs SEP_cr RIAL RIHI RILO SBAL SBHI SBLO SEP_qC CAL CHI CLO QHI QLO RA2 SPH SPA LO Clg"] Lemma enq_refill_gfa0 : forall (Q : machine_state -> Prop) (t0' t1' t2' a5' a6' a7' t3' t4' t5' t6' : word) (pad rpad : list byte)
      (m1 : word -> option byte),
    mem_inv rsegs m1 -> stk rsegs m1 lo (usp + -64 + -32) ->
    rw_cells rsegs m1 (usp + -64) (enqueue_frame pad s5 s4 s3 s2 s1 s0 ra) ->
    rw_cells rsegs m1 (usp + -64 + -32) (refill_frame rpad (wz C) (wz E) (wz enqueue_ret)) ->
    ro_cells rsegs m1 0xb1578 [C8 (wz sb)] -> ro_cells rsegs m1 0xb1588 [C8 (wz ri)] ->
    rw_cells rsegs m1 E [C4 (wz 0); C4 (wz 2); C8 (wz 8192); CB 64 (u32s ks)] ->
    rw_cells rsegs m1 (C + 2576) [C8 statv] ->
    rw_cells rsegs m1 q [C8 (wz 0); C8 (wz fb); C8 (wz lb); C8 (wz qb)] ->
    rw_cells rsegs m1 b [C8 bj0; C8 bj1; C8 bj2; C8 bj3] ->
    rw_cells rsegs m1 R [C8 (wz 0)] -> rw_cells rsegs m1 (R + 16) [C8 (wz nf)] -> rw_cells rsegs m1 (R + 72) [C8 na] ->
    u32arr rsegs m1 (fa + 4 * (nf - 1)) [w] ->
    (forall (t0'' t1'' t2'' a0'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' statv' : word) (m' : word -> option byte),
        rw_cells rsegs m' q [C8 (wz 1); C8 (wz b); C8 (wz b); C8 (wz (qb + (size + 8192)))] ->
        rw_cells rsegs m' E [C4 (wz 0); C4 (wz 2); C8 (wz 8192); CB 64 (u32s ([w] ++ skipn 1 ks))] ->
        rw_cells rsegs m' (C + 2576) [C8 statv'] ->
        rw_cells rsegs m' b [C8 (wz 0); C8 (wz (size + 8192)); C8 (wz 1); C8 (wz mch)] ->
        rw_cells rsegs m' R [C8 (wz 0)] -> rw_cells rsegs m' (R + 16) [C8 (wz (nf - 1))] ->
        rw_cells rsegs m' (R + 72) [C8 (wz (bv_unsigned na + 1))] ->
        u32arr rsegs m' (fa + 4 * (nf - 1)) [w] ->
        munch (enq_refill_W0 sp q C ri b) m1 m' -> wmono rsegs m1 m' -> mem_inv rsegs m' -> stk rsegs m' lo usp ->
        evt rsegs Q (MS (mkR ra sp gp tp t0'' t1'' t2'' s0 s1 a0'' a1'' a2'' a3'' a4'' a5'' a6'' a7''
                            s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3'' t4'' t5'' t6'')
                        F (ret_pc ra) fc None m' (seg_rom rsegs))) ->
    evt rsegs Q
        (MS (mkR (wz refill_ret) (wz (usp + -64 + -32)) gp tp t0' t1' t2' (wz E) (wz 1)
                 (wz 0xb1558) (wz (C + 2560)) (wz 24) (wz (E + 16)) (wz 1) a5' a6' a7'
                 (wz mch) (wz q) (wz sto) (wz size) s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
            F (wz gfa_entry) fc None m1 (seg_rom rsegs)).
  Proof. try clear Abr.   (* [comment removed for export] *)
    clear MI ST CSB CRI PC STA MX NFC NAL FARR BC NB NBR LBLO LBHI Albq AlbC Albr Albb LBFA LBC.
    intros Q t0' t1' t2' a5' a6' a7' t3' t4' t5' t6' pad rpad m1 MI1 ST1 EF1 RF1 CSB1 CRI1 PC1 STA1 QC1 BC1 MX1 NFC1 NAL1 FARR1 K.
    pose proof alloc_ceiling_val as CV. enq_lin CV. pose proof (zr_word sp) as SPR; unfold inr64 in SPR.
    assert (LO0 : 0 <= lo) by (destruct ST1 as [? _]; assumption).
    unfold kHighMemBeg, free_array_of, refill_frame, enqueue_frame in *.
    pose proof (munch_refl (enq_refill_W0 sp q C ri b) m1) as MU. unfold enq_refill_W0, free_array_of in MU. cbv zeta in MU.
    pose proof (wmono_refl rsegs m1) as WM.
    (* [comment removed for export] *)
    eapply (gfa_lock_ok _ _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s10 s11 _ _ _ _ F fc m1 lo ri sb 24);
      [> try (fside CV) .. | idtac].
    all: try (first [fside CV | kcellz | zmod]).
    intros t0b t1b t2b a0b a5b a6b a7b t3b t4b t5b t6b scr m2 MX2 GF2 MU2 WM2 MI2 ST2.
    rewrite ?unsigned_lit in GF2, MU2, ST2 by lia.
    clear MX1. kpost MU2 WM2.
    unfold gfa_locked. rewrite ?unsigned_lit by lia.
    (* [comment removed for export] *)
    eapply evt_cut; [eapply (gfa_fast_ok _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m2
                               (usp + -64 + -32) lo R sb 24 nf 1 E 0 2 8192 na [w] ks scr)
                    | eapply (enq_gfa_tail0 Q (nf - 1) pad rpad statv m2); first [kcellz | lia | idtac] ];
      [> try (fside CV) .. | idtac].
    all: try (first [fside CV | kcellz | zmod]).
    intros. try clear GF2. try clear MX2. try clear RF1. try clear EF1. lazymatch goal with MUg : munch (enq_refill_W0 _ _ _ _ _) m2 ?mb, WMg : wmono rsegs m2 ?mb' |- _ =>
      unfold enq_refill_W0, free_array_of in MUg; cbv zeta in MUg; kpost MUg WMg end.
    eapply K; first [kcellz | eassumption].
  Qed.

  (* [comment removed for export] *)
  #[using="PC AbC Abq LKS STO MCH SZ SEP_rs SEP_cs SEP_cr RIHI RILO SBHI SBLO SEP_qC CAL CHI CLO QHI QLO SPH LO ST MI w ks ri sb"] Lemma enq_to_gfa : forall (Q : machine_state -> Prop) (nb0 : Z),
    0 <= nb0 < 2^63 ->
    rw_cells rsegs m q [C8 (wz nb0); C8 (wz fb); C8 (wz lb); C8 (wz qb)] ->
    (nb0 <> 0 -> kHighMemBeg <= lb /\ lb + 8192 <= alloc_ceiling /\ (q + 32 <= lb \/ lb + 24 <= q) /\ (lb + 24 <= C + 1920 \/ C + 2584 <= lb)) ->
    (nb0 <> 0 -> rw_cells rsegs m lb [C8 (wz nx); C8 (wz bsz); C8 (wz 1021)]) ->
    (forall (a6' a7' : word) (pad rpad : list byte) (m1 : word -> option byte),
        mem_inv rsegs m1 -> stk rsegs m1 lo (usp + -64 + -32) ->
        rw_cells rsegs m1 (usp + -64) (enqueue_frame pad s5 s4 s3 s2 s1 s0 ra) ->
        rw_cells rsegs m1 (usp + -64 + -32) (refill_frame rpad (wz C) (wz E) (wz enqueue_ret)) ->
        munch [(usp - 224, usp)] m m1 -> wmono rsegs m m1 ->
        evt rsegs Q
            (MS (mkR (wz refill_ret) (wz (usp + -64 + -32)) gp tp t0 t1 t2 (wz E) (wz 1)
                     (wz 0xb1558) (wz (C + 2560)) (wz 24) (wz (E + 16)) (wz 1) (wz 0xb1558) a6' a7'
                     (wz mch) (wz q) (wz sto) (wz size) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (wz gfa_entry) fc None m1 (seg_rom rsegs))) ->
    evt rsegs Q
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz q) (wz C) (wz sto) (wz mch) (wz size) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (wz enqueue_entry) fc None m (seg_rom rsegs)).
  Proof. try clear SPA. try clear RA2. try clear SBAL. try clear RIAL. try clear SEP_qr. try clear SEP_qs. try clear WR. try clear NFR. try clear BLO. try clear BHI. try clear Abr. try clear BFA.   (* [comment removed for export] *)
    clear CSB CRI STA MX NFC NAL FARR BC.
    clear NB NBR LBLO LBHI Albq AlbC Albr Albb LBFA LBC.
    intros Q nb0 NBR0 QC LBF LBC0 K.
    pose proof alloc_ceiling_val as CV. enq_lin CV. pose proof (zr_word sp) as SPR; unfold inr64 in SPR.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(usp - 224, usp)] m) as MU.
    pose proof (wmono_refl rsegs m) as WM.
    unfold kHighMemBeg in *.
    (* [comment removed for export] *)
    eapply (enqueue_miss_pre_ok _ _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m
              q C sto mch size nb0 fb lb qb nx bsz 2 8192 lo ks); [> try (fside CV) .. | idtac].
    all: try (first [fside CV | kcellz | zmod]).
    intros a6' a7' pad m0 EF0 QC0 PC0 MU0 WM0 MI0 ST0. rewrite ?unsigned_lit in EF0, MU0, ST0 by lia.
    clear QC PC. kpost MU0 WM0. rewrite ?unsigned_lit by lia.
    (* [comment removed for export] *)
    eapply (refill_pre_ok _ _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s10 s11 _ _ _ _ F fc _ lo C E 24 0 2 8192 ks);
      [> try (fside CV) .. | idtac].
    all: try (first [fside CV | kcellz | zmod]).
    intros rpad mr RF1 PC1 MU1 WM1 MI1 ST1; rewrite ?unsigned_lit in RF1, MU1, ST1 by lia.
    clear PC0 PC1; kpost MU1 WM1; rewrite ?unsigned_lit by lia.
    change (Z.shiftr 2 1) with 1.
    eapply K; first [kcellz | eassumption].
  Qed.

  (* [comment removed for export] *)
  #[using="BC FARR NAL NFC MX STA PC CRI CSB BFA AbC Abq BHI BLO NFR WR LKS STO MCH SZ SEP_qs SEP_qr SEP_rs SEP_cs SEP_cr RIAL RIHI RILO SBAL SBHI SBLO SEP_qC CAL CHI CLO QHI QLO RA2 SPH SPA LO ST MI bj3 bj2 bj1 bj0 statv bsz nx Clg"] Lemma enq_refill_new0 :
    rw_cells rsegs m q [C8 (wz 0); C8 (wz fb); C8 (wz lb); C8 (wz qb)] ->
    evt rsegs (enq_refill_post0 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc q C mch size qb sb ri nf ks w na lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz q) (wz C) (wz sto) (wz mch) (wz size) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (wz enqueue_entry) fc None m (seg_rom rsegs)).
  Proof. try clear Abr.   (* [comment removed for export] *)
    clear NB NBR LBLO LBHI Albq AlbC Albr Albb LBFA LBC.
    intros QC.
    pose proof alloc_ceiling_val as CV. enq_lin CV. pose proof (zr_word sp) as SPR; unfold inr64 in SPR.
    pose proof (munch_refl (enq_refill_W0 sp q C ri b) m) as MU. unfold enq_refill_W0 in MU. cbv zeta in MU.
    pose proof (wmono_refl rsegs m) as WM.
    unfold kHighMemBeg, free_array_of in *.
    apply (enq_to_gfa _ 0); [clear; lia| exact QC| intros NZ; exfalso; exact (NZ eq_refl)| intros NZ; exfalso; exact (NZ eq_refl)|].
    intros a6' a7' pad rpad m1 MI1 ST1 EF1 RF1 MU1 WM1.
    kpost MU1 WM1.
    eapply enq_refill_gfa0; first [kcellz | eassumption | idtac].
    intros. apply evt_done. unfold enq_refill_post0, enq_refill_W0, free_array_of. cbv zeta.
    hot_eexists_all. split; [reflexivity|].
    try clear RF1. try clear EF1. lazymatch goal with MUg : munch (enq_refill_W0 _ _ _ _ _) ?ma ?mb |- _ =>
      lazymatch goal with WMg : wmono rsegs ma mb |- _ => unfold enq_refill_W0, free_array_of in MUg; cbv zeta in MUg; kpost MUg WMg end end.
    OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits; first [kcellz | eassumption].
  Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="LBFA Albb Albr AlbC Albq LBHI LBLO NBR NB BFA AbC Abq BHI BLO WR LKS STO MCH SZ SEP_qs SEP_qr SEP_rs SEP_cs SEP_cr RIHI RILO SBHI SBLO SEP_qC CAL CHI CLO QHI QLO RA2 SPH SPA LO Clg"] Lemma enq_gfa_tailF : forall (Q : machine_state -> Prop) (nf0 : Z) (pad rpad : list byte) (statv0 : word) (mg : word -> option byte),
    rw_cells rsegs mg (usp + -64) (enqueue_frame pad s5 s4 s3 s2 s1 s0 ra) ->
    rw_cells rsegs mg (usp + -64 + -32) (refill_frame rpad (wz C) (wz E) (wz enqueue_ret)) ->
    ro_cells rsegs mg 0xb1578 [C8 (wz sb)] ->
    rw_cells rsegs mg (C + 2576) [C8 statv0] ->
    rw_cells rsegs mg q [C8 (wz nb); C8 (wz fb); C8 (wz lb); C8 (wz qb)] -> rw_cells rsegs mg lb [C8 (wz nx); C8 (wz bsz); C8 (wz 1021)] ->
    rw_cells rsegs mg b [C8 bj0; C8 bj1; C8 bj2; C8 bj3] ->
    0 <= nf0 -> nf0 + 1 < 2^27 ->
    (forall (t0'' t1'' t2'' a0'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' statv' : word) (m' : word -> option byte),
        rw_cells rsegs m' q [C8 (wz (nb + 1)); C8 (wz fb); C8 (wz b); C8 (wz (qb + (size + 8192)))] -> rw_cells rsegs m' lb [C8 (wz b); C8 (wz bsz); C8 (wz 1021)] ->
        rw_cells rsegs m' E [C4 (wz 0); C4 (wz 2); C8 (wz 8192); CB 64 (u32s ([w] ++ skipn 1 ks))] ->
        rw_cells rsegs m' (C + 2576) [C8 statv'] ->
        rw_cells rsegs m' b [C8 (wz 0); C8 (wz (size + 8192)); C8 (wz 1); C8 (wz mch)] ->
        rw_cells rsegs m' R [C8 (wz 0)] -> rw_cells rsegs m' (R + 16) [C8 (wz nf0)] ->
        rw_cells rsegs m' (R + 72) [C8 (wz (bv_unsigned na + 1))] ->
        u32arr rsegs m' (fa + 4 * nf0) [w] ->
        munch (enq_refill_WF sp q C ri b lb) mg m' -> wmono rsegs mg m' -> mem_inv rsegs m' -> stk rsegs m' lo usp ->
        evt rsegs Q (MS (mkR ra sp gp tp t0'' t1'' t2'' s0 s1 a0'' a1'' a2'' a3'' a4'' a5'' a6'' a7''
                            s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3'' t4'' t5'' t6'')
                        F (ret_pc ra) fc None m' (seg_rom rsegs))) ->
    forall ms', gfa_post gp tp F fc (usp + -64 + -32) lo R fa nf0 1 E 0 2 8192 na [w] ks
                         s11 s10 s9 s8 s7 s6 (wz size) (wz sto) (wz q) (wz mch) (wz 1) (wz E) (wz refill_ret) mg ms' ->
    evt rsegs Q ms'.
  Proof. try clear SBAL. try clear RIAL. try clear NFR. try clear Abr. try clear CRI.   (* [comment removed for export] *)
    clear MI ST CSB PC STA MX NFC NAL FARR BC LBC.
    intros Q nf0 pad rpad statv0 mg EF1 RF1 CSB1 STA1 QC1 LBC1 BC1 NF0 NF1 K ms' PO.
    pose proof alloc_ceiling_val as CV. enq_linF CV. pose proof (zr_word sp) as SPR; unfold inr64 in SPR.
    unfold enq_refill_WF, kHighMemBeg, free_array_of, refill_frame, enqueue_frame in *.
    unfold gfa_post in PO. destruct_exs PO.
    (first [ dand10 PO as E3 MUc WMc MI3 ST3 MX3 NFC3 NAL3 FARR3 PC3 | destruct PO as (E3 & MUc & WMc & MI3 & ST3 & MX3 & NFC3 & NAL3 & FARR3 & PC3) ]). subst ms'.
    assert (LO0 : 0 <= lo) by (destruct ST3 as [? _]; assumption).
    rewrite ?unsigned_lit in MUc, ST3 by lia.
    pose proof (munch_refl [(usp - 224, usp); (q, q + 32); (lb, lb + 8); (E, E + 80); (C + 2576, C + 2584); (b, b + 32); (R, R + 8); (R + 16, R + 24); (R + 72, R + 80)] mg) as MU.
    pose proof (wmono_refl rsegs mg) as WM.
    kpost MUc WMc.
    replace (ret_pc (Z_to_bv 64 refill_ret)) with (Z_to_bv 64 refill_ret) by (symmetry; apply ret_pc_even; [unfold refill_ret; lia|reflexivity]).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename mc into m3 end.
    (* [comment removed for export] *)
    eapply (refill_epi_ok _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s10 s11 _ _ _ _ F fc m3 (usp + -64) lo E 1 1 0 2 8192
              ([w] ++ skipn 1 ks) rpad); [> try (fside CV) .. | idtac].
    all: try (first [fside CV | kcellz | zmod | f_equal; lia | cbn [length app]; rewrite length_skipn, LKS; reflexivity ]).
    intros m4 PC4 MU4 WM4 MI4 ST4. rewrite ?unsigned_lit in MU4, ST4 by lia. cbn [Z.eqb Pos.eqb] in PC4.
    clear PC3 RF1. kpost MU4 WM4.
    replace (ret_pc (Z_to_bv 64 enqueue_ret)) with (Z_to_bv 64 enqueue_ret) by (symmetry; apply ret_pc_even; [unfold enqueue_ret; lia|reflexivity]).
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename mc into m5 end.
    eapply evt_cut; [eapply (enqueue_miss_tailF_ok gp tp _ _ _ _ _ _ _ _ _ _ s6 s7 s8 s9 s10 s11 _ _ _ _ F fc m5
                               usp q C sto mch size nb fb lb qb nx bsz 1 1 2 sb lo ([w] ++ skipn 1 ks) w _ bj0 bj1 bj2 bj3 pad s5 s4 s3 s2 s1 s0 ra)
                    | ]; [> try (fside CV) .. | idtac].
    all: try (first [fside CV | kcellz | zmod | cbn [length app]; rewrite length_skipn, LKS; reflexivity ]).
    intros ms' PO. destruct_exs PO. (first [ dand10 PO as E6 MU6 WM6 MI6 ST6 QC6 LB6 PC6 STA6 BC6 | destruct PO as (E6 & MU6 & WM6 & MI6 & ST6 & QC6 & LB6 & PC6 & STA6 & BC6) ]). subst ms'.
    rewrite ?unsigned_lit in MU6, ST6 by lia. try clear EF1. kpost MU6 WM6.
    replace (1 - 1) with 0 in PC6 by lia. rewrite (Z_to_bv_bv_unsigned sp).
    eapply K; first [kcellz | eassumption].
  Qed.

  (* [comment removed for export] *)
  #[using="LBFA Albb Albr AlbC Albq LBHI LBLO NBR NB BFA AbC Abq BHI BLO NFR WR LKS STO MCH SZ SEP_qs SEP_qr SEP_rs SEP_cs SEP_cr RIAL RIHI RILO SBAL SBHI SBLO SEP_qC CAL CHI CLO QHI QLO RA2 SPH SPA LO Clg"] Lemma enq_refill_gfaF : forall (Q : machine_state -> Prop) (t0' t1' t2' a5' a6' a7' t3' t4' t5' t6' : word) (pad rpad : list byte)
      (m1 : word -> option byte),
    mem_inv rsegs m1 -> stk rsegs m1 lo (usp + -64 + -32) ->
    rw_cells rsegs m1 (usp + -64) (enqueue_frame pad s5 s4 s3 s2 s1 s0 ra) ->
    rw_cells rsegs m1 (usp + -64 + -32) (refill_frame rpad (wz C) (wz E) (wz enqueue_ret)) ->
    ro_cells rsegs m1 0xb1578 [C8 (wz sb)] -> ro_cells rsegs m1 0xb1588 [C8 (wz ri)] ->
    rw_cells rsegs m1 E [C4 (wz 0); C4 (wz 2); C8 (wz 8192); CB 64 (u32s ks)] ->
    rw_cells rsegs m1 (C + 2576) [C8 statv] ->
    rw_cells rsegs m1 q [C8 (wz nb); C8 (wz fb); C8 (wz lb); C8 (wz qb)] -> rw_cells rsegs m1 lb [C8 (wz nx); C8 (wz bsz); C8 (wz 1021)] ->
    rw_cells rsegs m1 b [C8 bj0; C8 bj1; C8 bj2; C8 bj3] ->
    rw_cells rsegs m1 R [C8 (wz 0)] -> rw_cells rsegs m1 (R + 16) [C8 (wz nf)] -> rw_cells rsegs m1 (R + 72) [C8 na] ->
    u32arr rsegs m1 (fa + 4 * (nf - 1)) [w] ->
    (forall (t0'' t1'' t2'' a0'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' statv' : word) (m' : word -> option byte),
        rw_cells rsegs m' q [C8 (wz (nb + 1)); C8 (wz fb); C8 (wz b); C8 (wz (qb + (size + 8192)))] -> rw_cells rsegs m' lb [C8 (wz b); C8 (wz bsz); C8 (wz 1021)] ->
        rw_cells rsegs m' E [C4 (wz 0); C4 (wz 2); C8 (wz 8192); CB 64 (u32s ([w] ++ skipn 1 ks))] ->
        rw_cells rsegs m' (C + 2576) [C8 statv'] ->
        rw_cells rsegs m' b [C8 (wz 0); C8 (wz (size + 8192)); C8 (wz 1); C8 (wz mch)] ->
        rw_cells rsegs m' R [C8 (wz 0)] -> rw_cells rsegs m' (R + 16) [C8 (wz (nf - 1))] ->
        rw_cells rsegs m' (R + 72) [C8 (wz (bv_unsigned na + 1))] ->
        u32arr rsegs m' (fa + 4 * (nf - 1)) [w] ->
        munch (enq_refill_WF sp q C ri b lb) m1 m' -> wmono rsegs m1 m' -> mem_inv rsegs m' -> stk rsegs m' lo usp ->
        evt rsegs Q (MS (mkR ra sp gp tp t0'' t1'' t2'' s0 s1 a0'' a1'' a2'' a3'' a4'' a5'' a6'' a7''
                            s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3'' t4'' t5'' t6'')
                        F (ret_pc ra) fc None m' (seg_rom rsegs))) ->
    evt rsegs Q
        (MS (mkR (wz refill_ret) (wz (usp + -64 + -32)) gp tp t0' t1' t2' (wz E) (wz 1)
                 (wz 0xb1558) (wz (C + 2560)) (wz 24) (wz (E + 16)) (wz 1) a5' a6' a7'
                 (wz mch) (wz q) (wz sto) (wz size) s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
            F (wz gfa_entry) fc None m1 (seg_rom rsegs)).
  Proof. try clear Abr.   (* [comment removed for export] *)
    clear MI ST CSB CRI PC STA MX NFC NAL FARR BC LBC.
    intros Q t0' t1' t2' a5' a6' a7' t3' t4' t5' t6' pad rpad m1 MI1 ST1 EF1 RF1 CSB1 CRI1 PC1 STA1 QC1 LBC1 BC1 MX1 NFC1 NAL1 FARR1 K.
    pose proof alloc_ceiling_val as CV. enq_linF CV. pose proof (zr_word sp) as SPR; unfold inr64 in SPR.
    assert (LO0 : 0 <= lo) by (destruct ST1 as [? _]; assumption).
    unfold kHighMemBeg, free_array_of, refill_frame, enqueue_frame in *.
    pose proof (munch_refl (enq_refill_WF sp q C ri b lb) m1) as MU. unfold enq_refill_WF, free_array_of in MU. cbv zeta in MU.
    pose proof (wmono_refl rsegs m1) as WM.
    (* [comment removed for export] *)
    eapply (gfa_lock_ok _ _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s10 s11 _ _ _ _ F fc m1 lo ri sb 24);
      [> try (fside CV) .. | idtac].
    all: try (first [fside CV | kcellz | zmod]).
    intros t0b t1b t2b a0b a5b a6b a7b t3b t4b t5b t6b scr m2 MX2 GF2 MU2 WM2 MI2 ST2.
    rewrite ?unsigned_lit in GF2, MU2, ST2 by lia.
    clear MX1. kpost MU2 WM2.
    unfold gfa_locked. rewrite ?unsigned_lit by lia.
    (* [comment removed for export] *)
    eapply evt_cut; [eapply (gfa_fast_ok _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m2
                               (usp + -64 + -32) lo R sb 24 nf 1 E 0 2 8192 na [w] ks scr)
                    | eapply (enq_gfa_tailF Q (nf - 1) pad rpad statv m2); first [kcellz | lia | idtac] ];
      [> try (fside CV) .. | idtac].
    all: try (first [fside CV | kcellz | zmod]).
    intros. try clear GF2. try clear MX2. try clear RF1. try clear EF1. lazymatch goal with MUg : munch (enq_refill_WF _ _ _ _ _ _) m2 ?mb, WMg : wmono rsegs m2 ?mb' |- _ =>
      unfold enq_refill_WF, free_array_of in MUg; cbv zeta in MUg; kpost MUg WMg end.
    eapply K; first [kcellz | eassumption].
  Qed.

  (* [comment removed for export] *)
  #[using="LBC LBFA Albb Albr AlbC Albq LBHI LBLO NBR NB BC FARR NAL NFC MX STA PC CRI CSB BFA AbC Abq BHI BLO NFR WR LKS STO MCH SZ SEP_qs SEP_qr SEP_rs SEP_cs SEP_cr RIAL RIHI RILO SBAL SBHI SBLO SEP_qC CAL CHI CLO QHI QLO RA2 SPH SPA LO ST MI bj3 bj2 bj1 bj0 statv nx Clg"] Lemma enq_refill_newfull :
    rw_cells rsegs m q [C8 (wz nb); C8 (wz fb); C8 (wz lb); C8 (wz qb)] ->
    evt rsegs (enq_refill_postF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc q C mch size nb fb lb qb bsz sb ri nf ks w na lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz q) (wz C) (wz sto) (wz mch) (wz size) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (wz enqueue_entry) fc None m (seg_rom rsegs)).
  Proof. try clear Abr.   (* [comment removed for export] *)
    intros QC.
    pose proof alloc_ceiling_val as CV. enq_linF CV. pose proof (zr_word sp) as SPR; unfold inr64 in SPR.
    pose proof (munch_refl (enq_refill_WF sp q C ri b lb) m) as MU. unfold enq_refill_WF in MU. cbv zeta in MU.
    pose proof (wmono_refl rsegs m) as WM.
    unfold kHighMemBeg, free_array_of in *.
    apply (enq_to_gfa _ nb); [exact NBR| exact QC| intros _; unfold boxed in *; unfold kHighMemBeg in *; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; assumption| intros _; exact LBC|].
    intros a6' a7' pad rpad m1 MI1 ST1 EF1 RF1 MU1 WM1.
    kpost MU1 WM1.
    eapply enq_refill_gfaF; first [kcellz | eassumption | idtac].
    intros. apply evt_done. unfold enq_refill_postF, enq_refill_WF, free_array_of. cbv zeta.
    hot_eexists_all. split; [reflexivity|].
    try clear RF1. try clear EF1. lazymatch goal with MUg : munch (enq_refill_WF _ _ _ _ _ _) ?ma ?mb |- _ =>
      lazymatch goal with WMg : wmono rsegs ma mb |- _ => unfold enq_refill_WF, free_array_of in MUg; cbv zeta in MUg; kpost MUg WMg end end.
    OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits; first [kcellz | eassumption].
  Qed.
End EnqRefill.
Ltac slia ::= first [ exact I | lia | split; [lia|exact I] ].
