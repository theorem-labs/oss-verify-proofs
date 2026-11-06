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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yd Require Import DA_Tac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo Asan12c Asanqj4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIface AIcpm9j ARtStmts ARtS4t2 AMTac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AMalc5w.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AMalc5w.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AMallocA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpm9j.

Module AMallocR.
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yd Require Import DA_Tac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo Asan12c Asanqj4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIface AState AIcpm9j ARtStmts ARtSscs ARtS4t2 AMTac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AMalc5w.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require ARt3o73.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require ARt3o73.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AMallocA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpm9j.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AFreeH AFreeH0 AFreeC.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIface OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AState OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpm9j OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARtStmts OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARtSscs OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARtS4t2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AMTac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AMalc5w.AMalloc2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARt3o73.ARt3dl2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARt3o73.ARt3_gfa OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AMallocA OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpm9j.AFreeLib OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeH OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeH0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeC.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tran6di.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= tryif OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.PropExec.noncert_goal_has_var then (Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker) else first [ solve [OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.PropExec.noncert_clear_all; Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker] | Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker ].
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.transport_chunks segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_chunks segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.footprint_after_store segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_footprint_after_store segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_mem_after_store.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_after_call segs m m' MU WM.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.addr_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_addr_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_zmlia.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.RL.sec := Ltac2.Init.true.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Stepobi.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yd.DA_Tac.astep_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.af_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yd.DA_Tac.azstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.af_zstep.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AMTac.amstep_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.amf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AMTac.amz ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.amf_zstep.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require LiaLt.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaLt.lia_tuned.
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require DietDL3.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.DL.sec_local := Ltac2.Init.true.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.DL.sep_idents := OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.DL.sep_idents_hide.
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
Ltac kcellz :=
  lazymatch goal with
  | |- rw_cells _ ?mm ?A ?cs => match goal with H : rw_cells _ mm ?B cs |- _ => replace A with B by lia; exact H end
  | |- ro_cells _ ?mm ?A ?cs => match goal with H : ro_cells _ mm ?B cs |- _ => replace A with B by lia; exact H end
  | |- u32arr _ ?mm ?A ?ws => match goal with H : u32arr _ mm ?B ws |- _ => replace A with B by lia; exact H end
  | |- bytes_at _ ?mm ?A ?bs => match goal with H : bytes_at _ mm ?B bs |- _ => replace A with B by lia; exact H end
  | |- stk _ ?mm ?lo ?A => match goal with H : stk _ mm lo ?B |- _ => replace A with B by lia; exact H end
  end.

(* [comment removed for export] *)
Definition comb_refill_call : Z := 0x3bbc8.   (* [comment removed for export] *)
Definition comb_refill_ret : Z := 0x3bbcc.
Definition comb_pop_blk : Z := 0x3bad0.

(* [comment removed for export] *)
Definition comb_refill_W (sp : word) (C c ri : Z) : list (Z * Z) :=
  let E := C + 80 * c in let R := ri + 128 * c in
  [(bv_unsigned sp - 208, bv_unsigned sp); (E, E + 80); (C + 2576, C + 2584); (R, R + 8); (R + 16, R + 24); (R + 72, R + 80)].

(* [comment removed for export] *)
Definition comb_refill_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (C c maxc csz sb ri nf : Z) (ks ws : list word) (kw na : word) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 statv' m',
    let E := C + 80 * c in let R := ri + 128 * c in let k := Z.shiftr maxc 1 in
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (sb + c * 2^32 + 16 * bv_unsigned kw)) a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch (comb_refill_W sp C c ri) m m'
    /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp)
    /\ rw_cells rsegs m' E [C4 (Z_to_bv 64 (k - 1)); C4 (Z_to_bv 64 maxc); C8 (Z_to_bv 64 csz); CB 64 (u32s (ws ++ skipn (Z.to_nat k) ks))]
    /\ rw_cells rsegs m' (C + 2576) [C8 statv']
    /\ rw_cells rsegs m' R [C8 (Z_to_bv 64 0)]
    /\ rw_cells rsegs m' (R + 16) [C8 (Z_to_bv 64 (nf - k))]
    /\ rw_cells rsegs m' (R + 72) [C8 (Z_to_bv 64 (bv_unsigned na + k))]
    /\ u32arr rsegs m' (free_array_of sb c + 4 * (nf - k)) ws.

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
  | |- _ \/ _ => first [ solve [kung; slia] | fside_tail E ]
  | |- _ => fside_tail E
  end.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Ltac2 Require Ltac2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require LiaTwx2.
Ltac2 hot_tf_keep_existing names :=
  let hs := Ltac2.List.map (fun h => let (id, _, _) := h in id) (Ltac2.Control.hyps ()) in
  Ltac2.Std.keep (Ltac2.List.filter (fun n => Ltac2.List.exist (fun h => Ltac2.Ident.equal h n) hs) names).
Ltac hot_tf_cut := ltac2:(Ltac2.Control.enter (fun () => hot_tf_keep_existing [@CR1; @LO; @RIHI; @ACLO; @HE; @RILO; @SEP_ER; @CHI])).
Ltac hot_tf_lia0 :=
  first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_prune; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
        | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_prune; Zify.zify; xlia zchecker
        | Zify.zify; xlia zchecker ].
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tran6di.tf_lia ::= hot_tf_cut; hot_tf_lia0.
(* [comment removed for export] *)
Section CombRefill.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte).
  Variables (lo C c maxc csz sb ri nf sz : Z) (ks ws : list word) (kw statv na : word).

  #[warnings="-notation-for-abbreviation"] Local Notation usp := (bv_unsigned sp).
  #[warnings="-notation-for-abbreviation"] Local Notation E := (C + 80 * c).
  #[warnings="-notation-for-abbreviation"] Local Notation R := (ri + 128 * c).
  #[warnings="-notation-for-abbreviation"] Local Notation k := (Z.shiftr maxc 1).
  #[warnings="-notation-for-abbreviation"] Local Notation fa := (free_array_of sb c).

  Hypothesis MI : mem_inv rsegs m.
  Hypothesis ST : stk rsegs m lo usp.
  Hypothesis LO : alloc_ceiling <= lo /\ lo <= usp - 208.
  Hypothesis SPA : usp mod 16 = 0.
  Hypothesis SPH : usp <= 2^47.
  Hypothesis RA2 : bv_unsigned ra mod 2 = 0.
  Hypothesis SZ : 1 <= sz <= 65536.
  Hypothesis SZ8 : sz mod 8 = 0.
  Hypothesis HC : c = size_class sz.
  Hypothesis BLK : classid_blk_stmt.
  Hypothesis CLO : aobj C 3888.   (* [comment removed for export] *)
  Hypothesis CHI : C + 3888 <= alloc_ceiling.
  Hypothesis CAL : C mod 16 = 0.
  Hypothesis SBLO : kHighMemBeg <= sb.
  Hypothesis SBHI : sb + 2^37 <= alloc_ceiling.
  Hypothesis SBAL : sb mod 4096 = 0.
  Hypothesis RILO : kHighMemBeg <= ri.
  Hypothesis RIHI : ri + 4096 <= alloc_ceiling.
  Hypothesis RIAL : ri mod 128 = 0.
  Hypothesis SEP_cr : apart C 3888 ri 4096.
  Hypothesis SEP_cs : apart C 3888 sb (2^37).
  Hypothesis SEP_rs : apart ri 4096 sb (2^37).
  Hypothesis MXR : 2 <= maxc <= 16.
  Hypothesis CSZ : 0 <= csz < 2^64.
  Hypothesis LKS : length ks = 16%nat.
  Hypothesis LWS : length ws = Z.to_nat k.
  Hypothesis NNF : k <= nf.
  Hypothesis NFH : nf < 2^27.
  Hypothesis KW : nth_error ws (Z.to_nat (k - 1)) = Some kw.
  Hypothesis KWR : bv_unsigned kw < 2^32.
  (* [comment removed for export] *)
  Hypothesis CSB : ro_cells rsegs m 0xb1d78 [C8 (wz sb)].
  Hypothesis CRI : ro_cells rsegs m 0xb1d88 [C8 (wz ri)].
  Hypothesis PC : rw_cells rsegs m E [C4 (wz 0); C4 (wz maxc); C8 (wz csz); CB 64 (u32s ks)].
  Hypothesis STA : rw_cells rsegs m (C + 2576) [C8 statv].
  Hypothesis MX : rw_cells rsegs m R [C8 (wz 0)].
  Hypothesis NFC : rw_cells rsegs m (R + 16) [C8 (wz nf)].
  Hypothesis NAL : rw_cells rsegs m (R + 72) [C8 na].
  Hypothesis FARR : u32arr rsegs m (fa + 4 * (nf - k)) ws.

  (* [comment removed for export] *)
  #[using="KWR KW LWS LKS CSZ MXR SEP_rs SEP_cs SEP_cr RIAL RIHI RILO SBAL SBHI SBLO CAL CLO HC SZ SPH SPA LO sz Clg"] Lemma comb_gfa_tail : forall (Q : machine_state -> Prop) (nf0 : Z) (pad : list byte) (statv0 : word) (mg : word -> option byte),
    rw_cells rsegs mg (usp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    rw_cells rsegs mg (usp + -48 + -32) (refill_frame pad (wz E) (wz c) (wz 244684)) ->
    ro_cells rsegs mg 0xb1d78 [C8 (wz sb)] ->
    rw_cells rsegs mg (C + 2576) [C8 statv0] ->
    0 <= nf0 -> nf0 + k < 2^27 ->
    (forall (t0'' t1'' t2'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' statv' : word) (m' : word -> option byte),
        rw_cells rsegs m' E [C4 (wz (k - 1)); C4 (wz maxc); C8 (wz csz); CB 64 (u32s (ws ++ skipn (Z.to_nat k) ks))] ->
        rw_cells rsegs m' (C + 2576) [C8 statv'] ->
        rw_cells rsegs m' R [C8 (wz 0)] -> rw_cells rsegs m' (R + 16) [C8 (wz nf0)] ->
        rw_cells rsegs m' (R + 72) [C8 (wz (bv_unsigned na + k))] ->
        u32arr rsegs m' (fa + 4 * nf0) ws ->
        munch (comb_refill_W sp C c ri) mg m' -> wmono rsegs mg m' -> mem_inv rsegs m' -> stk rsegs m' lo usp ->
        evt rsegs Q (MS (mkR ra sp gp tp t0'' t1'' t2'' s0 s1 (wz (sb + c * 2^32 + 16 * bv_unsigned kw)) a1'' a2'' a3'' a4'' a5'' a6'' a7''
                            s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3'' t4'' t5'' t6'')
                        F (ret_pc ra) fc None m' (seg_rom rsegs))) ->
    forall ms', gfa_post gp tp F fc (usp + -48 + -32) lo R fa nf0 k E 0 maxc csz na ws ks
                         s11 s10 s9 s8 s7 s6 s5 (wz 0xb1d58) (wz C) (wz 8) (wz k) (wz E) (wz refill_ret) mg ms' ->
    evt rsegs Q ms'.
  Proof. try clear RA2. try clear SZ8. try clear BLK. try clear CHI.   (* [comment removed for export] *)
    clear MI ST CSB CRI PC STA MX NFC NAL FARR NNF NFH.
    intros Q nf0 pad statv0 mg CF1 RF1 CSB1 STA1 NF0 NF1 K ms' PO.
    pose proof alloc_ceiling_val as CV. pose proof CLO as ACLO; aobj_lin1 ACLO. pose proof (zr_word sp) as SPR; unfold inr64 in SPR.
    pose proof (size_class_range sz ltac:(unfold kMaxSize; lia)) as CR1. rewrite <- HC in CR1.
    assert (KR : 1 <= k <= 8) by (rewrite Z.shiftr_div_pow2 by lia; change (2^1) with 2; split; [apply Z.div_le_lower_bound | apply Z.div_le_upper_bound]; lia).
    unfold comb_refill_W, kHighMemBeg, free_array_of, refill_frame in *.
    assert (SEP_ER : E + 80 <= R \/ R + 128 <= E) by (revert SEP_cr CR1; unfold apart; clear; intros; lia).
    assert (SEP_ES : E + 80 <= sb \/ sb + 2^37 <= E) by (revert SEP_cs CR1; unfold apart; clear; intros; lia).
    assert (SEP_RS : R + 128 <= sb \/ sb + 2^37 <= R) by (revert SEP_rs CR1; unfold apart; clear; intros; lia).
    (* [comment removed for export] *)
    remember (C + 80 * c) as Ev eqn:HE.
    unfold gfa_post in PO. destruct_exs PO.
    (first [ dand10 PO as E3 MUc WMc MI3 ST3 MX3 NFC3 NAL3 FARR3 PC3 | destruct PO as (E3 & MUc & WMc & MI3 & ST3 & MX3 & NFC3 & NAL3 & FARR3 & PC3) ]). subst ms'.
    assert (LO0 : 0 <= lo) by (destruct ST3 as [? _]; assumption).
    rewrite ?unsigned_lit in MUc, ST3 by lia.
    pose proof (munch_refl [(usp - 208, usp); (Ev, Ev + 80); (C + 2576, C + 2584); (R, R + 8); (R + 16, R + 24); (R + 72, R + 80)] mg) as MU.
    pose proof (wmono_refl rsegs mg) as WM.
    kpost MUc WMc.
    replace (ret_pc (Z_to_bv 64 refill_ret)) with (Z_to_bv 64 refill_ret) by (symmetry; apply ret_pc_even; [unfold refill_ret; lia|reflexivity]).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename mc into m3 end.
    (* [comment removed for export] *)
    eapply (refill_epi_ok _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s10 s11 _ _ _ _ F fc m3 (usp + -48) lo Ev k 1 0 maxc csz
              (ws ++ skipn (Z.to_nat k) ks) pad); [> try (fside CV) .. | idtac].
    all: try (first [fside CV | kcellz | zmod | rewrite HE; zmod | f_equal; lia | rewrite length_app, length_skipn, LWS, LKS; lia ]).
    intros m4 PC4 MU4 WM4 MI4 ST4. rewrite ?unsigned_lit in MU4, ST4 by lia. cbn [Z.eqb Pos.eqb] in PC4.
    clear PC3 RF1. kpost MU4 WM4.
    replace (ret_pc (Z_to_bv 64 244684)) with (Z_to_bv 64 244684) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    (* [comment removed for export] *)
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).  (* [comment removed for export] *)
    amz. br_not_taken. (* [comment removed for export] *)
    amz. rewrite sx32_small by lia. (* [comment removed for export] *)
    amz. amz. amz. amz. (* [comment removed for export] *)
    do 7 amz.
    rewrite slli32_srli30 by lia. amz.
    assert (LKS' : length (ws ++ skipn (Z.to_nat k) ks) = 16%nat) by (rewrite length_app, length_skipn, LWS, LKS; lia).
    assert (KW' : nth_error (ws ++ skipn (Z.to_nat k) ks) (Z.to_nat (k - 1)) = Some kw) by (rewrite nth_error_app1 by (rewrite LWS; lia); exact KW).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      lazymatch goal with H : rw_cells rsegs mm Ev _ |- _ =>
        pose proof (u32arr_read rsegs mm (Ev + 16) _ (k - 1) kw (wa (Ev + 16 + 4 * (k - 1))) (pc_chunks_u32arr mm Ev _ _ _ _ H LKS') KW' ltac:(lia) eq_refl) as HR end end.
    amz. rewrite (zx32_word kw KWR). clear HR.
    amz. (* [comment removed for export] *) amz. (* [comment removed for export] *)
    do 6 amz. first [if_true | if_false].
    do 8 amz.
    replace (Z_to_bv 64 (bv_unsigned kw ≪ 4 + (c ≪ 32 + sb))) with (Z_to_bv 64 (sb + c * 2^32 + 16 * bv_unsigned kw))
      by (rewrite !Z.shiftl_mul_pow2 by lia; f_equal; lia).
    lazymatch goal with H : rw_cells rsegs _ Ev _ |- _ => replace (k + -1) with (k - 1) in H by lia end.
    lazymatch goal with H : rw_cells rsegs _ (usp + -48) _ |- _ => lazymatch goal with S : stk rsegs _ lo _ |- _ => release_frame H S (bv_unsigned sp) end end.
    subst Ev. eapply K; first [kcellz | eassumption].
  Qed.

  (* [comment removed for export] *)
  #[using="KWR KW NFH NNF LWS LKS CSZ MXR SEP_rs SEP_cs SEP_cr RIAL RIHI RILO SBAL SBHI SBLO CAL CLO HC SZ SPH SPA LO sz Clg"] Lemma comb_refill_gfa : forall (Q : machine_state -> Prop) (t0' t1' t2' a5' a6' a7' t3' t4' t5' t6' : word) (pad : list byte)
      (m1 : word -> option byte),
    mem_inv rsegs m1 -> stk rsegs m1 lo (usp + -48 + -32) ->
    rw_cells rsegs m1 (usp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    rw_cells rsegs m1 (usp + -48 + -32) (refill_frame pad (wz E) (wz c) (wz 244684)) ->
    ro_cells rsegs m1 0xb1d78 [C8 (wz sb)] -> ro_cells rsegs m1 0xb1d88 [C8 (wz ri)] ->
    rw_cells rsegs m1 E [C4 (wz 0); C4 (wz maxc); C8 (wz csz); CB 64 (u32s ks)] ->
    rw_cells rsegs m1 (C + 2576) [C8 statv] ->
    rw_cells rsegs m1 R [C8 (wz 0)] -> rw_cells rsegs m1 (R + 16) [C8 (wz nf)] -> rw_cells rsegs m1 (R + 72) [C8 na] ->
    u32arr rsegs m1 (fa + 4 * (nf - k)) ws ->
    (forall (t0'' t1'' t2'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' statv' : word) (m' : word -> option byte),
        rw_cells rsegs m' E [C4 (wz (k - 1)); C4 (wz maxc); C8 (wz csz); CB 64 (u32s (ws ++ skipn (Z.to_nat k) ks))] ->
        rw_cells rsegs m' (C + 2576) [C8 statv'] ->
        rw_cells rsegs m' R [C8 (wz 0)] -> rw_cells rsegs m' (R + 16) [C8 (wz (nf - k))] ->
        rw_cells rsegs m' (R + 72) [C8 (wz (bv_unsigned na + k))] ->
        u32arr rsegs m' (fa + 4 * (nf - k)) ws ->
        munch (comb_refill_W sp C c ri) m1 m' -> wmono rsegs m1 m' -> mem_inv rsegs m' -> stk rsegs m' lo usp ->
        evt rsegs Q (MS (mkR ra sp gp tp t0'' t1'' t2'' s0 s1 (wz (sb + c * 2^32 + 16 * bv_unsigned kw)) a1'' a2'' a3'' a4'' a5'' a6'' a7''
                            s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3'' t4'' t5'' t6'')
                        F (ret_pc ra) fc None m' (seg_rom rsegs))) ->
    evt rsegs Q
        (MS (mkR (wz refill_ret) (wz (usp + -48 + -32)) gp tp t0' t1' t2' (wz E) (wz k)
                 (wz 0xb1d58) (wz (C + 2560)) (wz c) (wz (E + 16)) (wz k) a5' a6' a7'
                 (wz 8) (wz C) (wz 0xb1d58) s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
            F (wz gfa_entry) fc None m1 (seg_rom rsegs)).
  Proof. try clear RA2. try clear SZ8. try clear BLK. try clear CHI.   (* [comment removed for export] *)
    clear MI ST CSB CRI PC STA MX NFC NAL FARR.
    intros Q t0' t1' t2' a5' a6' a7' t3' t4' t5' t6' pad m1 MI1 ST1 CF1 RF1 CSB1 CRI1 PC1 STA1 MX1 NFC1 NAL1 FARR1 K.
    pose proof alloc_ceiling_val as CV. pose proof CLO as ACLO; aobj_lin1 ACLO. pose proof (zr_word sp) as SPR; unfold inr64 in SPR.
    assert (LO0 : 0 <= lo) by (destruct ST1 as [? _]; assumption).
    pose proof (size_class_range sz ltac:(unfold kMaxSize; lia)) as CR1. rewrite <- HC in CR1.
    assert (KR : 1 <= k <= 8) by (rewrite Z.shiftr_div_pow2 by lia; change (2^1) with 2; split; [apply Z.div_le_lower_bound | apply Z.div_le_upper_bound]; lia).
    unfold kHighMemBeg, free_array_of in *.
    assert (SEP_ER : E + 80 <= R \/ R + 128 <= E) by (revert SEP_cr CR1; unfold apart; clear; intros; lia).
    assert (SEP_ES : E + 80 <= sb \/ sb + 2^37 <= E) by (revert SEP_cs CR1; unfold apart; clear; intros; lia).
    assert (SEP_RS : R + 128 <= sb \/ sb + 2^37 <= R) by (revert SEP_rs CR1; unfold apart; clear; intros; lia).
    pose proof (munch_refl (comb_refill_W sp C c ri) m1) as MU. unfold comb_refill_W, free_array_of in MU. cbv zeta in MU.
    pose proof (wmono_refl rsegs m1) as WM.
    (* [comment removed for export] *)
    eapply (gfa_lock_ok _ _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s10 s11 _ _ _ _ F fc m1 lo ri sb c);
      [> try (fside CV) .. | idtac].
    all: try (first [fside CV | kcellz | zmod]).
    intros t0b t1b t2b a0b a5b a6b a7b t3b t4b t5b t6b scr m2 MX2 GF2 MU2 WM2 MI2 ST2.
    rewrite ?unsigned_lit in GF2, MU2, ST2 by lia.
    clear MX1. kpost MU2 WM2.
    unfold gfa_locked. rewrite ?unsigned_lit by lia.
    (* [comment removed for export] *)
    eapply evt_cut; [eapply (gfa_fast_ok _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m2
                               (usp + -48 + -32) lo R sb c nf k E 0 maxc csz na ws ks scr)
                    | eapply (comb_gfa_tail Q (nf - k) pad statv m2); first [kcellz | lia | idtac] ];
      [> try (fside CV) .. | idtac].
    all: try (first [fside CV | kcellz | zmod]).
    intros. lazymatch goal with MUg : munch (comb_refill_W _ _ _ _) m2 ?mb, WMg : wmono rsegs m2 ?mb' |- _ =>
      unfold comb_refill_W, free_array_of in MUg; cbv zeta in MUg; kpost MUg WMg end.
    eapply K; first [kcellz | eassumption].
  Qed.

  (* [comment removed for export] *)
  #[using="PC LKS CSZ MXR RILO SBLO CAL CHI CLO BLK HC SZ8 SZ SPH SPA LO ST MI ks ri sb csz Clg"] Lemma comb_to_gfa : forall (Q : machine_state -> Prop),
    (forall (t0' t1' a5' a6' a7' : word) (pad : list byte) (m1 : word -> option byte),
        mem_inv rsegs m1 -> stk rsegs m1 lo (usp + -48 + -32) ->
        rw_cells rsegs m1 (usp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
        rw_cells rsegs m1 (usp + -48 + -32) (refill_frame pad (wz E) (wz c) (wz 244684)) ->
        munch [(usp - 208, usp)] m m1 -> wmono rsegs m m1 ->
        evt rsegs Q
            (MS (mkR (wz refill_ret) (wz (usp + -48 + -32)) gp tp t0' t1' t2 (wz E) (wz k)
                     (wz 0xb1d58) (wz (C + 2560)) (wz c) (wz (E + 16)) (wz k) a5' a6' a7'
                     (wz 8) (wz C) (wz 0xb1d58) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (wz gfa_entry) fc None m1 (seg_rom rsegs))) ->
    evt rsegs Q
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0xb1d58) (Z_to_bv 64 C) (Z_to_bv 64 sz) (Z_to_bv 64 8) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 comb_hit_entry) fc None m (seg_rom rsegs)).
  Proof. try clear RA2. try clear SBHI. try clear SBAL. try clear RIHI. try clear RIAL. try clear SEP_cr. try clear SEP_cs. try clear SEP_rs.   (* [comment removed for export] *)
    clear CSB CRI STA MX NFC NAL FARR KW KWR LWS NNF NFH.
    intros Q K.
    pose proof (size_class_range sz ltac:(unfold kMaxSize; lia)) as CR1. rewrite <- HC in CR1.
    pose proof (class_size_range c CR1) as CSR.
    pose proof alloc_ceiling_val as CV. pose proof CLO as ACLO; aobj_lin1 ACLO. pose proof (zr_word sp) as SPR; unfold inr64 in SPR.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    assert (KR : 1 <= k <= 8) by (rewrite Z.shiftr_div_pow2 by lia; change (2^1) with 2; split; [apply Z.div_le_lower_bound | apply Z.div_le_upper_bound]; lia).
    pose proof (munch_refl [(usp - 208, usp)] m) as MU.
    pose proof (wmono_refl rsegs m) as WM.
    unfold kHighMemBeg in *.
    remember (C + 80 * c) as Ev eqn:HE.
    carve_frame 48%nat ST. unfold comb_hit_entry.
    do 11 amz.
    (* [comment removed for export] *)
    rewrite b2z_ltb_false by lia. rewrite Z.add_0_r, Z.mod_small by lia. rewrite lxor_ones64 by lia. br_taken.
    do 3 amz. br_taken.
    amz. amz. br_not_taken. amz. br_not_taken. amz. amz.
    (* [comment removed for export] *)
    let K := fresh "K" in if_cases K; zify_cond K;
    [ eapply BLK; [lia| exact SZ8 |]; intros a2' a4' a5' a6' a7' t0' t1'; unfold classid_blk_exit; rewrite <- HC
    | do 3 amz; rewrite (Z.shiftr_div_pow2 (sz + 31) 5) by lia; change (2^5) with 32;
      rewrite <- (size_class_small sz) by lia; rewrite <- HC ].
    all: amz; br_not_taken; amz; amz; br_not_taken; amz; amz; amz.
    (* [comment removed for export] *)
    all: replace (Z_to_bv 64 (C + c * 80)) with (Z_to_bv 64 Ev) by (f_equal; lia).
    all: amz; rewrite ?sx32_small by lia; amz; br_taken.   (* [comment removed for export] *)
    all: do 7 amz.                                         (* [comment removed for export] *)
    (* [comment removed for export] *)
    all: amz. (* [comment removed for export] *)
    all: eapply (refill_pre_ok _ _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s10 s11 _ _ _ _ F fc _ lo C Ev c 0 maxc csz ks);
      [> try (fside CV) .. | idtac].
    all: try (first [fside CV | kcellz | zmod | rewrite HE; zmod]).
    all: intros pad mr RF1 PC1 MU1 WM1 MI1 ST1; rewrite ?unsigned_lit in RF1, MU1, ST1 by lia.
    all: clear PC PC1; kpost MU1 WM1; rewrite ?unsigned_lit by lia.
    all: subst Ev; eapply K; first [kcellz | eassumption].
  Qed.

  (* [comment removed for export] *)
  #[using="FARR NAL NFC MX STA PC CRI CSB KWR KW NFH NNF LWS LKS CSZ MXR SEP_rs SEP_cs SEP_cr RIAL RIHI RILO SBAL SBHI SBLO CAL CHI CLO BLK HC SZ8 SZ SPH SPA LO ST MI statv Clg"] Lemma comb_alloc_refill :
    evt rsegs (comb_refill_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc C c maxc csz sb ri nf ks ws kw na lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0xb1d58) (Z_to_bv 64 C) (Z_to_bv 64 sz) (Z_to_bv 64 8) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 comb_hit_entry) fc None m (seg_rom rsegs)).
  Proof. try clear RA2.   (* [comment removed for export] *)
    pose proof alloc_ceiling_val as CV. pose proof CLO as ACLO; aobj_lin1 ACLO. pose proof (zr_word sp) as SPR; unfold inr64 in SPR.
    pose proof (size_class_range sz ltac:(unfold kMaxSize; lia)) as CR1. rewrite <- HC in CR1.
    assert (KR : 1 <= k <= 8) by (rewrite Z.shiftr_div_pow2 by lia; change (2^1) with 2; split; [apply Z.div_le_lower_bound | apply Z.div_le_upper_bound]; lia).
    pose proof (munch_refl (comb_refill_W sp C c ri) m) as MU. unfold comb_refill_W in MU. cbv zeta in MU.
    pose proof (wmono_refl rsegs m) as WM.
    unfold kHighMemBeg, free_array_of in *.
    apply comb_to_gfa. intros t0' t1' a5' a6' a7' pad m1 MI1 ST1 CF1 RF1 MU1 WM1.
    kpost MU1 WM1.
    eapply comb_refill_gfa; first [kcellz | eassumption | idtac].
    intros. apply evt_done. unfold comb_refill_post, comb_refill_W, free_array_of. cbv zeta.
    repeat (lazymatch goal with |- ex _ => eexists end). split; [reflexivity|].
    lazymatch goal with MUg : munch (comb_refill_W _ _ _ _) ?ma ?mb |- _ =>
      lazymatch goal with WMg : wmono rsegs ma mb |- _ => unfold comb_refill_W, free_array_of in MUg; cbv zeta in MUg; kpost MUg WMg end end.
    OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits; first [kcellz | eassumption].
  Qed.
End CombRefill.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition comb_refill0_W (sp : word) (C c ri : Z) : list (Z * Z) :=
  let R := ri + 128 * c in
  [(bv_unsigned sp - 208, bv_unsigned sp); (C + 80, C + 2560); (C + 2576, C + 2584); (R, R + 8); (R + 16, R + 24); (R + 72, R + 80)].

Definition comb_refill0_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (C c sb ri nf : Z) (cnt : Z -> Z) (ks : Z -> list word) (ws : list word) (kw na : word) (lo : Z) (m : word -> option byte)
    : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 statv' m',
    let R := ri + 128 * c in let k := refill_count c in
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (sb + c * 2^32 + 16 * bv_unsigned kw)) a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch (comb_refill0_W sp C c ri) m m'
    /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp)
    /\ (forall i, 1 <= i <= 31 -> i <> c ->
          rw_cells rsegs m' (C + 80 * i) [C4 (Z_to_bv 64 (cnt i)); C4 (Z_to_bv 64 (max_count i)); C8 (Z_to_bv 64 (class_size i)); CB 64 (u32s (ks i))])
    /\ rw_cells rsegs m' (C + 80 * c) [C4 (Z_to_bv 64 (k - 1)); C4 (Z_to_bv 64 (max_count c)); C8 (Z_to_bv 64 (class_size c));
                                      CB 64 (u32s (ws ++ skipn (Z.to_nat k) (ks c)))]
    /\ rw_cells rsegs m' (C + 2576) [C8 statv']
    /\ rw_cells rsegs m' R [C8 (Z_to_bv 64 0)]
    /\ rw_cells rsegs m' (R + 16) [C8 (Z_to_bv 64 (nf - k))]
    /\ rw_cells rsegs m' (R + 72) [C8 (Z_to_bv 64 (bv_unsigned na + k))]
    /\ u32arr rsegs m' (free_array_of sb c + 4 * (nf - k)) ws.

Section CombRefill0.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte).
  Variables (lo C c sb ri nf sz : Z) (cnt mc0 cs0 : Z -> Z) (ks : Z -> list word) (ws : list word) (kw statv na : word).

  #[warnings="-notation-for-abbreviation"] Local Notation usp := (bv_unsigned sp).
  #[warnings="-notation-for-abbreviation"] Local Notation E := (C + 80 * c).
  #[warnings="-notation-for-abbreviation"] Local Notation R := (ri + 128 * c).
  #[warnings="-notation-for-abbreviation"] Local Notation k := (refill_count c).
  #[warnings="-notation-for-abbreviation"] Local Notation fa := (free_array_of sb c).

  Hypothesis MI : mem_inv rsegs m.
  Hypothesis ST : stk rsegs m lo usp.
  Hypothesis LO : alloc_ceiling <= lo /\ lo <= usp - 208.
  Hypothesis SPA : usp mod 16 = 0.
  Hypothesis SPH : usp <= 2^47.
  Hypothesis RA2 : bv_unsigned ra mod 2 = 0.
  Hypothesis SZ : 1 <= sz <= 65536.
  Hypothesis SZ8 : sz mod 8 = 0.
  Hypothesis HC : c = size_class sz.
  Hypothesis BLK : classid_blk_stmt.
  Hypothesis CLO : aobj C 3888.   (* [comment removed for export] *)
  Hypothesis CHI : C + 3888 <= alloc_ceiling.
  Hypothesis CAL : C mod 16 = 0.
  Hypothesis SBLO : kHighMemBeg <= sb.
  Hypothesis SBHI : sb + 2^37 <= alloc_ceiling.
  Hypothesis SBAL : sb mod 4096 = 0.
  Hypothesis RILO : kHighMemBeg <= ri.
  Hypothesis RIHI : ri + 4096 <= alloc_ceiling.
  Hypothesis RIAL : ri mod 128 = 0.
  Hypothesis SEP_cr : apart C 3888 ri 4096.
  Hypothesis SEP_cs : apart C 3888 sb (2^37).
  Hypothesis SEP_rs : apart ri 4096 sb (2^37).
  Hypothesis LWS : length ws = Z.to_nat k.
  Hypothesis NNF : k <= nf.
  Hypothesis NFH : nf < 2^27.
  Hypothesis KW : nth_error ws (Z.to_nat (k - 1)) = Some kw.
  Hypothesis KWR : bv_unsigned kw < 2^32.
  (* [comment removed for export] *)
  Hypothesis CSB : ro_cells rsegs m 0xb1d78 [C8 (wz sb)].
  Hypothesis CRI : ro_cells rsegs m 0xb1d88 [C8 (wz ri)].
  Hypothesis LINES : forall i, 1 <= i <= 31 ->
      0 <= cnt i < 2^32 /\ 0 <= mc0 i < 2^32 /\ 0 <= cs0 i < 2^64 /\ length (ks i) = 16%nat /\
      rw_cells rsegs m (C + 80 * i) [C4 (wz (cnt i)); C4 (wz (mc0 i)); C8 (wz (cs0 i)); CB 64 (u32s (ks i))].
  Hypothesis MC0 : mc0 c = 0.
  Hypothesis CNT0 : cnt c = 0.
  Hypothesis STA : rw_cells rsegs m (C + 2576) [C8 statv].
  Hypothesis MX : rw_cells rsegs m R [C8 (wz 0)].
  Hypothesis NFC : rw_cells rsegs m (R + 16) [C8 (wz nf)].
  Hypothesis NAL : rw_cells rsegs m (R + 72) [C8 na].
  Hypothesis FARR : u32arr rsegs m (fa + 4 * (nf - k)) ws.

  (* [comment removed for export] *)
  #[using="CNT0 MC0 LINES RILO SBLO CHI CLO BLK HC SZ8 SZ SPH LO ST MI cs0 mc0 ri sb Clg"] Lemma comb_to_gfa0 : forall (Q : machine_state -> Prop),
    (forall (a5' a6' a7' t0' t1' t2' t3' t4' t5' : word) (pad : list byte) (m1 : word -> option byte),
        mem_inv rsegs m1 -> stk rsegs m1 lo (usp + -48 + -32) ->
        rw_cells rsegs m1 (usp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
        rw_cells rsegs m1 (usp + -48 + -32) (refill_frame pad (wz E) (wz c) (wz 244684)) ->
        (forall i, 1 <= i <= 31 ->
           rw_cells rsegs m1 (C + 80 * i) [C4 (wz (cnt i)); C4 (wz (max_count i)); C8 (wz (class_size i)); CB 64 (u32s (ks i))]) ->
        munch [(usp - 208, usp); (C + 80, C + 2560)] m m1 -> wmono rsegs m m1 ->
        evt rsegs Q
            (MS (mkR (wz refill_ret) (wz (usp + -48 + -32)) gp tp t0' t1' t2' (wz E) (wz k)
                     (wz 0xb1d58) (wz (C + 2560)) (wz c) (wz (E + 16)) (wz k) a5' a6' a7'
                     (wz 8) (wz C) (wz 0xb1d58) s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6)
                F (wz gfa_entry) fc None m1 (seg_rom rsegs))) ->
    evt rsegs Q
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0xb1d58) (Z_to_bv 64 C) (Z_to_bv 64 sz) (Z_to_bv 64 8) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 comb_hit_entry) fc None m (seg_rom rsegs)).
  Proof. try clear SPA. try clear RA2. try clear CAL. try clear SBHI. try clear SBAL. try clear RIHI. try clear RIAL. try clear SEP_cr. try clear SEP_cs. try clear SEP_rs. try clear MXR. try clear CSZ.   (* [comment removed for export] *)
    clear CSB CRI STA MX NFC NAL FARR KW KWR LWS NNF NFH.
    intros Q K.
    pose proof (size_class_range sz ltac:(unfold kMaxSize; lia)) as CR1. rewrite <- HC in CR1.
    pose proof (class_size_range c CR1) as CSR. unfold kMaxSize in CSR.
    pose proof alloc_ceiling_val as CV. pose proof CLO as ACLO; aobj_lin1 ACLO. pose proof (zr_word sp) as SPR; unfold inr64 in SPR.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    (first [ pose proof ((max_count_facts c ltac:(lia))) as dR_2; dand3 dR_2 as MCR MCH RCR | pose proof (max_count_facts c ltac:(lia)) as (MCR & MCH & RCR) ]).
    (first [ pose proof ((LINES c ltac:(lia))) as dR_3; dand5 dR_3 as _ _ _ LKS PC | pose proof (LINES c ltac:(lia)) as (_ & _ & _ & LKS & PC) ]). rewrite MC0, CNT0 in PC.
    pose proof (munch_refl [(usp - 208, usp); (C + 80, C + 2560)] m) as MU.
    pose proof (munch_refl [(usp - 208, usp)] m) as MUS.
    pose proof (wmono_refl rsegs m) as WM.
    unfold kHighMemBeg in *.
    remember (C + 80 * c) as Ev eqn:HE.
    carve_frame 48%nat ST. unfold comb_hit_entry.
    do 11 amz.
    rewrite b2z_ltb_false by lia. rewrite Z.add_0_r, Z.mod_small by lia. rewrite lxor_ones64 by lia. br_taken.
    do 3 amz. br_taken.
    amz. amz. br_not_taken. amz. br_not_taken. amz. amz.
    let K := fresh "K" in if_cases K; zify_cond K;
    [ eapply BLK; [lia| exact SZ8 |]; intros a2' a4' a5' a6' a7' t0' t1'; unfold classid_blk_exit; rewrite <- HC
    | do 3 amz; rewrite (Z.shiftr_div_pow2 (sz + 31) 5) by lia; change (2^5) with 32;
      rewrite <- (size_class_small sz) by lia; rewrite <- HC ].
    all: amz; br_not_taken; amz; amz; br_not_taken; amz; amz; amz.
    all: replace (Z_to_bv 64 (C + c * 80)) with (Z_to_bv 64 Ev) by (f_equal; lia).
    all: amz; rewrite ?sx32_small by lia; amz; br_taken.
    all: do 7 amz.
    (* [comment removed for export] *)
    all: amz. (* [comment removed for export] *)
    all: subst Ev.
    all: lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (LINES0 : forall i, 1 <= i <= 31 -> 0 <= cnt i < 2^32 /\ 0 <= mc0 i < 2^32 /\ 0 <= cs0 i < 2^64 /\ length (ks i) = 16%nat /\
                rw_cells rsegs mm (C + 80 * i) [C4 (wz (cnt i)); C4 (wz (mc0 i)); C8 (wz (cs0 i)); CB 64 (u32s (ks i))])
        by (intros i Hi; (first [ pose proof ((LINES i Hi)) as dR_4; dand5 dR_4 as X1 X2 X3 X4 X5 | destruct (LINES i Hi) as (X1 & X2 & X3 & X4 & X5) ]); refine (conj X1 (conj X2 (conj X3 (conj X4 _))));
            eapply (rw_cells_transport rsegs _ m mm); [exact X5 | exact MUS | exact WM | cbn [disjoint_from]; simpl_sizes; lia]) end.
    all: clear PC.
    all: eapply (refill_pre0_ok _ _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s10 s11 _ _ _ _ F fc _ lo C c cnt mc0 cs0 ks);
      [> try (fside CV) .. | idtac].
    all: try (first [fside CV | kcellz | zmod]).
    all: intros a5r a6r a7r t0e t1e t2e t3e t4e t5e pad mr RF1 LINES1 MU1 WM1 MI1 ST1;
         rewrite ?unsigned_lit in RF1, MU1, ST1 by lia.
    all: clear LINES0 MUS; kpost MU1 WM1; rewrite ?unsigned_lit by lia.
    all: eapply K; first [kcellz | eassumption].
  Qed.

  (* [comment removed for export] *)
End CombRefill0.
Ltac slia ::= first [ exact I | lia | split; [lia|exact I] ].
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End AMallocR.

Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIface OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpm9j OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARtStmts OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARtS4t2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AMTac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AMalc5w.AMalloc2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AMalc5w.AMalloc1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AMallocA OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpm9j.AFreeLib OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AMalz1i.AMallocR.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Ceiling.
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

(* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
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
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Stepobi.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yd.DA_Tac.astep_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.af_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yd.DA_Tac.azstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.af_zstep.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AMTac.amstep_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.amf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AMTac.amz ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.amf_zstep.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require LiaSec.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaSec.lia_sec.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Ltac2 Require Ltac2.
Ltac2 hot_lia_keep_existing names :=
  let hs := Ltac2.List.map (fun h => let (id, _, _) := h in id) (Ltac2.Control.hyps ()) in
  Ltac2.Std.keep (Ltac2.List.filter (fun n => Ltac2.List.exist (fun h => Ltac2.Ident.equal h n) hs) names).
Ltac hot_lia_cut := ltac2:(Ltac2.Control.enter (fun () => hot_lia_keep_existing [@LKS; @LWS; @LO; @ATHR; @NSB; @SBR; @RIR; @KR; @CV; @ABR; @RSR; @RGE; @NS; @NR; @CSR; @SPR; @H; @CGE; @K0; @MXR; @SEP_thr; @RLT; @CE0; @SEP_tr; @SEP_rs; @SEP_ctx; @SO; @SOA])).
Ltac hot_lia_full := OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaSec.lia_sec.
Local Ltac lia ::= hot_lia_cut; hot_lia_full.
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require DietDL3.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.DL.sec_local := Ltac2.Init.true.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.DL.sep_idents := OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.DL.sep_idents_hide.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac base_of1 t := lazymatch t with ?u + _ => base_of1 u | ?u - _ => base_of1 u | _ * ?u => base_of1 u | _ => t end.
Ltac apart_guided1 x y :=
  let bx := base_of1 x in let bz := base_of1 y in
  match goal with
  | H : apart ?a _ ?c _ |- _ =>
      let ba := base_of1 a in let bc := base_of1 c in
      first [ constr_eq bx ba; constr_eq bz bc | constr_eq bx bc; constr_eq bz ba ];
      unfold apart in H; lia
  end.
Ltac slia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits;
  first [ exact I | lia
        | lazymatch goal with
          | |- ?x + _ <= ?y \/ _ <= _ => apart_guided1 x y
          | |- ?x <= ?y \/ _ <= _ => apart_guided1 x y
          end ].
Ltac aobjL H := let A := fresh "A" H in pose proof (proj1 H) as A; aobj_lin1 A.
Ltac aobj_side := first
  [ assumption
  | match goal with H : aobj _ _ /\ _ |- _ => exact (proj1 H) end
  | match goal with K : aobjK _ _ |- _ => exact (aobjK_e _ _ K) end
  | match goal with H : aobj _ _ /\ _ |- _ => apply (aobj_sub _ _ _ _ (proj1 H)); kun; lia end
  | match goal with K : aobjK _ _ |- _ => apply (aobj_sub _ _ _ _ (aobjK_e _ _ K)); kun; lia end
  | apply aobj_hi; kun; lia ].
Ltac pz_side := first
  [ assumption
  | match goal with H : aobj _ _ /\ _ |- _ => apply (aobj_pz_in _ _ _ _ (proj1 H)); kun; lia end
  | match goal with K : aobjK _ _ |- _ => apply (aobj_pz_in _ _ _ _ (aobjK_e _ _ K)); kun; lia end
  | unfold pz_in, kLowShadowMapBeg, kHighMemBeg; kun; lia ].
Ltac sides ::= lazymatch goal with
  | |- evt _ _ _ => idtac
  | |- aobj _ _ => aobj_side
  | |- aobjK _ _ => apply aobjK_i; aobj_side
  | |- pz_in _ _ => pz_side
  | |- apart _ _ _ _ => first [ assumption | slia ]
  | |- forall _, _ -> evt _ _ _ => idtac
  | |- poison_consts _ => unfold poison_consts; sides
  | |- _ /\ _ => split; sides
  | |- _ => sides1 end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section S2R.
Context {Clg : Ceiling}.
  Variables (ra sp gp tp t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte).
  Variables (lo n stkobj canfill ctx thr c maxc sb ri nf AB : Z) (ks ws : list word) (b0w b1w : byte) (kw statv na h2 w4 d8 trace sztag : word)
            (Q : machine_state -> Prop).
  Variables (cs11 cs10 cs9 cs8 cs7 cs6 cs5 cs4 cs3 cs2 cs1 cs0 cra : word) (junk0 : list byte).
  #[warnings="-notation-for-abbreviation"] Local Notation k := (Z.shiftr maxc 1).
  #[warnings="-notation-for-abbreviation"] Local Notation R := (ri + 128 * c).
  Hypothesis MI : mem_inv rsegs m.
  Hypothesis ST : stk rsegs m lo (bv_unsigned sp + -128).
  Hypothesis LO : alloc_ceiling <= lo /\ lo <= bv_unsigned sp - 1024.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis SPR : bv_unsigned sp + 65536 < 2^64.
  Hypothesis NR : 1 <= n <= 64512.
  Hypothesis SO : 0 < stkobj /\ stkobj + 2064 <= 2^47.
  Hypothesis FR : rw_cells rsegs m (bv_unsigned sp + -128) (alloc_s1a_frame sp canfill cs11 cs10 cs9 cs8 cs7 cs6 cs5 cs4 cs3 cs2 cs1 cs0 cra junk0).
  Hypothesis HC : c = size_class (needed_size n).
  Hypothesis BLK : classid_blk_stmt.
  Hypothesis SBc : ro_cells rsegs m 0xb1d78 [C8 (Z_to_bv 64 sb)].
  Hypothesis CRI : ro_cells rsegs m 0xb1d88 [C8 (Z_to_bv 64 ri)].
  (* [comment removed for export] *)
  Hypothesis PC : rw_cells rsegs m (thr + 208 + 80 * c) [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 maxc); C8 (Z_to_bv 64 (class_size c)); CB 64 (u32s ks)].
  Hypothesis LKS : length ks = 16%nat.
  Hypothesis MXR : 2 <= maxc <= 16.
  Hypothesis STA : rw_cells rsegs m ((thr + 208) + 2576) [C8 statv].
  Hypothesis THR : aobj thr 4096 /\ thr + 4096 <= alloc_ceiling.
  Hypothesis THRA : thr mod 16 = 0.
  Hypothesis SBR : kHighMemBeg <= sb /\ sb + 2^37 <= alloc_ceiling.
  Hypothesis SBAL : sb mod 4096 = 0.
  (* [comment removed for export] *)
  Hypothesis RIR : kHighMemBeg <= ri /\ ri + 4096 <= alloc_ceiling.
  Hypothesis RIAL : ri mod 128 = 0.
  Hypothesis SEP_tr : apart thr 4096 ri 4096.
  Hypothesis SEP_rs : apart ri 4096 sb (2^37).
  Hypothesis MX : rw_cells rsegs m R [C8 (Z_to_bv 64 0)].
  Hypothesis NFC : rw_cells rsegs m (R + 16) [C8 (Z_to_bv 64 nf)].
  Hypothesis NAL : rw_cells rsegs m (R + 72) [C8 na].
  Hypothesis FARR : u32arr rsegs m (free_array_of sb c + 4 * (nf - k)) ws.
  Hypothesis LWS : length ws = Z.to_nat k.
  Hypothesis NNF : k <= nf.
  Hypothesis NFH : nf < 2^27.
  Hypothesis KW : nth_error ws (Z.to_nat (k - 1)) = Some kw.
  Hypothesis KWR : bv_unsigned kw < 2^32.
  Hypothesis ABE : AB = sb + c * 2^32 + 16 * bv_unsigned kw.
  Hypothesis ABA : AB mod 32 = 0.
  Hypothesis ABR : sb <= AB /\ AB + class_size c <= sb + 2^37.
  Hypothesis SEP_thr : apart thr 4096 sb (2^37).
  Hypothesis SEP_ctx : apart ctx 0x10000 sb (2^37).
  Hypothesis SEP_tc : apart ctx 0x10000 thr 4096.
  Hypothesis SEP_cri : apart ctx 0x10000 ri 4096.
  (* [comment removed for export] *)
  Hypothesis ABU : AB + class_size c <= sb + c * 2^32 + 3758096384.
  Hypothesis SOA : bv_unsigned sp <= stkobj.
  Hypothesis HDR : rw_cells rsegs m (AB + rz_size n + -16) [C1 b0w; C1 b1w; C2 h2; C4 w4; C8 d8].
  Hypothesis TH0 : ro_cells rsegs m thr [C8 (Z_to_bv 64 ctx)].
  Hypothesis CT8 : ro_cells rsegs m (ctx + 8) [C4 (Z_to_bv 64 0)].
  Hypothesis CTR : aobj ctx 0x10000 /\ ctx + 0x10000 <= alloc_ceiling.
  Hypothesis TRC : ro_cells rsegs m stkobj [C8 trace; C8 sztag].
  (* [comment removed for export] *)
  Definition alloc_seg2R_W : list (Z * Z) :=
    [(bv_unsigned sp - 1024, bv_unsigned sp + -128); ((thr + 208 + 80 * c), (thr + 208 + 80 * c) + 80);
     ((thr + 208) + 2576, (thr + 208) + 2584); (R, R + 8); (R + 16, R + 24); (R + 72, R + 80);
     (AB + rz_size n + -16, (AB + rz_size n))].
  Hypothesis K : forall (m1 : word -> option byte)
                        (ra' t0' t1' t2' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' statv' : word),
      mem_inv rsegs m1 -> stk rsegs m1 lo (bv_unsigned sp + -128) ->
      munch alloc_seg2R_W m m1 -> wmono rsegs m m1 ->
      rw_cells rsegs m1 (thr + 208 + 80 * c) [C4 (Z_to_bv 64 (k - 1)); C4 (Z_to_bv 64 maxc); C8 (Z_to_bv 64 (class_size c)); CB 64 (u32s (ws ++ skipn (Z.to_nat k) ks))] ->
      rw_cells rsegs m1 ((thr + 208) + 2576) [C8 statv'] ->
      rw_cells rsegs m1 R [C8 (Z_to_bv 64 0)] ->
      rw_cells rsegs m1 (R + 16) [C8 (Z_to_bv 64 (nf - k))] ->
      rw_cells rsegs m1 (R + 72) [C8 (Z_to_bv 64 (bv_unsigned na + k))] ->
      u32arr rsegs m1 (free_array_of sb c + 4 * (nf - k)) ws ->
      rw_cells rsegs m1 (AB + rz_size n + -16) [C1 b0w; C1 (Z_to_bv 8 (b1_mid (bv_unsigned b1w))); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 d8] ->
      evt rsegs Q
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0' t1' t2' (Z_to_bv 64 1) (Z_to_bv 64 n)
                 trace sztag a2' a3' a4' a5' a6' a7'
                 (Z_to_bv 64 AB) (Z_to_bv 64 (needed_size n)) (Z_to_bv 64 (AB + rz_size n)) (Z_to_bv 64 (AB + rz_size n + -16)) (Z_to_bv 64 0xb1d58) (Z_to_bv 64 stkobj)
                 (Z_to_bv 64 0) (Z_to_bv 64 ((AB + rz_size n) + n)) (Z_to_bv 64 thr) (Z_to_bv 64 1)
                 t3' t4' t5' t6')
            F (Z_to_bv 64 0x37544) fc None m1 (seg_rom rsegs)).

  #[using="K TRC CTR CT8 TH0 HDR SOA ABU SEP_cri SEP_tc SEP_ctx SEP_thr ABR ABA ABE KWR KW NFH NNF LWS FARR NAL NFC MX SEP_rs SEP_tr RIAL RIR SBAL SBR THRA THR STA MXR LKS PC CRI SBc BLK HC FR SO NR SPR SPA LO ST MI junk0 cra cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11 sztag trace d8 w4 h2 na statv kw b1w b0w ws ks AB nf ri sb maxc c ctx canfill lo Clg"] Lemma alloc_seg2R : evt rsegs Q
        (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2 (Z_to_bv 64 1) (Z_to_bv 64 n)
                 (Z_to_bv 64 0xb1d58) (Z_to_bv 64 (thr + 208)) (Z_to_bv 64 (needed_size n)) (Z_to_bv 64 8) a4 a5 a6 a7
                 (Z_to_bv 64 8) (Z_to_bv 64 (needed_size n)) (Z_to_bv 64 (rz_size n)) (Z_to_bv 64 n) (Z_to_bv 64 0xb1d58) (Z_to_bv 64 stkobj)
                 (Z_to_bv 64 (-8)) (Z_to_bv 64 7) (Z_to_bv 64 thr) (Z_to_bv 64 1)
                 t3 t4 t5 t6)
            F (Z_to_bv 64 0x37438) fc None m (seg_rom rsegs)).
  Proof.
    pose proof alloc_ceiling_val as CE0. aobjL THR. aobjL CTR.
    pose proof (munch_refl alloc_seg2R_W m) as MU. unfold alloc_seg2R_W in MU.
    pose proof (wmono_refl rsegs m) as WM.
    pose proof (rz_size_range n) as RSR. pose proof (rounded_size_ge n) as RGE. pose proof (rounded_size_lt n) as RLT.
    assert (NS : rounded_size n + rz_size n = needed_size n) by reflexivity.
    assert (NSB : 1 <= needed_size n <= 65536).
    { split; [lia|]. apply needed_size_primary_le; apply (proj2 (from_primary_iff n)); unfold kMaxPrimaryUser; lia. }
    pose proof (size_class_range (needed_size n) ltac:(unfold kMaxSize; lia)) as CR1. rewrite <- HC in CR1.
    pose proof (size_class_ge (needed_size n) ltac:(unfold kMaxSize; lia)) as CGE. rewrite <- HC in CGE.
    pose proof (class_size_range c CR1) as CSR. unfold kMaxSize in CSR. unfold kHighMemBeg in *.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (needed_size_mod8 n) as NS8.
    assert (KR : 1 <= k <= 8) by (rewrite Z.shiftr_div_pow2 by lia; change (2^1) with 2; split; [apply Z.div_le_lower_bound | apply Z.div_le_upper_bound]; lia).
    assert (CAL : (thr + 208) mod 16 = 0) by (rewrite Z.add_mod, THRA by lia; reflexivity).
    assert (SEP_cr : apart (thr + 208) 3888 ri 4096) by (generalize SEP_tr; unfold apart; clear; intros; lia).
    assert (SEP_cs : apart (thr + 208) 3888 sb (2^37)) by (generalize SEP_thr; unfold apart; clear; intros; lia).
    (* [comment removed for export] *)
    assert (SEP_tAB : apart thr 4096 AB (class_size c)) by (generalize SEP_thr ABR; unfold apart; clear; intros; lia).
    assert (SEP_rAB : apart ri 4096 AB (class_size c)) by (generalize SEP_rs ABR; unfold apart; clear; intros; lia).
    assert (SEP_cAB : apart ctx 0x10000 AB (class_size c)) by (generalize SEP_ctx ABR; unfold apart; clear; intros; lia).
    pose proof alloc_ceiling_val as CV. unfold alloc_s1a_frame in FR.
    (* [comment removed for export] *)
    box PC. box STA. box MX. box NFC. box NAL. box FARR.
    amz. callx (comb_alloc_refill _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                  lo (thr + 208) c maxc (class_size c) sb ri nf (needed_size n) ks ws kw statv na)
      cleaning (unfold comb_refill_post, comb_refill_W, free_array_of; cbv zeta).
    rewrite <- ABE. amz. amz. br_not_taken. amz. amz.
    replace (Z.land (AB + rz_size n) 7) with 0.
    2:{ symmetry. apply land7_of_mod8; [lia|]. apply mod_add_lit; [lia| |].
        - apply (mod0_down AB 32 8); [exists 4; reflexivity| exact ABA].
        - apply (mod0_down (rz_size n) 16 8); [exists 2; reflexivity| apply rz_size_mod16]. }
    amz. amz. br_taken. amz. amz. br_not_taken.
    (* [comment removed for export] *)
    amz. amz. amz. amz.
    amz. replace (Z.shiftr n 32) with 0 by (rewrite Z.shiftr_div_pow2, Z.div_small by lia; lia).
    amz. replace (Z.shiftr n 48) with 0 by (rewrite Z.shiftr_div_pow2, Z.div_small by lia; lia).
    amz. sb_done. amz. amz. amz. if_false. amz. amz. amz. amz. amz. sb_done.
    (* [comment removed for export] *)
    amz. br_not_taken. amz. amz. amz. amz. amz. amz.
    eapply K; try eassumption.
    all: unfold comb_refill_W, alloc_seg2R_W, free_array_of in *; cbv zeta in *; first [eassumption | idtac].
  Qed.
End S2R.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section PS2R.
Context {Clg : Ceiling}.
  Variables (ra sp gp tp t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte).
  Variables (lo n stkobj canfill ctx thr c maxc sb ri nf AB : Z) (ks ws : list word) (b0w b1w : byte) (kw statv na h2 w4 d8 trace sztag : word).
  Variables (cs11 cs10 cs9 cs8 cs7 cs6 cs5 cs4 cs3 cs2 cs1 cs0 cra : word) (junk0 : list byte).
  #[warnings="-notation-for-abbreviation"] Local Notation k := (Z.shiftr maxc 1).
  #[warnings="-notation-for-abbreviation"] Local Notation R := (ri + 128 * c).
  Hypothesis MI : mem_inv rsegs m.
  Hypothesis ST : stk rsegs m lo (bv_unsigned sp + -128).
  Hypothesis LO : alloc_ceiling <= lo /\ lo <= bv_unsigned sp - 1024.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis SPR : bv_unsigned sp + 65536 < 2^64.
  Hypothesis NR : 1 <= n <= 64512.
  Hypothesis SO : 0 < stkobj /\ stkobj + 2064 <= 2^47.
  Hypothesis FR : rw_cells rsegs m (bv_unsigned sp + -128) (alloc_s1a_frame sp canfill cs11 cs10 cs9 cs8 cs7 cs6 cs5 cs4 cs3 cs2 cs1 cs0 cra junk0).
  Hypothesis HC : c = size_class (needed_size n).
  Hypothesis BLK : classid_blk_stmt.
  Hypothesis SBc : ro_cells rsegs m 0xb1d78 [C8 (Z_to_bv 64 sb)].
  Hypothesis CRI : ro_cells rsegs m 0xb1d88 [C8 (Z_to_bv 64 ri)].
  Hypothesis PC : rw_cells rsegs m (thr + 208 + 80 * c) [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 maxc); C8 (Z_to_bv 64 (class_size c)); CB 64 (u32s ks)].
  Hypothesis LKS : length ks = 16%nat.
  Hypothesis MXR : 2 <= maxc <= 16.
  Hypothesis STA : rw_cells rsegs m ((thr + 208) + 2576) [C8 statv].
  Hypothesis THR : aobj thr 4096 /\ thr + 4096 <= alloc_ceiling.
  Hypothesis THRA : thr mod 16 = 0.
  Hypothesis SBR : kHighMemBeg <= sb /\ sb + 2^37 <= alloc_ceiling.
  Hypothesis SBAL : sb mod 4096 = 0.
  Hypothesis RIR : kHighMemBeg <= ri /\ ri + 4096 <= alloc_ceiling.
  Hypothesis RIAL : ri mod 128 = 0.
  Hypothesis SEP_tr : apart thr 4096 ri 4096.
  Hypothesis SEP_rs : apart ri 4096 sb (2^37).
  Hypothesis MX : rw_cells rsegs m R [C8 (Z_to_bv 64 0)].
  Hypothesis NFC : rw_cells rsegs m (R + 16) [C8 (Z_to_bv 64 nf)].
  Hypothesis NAL : rw_cells rsegs m (R + 72) [C8 na].
  Hypothesis FARR : u32arr rsegs m (free_array_of sb c + 4 * (nf - k)) ws.
  Hypothesis LWS : length ws = Z.to_nat k.
  Hypothesis NNF : k <= nf.
  Hypothesis NFH : nf < 2^27.
  Hypothesis KW : nth_error ws (Z.to_nat (k - 1)) = Some kw.
  Hypothesis KWR : bv_unsigned kw < 2^32.
  Hypothesis ABE : AB = sb + c * 2^32 + 16 * bv_unsigned kw.
  Hypothesis ABA : AB mod 32 = 0.
  Hypothesis ABR : sb <= AB /\ AB + class_size c <= sb + 2^37.
  Hypothesis SEP_thr : apart thr 4096 sb (2^37).
  Hypothesis SEP_ctx : apart ctx 0x10000 sb (2^37).
  Hypothesis SEP_tc : apart ctx 0x10000 thr 4096.
  Hypothesis SEP_cri : apart ctx 0x10000 ri 4096.
  (* [comment removed for export] *)
  Hypothesis ABU : AB + class_size c <= sb + c * 2^32 + 3758096384.
  Hypothesis SOA : bv_unsigned sp <= stkobj.
  Hypothesis HDR : rw_cells rsegs m (AB + rz_size n + -16) [C1 b0w; C1 b1w; C2 h2; C4 w4; C8 d8].
  Hypothesis TH0 : ro_cells rsegs m thr [C8 (Z_to_bv 64 ctx)].
  Hypothesis CT8 : ro_cells rsegs m (ctx + 8) [C4 (Z_to_bv 64 0)].
  Hypothesis CTR : aobj ctx 0x10000 /\ ctx + 0x10000 <= alloc_ceiling.
  Hypothesis TRC : ro_cells rsegs m stkobj [C8 trace; C8 sztag].
    Definition alloc_seg2R_post : machine_state -> Prop := fun ms' =>
    exists (m1 : word -> option byte) (ra' t0' t1' t2' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' statv' : word),
    ms' = (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0' t1' t2' (Z_to_bv 64 1) (Z_to_bv 64 n)
                 trace sztag a2' a3' a4' a5' a6' a7'
                 (Z_to_bv 64 AB) (Z_to_bv 64 (needed_size n)) (Z_to_bv 64 (AB + rz_size n)) (Z_to_bv 64 (AB + rz_size n + -16)) (Z_to_bv 64 0xb1d58) (Z_to_bv 64 stkobj)
                 (Z_to_bv 64 0) (Z_to_bv 64 ((AB + rz_size n) + n)) (Z_to_bv 64 thr) (Z_to_bv 64 1)
                 t3' t4' t5' t6')
            F (Z_to_bv 64 0x37544) fc None m1 (seg_rom rsegs)) /\
    munch (alloc_seg2R_W sp n thr c ri AB) m m1 /\
    wmono rsegs m m1 /\
    mem_inv rsegs m1 /\
    stk rsegs m1 lo (bv_unsigned sp + -128) /\
    rw_cells rsegs m1 (thr + 208 + 80 * c) [C4 (Z_to_bv 64 (k - 1)); C4 (Z_to_bv 64 maxc); C8 (Z_to_bv 64 (class_size c)); CB 64 (u32s (ws ++ skipn (Z.to_nat k) ks))] /\
    rw_cells rsegs m1 ((thr + 208) + 2576) [C8 statv'] /\
    rw_cells rsegs m1 R [C8 (Z_to_bv 64 0)] /\
    rw_cells rsegs m1 (R + 16) [C8 (Z_to_bv 64 (nf - k))] /\
    rw_cells rsegs m1 (R + 72) [C8 (Z_to_bv 64 (bv_unsigned na + k))] /\
    u32arr rsegs m1 (free_array_of sb c + 4 * (nf - k)) ws /\
    rw_cells rsegs m1 (AB + rz_size n + -16) [C1 b0w; C1 (Z_to_bv 8 (b1_mid (bv_unsigned b1w))); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 d8].

  #[using="TRC CTR CT8 TH0 HDR SOA ABU SEP_cri SEP_tc SEP_ctx SEP_thr ABR ABA ABE KWR KW NFH NNF LWS FARR NAL NFC MX SEP_rs SEP_tr RIAL RIR SBAL SBR THRA THR STA MXR LKS PC CRI SBc BLK HC FR SO NR SPR SPA LO ST MI junk0 cra cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11 w4 h2 statv kw ctx canfill Clg"] Lemma alloc_seg2R_spec : evt rsegs alloc_seg2R_post
        (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2 (Z_to_bv 64 1) (Z_to_bv 64 n)
                 (Z_to_bv 64 0xb1d58) (Z_to_bv 64 (thr + 208)) (Z_to_bv 64 (needed_size n)) (Z_to_bv 64 8) a4 a5 a6 a7
                 (Z_to_bv 64 8) (Z_to_bv 64 (needed_size n)) (Z_to_bv 64 (rz_size n)) (Z_to_bv 64 n) (Z_to_bv 64 0xb1d58) (Z_to_bv 64 stkobj)
                 (Z_to_bv 64 (-8)) (Z_to_bv 64 7) (Z_to_bv 64 thr) (Z_to_bv 64 1)
                 t3 t4 t5 t6)
            F (Z_to_bv 64 0x37438) fc None m (seg_rom rsegs)).
  Proof.
    eapply alloc_seg2R; try eassumption. intros. subst. apply evt_done. unfold alloc_seg2R_post.
    repeat (lazymatch goal with |- ex _ => eexists end). cbv zeta.
    OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits. all: first [reflexivity | eassumption].
  Qed.
End PS2R.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Ltac slia ::= first [ exact I | lia | split; [lia|exact I] ].
