(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep FP StoreFast.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.Sj Require Import SjPjNum SjPjDig.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.P Require Import Str_tac Sj_num_kit Sj_num_walk.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.A Require Import Layout Shadow RT_iface RT_iface2 D_defs D_kit Sj_akit Sj_acps Sj_hkit Sj_num_akit Sj_num_amem
     Sj_num_aframe Sj_num_lm_kit Pj_defsA Pj_tocharsA_defs Pj_tocharsA_a Pj_tocharsA_b Pj_tocharsA_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac solve_load ::= first [ solve_load_base | asan_load_hook | asan_zc_hook | num_load_hook | solve_load_image ].
Local Ltac solve_store ::= first [ num_solve_store0 | num_store_hook ].

Section Lay.
  Variable J : tcI.
  Hypothesis OK : tc_ok J.
  Variable mb : mem.
  Variable Q : machine_state -> Prop.
  Variables (e sg n : Z).
  Hypothesis HE : (SF_EMIN <= e <= SF_EMAX)%Z.
  Hypothesis HSG : (0 <= sg <= 1)%Z.
  Hypothesis HN : (1 <= n <= 20)%Z.
  Hypothesis SHPN : nb_shz J mb.

  Notation q := (ti_q J). Notation spq := (ti_spq J). Notation NB := (ti_NB J). Notation f := (ti_f J). Notation Sh := (ti_S J). Notation lo := (ti_lo J).
  Notation TCS pc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xs4 xs5 xs9 xt3 xt4 xt5 xt6 xF xfc m :=
    (MS (mkR xra (Z_to_bv 64 spq) (ti_gp J) (Z_to_bv 64 TPV_A) xt0 xt1 xt2 (Z_to_bv 64 q) (Z_to_bv 64 spq) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
              (Z_to_bv 64 f) xs3 xs4 xs5 (Z_to_bv 64 Sh) (Z_to_bv 64 f) (Z_to_bv 64 2147450880) xs9 (ti_s10 J) (ti_s11 J) xt3 xt4 xt5 xt6)
        xF (Z_to_bv 64 pc) xfc None m (seg_rom asegs)).

  Notation LS pc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs4 xt3 xt4 xt5 xt6 xF xfc m :=
    (TCS pc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 (NB + sg)) xs4 (Z_to_bv 64 n) (Z_to_bv 64 (n + e)) xt3 xt4 xt5 xt6 xF xfc m).

  Hypothesis KZ : tc_rel_k J mb Q.

  Ltac mark_data :=
    repeat match goal with
    | x : word |- _ => lazymatch goal with _ : IsData x |- _ => fail | _ => idtac end; let M := fresh "DM" in assert (M : IsData x) by exact Logic.I
    end.
  Ltac lay_open TI :=
    ti_open TI; ti_env OK;
    match goal with M : munch _ mb _ |- _ => unfold tc_W, ti_spq, ti_S in M end;
    match goal with P : nb_shz _ _ |- _ => unfold nb_shz, tc_W, ti_spq, ti_S in P end;
    match goal with H : (SF_EMIN <= _ <= SF_EMAX)%Z |- _ => unfold SF_EMIN, SF_EMAX in H end;
    match goal with H : rw_cells _ _ _ sh_poison |- _ => unfold sh_poison, pz in H | H : rw_cells _ _ _ sh_zero |- _ => unfold sh_zero, pz in H end;
    pose proof (tc_f8 J OK) as F8; mark_data.

  Ltac cut_rel e tac := first [ eapply evt_eq; [| eapply (KZ e)]; [num_st_eq | ti_close | assumption | tac] | fail 100 "cut: release" ].

  Ltac chk := zastep; zastep; zastep; zastep; if_false.

  Ltac to_rel e tac := zastep; zastep; astep; zastep;
    let K := fresh "K" in if_cases K; zify_cond K;
    [clear K; cut_rel e tac | exfalso; match goal with C : (0x6c9000 <= ti_f J)%Z |- _ => clear - K C; lia end].

  Lemma tc_l4b : forall xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 xF xfc mm,
    TINV J sh_poison mb mm -> frm0 xfc -> (2 <= n)%Z ->
    evt asegs Q (LS 0xb94c8 (Z_to_bv 64 0xb94c8) xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 (NB + sg + 1)) xt3 xt4 xt5 xt6 xF xfc mm).
  Proof using OK KZ SHPN HSG HN HE.
    intros until mm. intros TI FRM HN2. lay_open TI.
    chk. zastep. astep. zastep.
    eapply evt_eq; [| eapply (tc_exp J OK mb Q SHPN KZ (sg + n)%Z); [ti_close | exact FRM | clear - HSG HN; lia]]. num_st_eq.
  Qed.

  Lemma tc_l1b : forall xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 xF xfc mm,
    TINV J sh_poison mb mm -> frm0 xfc -> (0 <= e)%Z -> (n + e <= 15)%Z ->
    evt asegs Q (LS 0xb92fc (Z_to_bv 64 0xb92fc) xt0 xt1 xt2 (Z_to_bv 64 (NB + sg + n)) xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 (e mod 4294967296)) xt3 xt4 xt5 xt6 xF xfc mm).
  Proof using OK KZ SHPN HSG HN HE.
    intros until mm. intros TI FRM E0 P15. lay_open TI.
    zastep. chk. zastep. zastep. astep. chk. zastep. astep. zastep.
    to_rel (NB + sg + (n + e) + 2)%Z ltac:(clear - HSG HN E0 P15; lia).
  Qed.

  Lemma tc_l2b : forall xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 xF xfc mm,
    TINV J sh_poison mb mm -> frm0 xfc -> (1 <= n + e <= 15)%Z ->
    evt asegs Q (LS 0xb942c (Z_to_bv 64 0xb942c) xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 (NB + sg + (n + e))) xt3 xt4 xt5 xt6 xF xfc mm).
  Proof using OK KZ SHPN HSG HN HE.
    intros until mm. intros TI FRM P15. lay_open TI.
    chk. zastep. zastep. astep. zastep.
    zastep. zastep. astep.
    zastep. if_cases K; zify_cond K.
    - exfalso. clear - K Cflo. lia.
    - clear K. cut_rel (NB + sg + n + 1)%Z ltac:(clear - HSG HN; lia).
  Qed.

  Lemma tc_l3c : forall xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 xF xfc mm,
    TINV J sh_poison mb mm -> frm0 xfc -> (-3 <= n + e <= 0)%Z ->
    evt asegs Q (LS 0xb93f8 (Z_to_bv 64 0xb93f8) xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 (- (n + e))) xt3 xt4 xt5 xt6 xF xfc mm).
  Proof using OK KZ SHPN HSG HN HE.
    intros until mm. intros TI FRM P3. lay_open TI.
    zastep. zastep. zastep.
    to_rel (NB + sg + n - (n + e) + 2)%Z ltac:(clear - HSG HN P3; lia).
  Qed.

  Definition tc_l3c_k : Prop := forall xt0 xt1 xt2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 xF xfc mm,
    TINV J sh_poison mb mm -> frm0 xfc -> (-3 <= n + e <= 0)%Z ->
    evt asegs Q (LS e_asan_memcpy (Z_to_bv 64 0xb93f8) xt0 xt1 xt2 (Z_to_bv 64 (NB + sg + 2 - (n + e))) (Z_to_bv 64 (spq + 15)) (Z_to_bv 64 17) xa3 xa4 xa5 xa6 xa7
                    (Z_to_bv 64 (- (n + e))) xt3 xt4 xt5 xt6 xF xfc mm).
  Hypothesis KL3C : tc_l3c_k.

  Lemma tc_l3b : forall xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 xF xfc mm,
    TINV J sh_poison mb mm -> frm0 xfc -> (-3 <= n + e <= 0)%Z ->
    evt asegs Q (LS 0xb9374 (Z_to_bv 64 0xb9374) xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 (e mod 4294967296)) xt3 xt4 xt5 xt6 xF xfc mm).
  Proof using OK KL3C SHPN HSG HN HE.
    intros until mm. intros TI FRM P3. lay_open TI.
    chk. zastep. zastep. astep.
    chk. zastep. zastep. astep.
    chk. zastep. chk.
    zastep.
    replace (bv_swrap 32 (0 - (n + e) mod 18446744073709551616)) with (- (n + e))%Z
      by (rewrite swrap32_Z; clear - P3; Z.div_mod_to_equations; lia).
    zastep. astep. astep. astep. astep.
    zastep. zastep. zastep. zastep.
    eapply evt_eq; [| eapply KL3C; [ti_close | exact FRM | exact P3]]. num_st_eq.
  Qed.
End Lay.
