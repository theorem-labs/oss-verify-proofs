(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.A9 Require Import ImageA.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.Lib Require Import RzCPS NodesA SysStep Arr FP.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.Lib Require Import StoreFast.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.PG Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.A9 Require Import Layout.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.A9 Require Import RT_iface RT_traces RT_gaps_iface LeptTac D_kit D_iface D_defs Lept_kit Lept_iface Lept_env LeptC_kit Lept_chain Lept_objkit LeptL_kit Lept_fuzzkit LeptM_destroy_defs Ed_fp Ed_iface Numa_kit Ed_numa_addfast Ed_realloc.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

(* [comment removed for export] *)
Lemma munch_widen : forall W W' (m m' : mem), munch W m m' -> (forall x, outside W' x -> outside W x) -> munch W' m m'.
Proof. intros W W' m m' MU HW x Hx. apply MU. apply HW. exact Hx. Qed.

Lemma zx32_small : forall z, 0 <= z < 2^32 -> zx32 (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof. intros z Hz. unfold zx32. rewrite unsigned_lit by lia. rewrite Z.mod_small by lia. reflexivity. Qed.

Section NUMAADD.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis GP : rt_gaps RT.
Hypothesis EG : ed_gaps RT.
Hypothesis RC : rt_contracts RT.

(* [comment removed for export] *)
Ltac app_store A n :=
  lazymatch goal with |- evt _ _ (MS _ ?FF _ _ _ ?mm _) =>
    lazymatch goal with UAx : u32arr asegs mm A ?wsx |- _ =>
      let SOK := fresh "SOK" in
      pose proof (u32arr_store_ok asegs mm A wsx n (wa (A + 4 * n)) UAx ltac:(lia) ltac:(f_equal; lia)) as SOK;
      zstep;
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem mm _ (le4 ?v)) _) =>
        let N := fresh "UA" in
        pose proof (u32arr_write asegs mm A wsx n v UAx ltac:(lia)) as N; rewrite ?Nat2Z.id in N;
        clear UAx; store_done; rename N into UA
      end
    end end.

Theorem numaAddNumber_ok : numaAddNumber_cps RT.
Proof using AF GP EG RC.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo na cap arr vals v
    FDO MST -> -> FV OB CAP2 ENV RES.
  unfold lpost_f, lenv, lres, keeps, keepsL, freg_is in *. destruct ENV as (LH & SSP & ART0 & MI & ST & LOW & LOR & SPT & SPA & SPB).
  destruct RES as (FRB & LVB & CRB & LVP).
  pose proof (numa_obj_facts _ _ _ _ _ _ OB) as (LEN & CAP & NA0 & NA16 & AR0 & AR16 & INn & INa & NE).
  destruct OB as ((pad & NC) & (junk0 & AC) & CHn & CHa & _). unfold numa_cells in NC.
  destruct (numa_arr_view m arr cap vals junk0 AC ltac:(lia)) as (ws & UA & UAL).
  remember (vals ++ ws) as aws eqn:EA.
  pose proof (af_client_consts RT AF Σ m ART0) as (G1 & G2 & _).
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
  pose proof (af_acc_live RT AF Σ m na 32 ART0 INn) as (_ & ACCn).
  pose proof (af_acc_live RT AF Σ m arr (4 * cap) ART0 INa) as (_ & ACCa).
  pose proof (af_live_range RT AF Σ m na 32 ART0 INn) as (_ & NAR & NAS).
  pose proof (gp_live_hi RT GP Σ m na 32 ART0 INn) as NASH.
  pose proof (af_live_range RT AF Σ m arr (4 * cap) ART0 INa) as (_ & ARR & ARS).
  pose proof (gp_live_hi RT GP Σ m arr (4 * cap) ART0 INa) as ARSH.
  pose proof (live_apart RT AF Σ m na 32 arr (4 * cap) ART0 INn INa ltac:(congruence)) as DJ.
  unfold entry_st, e_numaAddNumber, g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address in *.
  set (usp := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (unfold usp; symmetry; apply Z_to_bv_bv_unsigned). rewrite ESP.
  assert (USP : 0 <= usp < 2^64) by (unfold usp; apply bv_unsigned_in_range).
  unfold LSTK, STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A, CALLOC_SEC_MAX in *. unfold SHB in *.
  lazymatch goal with |- cps _ _ ?Q => set (QF := Q) end.
  set (LVF := live_remove arr (rt_live RT Σ)) in *.
  set (PF := fun a => aclient LVF (rt_frames RT Σ) usp a /\ outside [(na, na + 32)] a).
  pose proof (agree_refl PF m) as AGF.
  assert (PFS : forall a, PF a -> usp <= a \/ a < lo).
  { intros a [Ha _]. destruct (aclient_split RT AF Σ m usp a ART0) as [Hs|Hs]; [| left; exact Hs| right; unfold STACK_WIN in Hs; lia].
    apply (aclient_mono LVF (rt_frames RT Σ) usp _ _ usp a Ha); [| auto| lia]. intros e He. exact (live_remove_sub _ _ _ He). }
  assert (OAP : forall a, PF a -> a < arr \/ arr + 4 * cap <= a).
  { intros a [Ha _]. apply (removed_chunk_apart RT AF Σ m arr (4 * cap) LVF usp a ART0 INa); [| unfold STACK_WIN; lia| exact Ha].
    intros e He. unfold LVF in He. destruct (live_remove_in _ _ _ He) as [He1 NE1]. split; [exact He1| exact NE1]. }
  (* [comment removed for export] *)
  hide AC.
  cps_walk AF MST.
  pose proof (munch_refl [(usp - 112, usp); (na, na + 32)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  awalk [0xeef6c; 0xeefc0; 0xef010; 0xef06c].        (* [comment removed for export] *)
  rewrite !sx32_small by lia.
  destruct (Z_lt_ge_dec (Z.of_nat (length vals)) cap) as [NLT|NGE].
  - (* [comment removed for export] *)
    brT.
    lazymatch goal with MUx : munch ?W m ?m1 |- _ =>
      apply (munch_widen W (W ++ [(arr, arr + 4 * cap)]) m m1) in MUx; [cbn [app] in MUx| clear; intros x Hx; cbn [outside app] in *; tauto] end.
    awalk [0xeef6c; 0xef010; 0xef06c].        (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ ?FF _ _ _ _ _) =>
      app_store arr (Z.of_nat (length vals));
      lazymatch goal with UAx : u32arr asegs ?mm arr (upd ?wsx ?i (reg_get FF ?r)) |- _ =>
        replace (reg_get FF r) with v in UAx by (symmetry; exact FV) end end.
    awalk [0xeef6c; 0xef010; 0xef06c].        (* [comment removed for export] *)
    cps_stop.
    art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [| split; [| exact I]]];
                        [ intros zz Hzz; right; right; left; exists na, 32; split; [exact INn| lia]
                        | intros zz Hzz; right; right; left; exists arr, (4 * cap); split; [exact INa| lia] ]).
    apply cps_finish. intros c Hc. subst QF. cbv beta.
    exists Σ, cap, arr, v. split; [| split; [left; repeat split; first [reflexivity| lia]| repeat split; unfold mcost; first [reflexivity| destruct (8 * cap <=? 64512); lia]]].
    eapply (ASTA_conseq RT); [exact Hc|]. intros ms <-. eexists.
    split; [unfold ret_st; rewrite ESP; do 16 eexists; reflexivity|].
    split; [split; [split; [assumption| split; [assumption| assumption]]| split; assumption]|].
    split.
    { intros a Ha Ho. lazymatch goal with MUx : munch _ m ?mf |- _ => apply MUx end. cbn [outside] in Ho |- *.
      destruct Ho as (Ho1 & _).
      assert (PFa : PF (bv_unsigned a)) by (split; [| cbn [outside]; split; [exact Ho1| exact I]]; unfold LVF; exact Ha).
      pose proof (PFS _ PFa). pose proof (OAP _ PFa). repeat split; lia. }
    unfold numa_obj. subst aws.
    lazymatch goal with NCx : rw_cells asegs ?mf na _, UAx : u32arr asegs ?mf arr _ |- _ =>
      rewrite ?sx32_small in NCx by lia; rewrite ?unsigned_lit in NCx by lia; rewrite ?swrap32_small in NCx by lia;
      destruct (numa_arr_app_unview mf arr cap vals ws v ltac:(rewrite Nat2Z.id; exact UAx) UAL NLT) as (junk' & AC');
      split; [eexists; rewrite length_app; cbn [length]; replace (Z.of_nat (length vals + 1)) with (Z.of_nat (length vals) + 1) by lia; unfold numa_cells; exact NCx|] end.
    split; [exists junk'; exact AC'|].
    split; [exact CHn|]. split; [exact CHa|]. split; [exact NE|]. split; [lia|]. rewrite length_app. cbn [length]. lia.
  - (* [comment removed for export] *)
    assert (NEQ : Z.of_nat (length vals) = cap) by lia. clear NGE.
    clear UA UAL EA.                           (* [comment removed for export] *)
    brF.
    awalk [e_reallocNew; 0xeefc0; 0xef010; 0xef06c; 0xef204; 0xef248; 0xef2cc].   (* [comment removed for export] *)
    rewrite zx32_small by lia. brT.
    awalk [e_reallocNew; 0xeefc0; 0xef010; 0xef06c; 0xef204; 0xef248; 0xef2cc].   (* [comment removed for export] *)
    (* [comment removed for export] *)
    lazymatch goal with NCx : rw_cells asegs ?mm na _ |- _ => split_at NCx 6%nat PC0 end.
    at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [| exact I]];
                        intros zz Hzz; right; right; left; exists na, 32; split; [exact INn| lia])
                  ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct Hx as [_ Hx2]; cbn [outside] in Hx2; repeat split; lia).
    unfold hid in AC.
    lazymatch goal with MUx : munch ?W m ?m1 |- cps _ (ASTA RT Σ _ (eq (MS _ _ _ _ _ ?m1 _))) _ =>
      assert (AC1 : rw_cells asegs m1 arr (numa_arr_cells cap vals junk0))
        by (apply (rw_cells_agree_nw asegs m m1 _ _ AC); apply (agree_of_munch W m m1 _ MUx); intros x Hx;
            unfold numa_arr_cells in Hx; rewrite cells_size_app, cells_size_mapC4 in Hx; cbn [cells_size csize] in Hx; rewrite Nat.add_0_r in Hx; cbn [outside];
            clear - Hx DJ ARR LOR LOW LEN NEQ CAP; repeat split; lia);
      clear AC; unfold numa_arr_cells in AC1 end.
    eapply cps_seq.
    { pose proof (reallocNew_ok RT AF GP EG RC) as RN; unfold reallocNew_cps, optr, optrL in RN.
      eapply RN with (lo := lo) (pind := na + 24) (old := arr) (oldsz := 4 * cap) (newsz := 4 * (2 * cap)) (vals := vals) (junk := junk0); rt_side idtac.
      all: lazymatch goal with
           | |- Z_to_bv 64 _ = Z_to_bv 64 _ => f_equal; lia
           | |- _ = Z_to_bv 64 _ => f_equal; lia
           | |- accok _ _ _ _ _ /\ _ => split; [left; exists na, 32; split; [exact INn| lia]| repeat split; first [lia | ul | clear - NA16; Z.div_mod_to_equations; lia]]
           | |- rw_cells _ _ (_ + 24) _ => exact PC0
           | |- rw_cells _ _ _ (map C4 _ ++ _) => exact AC1
           | |- chunk _ _ _ => exact CHa
           | |- _ \/ _ => clear - DJ; lia
           | |- lenv _ _ _ _ _ _ => lenv_tac
           | |- lres _ _ _ _ _ => replace (4 * (2 * cap)) with (8 * cap) by lia; unfold lres; repeat split; first [assumption | lia]
           | |- (_ <= _ <= _) => lia
           | |- (_ < _ <= _) => lia
           | |- (_ <= _) => unfold CALLOC_SEC_MAX; lia
           | |- ?g => idtac "LEFTOVER:" g
           end. }
    after_call RT AF.
    fold_ag ltac:(fun Hx => pose proof (PFS _ Hx); destruct Hx as [Hx1 Hx2]; cbn [outside] in Hx2; split;
                  [apply (aclient_mono LVF (rt_frames RT Σ) usp _ _ _ _ Hx1); [unfold LVF; auto| auto| lia]
                  | cbn [outside]; split; [lia| exact I]]).
    replace (4 * (2 * cap)) with (8 * cap) in * by lia.
    lazymatch goal with H : rt_live RT ?S = (?p, 8 * cap) :: _ |- _ => rename H into LVN; rename S into Σ1; set (nw := p) in * end.
    assert (INN : In (nw, 8 * cap) (rt_live RT Σ1)) by (rewrite LVN; left; reflexivity).
    assert (INn1 : In (na, 32) (rt_live RT Σ1)) by (rewrite LVN; right; apply live_remove_keep; [exact INn| cbn [fst]; congruence]).
    lazymatch goal with A : ART RT Σ1 ?mm |- cps _ (ASTA RT Σ1 _ _) _ =>
      pose proof (af_live_range RT AF Σ1 mm nw (8 * cap) A INN) as (_ & NWHI & NWSEG);
      pose proof (gp_live_hi RT GP Σ1 mm nw (8 * cap) A INN) as NWSH;
      pose proof (af_live_disj RT AF Σ1 mm nw (8 * cap) na 32 [] (live_remove arr (rt_live RT Σ)) A LVN
                    ltac:(cbn [app]; apply live_remove_keep; [exact INn| cbn [fst]; congruence])) as NWNA;
      assert (NCA : forall a, PF a -> a < nw \/ nw + 8 * cap <= a)
        by (intros a Ha; destruct Ha as [Ha _]; apply (new_chunk_apart RT AF Σ1 mm nw (8 * cap) LVF (rt_frames RT Σ) usp a A LVN);
            [ assumption | repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; ul | exact Ha ]);
      (* [comment removed for export] *)
      lazymatch goal with NWC : rw_cells asegs mm nw (map C4 vals ++ _) |- _ =>
        destruct (numa_arr_view mm nw (2 * cap) vals _ ltac:(unfold numa_arr_cells; replace (4 * (2 * cap)) with (8 * cap) by lia; exact NWC) ltac:(lia)) as (ws2 & UA2 & UAL2);
        clear NWC end;
      (* [comment removed for export] *)
      lazymatch goal with NCx : rw_cells asegs mm na ?cs6, PCx : rw_cells asegs mm (na + 24) [C8 (Z_to_bv 64 0)] |- _ =>
        assert (NC1 : rw_cells asegs mm na (cs6 ++ [C8 (Z_to_bv 64 0)]))
          by (apply (proj2 (rw_cells_app mm na cs6 [C8 (Z_to_bv 64 0)])); split; [exact NCx| exact PCx]);
        clear NCx PCx; cbn [app] in NC1 end
    end.
    assert (NWNZ : nw <> na) by (intros E; rewrite E in NWNA; lia).
    remember (vals ++ ws2) as aws2 eqn:EA2.
    repeat match goal with H : rt_sp0 RT _ = _ |- _ => rewrite H in * end.
    unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *.
    refresh RT AF. unfold SHB in *.
    lazymatch goal with C : chunk _ nw _ |- _ => destruct C as (INW & NW0 & NW16 & NWS0) end.
    walk_to AF MST [(usp - 112, usp); (na, na + 32); (nw + 4 * cap, nw + 4 * cap + 4)] [0xef2cc; 0xef010; 0xef06c; 0xeef88].
      (* [comment removed for export] *)
    assert (B1 : 1 <= cap <= 25600) by lia. assert (B2 : 0x7fff80000000 <= rt_sp0 RT Σ <= 2^47) by lia.
    lazymatch goal with A : ART RT Σ1 ?mp, MUx : munch ?W ?mp ?mc |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
      assert (ACCW : acc asegs mc nw (8 * cap))
        by (intros i Hi; destruct (acc_live RT AF Σ1 mp nw (8 * cap) A INN i Hi) as (b & Hb & OK); exists b; split; [| exact OK];
            apply (bytes_at_agree asegs mp mc _ _ Hb); apply (agree_of_munch W mp mc _ MUx); intros x Hx; cbn [length] in Hx; cbn [outside];
            unfold shad, SHB in Hx;
            clear - Hx Hi NWSH NASH NWNA NWHI NAR B1 B2 LOW LOR NW0 NA0; Z.div_mod_to_equations; lia) end.
    clear B1 B2.
    awalk [0xef010; 0xef06c; 0xeef88].        (* [comment removed for export] *)
    app_store nw cap.
    awalk [0xef010; 0xef06c; 0xeef88].        (* [comment removed for export] *)
    cps_stop.
    art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [| split; [| exact I]]];
                        [ intros zz Hzz; right; right; left; exists na, 32; split; [exact INn1| lia]
                        | intros zz Hzz; right; right; left; exists nw, (8 * cap); split; [exact INN| lia] ]).
    lazymatch goal with
    | AGFx : agree_on ?PFx _ ?mm, MUx : munch _ ?mm _ |- _ =>
        is_var PFx; agf_munch AGFx MUx ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); pose proof (NCA _ Hx); destruct Hx as [_ Hx2]; cbn [outside] in Hx2; repeat split; lia)
    end.
    apply cps_finish. intros c Hc. subst QF. cbv beta.
    lazymatch goal with UAx : u32arr asegs _ nw (upd _ _ ?vv) |- _ => exists Σ1, (2 * cap), nw, vv end.
    split.
    2:{ repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end.
        repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end.
        repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end.
        split; [right; split; [exact NEQ| split; [reflexivity| unfold LVF; replace (4 * (2 * cap)) with (8 * cap) by lia; reflexivity]]|].
        split; [reflexivity|]. split; [reflexivity|]. lia. }
    eapply (ASTA_conseq RT); [exact Hc|]. intros ms <-. eexists.
    split; [unfold ret_st; rewrite ESP; do 16 eexists; reflexivity|].
    split; [split; [split; [assumption| split; [assumption| assumption]]| split; assumption]|].
    split.
    { intros a Ha Ho. apply AGF. split; [exact Ha| exact Ho]. }
    unfold numa_obj. subst aws2.
    lazymatch goal with NCx : rw_cells asegs ?mf na _, UAx : u32arr asegs ?mf nw _ |- _ =>
      rewrite ?sx32_small in NCx by lia; rewrite ?unsigned_lit in NCx by lia; rewrite ?swrap32_small in NCx by lia;
      destruct (numa_arr_app_unview mf nw (2 * cap) vals ws2 _ ltac:(rewrite NEQ; exact UAx) UAL2 ltac:(lia)) as (junk' & AC');
      replace (cap * 2) with (2 * cap) in NCx by lia;
      split; [eexists; rewrite length_app; cbn [length]; replace (Z.of_nat (length vals + 1)) with (Z.of_nat (length vals) + 1) by lia; unfold numa_cells; exact NCx|] end.
    split; [exists junk'; exact AC'|].
    split; [split; [exact INn1| repeat split; lia]|].
    split; [split; [replace (4 * (2 * cap)) with (8 * cap) by lia; exact INN| repeat split; lia]|].
    split; [exact NWNZ|]. split; [lia|]. rewrite length_app. cbn [length]. lia.
Qed.
End NUMAADD.
