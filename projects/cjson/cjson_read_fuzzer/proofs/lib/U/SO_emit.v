(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import RelSpec.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import SFModel Arr SysStep Image FP ITree Nodes Decode SCPS.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Bytes PropExec.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import NodesSound.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require RzNodesImpl.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.RzNodesImpl.RzNodes.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import RzNodesImpl.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Import Prelim Monad SoftFloat FmtFp Stdio Driver.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import SFW1_lemmas.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require Exit.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Exit.F_memset.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require Import F_memcpy F_fwritex F_pad F_fmt_fp_lib.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require NumFacts_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.NumFacts_iface.F_fmt_fp.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require Import F_pop_arg Exit.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import Printf_model Printf_mlib.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require Import F_printf_iface F_printf_core F_printf_snsink F_vfprintf F_vsnprintf.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import Printf_pieces.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require Import UImg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require StoreCache.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.StoreFast.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import SO_model.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require Import SO_piface.   (* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import SO_rz.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require SO_exit.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.SO_exit.SO_fwritex_stdout.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require Import SO_vfprintf_stdout SO_exit.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require SO_piface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.SO_piface.SO_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import ShapeAlg ShapeSpec.      (* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import StoreCache.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
   (* [comment removed for export] *)
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

(* [comment removed for export] *)
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac mem_after_store ::= mem_after_store_cached.
Local Ltac addr_eq_tac ::= addr_eq_tac_cached.
Local Ltac arith_goal := lazymatch goal with
  | |- (_ <= _)%Z => idtac | |- (_ < _)%Z => idtac | |- (_ >= _)%Z => idtac | |- (_ > _)%Z => idtac
  | |- @eq Z _ _ => idtac | |- @eq nat _ _ => idtac | |- (_ <= _)%nat => idtac | |- (_ < _)%nat => idtac
  | |- ~ _ => idtac | |- _ /\ _ => idtac | |- _ \/ _ => idtac | |- False => idtac | |- True => idtac
  end.   (* [comment removed for export] *)
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_cached segs m m' MU WM.
Local Ltac lia ::= lia3.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require StoreCache.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.LiaClosure.
Local Ltac lia ::= lia4.
Local Ltac tlia ::= tlia4.
Local Ltac flia ::= first [ assumption | slim; lia ].   (* [comment removed for export] *)

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac zs := zstep; try (fix_litstore; mem_after_store_opt).
Ltac fix_ret := lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
  replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.
Ltac ienter := lazymatch goal with |- Monad.implM _ _ _ _ _ => unfold Monad.implM; apply impl_from_evt | |- ITree.impl _ _ _ _ _ => apply impl_from_evt | _ => idtac end.
Ltac ileave := lazymatch goal with |- evt _ _ _ => apply evt_done | _ => idtac end;
               lazymatch goal with |- ITree.impl _ _ (?c ?s) (epost (fun p => ?Q (fst p) (snd p))) ?ms => change (Monad.implM usegs c s Q ms) | _ => idtac end.

Notation mem := (word -> option byte).
Local Notation rzt := (SO_rz.rzt usegs).

(* [comment removed for export] *)
Definition FMT_emitd : list Z := [37; 100; 10; 0].      (* [comment removed for export] *)
Definition A_FMT_emitd : Z := 0x102d9.
Definition EMITD_PIECES : list (list Z) := [[]; []; [48]; []; [10]].

Lemma printf_pieces_emitd : printf_pieces FMT_emitd [PA_i 0] = Some (EMITD_PIECES, 2).
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Shell.
  Context {St : Type} (get_so : St -> stdout_st) (set_so : stdout_st -> St -> St).
  Hypothesis GS : forall x so, get_so (set_so so x) = so.
  Hypothesis SS : forall x so so', set_so so' (set_so so x) = set_so so' x.

  Lemma emitd_gen :
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (st : St) (lo : Z) (canary : word),
      stdout_file m (get_so st) ->
      bv_unsigned a1 mod 2^32 = 0 ->
      stk usegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - EMITD_DEPTH) -> (GLOBALS_TOP <= lo) ->
      (bv_unsigned sp < 2^63) ->
      ssp_cells m canary -> mem_inv usegs m -> frm0 fc ->
      Monad.implM usegs (stdout_towrite get_so set_so ;;; outsk (stdout_fwritex get_so set_so) EMITD_PIECES (mret tt)) st
            (emit_printf_post get_so ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo canary m)
            (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x135c4) fc None m (seg_rom usegs)).
  Proof using GS SS.
    intros until canary. intros SF HA1 ST LO GLO QHI SSP MI FRM.
    unfold EMITD_DEPTH, GLOBALS_TOP in *.
    pose proof (bv_unsigned_in_range 64 sp) as Rq. unfold bv_modulus in Rq. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in Rq.
    destruct SSP as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2. idtac. fold usegs in SSP1, SSP2.
    pose proof (munch_refl [(lo, bv_unsigned sp); (RSTDOUT, RSTDOUT + 232); (RSTDOUT_BUF, RSTDOUT_BUF + 1024)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
    pose proof (munch_refl [(lo, bv_unsigned sp)]%Z m) as MU1.
    ienter.
    carve_frame 80%nat ST.
    do 15 zs.
    (* [comment removed for export] *)
    do 7 zs.
    apply (proj1 (rw_cells_app usegs _ _ [_;_;_] _)) in FR. destruct FR as [FR VAC]. cbn [cells_size csize Nat.add app] in VAC.
    replace (bv_unsigned sp + -80 + Z.of_nat 24)%Z with (bv_unsigned sp + -56)%Z in VAC by lia.
    pose proof (rw_cells_bytes_at' _ _ _ _ VAC) as VAA. cbn [cells_bytes cbytes] in VAA.
    change (le8 a1 ++ le8 a2 ++ le8 a3 ++ le8 a4 ++ le8 a5 ++ le8 a6 ++ le8 a7 ++ []) with (u64s [a1; a2; a3; a4; a5; a6; a7]) in VAA.
    ileave.
    pose proof (vfprintf_stdout_proof get_so set_so GS SS fwritex_stdout_proof) as VF. unfold vfprintf_stdout_stmt in VF. cbv zeta in VF.
    eapply implM_post_evt.
    { eapply VF with (A := A_FMT_emitd) (VA := bv_unsigned sp + -56) (fmt := FMT_emitd) (slots := [a1; a2; a3; a4; a5; a6; a7]) (args := [PA_i 0])
                     (r := 2) (lo := lo) (canary := canary);
        clear VF; rewrite ?unsigned_lit by lia; unfold VF_FRAME, VF_DEPTH, GLOBALS_TOP, STATIC_SPLIT, zlength; cbn [length].
      all: try reflexivity. all: try (arith_goal; lia).
      - eapply stdout_file_stk; [exact SF | exact MU1 | exact WM | lia].
      - apply fmt_bytes_at; [exact MI | vm_compute; reflexivity | unfold A_FMT_emitd; lia | vm_compute; discriminate].
      - unfold FMT_emitd. forall_range.
      - exact VAA.
      - cbn [args_ok arg_ok]. split; [|exact I]. split; [lia|]. rewrite HA1. reflexivity.
      - exact ST.
      - split; [exact SSP1 | exact SSP2].
      - exact MI.
      - exact FRM.
      - unfold A_FMT_emitd, FMT_emitd. cbn [length]. lia.
      - unfold A_FMT_emitd, FMT_emitd. cbn [length]. lia. }
    cbv beta. intros [] st' ms' P. clear MU1.
    unfold vfprintf_stdout_post in P. rewrite !unsigned_lit in P by lia.
    destruct P as (y5 & y6 & y7 & d0 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & y28 & y29 & y30 & y31 & Ft & fc' & m3 & -> & MUc & WMc & MI3 & FRM' & FOK & ST3 & SF3 & SSP3).
    lazymatch type of MUc with munch _ ?mm _ => transport_after_call usegs mm m3 MUc WMc; clear MUc WMc; try clear MI end.
    fix_ret.
    zs. zs. zs.
    lazymatch goal with FR : rw_cells _ ?mm (bv_unsigned sp + -80)%Z ?hd, VAC : rw_cells _ ?mm (bv_unsigned sp + -56)%Z ?rest |- _ =>
      assert (FALL : rw_cells usegs mm (bv_unsigned sp + -80) (hd ++ rest));
      [ apply (proj2 (rw_cells_app usegs _ _ _ _)); split; [exact FR|]; cbn [cells_size csize Nat.add app]; eapply rwc_eq; [exact VAC | lia]
      | clear FR VAC ] end.
    cbn [app] in FALL.
    release_frame FALL ST3 (bv_unsigned sp).
    apply evt_done. unfold emit_printf_post. repeat (lazymatch goal with |- ex _ => eexists end).
    split; [cbv delta [mkR]; reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI3|]. split; [exact FRM'|]. split; [exact FOK|].
    split; [exact ST3|]. split; [exact SF3|]. exact SSP3.
  Qed.
End Shell.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section StdoutModel.
  Let get_so : stdout_st -> stdout_st := fun s => s.
  Let set_so : stdout_st -> stdout_st -> stdout_st := fun so _ => so.
  Local Notation OUT := (stdout_fwritex get_so set_so).

  Lemma zlength_app' : forall {A} (a b : list A), zlength (a ++ b) = zlength a + zlength b.
  Proof. intros. unfold zlength. rewrite length_app. lia. Qed.

  Lemma rzt_stdout_towrite : forall st mo (R : unit * stdout_st -> Prop),
    R (tt, if so_active st then st else mkStdout true [] (so_lbf_nl st) (so_first st)) ->
    rzt (stdout_towrite get_so set_so st) mo [] R.
  Proof. intros st mo R HR. unfold stdout_towrite. apply rzt_upd_so. exact HR. Qed.

  (* [comment removed for export] *)
  Lemma rzt_fwritex_keep : forall s buf lbf first mo,
    zlength buf + zlength s <= STDOUT_BUFSIZ -> (lbf = false \/ after_last_nl s = 0) ->
    rzt (OUT s (mkStdout true buf lbf first)) mo [] (fun r => snd r = mkStdout true (buf ++ s) lbf first).
  Proof.
    intros s buf lbf first mo B NL. unfold stdout_fwritex.
    eapply (rzt_mbind_nil_l usegs _ _ _ _ _ (fun r => r = (tt, mkStdout true buf lbf first))); [apply rzt_stdout_towrite; reflexivity|].
    intros [] s1 E. injection E as ->.
    eapply (rzt_mbind_nil_l usegs _ _ _ _ _ (fun r => r = (mkStdout true buf lbf first, mkStdout true buf lbf first))); [apply rzt_rd_so; reflexivity|].
    intros so s1 E. injection E as -> ->. cbn [so_buf so_lbf_nl so_active so_first].
    destruct (Z.ltb_spec (STDOUT_BUFSIZ - zlength buf) (zlength s)) as [X|X]; [lia|].
    destruct lbf.
    - destruct NL as [NL|NL]; [discriminate|]. rewrite NL. cbn [Z.ltb Z.to_nat skipn].
      eapply (rzt_mbind_nil_l usegs _ _ _ _ _ (fun r => r = (tt, mkStdout true buf true first))); [apply rzt_mret; reflexivity|].
      intros [] s1 E. injection E as ->. apply rzt_upd_so. reflexivity.
    - apply rzt_upd_so. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma rzt_fwritex_flushline : forall s buf first mo,
    chan_ok mo 1 -> zlength buf + zlength s <= STDOUT_BUFSIZ -> after_last_nl s = zlength s -> 0 < zlength s ->
    rzt (OUT s (mkStdout true buf true first)) mo (map (WriteEv (Z_to_bv 64 1)) (to_bytes (buf ++ s)))
        (fun r => snd r = mkStdout true [] (if first then false else true) false).
  Proof.
    intros s buf first mo CH B NL POS. unfold stdout_fwritex.
    eapply (rzt_mbind_nil_l usegs _ _ _ _ _ (fun r => r = (tt, mkStdout true buf true first))); [apply rzt_stdout_towrite; reflexivity|].
    intros [] s1 E. injection E as ->.
    eapply (rzt_mbind_nil_l usegs _ _ _ _ _ (fun r => r = (mkStdout true buf true first, mkStdout true buf true first))); [apply rzt_rd_so; reflexivity|].
    intros so s1 E. injection E as -> ->. cbn [so_buf so_lbf_nl so_active so_first].
    destruct (Z.ltb_spec (STDOUT_BUFSIZ - zlength buf) (zlength s)) as [X|X]; [lia|].
    rewrite NL. rewrite (proj2 (Z.ltb_lt 0 (zlength s))) by exact POS.
    rewrite firstn_all2 by (unfold zlength; lia). rewrite skipn_all2 by (unfold zlength; lia).
    eapply rzt_mbind_nil_r.
    - eapply rzt_mono; [apply rzt_stdout_writefn; [exact CH| cbn [so_buf]; unfold STDOUT_BUFSIZ in B; lia]|]. intros r Hr; exact Hr.
    - intros [] s1 E. cbn [snd so_first] in E. subst s1. apply rzt_upd_so. cbn [snd so_active so_buf so_lbf_nl so_first]. reflexivity.
  Qed.

  Local Notation EMRUN := (stdout_towrite get_so set_so ;;; outsk OUT EMITD_PIECES (mret tt)).

  Ltac em_keep B :=
    eapply (rzt_mbind_nil_l usegs _ _ _ _ _ (fun r => snd r = B)); [ | intros [] ? E; cbn [snd] in E; subst ].

  (* [comment removed for export] *)
  Lemma rzt_emit_first : forall mo, chan_ok mo 1 ->
    rzt (EMRUN stdout_init) mo (W 1 emit_line) (fun r => snd r = emit_after_first).
  Proof.
    intros mo CH. unfold stdout_init, emit_after_first, W, emit_line. cbn [outsk].
    em_keep (mkStdout true [] true true); [apply rzt_stdout_towrite; reflexivity|].
    em_keep (mkStdout true ([] ++ []) true true); [apply rzt_fwritex_keep; [apply Z.leb_le; reflexivity| right; reflexivity]|]. cbn [app].
    em_keep (mkStdout true ([] ++ []) true true); [apply rzt_fwritex_keep; [apply Z.leb_le; reflexivity| right; reflexivity]|]. cbn [app].
    em_keep (mkStdout true ([] ++ [48]) true true); [apply rzt_fwritex_keep; [apply Z.leb_le; reflexivity| right; reflexivity]|]. cbn [app].
    em_keep (mkStdout true ([48] ++ []) true true); [apply rzt_fwritex_keep; [apply Z.leb_le; reflexivity| right; reflexivity]|]. cbn [app].
    eapply rzt_mbind_nil_r.
    - change [Z_to_bv 8 48; Z_to_bv 8 10] with (to_bytes ([48] ++ [10])).
      apply (rzt_fwritex_flushline [10] [48] true mo CH); [apply Z.leb_le; reflexivity| reflexivity| reflexivity].
    - intros [] s1 E. cbn [snd] in E. subst s1. apply rzt_mret. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma rzt_emit_again : forall mo buf, chan_ok mo 1 -> zlength buf + 2 <= STDOUT_BUFSIZ ->
    rzt (EMRUN (mkStdout true buf false false)) mo (W 1 []) (fun r => snd r = mkStdout true (buf ++ [48; 10]) false false).
  Proof.
    intros mo buf CH B. unfold W. cbn [outsk map].
    em_keep (mkStdout true buf false false); [apply rzt_stdout_towrite; reflexivity|].
    em_keep (mkStdout true (buf ++ []) false false); [apply rzt_fwritex_keep; [unfold zlength in *; cbn [length]; lia| left; reflexivity]|]. rewrite app_nil_r.
    em_keep (mkStdout true (buf ++ []) false false); [apply rzt_fwritex_keep; [unfold zlength in *; cbn [length]; lia| left; reflexivity]|]. rewrite app_nil_r.
    em_keep (mkStdout true (buf ++ [48]) false false); [apply rzt_fwritex_keep; [unfold zlength in *; cbn [length]; lia| left; reflexivity]|].
    em_keep (mkStdout true ((buf ++ [48]) ++ []) false false); [apply rzt_fwritex_keep; [rewrite zlength_app'; unfold zlength in *; cbn [length]; lia| left; reflexivity]|]. rewrite app_nil_r.
    em_keep (mkStdout true ((buf ++ [48]) ++ [10]) false false); [apply rzt_fwritex_keep; [rewrite zlength_app'; unfold zlength in *; cbn [length]; lia| left; reflexivity]|].
    apply rzt_mret. cbn [snd]. rewrite <- app_assoc. reflexivity.
  Qed.
End StdoutModel.

(* [comment removed for export] *)
(* [comment removed for export] *)

Theorem so_emit_first_proof : so_emit_first_stmt.
Proof.
  unfold so_emit_first_stmt. intros until K. intros HM CH SF HA1 ST LO GLO QHI SSP MI FRM HK HC.
  pose proof (emitd_gen (fun s : stdout_st => s) (fun so _ => so) (fun _ _ => eq_refl) (fun _ _ _ => eq_refl)
                ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                F fc m stdout_init lo canary SF HA1 ST LO GLO QHI SSP MI FRM) as H.
  unfold Monad.implM in H.
  pose proof (rzt_emit_first mo CH) as RZ.
  apply (RZ _ _ K HM H HK). intros [[] st'] ms' PO E. cbn [snd] in E. subst st'. cbn [fst snd] in PO. unfold emit_printf_post in PO.
  destruct PO as (x5 & x6 & x7 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & x28 & x29 & x30 & x31 & Ft & fc' & m' & -> & MU & WM & MI' & FRM' & FOK & ST' & SF' & SSP').
  eapply HC; eassumption.
Qed.

Theorem so_emit_again_proof : so_emit_again_stmt.
Proof.
  unfold so_emit_again_stmt. intros until K. intros HM CH SF B HF HA1 ST LO GLO QHI SSP MI FRM HK HC.
  pose proof (emitd_gen (fun s : stdout_st => s) (fun so _ => so) (fun _ _ => eq_refl) (fun _ _ _ => eq_refl)
                ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                F fc m (mkStdout true buf false false) lo canary SF HA1 ST LO GLO QHI SSP MI FRM) as H.
  unfold Monad.implM in H.
  pose proof (rzt_emit_again mo buf CH B) as RZ.
  apply (RZ _ _ K HM H HK). intros [[] st'] ms' PO E. cbn [snd] in E. subst st'. cbn [fst snd] in PO. unfold emit_printf_post in PO.
  destruct PO as (x5 & x6 & x7 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & x28 & x29 & x30 & x31 & Ft & fc' & m' & -> & MU & WM & MI' & FRM' & FOK & ST' & SF' & SSP').
  eapply HC; eassumption.
Qed.
