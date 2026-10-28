(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib Require Import SFModel.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib Require Import Arr.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib Require Import SysStep.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib Require Import Image.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib Require Import FP.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib Require Import ITree.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib Require Import Nodes.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib Require Import Decode.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib Require Bytes.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib Require PropExec.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Spec Require Import Prelim.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Spec Require Import Monad.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Spec Require Import SoftFloat.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Spec Require Import FmtFp.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Spec Require Import Stdio.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.FA Require Import SFW1_lemmas.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CJ.F10 Require Import F_memset_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CJ.F10 Require Import F_memcpy_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CJ.F10 Require Import F_fwritex_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CJ.F10 Require Import F_pad_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CJ.F10 Require Import F_fmt_fp_lib_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CJ.F10 Require Import F_fmt_fp_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CJ.F10 Require Import F_pop_arg_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CJ.F10 Require Import Exit_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.F10 Require Import Printf_model.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.F10 Require Import Printf_mlib.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CJ.F10 Require Import F_printf_iface_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CJ.F10 Require Import F_printf_core_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CJ.F10 Require Import F_printf_snsink_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CJ.F10 Require Import F_sn_write_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CJ.F10 Require Import F_vfprintf_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CJ.F10 Require Import Printf_sn_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CJ.F10 Require Import F_vsnprintf_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.F10 Require Import FmtFpNF.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CJ.F10 Require Import F_fmt_fp_nf_u.
From OssFuzzTheorems.jsoncons.fuzz_json_cursor.images Require Import Ubsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition SNPRINTF_DEPTH : Z := 5936.
Definition snprintf_post := vsnprintf_post.

Definition snprintf_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem)
         (D n A : Z) (dn : nat) (junkd : list byte) (fmt : list Z) (args : list parg)
         (lo : Z) (canary : word) (r : Z) (o : list Z),
    let q := bv_unsigned sp in
    a0 = Z_to_bv 64 D -> a1 = Z_to_bv 64 n -> a2 = Z_to_bv 64 A ->
    rw_cells rsegs m D [CB dn junkd] ->
    bytes_at rsegs m A (zb fmt) -> Forall (fun c => 0 <= c < 256) fmt -> pass1_ok fmt = true ->
    Forall no_s args -> args_ok 0 0 0 m lo q 0 [a3; a4; a5; a6; a7] args ->
    printf_model OUT_sn OUTFP_sn fmt args [] = ITree.Ret (Ok (r, o)) ->
    Forall (fun c => let '(y, w, p, fl, t) := c in fmt_fp_facts' y fl p t) (fp_calls (length fmt) fmt args) ->
    (length o < dn)%nat -> (zlength o <= n - 1) -> (1 <= n < 2^63) ->
    stk rsegs m lo q -> (lo <= q - SNPRINTF_DEPTH) -> (GLOBALS_TOP <= lo) -> (q < 2^63) ->
    ssp_cells m canary -> mem_inv rsegs m -> frm0 fc ->
    (65536 <= A) -> (A + zlength fmt <= STATIC_SPLIT) ->
    (D + Z.of_nat dn <= lo \/ q <= D) -> (D + Z.of_nat dn <= 65536 \/ GLOBALS_TOP <= D) ->
    evt rsegs (snprintf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F D dn junkd r o lo canary m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0xacd08) fc None m (seg_rom rsegs)).

Theorem snprintf_proof : snprintf_stmt.
Proof.
  unfold snprintf_stmt. intros until o. cbv zeta.
  intros -> -> -> DST BY HF P1 NOS AOK MODEL FPF ROOM Hn Hn1 ST LO GLO QHI SSP MI FRM HA0 HA DD1 GD.
  unfold SNPRINTF_DEPTH, GLOBALS_TOP, STATIC_SPLIT in *.
  pose proof (bv_unsigned_in_range 64 sp) as Rq. unfold bv_modulus in Rq. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in Rq.
  pose proof (rw_cells_bound _ _ _ _ DST) as DB. cbn [cells_size csize Nat.add] in DB.
  pose proof (bytes_at_bound _ _ _ _ BY) as AB. pose proof (zb_length fmt) as LZB. rewrite LZB in AB. unfold zlength in *.
  destruct SSP as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2. cbv delta [F_memcpy_u.rsegs] in SSP1, SSP2. fold F_memset_u.rsegs in SSP1, SSP2.
  pose proof (munch_refl [(lo, bv_unsigned sp); (D, D + Z.of_nat dn)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
  carve_frame 80%nat ST.
  do 16 zs.
  apply (proj1 (rw_cells_app rsegs _ _ [_;_;_;_;_] _)) in FR. destruct FR as [FR VAC]. cbn [cells_size csize Nat.add app] in VAC.
  replace (bv_unsigned sp + -80 + Z.of_nat 40)%Z with (bv_unsigned sp + -40)%Z in VAC by lia.
  pose proof (rw_cells_bytes_at' _ _ _ _ VAC) as VAA. cbn [cells_bytes cbytes] in VAA.
  change (le8 a3 ++ le8 a4 ++ le8 a5 ++ le8 a6 ++ le8 a7 ++ []) with (u64s [a3; a4; a5; a6; a7]) in VAA.

  pose proof vsnprintf_proof as VS. unfold vsnprintf_stmt in VS. cbv zeta in VS.
  eapply evt_cut.
  { eapply VS with (D := D) (n := n) (A := A) (VA := (bv_unsigned sp + -40)%Z) (dn := dn) (junkd := junkd) (fmt := fmt) (slots := [a3; a4; a5; a6; a7]) (args := args)
                   (lo := lo) (canary := canary) (r := r) (o := o);
      clear VS; rewrite ?unsigned_lit by lia; unfold VSN_DEPTH, GLOBALS_TOP, STATIC_SPLIT, zlength; cbn [length].
    all: try reflexivity.
    all: try lia.
    all: try eassumption.
    - eapply args_ok_nos; [exact NOS | exact AOK].
    - split; [exact SSP1 | exact SSP2]. }
  cbv beta. intros ms' P.
  unfold vsnprintf_post in P. rewrite !unsigned_lit in P by lia.
  destruct P as (y5 & y6 & y7 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & y28 & y29 & y30 & y31 & Ft & fc' & m3 & -> & MUc & WMc & MI3 & FRM' & FOK & ST3 & SSP3 & DST3).
  lazymatch type of MUc with munch _ ?mm _ => transport_after_call rsegs mm m3 MUc WMc; clear MUc WMc; try clear MI end.
  fix_ret.
  clear SSP1 SSP2. destruct SSP3 as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2.
  change F_memcpy_u.rsegs with F_memset_u.rsegs in SSP1, SSP2.

  zs. zs. zs. if_cases Kc; zify_cond Kc. { exfalso. clear -Kc. apply Kc. reflexivity. }
  zs. zs. zs. zs.
  lazymatch goal with FR : rw_cells _ ?mm (bv_unsigned sp + -80)%Z ?cs1, VAC : rw_cells _ ?mm (bv_unsigned sp + -40)%Z _ |- _ =>
    assert (FALL : rw_cells rsegs mm (bv_unsigned sp + -80) (cs1 ++ [C8 a3; C8 a4; C8 a5; C8 a6; C8 a7]));
    [ apply (proj2 (rw_cells_app rsegs _ _ _ _)); split; [exact FR|]; cbn [cells_size csize Nat.add app]; eapply rwc_eq; [exact VAC | lia]
    | clear FR VAC ] end.
  cbn [app] in FALL.
  release_frame FALL ST3 (bv_unsigned sp).
  apply evt_done. unfold snprintf_post, vsnprintf_post. repeat (lazymatch goal with |- ex _ => eexists end).
  split; [cbv delta [mkR]; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI3|]. split; [exact FRM'|]. split; [exact FOK|].
  split; [exact ST3|]. split; [split; [exact SSP1 | exact SSP2] | exact DST3].
Qed.

Local Open Scope Z_scope.
Definition FMT_STAR : list Z := [37; 49; 46; 42; 103; 0].
Lemma pass1_ok_star : pass1_ok FMT_STAR = true. Proof. reflexivity. Qed.
Lemma fp_calls_star : forall prec d, (prec = 15 \/ prec = 17) ->
  fp_calls (length FMT_STAR) FMT_STAR [PA_i prec; PA_g d] = [(f128_of_d d, 1, prec, 0, CHR_g)].
Proof. intros prec d [-> | ->]; reflexivity. Qed.

Lemma printf_sn_star : forall d prec o l, (prec = 15 \/ prec = 17) ->
  fmt_fp' [] (f128_of_d d) 1 prec 0 CHR_g = Some (o, l) -> 0 <= l <= INT_MAX -> zlength o <= SN_CAP ->
  printf_model OUT_sn OUTFP_sn FMT_STAR [PA_i prec; PA_g d] [] = ITree.Ret (Ok (l, o)).
Proof.
  intros d prec o l Hp F Hl Ho.
  destruct Hp as [-> | ->];
    unfold printf_model; lhs_cbvg1;
    (pose proof (OUT_sn_eq [] [] ltac:(rewrite zlength_nil; unfold SN_CAP; lia)) as E0; msn E0; clear E0);
    unfold conv; lhs_cbvg2.
  - replace (15 <? 0) with false by reflexivity. replace ((1 <? 1) || (1048576 <=? 15))%bool with false by reflexivity.
    change CHR_g with 103 in F.
    pose proof (OUTFP_sn_eq _ _ _ _ _ _ _ _ F Ho) as E1. msn E1.
    replace ((l <? 0) || (2147483647 - 0 <? l))%bool with false by (symmetry; apply Bool.orb_false_intro; apply Z.ltb_ge; unfold INT_MAX in Hl; lia).
    rewrite mbind_mret. cbv -[Z.add]. rewrite Z.add_0_l. reflexivity.
  - replace (17 <? 0) with false by reflexivity. replace ((1 <? 1) || (1048576 <=? 17))%bool with false by reflexivity.
    change CHR_g with 103 in F.
    pose proof (OUTFP_sn_eq _ _ _ _ _ _ _ _ F Ho) as E1. msn E1.
    replace ((l <? 0) || (2147483647 - 0 <? l))%bool with false by (symmetry; apply Bool.orb_false_intro; apply Z.ltb_ge; unfold INT_MAX in Hl; lia).
    rewrite mbind_mret. cbv -[Z.add]. rewrite Z.add_0_l. reflexivity.
Qed.

Lemma fmt_bytes_at : forall m A f, mem_inv rsegs m -> ro_bytes_b rsegs A (zb f) = true -> 0 <= A -> A + zlength f <= 2^64 ->
  bytes_at rsegs m A (zb f).
Proof.
  intros m A f MI RB H0 H1.
  pose proof (ro_cells_bytes_at rsegs m A _ (ro_cells_image rsegs m A (zb f) MI RB H0 ltac:(rewrite zb_length; unfold zlength in H1; lia))) as B.
  cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B. exact B.
Qed.

Definition A_FMT_STAR : Z := 78040.
Lemma fmt_star_bytes : forall m, mem_inv rsegs m -> bytes_at rsegs m A_FMT_STAR (zb FMT_STAR).
Proof. intros m MI. apply fmt_bytes_at; [exact MI | vm_compute; reflexivity | unfold A_FMT_STAR; lia | vm_compute; discriminate]. Qed.

Ltac forall_range8 := repeat (apply Forall_cons; [lia|]); apply Forall_nil.

Definition snprintf_star_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem)
         (D : Z) (junkd : list byte) (prec : Z) (lo : Z) (canary : word) (o : list Z) (l : Z),
    let q := bv_unsigned sp in
    a0 = Z_to_bv 64 D -> a1 = Z_to_bv 64 100 -> a2 = Z_to_bv 64 A_FMT_STAR -> (prec = 15 \/ prec = 17) -> a3 = Z_to_bv 64 prec ->
    fmt_fp' [] (f128_of_d (bv_unsigned a4)) 1 prec 0 CHR_g = Some (o, l) ->
    fmt_fp_facts' (f128_of_d (bv_unsigned a4)) 0 prec CHR_g ->
    l = zlength o -> zlength o <= 25 ->
    rw_cells rsegs m D [CB 100 junkd] ->
    stk rsegs m lo q -> (lo <= q - SNPRINTF_DEPTH) -> (GLOBALS_TOP <= lo) -> (q < 2^63) ->
    ssp_cells m canary -> mem_inv rsegs m -> frm0 fc ->
    (D + 100 <= lo \/ q <= D) -> (D + 100 <= 65536 \/ GLOBALS_TOP <= D) ->
    evt rsegs (snprintf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F D 100 junkd l o lo canary m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0xacd08) fc None m (seg_rom rsegs)).

Theorem snprintf_star_proof : snprintf_star_stmt.
Proof.
  unfold snprintf_star_stmt. intros until l. cbv zeta.
  intros Ha0 Ha1 Ha2 Hp Ha3 FM FACTS Hl Ho DST ST LO GLO QHI SSP MI FRM DD1 GD.
  assert (Rp : (0 <= prec < 2^31)%Z) by lia.
  pose proof (zlength_nonneg o) as Lo0.
  pose proof snprintf_proof as SN. unfold snprintf_stmt in SN. cbv zeta in SN.
  eapply SN with (D := D) (n := 100%Z) (A := A_FMT_STAR) (dn := 100%nat) (fmt := FMT_STAR) (args := [PA_i prec; PA_g (bv_unsigned a4)]);
    clear SN;
    first [ exact Ha0 | exact Ha1 | exact Ha2 | exact DST | exact ST | exact SSP | exact MI | exact FRM
          | apply fmt_star_bytes; exact MI
          | unfold FMT_STAR; forall_range8
          | apply pass1_ok_star
          | apply Forall_cons; [exact I | apply Forall_cons; [exact I | apply Forall_nil]]
          | cbn [args_ok arg_ok]; split; [split; [lia | rewrite Ha3, unsigned_lit by lia; rewrite Z.mod_small by lia; reflexivity] | split; [reflexivity | exact I]]
          | apply printf_sn_star; [exact Hp | exact FM | unfold INT_MAX; lia | unfold SN_CAP; lia]
          | rewrite fp_calls_star by exact Hp; apply Forall_cons; [exact FACTS | apply Forall_nil]
          | unfold zlength in Ho; lia
          | unfold A_FMT_STAR, STATIC_SPLIT, FMT_STAR, zlength; cbn; lia
          | lia ].
Qed.
