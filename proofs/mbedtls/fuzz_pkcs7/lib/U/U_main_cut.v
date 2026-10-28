(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.mbedtls.fuzz_pkcs7.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import PropExec Shape MState Frame RegsExt.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Common Require Import SimInv ExitSim.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BB Require Import Amb CatExec CatSim SeqExec StoreOk ShapeX ShapeLaws MmapSim AllocSim FileSim AgentLib SpecConsts SymExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX LibKnowFrame MemcpyLib Hoare MemSplit.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Sys Require Import Nodes LibWritev SysNodes.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Spec.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import U_stdio_call U_startup U_startup_facts U_main_entry U_main_open_defs U_main_open U_main_opendir U_mainleaf_usage U_mainleaf_openfail U_mainleaf_openfail_branch U_main_skel.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.
#[local] Existing Instance PropExec.fx0.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_P_main_cut () : Init.string Init.list := ["RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "stdpp.bitvector.definitions.Z_to_bv"; "Stdlib.ZArith.BinInt.Z.sub"; "stdpp.bitvector.definitions.bv_unsigned"; "Cut.pathp"; "Stdlib.ZArith.BinInt.Z.add"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Cut.cut_mem"; "RocqVerifyHarness.AgentSubmission.Lib.Shape.realizes"; "RocqVerifyHarness.ProcessOversight.Tgt_fuzz_pkcs7_ubsan.M.loaded_segments"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "Cut.cut_regs"; "LinuxProcessSemantics.Riscv.Prelude.bvmap_empty"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.U.U_main_open.model1g"; "Corelib.Init.Datatypes.list"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.BB.SymRun.vals_ev"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2Sound.SX2S.regs_ok"; "RocqVerifyHarness.AgentSubmission.U.U_mainleaf_openfail.ENV"; "srK"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.getr"; "LinuxProcessSemantics.LinuxProcessSem.State.FdEntry"; "RocqVerifyHarness.AgentSubmission.Lib.Shape.TSet"; "Cut.file_kont_concrete"; "RocqVerifyHarness.AgentSubmission.U.U_main_open.file_seg2_kont_g"; "LinuxProcessSemantics.LinuxProcessSem.MemImageType.Segment"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Datatypes.bool"; "Stdlib.Lists.List.forallb"; "Stdlib.ZArith.BinInt.Z.leb"; "Stdlib.ZArith.BinInt.Z.of_N"; "LinuxProcessSemantics.LinuxProcessSem.MemImageType.seg_base"; "LinuxProcessSemantics.LinuxProcessSem.MemImageType.seg_size"; "Corelib.Init.Datatypes.true"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.lt"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.find_segment"].


(* [comment removed for export] *)
Definition STOPS_CUT : list Z := (0x1d28c :: STOPS)%Z.

(* [comment removed for export] *)
Definition rK := Eval vm_compute in sym_exec RSEGS FUEL true STOPS_CUT scr0 ssB0 [].
Definition srK : list expr := Eval vm_compute in s_regs (fst (fst rK)).

Section Cut.
  Context {AMB : Amb}.
  Context {LM : Lim}.
  Variable sp0 : word.
  Variables a0s path : list byte.
  Variable envv : list (list byte).
  Variable tid : word.
  Variable rd : EntryDraw.
  Variable regs0 : bvmap 5 word.
  Variable mem0 : word -> option byte.
  Variable brk : word.
  Variable mbase : word.
  Variable fs0 : Fs.
  Variable stdin0 : InputStream.
  Hypothesis Hva : valid_argv [a0s; path].
  Hypothesis Hve : valid_envp envv.
  Hypothesis Hvsp : valid_sp sp0.
  Hypothesis Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z.
  Hypothesis ME : main_entry sp0 [a0s; path] envv tid rd regs0 mem0.

  Let SPlo : (0x7fff80000000 <= bv_unsigned sp0)%Z := proj1 Hvsp.
  Let SPhi : (bv_unsigned sp0 <= 0x800000000000)%Z := proj1 (proj2 Hvsp).

  (* [comment removed for export] *)
  Definition pathp : word := p1 sp0 a0s path envv.

  (* [comment removed for export] *)
  Definition cut_regs (t1 t2 a12 t3 t4 t5 t6 : word) : bvmap 5 word := ltac2:(CDefT.buildp (gd_tbl_P_main_cut ()) "(0.(1.&40.+1=28<.)(1.&40.(2.(3.&40.Vsp0,)+80.))(1.&40.+10800.)(1.&40.+5=0<8.)$4.O7.O6.(1.&40.+2.)(1.&40.+2.)(1.&40.+3.)O5.O5.(1.&40.+3.)(1.&40.=)(1.&40.=)(1.&40.=)(1.&40.+38.)$4.(1.&40.(5.(3.&40.Vsp0,)+20.))(1.&40.=)(1.&40.=)(1.&40.=)(1.&40.=)(1.&40.=)(1.&40.=)(1.&40.=)(1.&40.=)O4.O3.O2.O1.)")
(* [comment removed for export] *).

  (* [comment removed for export] *)
  Definition cell8 (M : word -> option byte) (a : Z) (v : word) : Prop :=
    rdn RSEGS M (Z_to_bv 64 a) 8 = Some (word_to_le_bytes 8 v).

  (* [comment removed for export] *)
  Record cut_mem (M : word -> option byte) : Prop := {
    cm_above : forall a : word, (bv_unsigned sp0 <= bv_unsigned a)%Z -> M a = mem0 a;
    cm_below : forall a : word, (bv_unsigned a < bv_unsigned sp0 - 8388608)%Z -> M a = mem0 a;
    (* [comment removed for export] *)
    cm_win_ok : forall (d : Z) (m : nat), (0 <= d)%Z -> (d + Z.of_nat m <= 8388608)%Z ->
                  store_ok RSEGS M (Z_to_bv 64 (bv_unsigned sp0 - 8388608 + d)) m = true;
    cm_win : forall a : word,
               (bv_unsigned sp0 - 8388608 <= bv_unsigned a < bv_unsigned sp0)%Z -> wview RSEGS M a <> None;
    (* [comment removed for export] *)
    cm_ra : cell8 M (bv_unsigned sp0 - 56) (Z_to_bv 64 0x3f2a8);
    cm_s0 : cell8 M (bv_unsigned sp0 - 64) (Z_to_bv 64 (bv_unsigned sp0 + 8));
    cm_s1 : cell8 M (bv_unsigned sp0 - 72) (Z_to_bv 64 2);
    cm_s2 : cell8 M (bv_unsigned sp0 - 80) (Z_to_bv 64 0x1d24c);
    cm_s3 : cell8 M (bv_unsigned sp0 - 88) (Z_to_bv 64 (bv_unsigned sp0 + 32));
    cm_s4 : cell8 M (bv_unsigned sp0 - 96) (Z_to_bv 64 0);
    cm_s5 : cell8 M (bv_unsigned sp0 - 104) (Z_to_bv 64 0);
    cm_s6 : cell8 M (bv_unsigned sp0 - 112) (Z_to_bv 64 0);
    cm_s7 : cell8 M (bv_unsigned sp0 - 120) (Z_to_bv 64 0);
    (* [comment removed for export] *)
    cm_path : rdn RSEGS M pathp (length path + 1) = Some (path ++ [Z_to_bv 8 0]);
    cm_path_lo : (bv_unsigned sp0 <= bv_unsigned pathp)%Z;
    cm_path_hi : (bv_unsigned pathp + Z.of_nat (length path) + 1 <= 0x800000400000)%Z
  }.

  (* [comment removed for export] *)
  Definition file_kont_concrete (fd3 : FdEntry) (KB : TSet) : Prop := ltac2:(CDefT.buildp (gd_tbl_P_main_cut ()) "Pt1,(6.&40.)Pt2,(6.&40.)Pa12,(6.&40.)Pt3,(6.&40.)Pt4,(6.&40.)Pt5,(6.&40.)Pt6,(6.&40.)PM,P,(6.&40.)(7.(6.&8.))P,(8.R1.)(9.$:.(;.(<.(=.R9.R8.R7.R6.R5.R4.R3.)(>.&5.(6.&40.))(1.&40.+1=28<.)(1.&20.=)(?.(6.&40.))R2.(10.$:.))(11.VAMB,VLM,Vsp0,Vtid,Vbrk,Vmbase,Vfs0,Vstdin0,O2.))O1.)")
(* [comment removed for export] *).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  #[using="Hvsp SPlo SPhi"] Lemma cut_regs_getr : ltac2:(CDefT.buildp (gd_tbl_P_main_cut ()) "Pvals,(12.(6.&40.))PR,(13.&5.(6.&40.))P,(14.(6.&40.)(15.R2.#0.)Vsp0,)P,(14.(6.&40.)(15.R3.#2.)$4.)P,(16.(17.Va0s,Vpath,R4.)$18.R3.)Pr,(6.&5.)(14.(6.&40.)(19.(=.(19.R5.(1.&5.+6.))(19.R5.(1.&5.+7.))(19.R5.(1.&5.+;.))(19.R5.(1.&5.+1<.))(19.R5.(1.&5.+1=.))(19.R5.(1.&5.+1>.))(19.R5.(1.&5.+1?.)))R1.)(19.R5.R1.))")
(* [comment removed for export] *).
  Proof.
    intros vals R P0 P2 HR r. pose proof SPlo. pose proof SPhi.
    pose proof (ridx_range r) as Hi.
    rewrite <- (ridx_roundtrip r). set (i := ridx r) in *. clearbody i.
    destruct i as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|i]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]];
      [ .. | lia];
      lazymatch goal with |- _ = getr R (Z_to_bv 5 (Z.of_nat ?k)) =>
        first
          [ (* [comment removed for export] *)
            lazymatch k with
            | 6%nat => idtac | 7%nat => idtac | 11%nat => idtac | 28%nat => idtac | 29%nat => idtac | 30%nat => idtac | 31%nat => idtac
            end;
            transitivity (getr R (Z_to_bv 5 (Z.of_nat k))); [reflexivity|reflexivity]
          | (* [comment removed for export] *)
            lazymatch k with 12%nat => idtac end;
            transitivity (getr R (Z_to_bv 5 11)); [reflexivity|];
            rewrite (HR (Z_to_bv 5 11)), (HR (Z_to_bv 5 (Z.of_nat k)));
            let e1 := eval vm_compute in (sr_get srK (Z_to_bv 5 11)) in change (sr_get srK (Z_to_bv 5 11)) with e1;
            let e2 := eval vm_compute in (sr_get srK (Z_to_bv 5 (Z.of_nat k))) in change (sr_get srK (Z_to_bv 5 (Z.of_nat k))) with e2;
            reflexivity
          | rewrite (HR (Z_to_bv 5 (Z.of_nat k)));
            let e := eval vm_compute in (sr_get srK (Z_to_bv 5 (Z.of_nat k))) in
            change (sr_get srK (Z_to_bv 5 (Z.of_nat k))) with e;
            cbn [edenot];
            first [ reflexivity
                  | (change (ev (ENV a0s path vals) 2) with (vals_ev vals 2); rewrite P2; reflexivity)
                  | (rewrite alu_add; change (ev (ENV a0s path vals) 0) with (vals_ev vals 0); rewrite P0;
                     unfold v_add; etransitivity; [reflexivity|];
                     apply bv_eq; rewrite !Z_to_bv_unsigned, !bv_wrap64_mod; try rewrite Zplus_mod_idemp_r; f_equal; lia) ] ]
      end.
  Qed.


  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Ltac frame_cell_gen FR k :=
    let r := eval vm_compute in (kread RSEGS knA (EVar 0) k 8) in
    lazymatch r with
    | Some ?v => generalize (FR k v ltac:(vm_cast_no_check (@eq_refl _ (Some v))) ltac:(lia) ltac:(lia))
    end.
  Ltac frame_cell FR k := frame_cell_gen FR k; let W := fresh "W" in intros W; exact W.

  #[using="rd regs0 Hva Hve Hvsp ME SPlo SPhi"] Theorem file_kont_of_concrete : ltac2:(CDefT.buildp (gd_tbl_P_main_cut ()) "Pfd3,$1:.PKB,$1;.P,(1<.R2.R1.)(1=.VAMB,VLM,Vsp0,Va0s,Vpath,Venvv,Vtid,Vmem0,Vbrk,Vmbase,Vfs0,Vstdin0,R3.R2.)")
(* [comment removed for export] *).
  Proof.
    intros fd3 KB HC. unfold file_seg2_kont_g.
    intros vals R M HL P0 P1 P2 P5 HR HK HA HB.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    ddestruct (main_str sp0 a0s path envv tid rd regs0 mem0 Hva Hve Hvsp ME 1%nat ltac:(cbn; lia)) as (Sr & Slo & Shi & Slen).
    cbn [nth] in Sr, Slo, Shi, Slen.
    (* [comment removed for export] *)
    run_block_gen FUEL STOPS_CUT scr0 38%nat true.
    cbn [mem_denot] in EQM. subst M0.
    (* [comment removed for export] *)
    apply (realizes_getr_ext RSEGS (cut_regs (getr R0 (Z_to_bv 5 6)) (getr R0 (Z_to_bv 5 7)) (getr R0 (Z_to_bv 5 11)) (getr R0 (Z_to_bv 5 28))
                                             (getr R0 (Z_to_bv 5 29)) (getr R0 (Z_to_bv 5 30)) (getr R0 (Z_to_bv 5 31))) R0).
    { apply (cut_regs_getr vals R0 P0 P2 HR). }
    change (mkst ?Rx ?pc ?Mx ?rom) with (MS Rx bvmap_empty pc (Z_to_bv 32 0) None Mx rom).
    apply HC.
    (* [comment removed for export] *)
    assert (WOK : forall (d : Z) (m : nat), (0 <= d)%Z -> (d + Z.of_nat m <= 8388608)%Z ->
                  store_ok RSEGS M (Z_to_bv 64 (bv_unsigned sp0 - 8388608 + d)) m = true).
    { intros d m Hd Hdm.
      pose proof (kwr_store_ok RSEGS (ENV a0s path vals) _ knA ltac:(let i := kidx knA (is_kwr_cov (EVar 0) (-8388608) 8388608) in exact i)
                    _ _ _ (-8388608 + d) m HK eq_refl ltac:(lia) ltac:(lia)) as Hst.
      unfold adenot, v_addi in Hst. cbn [a_base a_off edenot ev ENV] in Hst. rewrite P0 in Hst.
      replace (bv_unsigned sp0 - 8388608 + d)%Z with (bv_unsigned sp0 + (-8388608 + d))%Z by lia. exact Hst. }
    assert (FR : forall k v, kread RSEGS knA (EVar 0) k 8 = Some v -> (-8388608 <= k)%Z -> (k + 8 <= 0)%Z ->
                 cell8 M (bv_unsigned sp0 + k) (edenot (ENV a0s path vals) v)).
    { intros k v Hk H1 H2. unfold cell8.
      pose proof (kread_rdn RSEGS (ENV a0s path vals) M knA (EVar 0) k 8 v HK Hk ltac:(lia) ltac:(lia)
                   ltac:(unfold flat, estart; cbn [a_base a_off edenot ev ENV]; rewrite P0; lia)) as W.
      unfold adenot, v_addi in W. cbn [a_base a_off edenot ev ENV] in W. rewrite P0 in W. exact W. }
    split.
    - exact HA.
    - exact HB.
    - exact WOK.
    - intros a Ha.
      apply (store_ok_all RSEGS M (Z.to_nat 8388608) (Z_to_bv 64 (bv_unsigned sp0 - 8388608 + 0)));
        rewrite ?Z2Nat.id, ?u_small by lia; [lia | apply WOK; rewrite ?Z2Nat.id by lia; lia | lia].
    - frame_cell FR (-56)%Z.
    - frame_cell_gen FR (-64)%Z. intros W.
      unfold cell8 in W |- *. replace (bv_unsigned sp0 - 64)%Z with (bv_unsigned sp0 + -64)%Z by lia. rewrite W. cbn [edenot ev ENV]. rewrite alu_add, P0. do 2 f_equal;
      unfold v_add; apply bv_eq; rewrite !Z_to_bv_unsigned, !bv_wrap64_mod; rewrite ?Zplus_mod_idemp_r; reflexivity.
    - frame_cell FR (-72)%Z.
    - frame_cell FR (-80)%Z.
    - frame_cell_gen FR (-88)%Z. intros W.
      unfold cell8 in W |- *. replace (bv_unsigned sp0 - 88)%Z with (bv_unsigned sp0 + -88)%Z by lia. rewrite W. cbn [edenot ev ENV]. rewrite alu_add, P0. do 2 f_equal;
      unfold v_add; apply bv_eq; rewrite !Z_to_bv_unsigned, !bv_wrap64_mod; rewrite ?Zplus_mod_idemp_r; reflexivity.
    - frame_cell FR (-96)%Z.
    - frame_cell FR (-104)%Z.
    - frame_cell FR (-112)%Z.
    - frame_cell FR (-120)%Z.
    - rewrite <- Sr. apply rdn_agree. intros j Hj. apply HA. unfold pathp, p1 in *.
      pose proof (u64_range (cat_argv_ptr sp0 [a0s; path] envv 1)). rewrite u_small by lia. lia.
    - unfold pathp, p1. lia.
    - unfold pathp, p1. lia.
  Qed.
End Cut.

(* [comment removed for export] *)
Lemma find_segment_above : ltac2:(CDefT.buildp (gd_tbl_P_main_cut ()) "Psegs,(12.$1>.)Pz,$1?.Pn,$1?.PHI,$1?.P,(14.$20.(21.$1>.Lseg,$1>.(22.(5.(23.(24.R1.))(23.(25.R1.)))R2.)R4.)$26.)P,(27.R2.R4.)P,(28.=R4.)(14.(7.$1>.)(29.R7.R6.R5.)(?.$1>.))")
(* [comment removed for export] *).
Proof.
  induction segs as [|seg rest IH]; intros z n HI Hb Hz Hn; [reflexivity|].
  cbn [forallb] in Hb. apply andb_prop in Hb as [H1 H2]. apply Z.leb_le in H1.
  cbn [find_segment].
  destruct (Z.leb_spec0 (Z.of_N (seg_base seg)) z);
    destruct (Z.leb_spec0 (z + n) (Z.of_N (seg_base seg) + Z.of_N (seg_size seg))); cbn [andb]; try lia;
    apply (IH z n HI H2 Hz Hn).
Qed.

Lemma find_segment_high : forall z n, (0x7e000 <= z)%Z -> (0 < n)%Z -> find_segment RSEGS z n = None.
Proof.
  intros z n Hz Hn. apply (find_segment_above RSEGS z n 0x7e000); [vm_compute; reflexivity | lia | lia].
Qed.

Lemma wview_high_some : forall M (a : word), (0x7e000 <= bv_unsigned a)%Z ->
  wview RSEGS M a <> None -> M a <> None.
Proof.
  intros M a Ha H. unfold wview in H. destruct (M a); [discriminate|].
  rewrite find_segment_high in H by lia. exact H.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition file_kont_stmt_c {LM : Lim} : Prop :=
  forall (AMB : Amb) (sp0 : word) (a0s path : list byte) (envv : list (list byte)) (tid : word) (rd : EntryDraw)
         (regs0 : bvmap 5 word) (mem0 : word -> option byte) (brk mbase : word) (fs0 : Fs) (stdin0 : InputStream)
         (fdata : list byte),
    valid_argv [a0s; path] -> valid_envp envv -> valid_sp sp0 -> (0 < bv_unsigned tid < 2 ^ 22)%Z ->
    main_entry sp0 [a0s; path] envv tid rd regs0 mem0 -> valid_brk Ubsan.M.loaded_segments brk ->
    fs_lookup fs0 path = Some fdata -> path <> [] -> path <> dot_path -> (length path <= 4095)%nat ->
    file_kont_concrete sp0 a0s path envv tid mem0 brk mbase fs0 stdin0 (FdFile path (Z_to_bv 64 0)) (t_opened fdata fs0).

(* [comment removed for export] *)
Definition dir_kont_stmt_c {LM : Lim} : Prop :=
  forall (AMB : Amb) (sp0 : word) (a0s : list byte) (envv : list (list byte)) (tid : word) (rd : EntryDraw)
         (regs0 : bvmap 5 word) (mem0 : word -> option byte) (brk mbase : word) (fs0 : Fs) (stdin0 : InputStream),
    valid_argv [a0s; dot_path] -> valid_envp envv -> valid_sp sp0 -> (0 < bv_unsigned tid < 2 ^ 22)%Z ->
    main_entry sp0 [a0s; dot_path] envv tid rd regs0 mem0 -> valid_brk Ubsan.M.loaded_segments brk ->
    file_kont_concrete sp0 a0s dot_path envv tid mem0 brk mbase fs0 stdin0 FdDir (t_opened_dir dot_path fs0).

Lemma file_kont_stmt_of_c {LM : Lim} : file_kont_stmt_c -> file_kont_stmt.
Proof.
  intros H AMB sp0 a0s path envv tid rd regs0 mem0 brk mbase fs0 stdin0 fdata Hva Hve Hvsp Htid ME Hbrk Hf Hne Hnd Hlen.
  eapply (file_kont_of_concrete sp0 a0s path envv tid rd regs0 mem0 brk mbase fs0 stdin0); try eassumption.
  exact (H AMB sp0 a0s path envv tid rd regs0 mem0 brk mbase fs0 stdin0 fdata Hva Hve Hvsp Htid ME Hbrk Hf Hne Hnd Hlen).
Qed.

Lemma dir_kont_stmt_of_c {LM : Lim} : dir_kont_stmt_c -> dir_kont_stmt.
Proof.
  intros H AMB sp0 a0s envv tid rd regs0 mem0 brk mbase fs0 stdin0 Hva Hve Hvsp Htid ME Hbrk.
  unfold dir_seg2_kont.
  pose proof (H AMB sp0 a0s envv tid rd regs0 mem0 brk mbase fs0 stdin0 Hva Hve Hvsp Htid ME Hbrk) as HC.
  eapply (file_kont_of_concrete sp0 a0s dot_path envv tid rd regs0 mem0 brk mbase fs0 stdin0) in HC; try eassumption.
  all: unfold file_seg2_kont_g in HC; intros vals R M HL P0 P1 P2 P5 HR HK HA HB; eapply HC; eassumption.
Qed.

(* [comment removed for export] *)
Theorem U_realizes_spec_c {LM : Lim} :
  file_kont_stmt_c -> dir_kont_stmt_c ->
  forall sp brk mbase rd (inp : ProcInput),
    valid_sp sp -> valid_brk usegs' brk ->
    valid_argv (in_argv inp) -> valid_envp (in_envp inp) -> valid_fs (in_fs inp) ->
    entry_stack_fits sp (in_argv inp) (in_envp inp) ->     (* [comment removed for export] *)
    realizes usegs'
      (init_config usegs' upc uph sp brk mbase rd LIM inp)
      (spec (in_argv inp) (in_fs inp)).
Proof.
  intros HF HD. apply U_realizes_spec; [apply file_kont_stmt_of_c; exact HF | apply dir_kont_stmt_of_c; exact HD].
Qed.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
