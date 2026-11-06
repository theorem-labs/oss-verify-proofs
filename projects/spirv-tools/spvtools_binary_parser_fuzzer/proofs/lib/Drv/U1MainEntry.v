(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Ubsan.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import Amb PropExec CatExec CatSim SeqExec StoreOk FileSim ArgvEnv SymExec SymExec2 SymExec2Sound SymRun SymDrive MemSplit RefLayout StartupTac.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Drv Require Import Overlay RunsLib U1BootDefs U1Boot U1StartInit U1CxxTable U1Start U1CxxLink U1StartupFacts U1ExitKn U1Statics U1SxKn.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.

Abbreviation RSEGS := Ubsan.M.loaded_segments.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Lemma seg_rom_high : forall (a : word), (0x124000 <= bv_unsigned a)%Z -> seg_rom RSEGS a = None.
Proof.
  intros a Ha. unfold seg_rom. unfold memory_read.
  cbn -[bv_unsigned Z.leb Z.ltb Z.add Z.sub N.leb N.ltb N.add bv_extract Z.of_N Z.to_N].
  cbn [Z.of_N].
  repeat (lazymatch goal with
          | |- context [((?lo <=? bv_unsigned a)%Z && ?c)%bool] =>
              replace c with false by (symmetry; apply Z.leb_gt; lia); rewrite andb_false_r
          end).
  reflexivity.
Qed.

Section MainEntry.
  Context {AMB : Amb}.
  Variable sp0 : word.
  Variables a0s path : list byte.
  Variable ev : list (list byte).
  Variable tid : word.
  Variable rdraw : EntryDraw.
  Variable regs : bvmap 5 word.
  Variable mem : word -> option byte.
  Let av := [a0s; path].
  Hypothesis Hva : valid_argv av.
  Hypothesis Hve : valid_envp ev.
  Hypothesis Hvsp : valid_sp sp0.
  Hypothesis Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z.
  Hypothesis ME : main_entry sp0 rdraw av ev a_uid a_hwcap tid regs mem.

  Let Hlo : (0x7fff80000000 <= bv_unsigned sp0)%Z := proj1 Hvsp.
  Let Hhi : (bv_unsigned sp0 <= 0x800000000000)%Z := proj1 (proj2 Hvsp).
  Let Hal : (bv_unsigned sp0 mod 16 = 0)%Z := proj2 (proj2 Hvsp).

  Definition p0 : word := cat_argv_ptr sp0 av ev 0.
  Definition p1 : word := cat_argv_ptr sp0 av ev 1.
  Definition auxvp : word := auxv_w sp0 av ev.

  Definition rnd : word := canary rdraw.

  Definition vals0 : list word := [sp0; p0; p1; auxvp; rnd; tid] ++ junk_vals regs.

  Definition blobs0 : list (list byte) := [a0s ++ [Z_to_bv 8 0]; path ++ [Z_to_bv 8 0]] ++ dsx_blobs.
  Definition E0 : env := Env (vals_ev vals0) (blobs_ev blobs0).

  Definition spx (k : Z) : expr := EAlu ALU_ADD (EVar 0) (ELit k).

  Definition sr_main : list expr :=
    [ELit 0; ELit 0xd1808; spx (-48); ELit 0x10800; ELit 0x102418; EVar 11; EVar 12; EVar 13;
     spx 8; ELit 2; ELit 2; spx 8; spx 32; EVar 19; EVar 20; EVar 21;
     EVar 22; EVar 23; ELit 0x6583c; spx 32; ELit 0; ELit 0; ELit 0; ELit 0;
     ELit 0; ELit 0; ELit 0; ELit 0; EVar 34; EVar 35; EVar 36; EVar 37].

  Definition kn_stack : list kentry :=
    [KAlign (EVar 0) 16; KRange (EVar 0) 0x7fff80000000 0x800000000000;
     KWr (SA (EVar 0) (-8388608)) 8388608;
     KWord (SA (EVar 0) 0) 8 (ELit 2); KWord (SA (EVar 0) 8) 8 (EVar 1);
     KWord (SA (EVar 0) 16) 8 (EVar 2); KWord (SA (EVar 0) 24) 8 (ELit 0)].

  Definition kn_auxv : list kentry :=
    [KRange (EVar 3) 0x7fff80000000 0x800000400000;
     KDisj (SA (EVar 0) (-8388608)) 8388608 (SA (EVar 3) 0) 160;
     KAlign (EVar 3) 8;
     KWord (SA (EVar 3) 0) 8 (ELit 3); KWord (SA (EVar 3) 8) 8 (ELit 0x10040);
     KWord (SA (EVar 3) 16) 8 (ELit 4); KWord (SA (EVar 3) 24) 8 (ELit 56);
     KWord (SA (EVar 3) 32) 8 (ELit 5); KWord (SA (EVar 3) 40) 8 (ELit 10);
     KWord (SA (EVar 3) 48) 8 (ELit 16);
     KWord (SA (EVar 3) 64) 8 (ELit 6); KWord (SA (EVar 3) 72) 8 (ELit 4096);
     KWord (SA (EVar 3) 80) 8 (ELit 11);
     KWord (SA (EVar 3) 96) 8 (ELit 12);
     KWord (SA (EVar 3) 112) 8 (ELit 23); KWord (SA (EVar 3) 120) 8 (ELit 0);
     KWord (SA (EVar 3) 128) 8 (ELit 25);
     KWord (SA (EVar 3) 144) 8 (ELit 0); KWord (SA (EVar 3) 152) 8 (ELit 0)].

  Definition kn_image0 : list kentry :=
    [KWr (SA (ELit 0) 0xef000) 0x35000;
     KImg 0x10000 0xf0200;
     KImg 0xf0201 0x1004f0;
     KImg 0x1004f2 0x1004f8;
     KImg 0x100551 0x100558;
     KImg 0x1005b1 0x1005b8;
     KImg 0x100611 0x100618;
     KImg 0x100671 0x100678;
     KImg 0x1006da 0x1006e0;
     KImg 0x100742 0x100748;
     KImg 0x10075c 0x100760;
     KImg 0x1007e4 0x1007e8;
     KImg 0x1007fc 0x100800;
     KImg 0x100884 0x100888;
     KImg 0x10089c 0x1008a0;
     KImg 0x100924 0x100928;
     KImg 0x10093c 0x100940;
     KImg 0x1009c4 0x1009c8;
     KImg 0x1009dc 0x1009e0;
     KImg 0x100a64 0x100a68;
     KImg 0x100a7c 0x100a80;
     KImg 0x100b04 0x100b08;
     KImg 0x100b24 0x100b28;
     KImg 0x100bac 0x100bb0;
     KImg 0x100bcc 0x100bd0;
     KImg 0x100c54 0x100c58;
     KImg 0x100c64 0x100c68;
     KImg 0x100c74 0x100c78;
     KImg 0x100c84 0x100c88;
     KImg 0x100c94 0x100c98;
     KImg 0x100ca4 0x100ca8;
     KImg 0x100cb4 0x100cb8;
     KImg 0x100cc4 0x100cc8;
     KImg 0x100cd4 0x100cd8;
     KImg 0x100ce4 0x100ce8;
     KImg 0x100cf4 0x100cf8;
     KImg 0x100d04 0x100d08;
     KImg 0x100d14 0x100d18;
     KImg 0x100d24 0x100d28;
     KImg 0x100d34 0x100d38;
     KImg 0x100d44 0x100d48;
     KImg 0x100d54 0x100d58;
     KImg 0x100d64 0x100d68;
     KImg 0x100d74 0x100d78;
     KImg 0x100d84 0x100d88;
     KImg 0x100d94 0x100d98;
     KImg 0x100d9c 0x100da0;
     KImg 0x100dac 0x100db0;
     KImg 0x100dbc 0x100dc0;
     KImg 0x100dcc 0x100dd0;
     KImg 0x100ddc 0x100de0;
     KImg 0x100dec 0x100df0;
     KImg 0x100dfc 0x100e20;
     KImg 0x100e2a 0x100e30;
     KImg 0x100e3a 0x100e40;
     KImg 0x100e4a 0x100f00;
     KImg 0x100f0c 0x100f10;
     KImg 0x100f1c 0x100f20;
     KImg 0x100f2c 0x100f30;
     KImg 0x100f3c 0x100f40;
     KImg 0x1010a0 0x101100;
     KImg 0x101191 0x1011f8;
     KImg 0x10120a 0x101210;
     KImg 0x10137b 0x101ab4;
     KImg 0x101ab8 0x101ae0;
     KImg 0x101ae8 0x101af8;
     KImg 0x101afc 0x101b00;
     KImg 0x101b08 0x102348;
     KImg 0x122420 0x122440;
     KWord (SA (ELit 0) 0x102350) 8 (ELit 0x102350);
     KWord (SA (ELit 0) 0x102370) 4 (EVar 5);
     KImg 0x102374 0x102378;
     KImg 0x10237c 0x1023c8;
     KImg 0x1023d0 0x1023e8;
     KImg 0x1023f0 0x102408;
     KWord (SA (ELit 0) 0x102408) 8 (EVar 4);
     KImg 0x102418 0x102428;
     KImg 0x122458 0x122468;
     KImg 0x12246c 0x122470;
     KImg 0x122478 0x122480;
     KImg 0x122488 0x122580;
     KImg 0x122588 0x122688;
     KWord (SA (ELit 0) 0x122688) 8 (EVar 4);
     KImg 0x122690 0x122698;
     KImg 0x1226a9 0x1226b0;
     KWord (SA (ELit 0) 0x1226b0) 8 (EVar 3);
     KImg 0x1226b8 0x1226c0;
     KImg 0x1226d0 0x1226d8;
     KWord (SA (ELit 0) 0x1226d8) 8 (ELit 4096);
     KImg 0x1226e0 0x122710;
     KImg 0x122718 0x124000;
     KRange (EVar 5) 1 4194303;
     KImg 0 0x1000  ].

  Definition kn_image : list kentry :=
    kn_image0 ++ kn_cxx_exit2 ++ [KWord (SA (ELit 0) 0x1023e8) 8 (ELit 0x1226e0)].

  Definition kn_main : list kentry := kn_stack ++ kn_auxv ++ kn_image.
End MainEntry.

Definition all_regs : list reg := [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv.

Lemma nth_all_regs : forall n, (n < 32)%nat -> nth n all_regs 0%bv = Z_to_bv 5 (Z.of_nat n).
Proof.
  intros n Hn.
  destruct n as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|n]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]; [ .. | lia]; apply bv_eq; reflexivity.
Qed.

Lemma regs_ok_by_index : forall E sr R,
  (forall i, (i < 32)%nat -> getr R (nth i all_regs 0%bv) = edenot E (nth i sr (ELit 0))) ->
  regs_ok E sr R.
Proof.
  intros E sr R H r. unfold sr_get. destruct (bv_eqb r 0) eqn:Hr0.
  - assert (r = 0%bv) by (apply bv_eq; unfold bv_eqb in Hr0; lia). subst r. cbn [edenot].
    reflexivity.
  - pose proof (H (ridx r) (ridx_range r)) as Hx. rewrite nth_all_regs in Hx by apply ridx_range.
    rewrite ridx_roundtrip in Hx. exact Hx.
Qed.

Section MainEntryProofs.
  Context {AMB : Amb}.
  Variable sp0 : word.
  Variables a0s path : list byte.
  Variable envv : list (list byte).
  Variable tid : word.
  Variable rdraw : EntryDraw.
  Variable regs : bvmap 5 word.
  Variable mem : word -> option byte.
  Let av := [a0s; path].
  Hypothesis Hva : valid_argv av.
  Hypothesis Hve : valid_envp envv.
  Hypothesis Hvsp : valid_sp sp0.
  Hypothesis Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z.
  Hypothesis ME : main_entry sp0 rdraw av envv a_uid a_hwcap tid regs mem.

  Let E := E0 sp0 a0s path envv tid rdraw regs.

  Lemma ev_vals : forall n, ev E n = nth n ([sp0; p0 sp0 a0s path envv; p1 sp0 a0s path envv; auxvp sp0 a0s path envv; rnd rdraw; tid] ++ junk_vals regs) (Z_to_bv 64 0).
  Proof. intros n. reflexivity. Qed.

  Lemma ev_junk : forall i, (i < 32)%nat -> ev E (6 + i) = getr regs (Z_to_bv 5 (Z.of_nat i)).
  Proof.
    intros i Hi. rewrite ev_vals. change (6 + i)%nat with (length [sp0; p0 sp0 a0s path envv; p1 sp0 a0s path envv; auxvp sp0 a0s path envv; rnd rdraw; tid] + i)%nat.
    rewrite app_nth2_plus. unfold junk_vals. rewrite (nth_map_seq (fun i => getr regs (Z_to_bv 5 (Z.of_nat i)))) by exact Hi. reflexivity.
  Qed.

  Lemma spx_val : forall k, edenot E (spx k) = Z_to_bv 64 (bv_unsigned sp0 + k).
  Proof. intros k. cbn [spx edenot]. rewrite alu_add. unfold v_add. change (ev E 0) with sp0.
    apply bv_eq. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod. rewrite Zplus_mod_idemp_r. reflexivity. Qed.

End MainEntryProofs.

Section MainRegs.
  Context {AMB : Amb}.
  Variable sp0 : word.
  Variables a0s path : list byte.
  Variable envv : list (list byte).
  Variable tid : word.
  Variable rdraw : EntryDraw.
  Variable regs : bvmap 5 word.
  Variable mem : word -> option byte.
  Let av := [a0s; path].
  Hypothesis Hva : valid_argv av.
  Hypothesis Hve : valid_envp envv.
  Hypothesis Hvsp : valid_sp sp0.
  Hypothesis Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z.
  Hypothesis ME : main_entry sp0 rdraw av envv a_uid a_hwcap tid regs mem.
  Let E := E0 sp0 a0s path envv tid rdraw regs.

  Ltac reg_case :=
    cbn [nth sr_main all_regs];
          first [ rewrite (spx_val sp0 a0s path envv tid rdraw regs)
                | lazymatch goal with |- _ = edenot _ (EVar ?n) =>
                    change (edenot E (EVar n)) with (ev E n);
                    first [ rewrite (ev_junk sp0 a0s path envv tid rdraw regs (n - 6)) by lia; reflexivity | idtac ]
                  | |- _ => cbn [edenot] end ];
          first [ reflexivity
                | exact (me_ra _ _ _ _ _ _ _ _ _ ME) | exact (me_gp _ _ _ _ _ _ _ _ _ ME) | exact (me_tp _ _ _ _ _ _ _ _ _ ME)
                | exact (me_s2 _ _ _ _ _ _ _ _ _ ME)
                | rewrite (me_sp _ _ _ _ _ _ _ _ _ ME); apply bv_eq; rewrite !u_small by lia; lia
                | rewrite (me_s0 _ _ _ _ _ _ _ _ _ ME); reflexivity
                | rewrite (me_a1 _ _ _ _ _ _ _ _ _ ME); reflexivity
                | rewrite (me_a2 _ _ _ _ _ _ _ _ _ ME); f_equal; subst av; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ Pos.mul Z.mul Pos.add]; lia
                | rewrite (me_s3 _ _ _ _ _ _ _ _ _ ME); f_equal; subst av; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ Pos.mul Z.mul Pos.add]; lia
                | rewrite (me_s1 _ _ _ _ _ _ _ _ _ ME); unfold argc_w, argcN, len_word; reflexivity
                | rewrite (me_a0 _ _ _ _ _ _ _ _ _ ME); unfold argc_w, argcN, len_word; reflexivity
                | apply (me_szero _ _ _ _ _ _ _ _ _ ME); cbn; tauto
                | idtac ].

  Theorem main_regs_ok : regs_ok E sr_main regs.
  Proof.
    pose proof (proj1 Hvsp) as Hlo. pose proof (proj1 (proj2 Hvsp)) as Hhi. unfold sp_window_lo, sp_window_hi in *.
    apply regs_ok_by_index.
    intros i Hi.
    destruct i as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|i]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]; [ .. | lia]; reg_case.
  Qed.
End MainRegs.

Section KnowProofs.
  Context {AMB : Amb}.
  Variable sp0 : word.
  Variables a0s path : list byte.
  Variable envv : list (list byte).
  Variable tid : word.
  Variable rdraw : EntryDraw.
  Variable regs : bvmap 5 word.
  Variable mem : word -> option byte.
  Let av := [a0s; path].
  Hypothesis Hva : valid_argv av.
  Hypothesis Hve : valid_envp envv.
  Hypothesis Hvsp : valid_sp sp0.
  Hypothesis Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z.
  Hypothesis ME : main_entry sp0 rdraw av envv a_uid a_hwcap tid regs mem.
  Let E := E0 sp0 a0s path envv tid rdraw regs.

  Lemma kp_lo : (0x7fff80000000 <= bv_unsigned sp0)%Z. Proof. exact (proj1 Hvsp). Qed.
  Lemma kp_hi : (bv_unsigned sp0 <= 0x800000000000)%Z. Proof. exact (proj1 (proj2 Hvsp)). Qed.
  Lemma kp_al : (bv_unsigned sp0 mod 16 = 0)%Z. Proof. exact (proj2 (proj2 Hvsp)). Qed.
  Lemma ke0 : ev E 0 = sp0. Proof. reflexivity. Qed.
  Lemma ke1 : ev E 1 = p0 sp0 a0s path envv. Proof. reflexivity. Qed.
  Lemma ke2 : ev E 2 = p1 sp0 a0s path envv. Proof. reflexivity. Qed.
  Lemma ke3 : ev E 3 = auxvp sp0 a0s path envv. Proof. reflexivity. Qed.
  Lemma ke4 : ev E 4 = rnd rdraw. Proof. reflexivity. Qed.
  Lemma ke5 : ev E 5 = tid. Proof. reflexivity. Qed.

  Lemma know_stack : know_ok RSEGS E mem kn_stack.
  Proof.
    pose proof kp_lo as Hlo. pose proof kp_hi as Hhi. pose proof kp_al as Hal.
    unfold kn_stack, know_ok.
    repeat apply Forall_cons; try apply Forall_nil; cbn [kentry_ok a_base a_off edenot]; rewrite ?ke0, ?ke1, ?ke2;
      unfold flat, estart; cbn [a_base a_off edenot]; rewrite ?ke0.
    - split; [lia | exact Hal].
    - lia.
    - split; [lia|]. intros d m Hd Hm.
      apply (main_entry_store_ok_win sp0 rdraw av envv a_uid a_hwcap tid regs mem ME); rewrite u_small by lia; unfold stack_max_size; lia.
    - split; [lia|]. split; [lia|].
      unfold adenot. cbn [a_base a_off edenot]. rewrite ke0. unfold v_addi. rewrite Z.add_0_r, Z_to_bv_bv_unsigned.
      rewrite (main_entry_rdn_above sp0 rdraw av envv a_uid a_hwcap tid regs mem ME) by lia.
      pose proof (read_argc_w RSEGS RPH sp0 av envv a_uid a_hwcap rdraw Hva) as Hr. unfold wmem in Hr.
      rewrite (Hr Hve) by (unfold sp_window_hi; lia).
      rewrite n_to_le_8_spec. reflexivity.
    - split; [lia|]. split; [lia|].
      unfold adenot. cbn [a_base a_off edenot]. rewrite ke0. unfold v_addi.
      rewrite (main_entry_rdn_above sp0 rdraw av envv a_uid a_hwcap tid regs mem ME) by (rewrite u_small by lia; lia).
      pose proof (read_argv_ptr_w RSEGS RPH sp0 av envv a_uid a_hwcap rdraw Hva Hve ltac:(unfold sp_window_lo; lia) ltac:(unfold sp_window_hi; lia) 0%nat ltac:(subst av; cbn; lia)) as Hr.
      unfold wmem in Hr. rewrite w_add_nat in Hr. change (Z.of_nat (8 + 8 * 0)) with 8%Z in Hr.
      rewrite Hr. rewrite n_to_le_8_spec. reflexivity.
    - split; [lia|]. split; [lia|].
      unfold adenot. cbn [a_base a_off edenot]. rewrite ke0. unfold v_addi.
      rewrite (main_entry_rdn_above sp0 rdraw av envv a_uid a_hwcap tid regs mem ME) by (rewrite u_small by lia; lia).
      pose proof (read_argv_ptr_w RSEGS RPH sp0 av envv a_uid a_hwcap rdraw Hva Hve ltac:(unfold sp_window_lo; lia) ltac:(unfold sp_window_hi; lia) 1%nat ltac:(subst av; cbn; lia)) as Hr.
      unfold wmem in Hr. rewrite w_add_nat in Hr. change (Z.of_nat (8 + 8 * 1)) with 16%Z in Hr.
      rewrite Hr. rewrite n_to_le_8_spec. reflexivity.
    - split; [lia|]. split; [lia|].
      unfold adenot. cbn [a_base a_off edenot]. rewrite ke0. unfold v_addi.
      rewrite (main_entry_rdn_above sp0 rdraw av envv a_uid a_hwcap tid regs mem ME) by (rewrite u_small by lia; lia).
      pose proof (read_argv_null RSEGS RPH sp0 rdraw av envv a_uid a_hwcap Hva Hve ltac:(unfold sp_window_hi; lia)) as Hr.
      rewrite w_add_nat in Hr. subst av. change (Z.of_nat (8 + 8 * length [a0s; path])) with 24%Z in Hr.
      rewrite <- (rdn_wmem_stack RSEGS RPH sp0 [a0s; path] envv a_uid a_hwcap rdraw) in Hr by (try rewrite u_small by lia; lia).
      unfold wmem in Hr. rewrite n_to_le_8_spec in Hr. exact Hr.
  Qed.

  Lemma auxvp_eq : auxvp sp0 a0s path envv = Z_to_bv 64 (bv_unsigned sp0 + Z.of_nat (auxv_off av envv)).
  Proof. unfold auxvp, auxv_w, auxv_off. subst av. cbn [length]. f_equal. lia. Qed.

  Lemma auxvp_u : bv_unsigned (auxvp sp0 a0s path envv) = (bv_unsigned sp0 + Z.of_nat (auxv_off av envv))%Z
    /\ (Z.of_nat (auxv_off av envv) + 160 <= 2240000)%Z.
  Proof.
    pose proof kp_lo. pose proof kp_hi.
    pose proof (auxv_off_bound RPH sp0 rdraw av envv a_uid a_hwcap) as Hb.
    pose proof (lay_bsb_len RPH sp0 rdraw av envv a_uid a_hwcap Hva Hve) as Hl.
    rewrite auxvp_eq. rewrite u_small by lia. lia.
  Qed.

  Lemma rnd_u2 : (bv_unsigned sp0 <= bv_unsigned (at_random_ptr sp0 av envv))%Z
    /\ (bv_unsigned (at_random_ptr sp0 av envv) + 16 <= bv_unsigned sp0 + 2240000)%Z
    /\ (bv_unsigned (at_random_ptr sp0 av envv) mod 8 = 0)%Z
    /\ (forall j n, (j + n <= 16)%nat ->
          rdn RSEGS mem (Z_to_bv 64 (bv_unsigned (at_random_ptr sp0 av envv) + Z.of_nat j)) n
          = Some (firstn n (skipn j (at_random_bytes (ed_random rdraw))))).
  Proof.
    pose proof kp_lo as HLO. pose proof kp_hi as HHI.
    pose proof (lay_bsb_len RPH sp0 rdraw av envv a_uid a_hwcap Hva Hve) as Hl.
    destruct (rnd_facts RSEGS RPH sp0 rdraw av envv a_uid a_hwcap Hva Hve ltac:(unfold sp_window_lo; lia) ltac:(unfold sp_window_hi; lia) kp_al)
      as (A & B & C & D & F).
    split; [exact A|]. split; [lia|]. split; [exact D|].
    intros j n Hjn. rewrite (main_entry_rdn_above sp0 rdraw av envv a_uid a_hwcap tid regs mem ME) by (rewrite u_small by lia; lia).
    pose proof (rdn_wmem_stack RSEGS RPH sp0 av envv a_uid a_hwcap rdraw) as Hw. unfold wmem in Hw.
    rewrite Hw by (rewrite u_small by lia; lia). apply F. exact Hjn.
  Qed.

  Lemma auxv_word_at : forall j, (j < 20)%nat ->
    rdn RSEGS mem (Z_to_bv 64 (bv_unsigned (auxvp sp0 a0s path envv) + 8 * Z.of_nat j)) 8
    = Some (word_to_le_bytes 8 (nth j (auxv_words RPH (at_random_ptr sp0 av envv) a_uid a_hwcap) (Z_to_bv 64 0))).
  Proof.
    intros j Hj. pose proof kp_lo as HLO. pose proof kp_hi as HHI.
    destruct auxvp_u as [Hu Hb].
    rewrite (main_entry_rdn_above sp0 rdraw av envv a_uid a_hwcap tid regs mem ME) by (rewrite u_small by lia; lia).
    pose proof (rdn_wmem_stack RSEGS RPH sp0 av envv a_uid a_hwcap rdraw) as Hw. unfold wmem in Hw.
    rewrite Hw by (rewrite u_small by lia; lia).
    replace (Z_to_bv 64 (bv_unsigned (auxvp sp0 a0s path envv) + 8 * Z.of_nat j))
      with (sp0 + nat_to_word (auxv_off av envv + 8 * j)) by (rewrite w_add_nat; f_equal; lia).
    rewrite (read_auxv_word RSEGS RPH sp0 rdraw av envv a_uid a_hwcap Hva Hve ltac:(unfold sp_window_hi; lia) j Hj).
    rewrite n_to_le_8_spec. reflexivity.
  Qed.

  Ltac kw_auxv j :=
    split; [lia|]; split; [lia|];
    unfold adenot; cbn [a_base a_off edenot]; rewrite ke3; unfold v_addi;
    lazymatch goal with |- rdn _ _ (Z_to_bv 64 (?u + ?k)) 8 = _ =>
      replace k with (8 * Z.of_nat j)%Z by reflexivity end;
    rewrite (auxv_word_at j) by lia; unfold auxv_words; cbn [nth]; try reflexivity.

  Lemma know_auxv : know_ok RSEGS E mem kn_auxv.
  Proof.
    pose proof kp_lo as Hlo. pose proof kp_hi as Hhi. pose proof kp_al as Hal.
    destruct auxvp_u as [Hau Hab].
    unfold kn_auxv, know_ok.
    repeat apply Forall_cons; try apply Forall_nil; cbn [kentry_ok a_base a_off edenot];
      rewrite ?ke0, ?ke3, ?ke4; unfold flat, estart, elenZ; cbn [a_base a_off edenot]; rewrite ?ke0, ?ke3, ?ke4;
      try rewrite Hau; try lia.
    -   split; [lia|].
      destruct (proj1 (Z.mod_divide (bv_unsigned sp0) 16 ltac:(lia)) Hal) as [q Hq].
      replace (bv_unsigned sp0 + Z.of_nat (auxv_off av envv))%Z with ((2 * q + 5 + Z.of_nat (length envv)) * 8)%Z
        by (unfold auxv_off; subst av; cbn [length]; lia).
      apply Z_mod_mult.
    - kw_auxv 0%nat. - kw_auxv 1%nat. - kw_auxv 2%nat. - kw_auxv 3%nat. - kw_auxv 4%nat. - kw_auxv 5%nat.
    - kw_auxv 6%nat. - kw_auxv 8%nat. - kw_auxv 9%nat. - kw_auxv 10%nat. - kw_auxv 12%nat.
    - kw_auxv 14%nat. - kw_auxv 15%nat. - kw_auxv 16%nat. - kw_auxv 18%nat. - kw_auxv 19%nat.
  Qed.

  Lemma auxvp_w : auxvp sp0 a0s path envv = auxv_w sp0 av envv.
  Proof. reflexivity. Qed.

  Lemma kimg_ok : forall lo hi, D_main_missb lo (Z.to_nat (hi - lo)) = true -> (lo <= hi)%Z -> (hi <= 0x124000)%Z ->
    kentry_ok RSEGS E mem (KImg lo hi).
  Proof.
    intros lo hi Hb Hle Hhi. pose proof kp_lo as HLO. pose proof kp_hi as HHI.
    destruct (missb_parts lo _ Hb) as (_ & _ & Hlo0 & _).
    cbn [kentry_ok]. split; [lia|]. split; [lia|]. intros i Hi.
    rewrite (main_entry_mem_data sp0 rdraw av envv a_uid a_hwcap tid regs mem ME) by (rewrite u_small by lia; unfold stack_max_size; lia).
    apply (D_main_none sp0 av envv tid rdraw Hva).
    apply (missb_sub lo (Z.to_nat (hi - lo))); [exact Hb | lia | rewrite Z2Nat.id by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia].
  Qed.

  Ltac kimg := apply kimg_ok; [vm_compute; reflexivity | lia | lia].

  Ltac kw_pre :=
    split; [lia|]; split; [lia|];
    unfold adenot; cbn [a_base a_off edenot]; unfold v_addi; rewrite u_small by lia; rewrite Z.add_0_l.
  Ltac kw_data L :=
    kw_pre;
    rewrite (main_entry_rdn_data sp0 rdraw av envv a_uid a_hwcap tid regs mem ME) by (rewrite u_small by lia; unfold stack_max_size; lia);
    rewrite (L RSEGS); try reflexivity.
  Ltac kw_mem L := kw_pre; rewrite (L RSEGS); try reflexivity.

  Lemma know_image0 : know_ok RSEGS E mem kn_image0.
  Proof.
    pose proof kp_lo as Hlo. pose proof kp_hi as Hhi. pose proof (u64_range tid) as Ht.
    unfold kn_image0, know_ok.
    repeat apply Forall_cons; try apply Forall_nil;
      try kimg;
      cbn [kentry_ok a_base a_off edenot]; rewrite ?ke3, ?ke5; unfold flat, estart, elenZ; cbn [a_base a_off edenot];
      rewrite ?(u_small 0) by lia; cbn [Z.add].
    -   split; [lia|]. intros d m Hd Hm.
      apply store_ok_of_all; [rewrite u_small by lia; lia|]. intros x Hx. rewrite u_small in Hx by lia.
      apply rw_wview. lia.
    - kw_data (D_main_self sp0 av envv tid rdraw Hva).
    - kw_mem (main_entry_tid sp0 av envv tid rdraw Hva Hlo regs mem ME).
    - kw_data (D_main_canary sp0 av envv tid rdraw Hva).
    - kw_mem (main_entry_guard sp0 av envv tid rdraw Hva Hlo regs mem ME).
    - rewrite auxvp_w. kw_data (D_main_auxv sp0 av envv tid rdraw Hva).
    - kw_data (D_main_pagesize sp0 av envv tid rdraw Hva).
    -   lia.
  Qed.

  Fixpoint zlist_eqb (l1 l2 : list Z) : bool :=
    match l1, l2 with
    | [], [] => true
    | x :: t, y :: u => (Z.eqb x y && zlist_eqb t u)%bool
    | _, _ => false
    end.
  Lemma zlist_eqb_eq : forall l1 l2, zlist_eqb l1 l2 = true -> l1 = l2.
  Proof.
    induction l1 as [|x t IH]; intros [|y u] H; cbn in H; try discriminate; [reflexivity|].
    apply andb_prop in H as [H1 H2]. apply Z.eqb_eq in H1. f_equal; [exact H1 | apply IH; exact H2].
  Qed.

  Definition cells_in_cxx (cells : list (Z * nat * Z)) : bool :=
    forallb (fun c : Z * nat * Z => match c with (a, w, v) =>
      (Nat.leb w 8 && (0 <=? a)%Z && (a + Z.of_nat w <=? 0x100000000)%Z &&
       match lookup_runs D_CXX a w with
       | Some zs => zlist_eqb (map (fun z => bv_unsigned (Z_to_bv 8 z)) zs) (map bv_unsigned (word_to_le_bytes w (Z_to_bv 64 v)))
       | None => false end)%bool end) cells.

  Lemma byte_list_eq2 : forall (l1 l2 : list byte), map bv_unsigned l1 = map bv_unsigned l2 -> l1 = l2.
  Proof.
    induction l1 as [|x t IH]; intros [|y u] H; cbn in H; try discriminate; [reflexivity|].
    injection H as Hx Ht. f_equal; [apply bv_eq; exact Hx | apply IH; exact Ht].
  Qed.

  Lemma know_cells2 : forall cells, cells_in_cxx cells = true ->
    know_ok RSEGS E mem (map (fun c : Z * nat * Z => match c with (a, w, v) => KWord (SA (ELit 0) a) w (ELit v) end) cells).
  Proof.
    pose proof kp_lo as Hlo. pose proof kp_hi as Hhi.
    induction cells as [|[[a w] v] rest IH]; intros Hc; [constructor|].
    cbn [cells_in_cxx forallb] in Hc. apply andb_prop in Hc as [Hc Hrest].
    apply andb_prop in Hc as [Hc HL]. apply andb_prop in Hc as [Hc H2]. apply andb_prop in Hc as [H0 H1].
    apply Nat.leb_le in H0. apply Z.leb_le in H1. apply Z.leb_le in H2.
    destruct (lookup_runs D_CXX a w) as [zs|] eqn:HLK; [|discriminate].
    constructor; [|apply IH; exact Hrest].
    cbn [kentry_ok a_base a_off edenot]. split; [exact H0|]. unfold flat, estart, adenot. cbn [a_base a_off edenot].
    rewrite (u_small 0) by lia. split; [lia|]. unfold v_addi. rewrite (u_small 0) by lia. rewrite Z.add_0_l.
    rewrite (main_entry_cxx sp0 av envv tid rdraw Hlo regs mem ME RSEGS a w zs) by (try exact HLK; lia).
    f_equal. apply byte_list_eq2. rewrite map_map. apply zlist_eqb_eq in HL. exact HL.
  Qed.

  Lemma know_image : know_ok RSEGS E mem kn_image.
  Proof.
    unfold kn_image. unfold know_ok. rewrite !Forall_app. split; [apply know_image0|]. split.
    - unfold kn_cxx_exit2. apply know_cells2. vm_compute. reflexivity.
    - pose proof kp_lo as Hlo. pose proof kp_hi as Hhi.
      repeat apply Forall_cons; try apply Forall_nil.
      cbn [kentry_ok a_base a_off edenot]. split; [lia|]. unfold flat, estart, adenot. cbn [a_base a_off edenot].
      rewrite (u_small 0) by lia. split; [lia|]. unfold v_addi. rewrite (u_small 0) by lia. rewrite Z.add_0_l.
      erewrite (main_entry_cxx sp0 av envv tid rdraw Hlo regs mem ME RSEGS); [ | lia | cbn; lia | reflexivity].
      f_equal. apply byte_list_eq2. vm_compute. reflexivity.
  Qed.

  Theorem main_know_ok : know_ok RSEGS E mem kn_main.
  Proof.
    unfold kn_main, know_ok.
    apply Forall_app; split; [apply know_stack|].
    apply Forall_app; split; [apply know_auxv | apply know_image].
  Qed.

  Theorem main_know_sx : know_ok RSEGS E mem kn_sx.
  Proof.
    apply know_sx.
    - unfold E, E0, blobs0. apply blobs_sx_ok_app. reflexivity.
    - eapply main_entry_pins_sx; [exact (proj1 Hvsp) | exact ME].
  Qed.

  Lemma main_str : forall k, (k < 2)%nat ->
    rdn RSEGS mem (cat_argv_ptr sp0 av envv k) (length (nth k av []) + 1) = Some (nth k av [] ++ [Z_to_bv 8 0])
    /\ (bv_unsigned sp0 <= bv_unsigned (cat_argv_ptr sp0 av envv k))%Z
    /\ (bv_unsigned (cat_argv_ptr sp0 av envv k) <= bv_unsigned sp0 + 2107576)%Z
    /\ (Z.of_nat (length (nth k av [])) <= 131071)%Z.
  Proof.
    intros k Hk. pose proof kp_lo as Hlo. pose proof kp_hi as Hhi.
    pose proof (lay_bsb_nw RPH sp0 rdraw av envv a_uid a_hwcap Hva Hve ltac:(unfold sp_window_hi; lia)) as Hnw.
    assert (Hk' : (k < length av)%nat) by (subst av; cbn; lia).
    destruct (argv_ptr_bounds_at sp0 av envv Hva Hve ltac:(unfold sp_window_hi; lia) k Hk') as [B1 B2].
    pose proof (u_cat_argv_ptr RPH sp0 rdraw av envv a_uid a_hwcap Hva Hve ltac:(unfold sp_window_lo; lia) ltac:(unfold sp_window_hi; lia) k Hk') as Hu.
    pose proof (struct_av_bound RPH sp0 rdraw av envv a_uid a_hwcap Hva Hve) as Hsb.
    pose proof (total_arg_bytes_firstn_le k av) as Hf.
    pose proof (argv_str_len av Hva k Hk') as Hlen.
    repeat split.
    - rewrite (main_entry_rdn_above sp0 rdraw av envv a_uid a_hwcap tid regs mem ME) by lia.
      pose proof (rdn_wmem_stack RSEGS RPH sp0 av envv a_uid a_hwcap rdraw) as Hw. unfold wmem in Hw. rewrite Hw by lia.
      apply read_argv_cstr_k; [exact Hk' | exact Hnw].
    - exact B1.
    - lia.
    - exact Hlen.
  Qed.
End KnowProofs.
