(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import Amb PropExec CatExec CatSim SeqExec StoreOk FileSim ArgvEnv SymExec SymExec2 SymExec2Sound SymRun SymDrive MemSplit RefLayout StartupTac.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Drv Require Import Overlay RunsLib S1BootDefs S1Boot S1StartInit S1CxxTable S1Start S1CxxLink S1StartupFacts S1ExitKn S1Statics S1SxKn.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.

Abbreviation RSEGS := Plain.M.loaded_segments.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Lemma seg_rom_high : forall (a : word), (0x122000 <= bv_unsigned a)%Z -> seg_rom RSEGS a = None.
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
    [ELit 0; ELit 0xcfab0; spx (-48); ELit 0x10800; ELit 0x1006b8; EVar 11; EVar 12; EVar 13;
     spx 8; ELit 2; ELit 2; spx 8; spx 32; EVar 19; EVar 20; EVar 21;
     EVar 22; EVar 23; ELit 0x655e8; spx 32; ELit 0; ELit 0; ELit 0; ELit 0;
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
    [KWr (SA (ELit 0) 0xee000) 0x34000;
     KImg 0x10000 0xee4a0;
     KImg 0xee4a1 0xfe790;
     KImg 0xfe792 0xfe798;
     KImg 0xfe7f1 0xfe7f8;
     KImg 0xfe851 0xfe858;
     KImg 0xfe8b1 0xfe8b8;
     KImg 0xfe911 0xfe918;
     KImg 0xfe97a 0xfe980;
     KImg 0xfe9e2 0xfe9e8;
     KImg 0xfe9fc 0xfea00;
     KImg 0xfea84 0xfea88;
     KImg 0xfea9c 0xfeaa0;
     KImg 0xfeb24 0xfeb28;
     KImg 0xfeb3c 0xfeb40;
     KImg 0xfebc4 0xfebc8;
     KImg 0xfebdc 0xfebe0;
     KImg 0xfec64 0xfec68;
     KImg 0xfec7c 0xfec80;
     KImg 0xfed04 0xfed08;
     KImg 0xfed1c 0xfed20;
     KImg 0xfeda4 0xfeda8;
     KImg 0xfedc4 0xfedc8;
     KImg 0xfee4c 0xfee50;
     KImg 0xfee6c 0xfee70;
     KImg 0xfeef4 0xfeef8;
     KImg 0xfef04 0xfef08;
     KImg 0xfef14 0xfef18;
     KImg 0xfef24 0xfef28;
     KImg 0xfef34 0xfef38;
     KImg 0xfef44 0xfef48;
     KImg 0xfef54 0xfef58;
     KImg 0xfef64 0xfef68;
     KImg 0xfef74 0xfef78;
     KImg 0xfef84 0xfef88;
     KImg 0xfef94 0xfef98;
     KImg 0xfefa4 0xfefa8;
     KImg 0xfefb4 0xfefb8;
     KImg 0xfefc4 0xfefc8;
     KImg 0xfefd4 0xfefd8;
     KImg 0xfefe4 0xfefe8;
     KImg 0xfeff4 0xfeff8;
     KImg 0xff004 0xff008;
     KImg 0xff014 0xff018;
     KImg 0xff024 0xff028;
     KImg 0xff034 0xff038;
     KImg 0xff03c 0xff040;
     KImg 0xff04c 0xff050;
     KImg 0xff05c 0xff060;
     KImg 0xff06c 0xff070;
     KImg 0xff07c 0xff080;
     KImg 0xff08c 0xff090;
     KImg 0xff09c 0xff0c0;
     KImg 0xff0ca 0xff0d0;
     KImg 0xff0da 0xff0e0;
     KImg 0xff0ea 0xff1a0;
     KImg 0xff1ac 0xff1b0;
     KImg 0xff1bc 0xff1c0;
     KImg 0xff1cc 0xff1d0;
     KImg 0xff1dc 0xff1e0;
     KImg 0xff340 0xff3a0;
     KImg 0xff431 0xff498;
     KImg 0xff4aa 0xff4b0;
     KImg 0xff61b 0xffd54;
     KImg 0xffd58 0xffd80;
     KImg 0xffd88 0xffd98;
     KImg 0xffd9c 0xffda0;
     KImg 0xffda8 0x1005e8;
     KImg 0x1206c0 0x1206e0;
     KWord (SA (ELit 0) 0x1005f0) 8 (ELit 0x1005f0);
     KWord (SA (ELit 0) 0x100610) 4 (EVar 5);
     KImg 0x100614 0x100618;
     KImg 0x10061c 0x100668;
     KImg 0x100670 0x100688;
     KImg 0x100690 0x1006a8;
     KWord (SA (ELit 0) 0x1006a8) 8 (EVar 4);
     KImg 0x1006b8 0x1006c8;
     KImg 0x1206f8 0x120708;
     KImg 0x12070c 0x120710;
     KImg 0x120718 0x120720;
     KImg 0x120728 0x120820;
     KImg 0x120828 0x120928;
     KWord (SA (ELit 0) 0x120928) 8 (EVar 4);
     KImg 0x120930 0x120938;
     KImg 0x120949 0x120950;
     KWord (SA (ELit 0) 0x120950) 8 (EVar 3);
     KImg 0x120958 0x120960;
     KImg 0x120970 0x120978;
     KWord (SA (ELit 0) 0x120978) 8 (ELit 4096);
     KImg 0x120980 0x1209b0;
     KImg 0x1209b8 0x122000;
     KRange (EVar 5) 1 4194303;
     KImg 0 0x1000  ].

  Definition kn_image : list kentry :=
    kn_image0 ++ kn_cxx_exit2 ++ [KWord (SA (ELit 0) 0x100688) 8 (ELit 0x120980)].

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

  Lemma kimg_ok : forall lo hi, D_main_missb lo (Z.to_nat (hi - lo)) = true -> (lo <= hi)%Z -> (hi <= 0x122000)%Z ->
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
