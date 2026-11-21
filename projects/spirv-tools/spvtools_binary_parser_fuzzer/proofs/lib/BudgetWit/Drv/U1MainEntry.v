(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from Drv/U1MainEntry.v for the budget-premise witness: the same proofs over BudgetWit.SRealizes.srealizes, the released srealizes with a no-allocation-call check at each node; only module paths change. *)
(* Modified by Theorem Labs, 2026-11: launch_auxv / vdso_text_base at the entry's stack pointer (LPS b84e73ef); ported to LPS 727298f3 (the revised entry stack block, with the strings at its top, and the launch facts; the group id in the auxv; the run's mmap base; the revised stack window). *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Ubsan.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import Amb PropExec CatExec CatSim SeqExec StoreOk FileSim ArgvEnv SymExec SymExec2 SymExec2Sound SymRun SymDrive MemSplit RefLayout StartupTac.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Drv Require Import Overlay RunsLib U1BootDefs U1Boot U1StartInit U1CxxTable.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.BudgetWit.Drv Require Import U1Start U1CxxLink U1StartupFacts.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Drv Require Import U1ExitKn.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.BudgetWit.Drv Require Import U1Statics U1SxKn.
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

  (* LPS 75d69e00 (#38).  The argv strings now sit in the string block that hangs below
     [ed_top rdraw] after AT_EXECFN's bytes ([CatExec.cat_argv_ptr top av ev execfn k],
     the same spelling [S1BootDefs.pn_w] uses), not at a fixed offset from [sp0]; the
     execfn comes from the ambient launch record by name ([a_execfn], Amb.v:23), so no
     new binder.  [auxvp] is [S1BootDefs.auxv_w]'s own body for an input whose argv/envp
     are [av]/[ev] ([auxvp_w] below is [reflexivity]); it is spelled out so the
     definition does not take the input's fs/stdin, which it does not read. *)
  Definition p0 : word := cat_argv_ptr (ed_top rdraw) av ev a_execfn 0.
  Definition p1 : word := cat_argv_ptr (ed_top rdraw) av ev a_execfn 1.
  Definition auxvp : word :=
    Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev)).

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
     (* #38 rule 12i: the certified window is [[wok_lo sp0, sp0)], not the whole
        8 MiB; written with the symbol, never the literal 6144513. *)
     KWr (SA (EVar 0) (- stack_window_depth)) stack_window_depth;
     KWord (SA (EVar 0) 0) 8 (ELit 2); KWord (SA (EVar 0) 8) 8 (EVar 1);
     KWord (SA (EVar 0) 16) 8 (EVar 2); KWord (SA (EVar 0) 24) 8 (ELit 0)].

  (* LPS 75d69e00 (#38), rule 12k.  The auxv is REWRITTEN, not shifted
     (StackLayout.auxv_entries): ARCH_DLINFO's ten entries first (AT_SYSINFO_EHDR, the
     eight cache words, AT_MINSIGSTKSZ), then create_elf_tables' sixteen, then the
     CONFIG_RSEQ pair, then AT_NULL; [auxv_count] is 29 with CONFIG_RSEQ and 27 without,
     16 bytes a pair.  The old table here was the pre-revision ten pairs, so every row
     moved.  Recorded: every a_TYPE word of pairs 0..25 (each index is below
     [auxv_count] at BOTH [kb_rseq] values, so no row pins the flag), and the same five
     VALUE words the old table recorded (AT_PAGESZ 4096, AT_PHDR/AT_PHENT/AT_PHNUM from
     [RPH], AT_SECURE 0), at their new slots.  The pairs from 26 on depend on the free
     kernel field [kb_rseq]; they are NOT here but in [kn_termT]/[kn_termF] below, which
     [know_auxv_term] proves as a disjunction (the flag is case-split, never fixed).
     The disjointness span is 464 = [auxv_size true], the larger of the two, so the row
     stays kernel-free and claims more than either layout needs. *)
  Definition kn_auxv : list kentry :=
    [KRange (EVar 3) 0x7fff80000000 0x800000400000;
     KDisj (SA (EVar 0) (-8388608)) 8388608 (SA (EVar 3) 0) 464;
     KAlign (EVar 3) 8;
     KWord (SA (EVar 3) 0) 8 (ELit 33);     (*  0 AT_SYSINFO_EHDR *)
     KWord (SA (EVar 3) 16) 8 (ELit 40);    (*  1 AT_L1I_CACHESIZE *)
     KWord (SA (EVar 3) 32) 8 (ELit 41);    (*  2 AT_L1I_CACHEGEOMETRY *)
     KWord (SA (EVar 3) 48) 8 (ELit 42);    (*  3 AT_L1D_CACHESIZE *)
     KWord (SA (EVar 3) 64) 8 (ELit 43);    (*  4 AT_L1D_CACHEGEOMETRY *)
     KWord (SA (EVar 3) 80) 8 (ELit 44);    (*  5 AT_L2_CACHESIZE *)
     KWord (SA (EVar 3) 96) 8 (ELit 45);    (*  6 AT_L2_CACHEGEOMETRY *)
     KWord (SA (EVar 3) 112) 8 (ELit 46);   (*  7 AT_L3_CACHESIZE *)
     KWord (SA (EVar 3) 128) 8 (ELit 47);   (*  8 AT_L3_CACHEGEOMETRY *)
     KWord (SA (EVar 3) 144) 8 (ELit 51);   (*  9 AT_MINSIGSTKSZ *)
     KWord (SA (EVar 3) 160) 8 (ELit 16);   (* 10 AT_HWCAP *)
     KWord (SA (EVar 3) 176) 8 (ELit 6);    (* 11 AT_PAGESZ *)
     KWord (SA (EVar 3) 184) 8 (ELit 4096); (*    its value *)
     KWord (SA (EVar 3) 192) 8 (ELit 17);   (* 12 AT_CLKTCK *)
     KWord (SA (EVar 3) 208) 8 (ELit 3);    (* 13 AT_PHDR *)
     KWord (SA (EVar 3) 216) 8 (ELit 0x10040); (* its value, RPH.ph_addr *)
     KWord (SA (EVar 3) 224) 8 (ELit 4);    (* 14 AT_PHENT *)
     KWord (SA (EVar 3) 232) 8 (ELit 56);   (*    its value, RPH.ph_ent *)
     KWord (SA (EVar 3) 240) 8 (ELit 5);    (* 15 AT_PHNUM *)
     KWord (SA (EVar 3) 248) 8 (ELit 10);   (*    its value, RPH.ph_num *)
     KWord (SA (EVar 3) 256) 8 (ELit 7);    (* 16 AT_BASE *)
     KWord (SA (EVar 3) 272) 8 (ELit 8);    (* 17 AT_FLAGS *)
     KWord (SA (EVar 3) 288) 8 (ELit 9);    (* 18 AT_ENTRY *)
     KWord (SA (EVar 3) 304) 8 (ELit 11);   (* 19 AT_UID *)
     KWord (SA (EVar 3) 320) 8 (ELit 12);   (* 20 AT_EUID *)
     KWord (SA (EVar 3) 336) 8 (ELit 13);   (* 21 AT_GID *)
     KWord (SA (EVar 3) 352) 8 (ELit 14);   (* 22 AT_EGID *)
     KWord (SA (EVar 3) 368) 8 (ELit 23);   (* 23 AT_SECURE *)
     KWord (SA (EVar 3) 376) 8 (ELit 0);    (*    its value *)
     KWord (SA (EVar 3) 384) 8 (ELit 25);   (* 24 AT_RANDOM *)
     KWord (SA (EVar 3) 400) 8 (ELit 31)].  (* 25 AT_EXECFN *)

  (* The auxv TERMINATOR, which depends on the free kernel field [kb_rseq]: with
     CONFIG_RSEQ pairs 26/27 are AT_RSEQ_FEATURE_SIZE (27) / AT_RSEQ_ALIGN (28) and AT_NULL
     is pair 28; without it AT_NULL is pair 26.  Not in [kn_main]; [know_auxv_term]
     proves the one that holds, as a disjunction.  (Shape from bzip2's S0MainEntry;
     every offset here is re-derived from [auxv_entries].) *)
  Definition kn_termT : list kentry :=
    [KWord (SA (EVar 3) 416) 8 (ELit 27); KWord (SA (EVar 3) 432) 8 (ELit 28);
     KWord (SA (EVar 3) 448) 8 (ELit 0)].
  Definition kn_termF : list kentry := [KWord (SA (EVar 3) 416) 8 (ELit 0)].


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

(* LPS 75d69e00 (#38).  [S1Start.main_entry] now takes the run's whole ProcInput and the
   mmap base ([sp0 rdraw inp mbase tid regs mem]).  The input is the one the drivers
   run, [mkProcInputC av envv fs0 stdin0] (Amb.v:41), whose argv/envp reduce to the
   [av]/[envv] these Sections name, and whose kernel / execfn / uid / gid / hwcap are the
   ambient record's fields; fs0/stdin0/mbase are implicit, so an already-converted call
   such as [main_know_ok sp0 a0s path envv tid rdraw regs mem Hva Hve Hvsp Htid ME] keeps
   its explicit slots and infers them from [ME].  The launch facts the stack-image
   lemmas need ([valid_launch], [entry_launch_ok_va]) are fields of [ME] ([me_vl],
   [me_lau]); no new Hypothesis. *)
Section MainEntryProofs.
  Context {AMB : Amb}.
  Variable sp0 : word.
  Variables a0s path : list byte.
  Variable envv : list (list byte).
  Variable tid : word.
  Variable rdraw : EntryDraw.
  Variable regs : bvmap 5 word.
  Variable mem : word -> option byte.

  Let E := E0 sp0 a0s path envv tid rdraw regs.

  Lemma ev_vals : forall n, ev E n = nth n ([sp0; p0 a0s path envv rdraw; p1 a0s path envv rdraw; auxvp sp0 a0s path envv; rnd rdraw; tid] ++ junk_vals regs) (Z_to_bv 64 0).
  Proof. intros n. reflexivity. Qed.

  Lemma ev_junk : forall i, (i < 32)%nat -> ev E (6 + i) = getr regs (Z_to_bv 5 (Z.of_nat i)).
  Proof.
    intros i Hi. rewrite ev_vals. change (6 + i)%nat with (length [sp0; p0 a0s path envv rdraw; p1 a0s path envv rdraw; auxvp sp0 a0s path envv; rnd rdraw; tid] + i)%nat.
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
  Context {fs0 : Fs.Fs} {stdin0 : InputStream} {mbase : word}.
  Let av := [a0s; path].
  Hypothesis Hva : valid_argv av.
  Hypothesis Hve : valid_envp envv.
  Hypothesis Hvsp : valid_sp sp0.
  Hypothesis Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z.
  Hypothesis ME : main_entry sp0 rdraw (mkProcInputC av envv fs0 stdin0) mbase tid regs mem.
  Let E := E0 sp0 a0s path envv tid rdraw regs.

  (* [main_entry]'s projections take its seven parameters, then the record. *)
  (* [spx_val] is discharged over Section MainEntryProofs' own [Let E]; THIS Section
     rebinds its own [Let E] at :313, and [rewrite] does not delta-unfold a section
     [Let] to unify, so the rewrite has to unfold [E] first.  Measured without it
     (an earlier farm round, the S twin): registers 2, 12 and 19 -- the only
     [spx] entries of [sr_main] -- reach the close block as [edenot E (spx k)], no
     branch applies, and the miss surfaces at [Qed] naming no register. *)
  Ltac reg_case :=
    cbn [nth sr_main all_regs];
          first [ (unfold E; rewrite (spx_val sp0 a0s path envv tid rdraw regs))
                | lazymatch goal with |- _ = edenot _ (EVar ?n) =>
                    change (edenot E (EVar n)) with (ev E n);
                    try (rewrite (ev_junk _ _ _ _ _ _ _ (n - 6)) by lia; reflexivity)
                  | |- _ => cbn [edenot] end ];
          first [ reflexivity
                | exact (me_ra _ _ _ _ _ _ _ ME) | exact (me_gp _ _ _ _ _ _ _ ME) | exact (me_tp _ _ _ _ _ _ _ ME)
                | exact (me_s2 _ _ _ _ _ _ _ ME)
                | rewrite (me_sp _ _ _ _ _ _ _ ME); apply bv_eq; rewrite !u_small by lia; lia
                | rewrite (me_s0 _ _ _ _ _ _ _ ME); reflexivity
                | rewrite (me_a1 _ _ _ _ _ _ _ ME); reflexivity
                | rewrite (me_a2 _ _ _ _ _ _ _ ME); f_equal; change (in_argv (mkProcInputC av envv fs0 stdin0)) with av;
                  subst av; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ Pos.mul Z.mul Pos.add]; lia
                | rewrite (me_s3 _ _ _ _ _ _ _ ME); f_equal; change (in_argv (mkProcInputC av envv fs0 stdin0)) with av;
                  subst av; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ Pos.mul Z.mul Pos.add]; lia
                | rewrite (me_s1 _ _ _ _ _ _ _ ME); unfold argc_w, argcN, len_word; reflexivity
                | rewrite (me_a0 _ _ _ _ _ _ _ ME); unfold argc_w, argcN, len_word; reflexivity
                | apply (me_szero _ _ _ _ _ _ _ ME); cbn; tauto
                  (* No silent fallthrough: a register no branch above discharges is NAMED
                     here, at the [reg_case] call site, rather than reaching [Qed] as
                     "incomplete proof" naming nothing. *)
                | fail "reg_case: no close branch for register goal" ].

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
  Context {fs0 : Fs.Fs} {stdin0 : InputStream} {mbase : word}.
  Let av := [a0s; path].
  Hypothesis Hva : valid_argv av.
  Hypothesis Hve : valid_envp envv.
  Hypothesis Hvsp : valid_sp sp0.
  Hypothesis Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z.
  Hypothesis ME : main_entry sp0 rdraw (mkProcInputC av envv fs0 stdin0) mbase tid regs mem.
  Let E := E0 sp0 a0s path envv tid rdraw regs.

  Lemma kp_lo : (0x7fff80000000 <= bv_unsigned sp0)%Z. Proof. exact (proj1 Hvsp). Qed.
  Lemma kp_hi : (bv_unsigned sp0 <= 0x800000000000)%Z. Proof. exact (proj1 (proj2 Hvsp)). Qed.
  Lemma kp_al : (bv_unsigned sp0 mod 16 = 0)%Z. Proof. exact (proj2 (proj2 Hvsp)). Qed.
  Lemma ke0 : ev E 0 = sp0. Proof. reflexivity. Qed.
  Lemma ke1 : ev E 1 = p0 a0s path envv rdraw. Proof. reflexivity. Qed.
  Lemma ke2 : ev E 2 = p1 a0s path envv rdraw. Proof. reflexivity. Qed.
  Lemma ke3 : ev E 3 = auxvp sp0 a0s path envv. Proof. reflexivity. Qed.
  Lemma ke4 : ev E 4 = rnd rdraw. Proof. reflexivity. Qed.
  Lemma ke5 : ev E 5 = tid. Proof. reflexivity. Qed.

  Lemma me38_argv : in_argv (mkProcInputC av envv fs0 stdin0) = av. Proof. reflexivity. Qed.
  Lemma me38_vl : valid_launch (mkProcInputC av envv fs0 stdin0).
  Proof. exact (me_vl _ _ _ _ _ _ _ ME). Qed.
  Lemma me38_lau : exists brk, entry_launch_ok_va Sv48 (mkEntry sp0 brk mbase rdraw) (mkProcInputC av envv fs0 stdin0).
  Proof. exact (me_lau _ _ _ _ _ _ _ ME). Qed.

  Ltac me_prep := destruct me38_lau as [brk Hlau]; pose proof me38_vl as Hvl.

  (* Rewrite the launch input's projections back to the names this Section uses, so
     [lia] sees one atom per quantity (it collects atoms syntactically). *)
  Ltac inp_norm H :=
    try change (in_argv (mkProcInputC av envv fs0 stdin0)) with av in H;
    try change (in_envp (mkProcInputC av envv fs0 stdin0)) with envv in H;
    try change (in_execfn (mkProcInputC av envv fs0 stdin0)) with a_execfn in H;
    try change (in_kernel (mkProcInputC av envv fs0 stdin0)) with a_kernel in H.

  Lemma know_stack : know_ok RSEGS E mem kn_stack.
  Proof.
    pose proof kp_lo as Hlo. pose proof kp_hi as Hhi. pose proof kp_al as Hal.
    unfold kn_stack, know_ok.
    repeat apply Forall_cons; try apply Forall_nil; cbn [kentry_ok a_base a_off edenot]; rewrite ?ke0, ?ke1, ?ke2;
      unfold flat, estart; cbn [a_base a_off edenot]; rewrite ?ke0.
    - split; [lia | exact Hal].
    - lia.
    - (* [stack_window_depth] is an opaque model constant: [lia] does not unfold it
         (an earlier farm round: "Cannot find witness" here), so name its value. *)
      rewrite ?stack_window_depth_val. split; [lia|]. intros d m Hd Hm.
      (* #38 rule 12i: [main_entry_store_ok_win]'s low premise is now [wok_lo sp0]
         and the row's own bound is [stack_window_depth]; both are normalised to
         the same Z before lia.  Every unfold is [try], so neither side goal can
         fail merely because its constant is absent from that goal. *)
      apply (main_entry_store_ok_win _ _ _ _ _ _ _ ME);
        rewrite ?stack_window_depth_val; rewrite u_small by lia;
        try unfold wok_lo; try unfold stack_window_reach; try unfold stack_max_size; lia.
    - split; [lia|]. split; [lia|].
      unfold adenot. cbn [a_base a_off edenot]. rewrite ke0. unfold v_addi. rewrite Z.add_0_r, Z_to_bv_bv_unsigned.
      rewrite (main_entry_rdn_above _ _ _ _ _ _ _ ME) by lia.
      me_prep.
      assert (Hr : rdn RSEGS (wrap_mem (mkProcInputC av envv fs0 stdin0) mbase RPH (0x656f0 : word) sp0 rdraw) sp0 8
                   = Some (word_le8 (argcN (mkProcInputC av envv fs0 stdin0))))
        by (eapply (read_argc_w RSEGS Sv48 (mkProcInputC av envv fs0 stdin0) mbase RPH (0x656f0 : word) sp0 brk rdraw);
            try eassumption; first [unfold sp_window_lo; lia | unfold sp_window_hi; lia]).
      rewrite Hr. rewrite n_to_le_8_spec. reflexivity.
    - split; [lia|]. split; [lia|].
      unfold adenot. cbn [a_base a_off edenot]. rewrite ke0. unfold v_addi.
      rewrite (main_entry_rdn_above _ _ _ _ _ _ _ ME) by (rewrite u_small by lia; lia).
      me_prep.
      assert (Hr : rdn RSEGS (wrap_mem (mkProcInputC av envv fs0 stdin0) mbase RPH (0x656f0 : word) sp0 rdraw)
                     (sp0 + nat_to_word (8 + 8 * 0)) 8
                   = Some (word_le8 (cat_argv_ptr (ed_top rdraw) (in_argv (mkProcInputC av envv fs0 stdin0))
                                       (in_envp (mkProcInputC av envv fs0 stdin0)) (in_execfn (mkProcInputC av envv fs0 stdin0)) 0)))
        by (eapply (read_argv_ptr_w RSEGS Sv48 (mkProcInputC av envv fs0 stdin0) mbase RPH (0x656f0 : word) sp0 brk rdraw);
            try eassumption; first [unfold sp_window_lo; lia | unfold sp_window_hi; lia | rewrite me38_argv; subst av; cbn; lia]).
      rewrite w_add_nat in Hr. change (Z.of_nat (8 + 8 * 0)) with 8%Z in Hr.
      rewrite Hr. rewrite n_to_le_8_spec. reflexivity.
    - split; [lia|]. split; [lia|].
      unfold adenot. cbn [a_base a_off edenot]. rewrite ke0. unfold v_addi.
      rewrite (main_entry_rdn_above _ _ _ _ _ _ _ ME) by (rewrite u_small by lia; lia).
      me_prep.
      assert (Hr : rdn RSEGS (wrap_mem (mkProcInputC av envv fs0 stdin0) mbase RPH (0x656f0 : word) sp0 rdraw)
                     (sp0 + nat_to_word (8 + 8 * 1)) 8
                   = Some (word_le8 (cat_argv_ptr (ed_top rdraw) (in_argv (mkProcInputC av envv fs0 stdin0))
                                       (in_envp (mkProcInputC av envv fs0 stdin0)) (in_execfn (mkProcInputC av envv fs0 stdin0)) 1)))
        by (eapply (read_argv_ptr_w RSEGS Sv48 (mkProcInputC av envv fs0 stdin0) mbase RPH (0x656f0 : word) sp0 brk rdraw);
            try eassumption; first [unfold sp_window_lo; lia | unfold sp_window_hi; lia | rewrite me38_argv; subst av; cbn; lia]).
      rewrite w_add_nat in Hr. change (Z.of_nat (8 + 8 * 1)) with 16%Z in Hr.
      rewrite Hr. rewrite n_to_le_8_spec. reflexivity.
    - split; [lia|]. split; [lia|].
      unfold adenot. cbn [a_base a_off edenot]. rewrite ke0. unfold v_addi.
      rewrite (main_entry_rdn_above _ _ _ _ _ _ _ ME) by (rewrite u_small by lia; lia).
      me_prep.
      assert (Hr : rdn RSEGS (stack_to_mem sp0 (entry_stack_image (mkProcInputC av envv fs0 stdin0) mbase RPH (0x656f0 : word) sp0 rdraw))
                     (sp0 + nat_to_word (8 + 8 * length (in_argv (mkProcInputC av envv fs0 stdin0)))) 8
                   = Some (word_le8 (Z_to_bv 64 0)))
        by (eapply (read_argv_null RSEGS Sv48 (mkProcInputC av envv fs0 stdin0) mbase RPH (0x656f0 : word) sp0 brk rdraw);
            try eassumption; first [unfold sp_window_lo; lia | unfold sp_window_hi; lia]).
      rewrite w_add_nat in Hr. rewrite me38_argv in Hr. subst av. change (Z.of_nat (8 + 8 * length [a0s; path])) with 24%Z in Hr.
      rewrite <- (rdn_wmem_stack RSEGS (mkProcInputC [a0s; path] envv fs0 stdin0) mbase RPH (0x656f0 : word) sp0 rdraw) in Hr
        by (try rewrite u_small by lia; lia).
      unfold wmem in Hr. rewrite n_to_le_8_spec in Hr. exact Hr.
  Qed.

  Lemma auxvp_eq : auxvp sp0 a0s path envv = Z_to_bv 64 (bv_unsigned sp0 + Z.of_nat (auxv_off av envv)).
  Proof. unfold auxvp, auxv_off. subst av. cbn [length]. f_equal. lia. Qed.

  (* 464 = [auxv_size true], the larger layout: the row stays kernel-free. *)
  Lemma auxvp_u : bv_unsigned (auxvp sp0 a0s path envv) = (bv_unsigned sp0 + Z.of_nat (auxv_off av envv))%Z
    /\ (Z.of_nat (auxv_off av envv) + 464 <= 2240000)%Z.
  Proof.
    pose proof kp_lo. pose proof kp_hi. destruct Hve as [Hle _].
    rewrite auxvp_eq. unfold auxv_off in *. subst av. cbn [length] in *.
    rewrite u_small by lia. split; lia.
  Qed.

  Lemma rnd_u2 : (bv_unsigned sp0 <= bv_unsigned (at_random_ptr sp0 (kb_rseq a_kernel) av envv))%Z
    /\ (bv_unsigned (at_random_ptr sp0 (kb_rseq a_kernel) av envv) + 16 <= bv_unsigned sp0 + 2240000)%Z
    /\ (bv_unsigned (at_random_ptr sp0 (kb_rseq a_kernel) av envv) mod 8 = 0)%Z
    /\ (forall j n, (j + n <= 16)%nat ->
          rdn RSEGS mem (Z_to_bv 64 (bv_unsigned (at_random_ptr sp0 (kb_rseq a_kernel) av envv) + Z.of_nat j)) n
          = Some (firstn n (skipn j (at_random_bytes (ed_random rdraw))))).
  Proof.
    me_prep. pose proof kp_lo as HLO. pose proof kp_hi as HHI.
    pose proof (lay_bsb_len Sv48 (mkProcInputC av envv fs0 stdin0) mbase RPH (0x656f0 : word) sp0 brk rdraw Hvl Hlau) as Hl.
    assert (RF := rnd_facts RSEGS Sv48 (mkProcInputC av envv fs0 stdin0) mbase RPH (0x656f0 : word) sp0 brk rdraw).
    repeat match type of RF with ?P -> _ =>
      specialize (RF ltac:(first [exact Hva | exact Hve | exact Hvl | exact Hlau | exact kp_al
                                 | (unfold sp_window_lo; lia) | (unfold sp_window_hi; lia)])) end.
    destruct RF as (A & B & C & D & F).
    (* #38.  [RefLayout.rnd_facts] states its bounds in the INPUT's spelling and this
       Section states them in [av]/[envv]/[a_kernel].  The two are CONVERTIBLE but NOT
       SYNTACTICALLY EQUAL, which is invisible to [exact] and fatal to [lia]: zify
       abstracts a non-arithmetic application as an ATOM and matches atoms
       syntactically, so it sees A's bound and the goal's term as two unrelated
       variables and answers "Cannot find witness".
       PRINTED on the S twin, not inferred (a diagnostic farm
       round): A came out in the input spelling while the [u_small] side condition
       came out as
         0 <= bv_unsigned (at_random_ptr sp0 (kb_rseq a_kernel) av envv)
                + Z.of_nat j < 2 ^ 64
       -- two spellings of one term.  The same round showed that normalising the
       HYPOTHESES with [reflexivity] equations and [rewrite ? .. in A,B,C,D,F] DID
       NOTHING, so that route is removed rather than left in place: `?` makes a no-op
       silent, the fallthrough class this file was already bitten by at :345.
       Instead restate the two bounds in THE GOAL'S OWN SPELLING and discharge them by
       [exact], which goes through conversion.  Both are round-backed: the next line
       already proves exactly these two statements and both SUCCEEDED in
       a later farm round.  No bound is adjusted and nothing is assumed. *)
    assert (RA : (bv_unsigned sp0
                  <= bv_unsigned (at_random_ptr sp0 (kb_rseq a_kernel) av envv))%Z)
      by exact A.
    assert (RB : (bv_unsigned (at_random_ptr sp0 (kb_rseq a_kernel) av envv) + 16
                  <= bv_unsigned sp0 + 2240000)%Z)
      by (eapply Z.le_trans; [exact B | lia]).
    split; [exact A|]. split; [eapply Z.le_trans; [exact B | lia]|]. split; [exact D|].
    intros j n Hjn. rewrite (main_entry_rdn_above _ _ _ _ _ _ _ ME) by (rewrite u_small by lia; lia).
    pose proof (rdn_wmem_stack RSEGS (mkProcInputC av envv fs0 stdin0) mbase RPH (0x656f0 : word) sp0 rdraw) as Hw.
    unfold wmem in Hw. rewrite Hw by (rewrite u_small by lia; lia). apply F. exact Hjn.
  Qed.

  (* An auxv word of the main entry's memory, read off the stack image
     ([RefLayout.read_auxv_word]), for both CONFIG_RSEQ layouts, [j] ranging over the
     vector.  (bzip2 S0MainEntry's [rd_auxv_main], re-keyed to this tree's entry point
     0x656f0 and launch input.) *)
  Lemma rd_auxv_main : forall j w a,
    (j < 2 * auxv_count (kb_rseq (in_kernel (mkProcInputC av envv fs0 stdin0))))%nat ->
    nth j (auxv_words (launch_auxv (mkProcInputC av envv fs0 stdin0) sp0 mbase) RPH (0x656f0 : word)
             (in_uid (mkProcInputC av envv fs0 stdin0)) (in_gid (mkProcInputC av envv fs0 stdin0))
             (in_hwcap (mkProcInputC av envv fs0 stdin0))
             (at_random_ptr sp0 (kb_rseq (in_kernel (mkProcInputC av envv fs0 stdin0)))
                (in_argv (mkProcInputC av envv fs0 stdin0)) (in_envp (mkProcInputC av envv fs0 stdin0)))
             (at_execfn_ptr (ed_top rdraw) (in_execfn (mkProcInputC av envv fs0 stdin0)))) (Z_to_bv 64 0) = w ->
    a = (bv_unsigned (auxvp sp0 a0s path envv) + 8 * Z.of_nat j)%Z ->
    rdn RSEGS mem (Z_to_bv 64 a) 8 = Some (word_to_le_bytes 8 w).
  Proof.
    intros j w a Hj Hw ->. me_prep. pose proof kp_lo as Hlo. pose proof kp_hi as Hhi.
    destruct auxvp_u as [Hau Hab].
    assert (Hac : (auxv_count (kb_rseq (in_kernel (mkProcInputC av envv fs0 stdin0))) <= 29)%nat)
      by (unfold auxv_count; destruct (kb_rseq (in_kernel (mkProcInputC av envv fs0 stdin0))); lia).
    rewrite (main_entry_rdn_above _ _ _ _ _ _ _ ME) by (rewrite u_small by lia; lia).
    pose proof (rdn_wmem_stack RSEGS (mkProcInputC av envv fs0 stdin0) mbase RPH (0x656f0 : word) sp0 rdraw) as Hwm.
    unfold wmem in Hwm. rewrite Hwm by (rewrite u_small by lia; lia).
    replace (Z_to_bv 64 (bv_unsigned (auxvp sp0 a0s path envv) + 8 * Z.of_nat j))
      with (sp0 + nat_to_word (auxv_off (in_argv (mkProcInputC av envv fs0 stdin0)) (in_envp (mkProcInputC av envv fs0 stdin0)) + 8 * j))
      by (rewrite w_add_nat; f_equal; rewrite Hau;
          change (in_argv (mkProcInputC av envv fs0 stdin0)) with av;
          change (in_envp (mkProcInputC av envv fs0 stdin0)) with envv; lia).
    rewrite <- Hw.
    eapply read_auxv_word; first [exact Hva | exact Hve | exact Hvl | exact Hlau | exact Hj
                                 | (unfold sp_window_lo; lia) | (unfold sp_window_hi; lia) | eassumption].
  Qed.

  (* One recorded auxv word: element [j] of [auxv_words], at byte offset [8 * j] from
     [auxvp].  Proved once and applied per row.  The bound is [j < 2 * auxv_count], so a
     row below pair 26 holds at BOTH [kb_rseq] values and pins nothing. *)
  Lemma kauxv_word : forall (j : nat) (t : Z),
    (j < 2 * auxv_count (kb_rseq (in_kernel (mkProcInputC av envv fs0 stdin0))))%nat ->
    nth j (auxv_words (launch_auxv (mkProcInputC av envv fs0 stdin0) sp0 mbase) RPH (0x656f0 : word)
             (in_uid (mkProcInputC av envv fs0 stdin0)) (in_gid (mkProcInputC av envv fs0 stdin0))
             (in_hwcap (mkProcInputC av envv fs0 stdin0))
             (at_random_ptr sp0 (kb_rseq (in_kernel (mkProcInputC av envv fs0 stdin0)))
                (in_argv (mkProcInputC av envv fs0 stdin0)) (in_envp (mkProcInputC av envv fs0 stdin0)))
             (at_execfn_ptr (ed_top rdraw) (in_execfn (mkProcInputC av envv fs0 stdin0)))) (Z_to_bv 64 0) = Z_to_bv 64 t ->
    kentry_ok RSEGS E mem (KWord (SA (EVar 3) (8 * Z.of_nat j)) 8 (ELit t)).
  Proof.
    intros j t Hj Ht. pose proof kp_lo as Hlo. pose proof kp_hi as Hhi.
    destruct auxvp_u as [Hau Hab].
    assert (Hac : (auxv_count (kb_rseq (in_kernel (mkProcInputC av envv fs0 stdin0))) <= 29)%nat)
      by (unfold auxv_count; destruct (kb_rseq (in_kernel (mkProcInputC av envv fs0 stdin0))); lia).
    cbn [kentry_ok]. split; [lia|].
    unfold flat, estart. cbn [a_base a_off edenot]. rewrite ke3. rewrite Hau.
    split; [repeat split; lia|].
    cbn [adenot a_base a_off edenot]. rewrite ?ke3.
    erewrite <- (rd_auxv_main j (Z_to_bv 64 t));
      [ f_equal
      | exact Hj
      | exact Ht
      | cbn [a_base a_off edenot]; rewrite ke3; lia ].
  Qed.

  Ltac kgen Hau :=
    cbn [kentry_ok a_base a_off edenot];
    rewrite ?ke0, ?ke3, ?ke4; unfold flat, estart, elenZ; cbn [a_base a_off edenot]; rewrite ?ke0, ?ke3, ?ke4;
    try rewrite Hau; try lia.

  Ltac kauxv_side :=
    first [ match goal with |- context [auxv_count ?b] => unfold auxv_count; destruct b; lia end
          | vm_compute; reflexivity ].

  Lemma know_auxv : know_ok RSEGS E mem kn_auxv.
  Proof.
    pose proof kp_lo as Hlo. pose proof kp_hi as Hhi. pose proof kp_al as Hal.
    destruct auxvp_u as [Hau Hab].
    unfold kn_auxv, know_ok.
    apply Forall_cons; [solve [kgen Hau]|].
    apply Forall_cons; [solve [kgen Hau]|].
    apply Forall_cons.
    { kgen Hau. split; [lia|].
      destruct (proj1 (Z.mod_divide (bv_unsigned sp0) 16 ltac:(lia)) Hal) as [q Hq].
      replace (bv_unsigned sp0 + Z.of_nat (auxv_off av envv))%Z with ((2 * q + 5 + Z.of_nat (length envv)) * 8)%Z
        by (unfold auxv_off; subst av; cbn [length]; lia).
      apply Z_mod_mult. }
    repeat apply Forall_cons; try apply Forall_nil;
      [ apply (kauxv_word 0 33)   | apply (kauxv_word 2 40)   | apply (kauxv_word 4 41)
      | apply (kauxv_word 6 42)   | apply (kauxv_word 8 43)   | apply (kauxv_word 10 44)
      | apply (kauxv_word 12 45)  | apply (kauxv_word 14 46)  | apply (kauxv_word 16 47)
      | apply (kauxv_word 18 51)  | apply (kauxv_word 20 16)  | apply (kauxv_word 22 6)
      | apply (kauxv_word 23 4096) | apply (kauxv_word 24 17) | apply (kauxv_word 26 3)
      | apply (kauxv_word 27 0x10040) | apply (kauxv_word 28 4) | apply (kauxv_word 29 56)
      | apply (kauxv_word 30 5)   | apply (kauxv_word 31 10)  | apply (kauxv_word 32 7)
      | apply (kauxv_word 34 8)   | apply (kauxv_word 36 9)   | apply (kauxv_word 38 11)
      | apply (kauxv_word 40 12)  | apply (kauxv_word 42 13)  | apply (kauxv_word 44 14)
      | apply (kauxv_word 46 23)  | apply (kauxv_word 47 0)   | apply (kauxv_word 48 25)
      | apply (kauxv_word 50 31) ];
      kauxv_side.
  Qed.

  (* The terminator words ([kn_termT] / [kn_termF]) as the disjunction of the two
     [kb_rseq] cases: the flag is case-split here and never fixed.  Each row is
     [kauxv_word] at an index below that case's [2 * auxv_count] (52, 54, 56 < 58 with
     CONFIG_RSEQ; 52 < 54 without), and the word itself is read off [auxv_entries] once
     the launch record's [la_rseq] is the case's literal. *)
  Lemma know_auxv_term : know_ok RSEGS E mem kn_termT \/ know_ok RSEGS E mem kn_termF.
  Proof.
    destruct (kb_rseq (in_kernel (mkProcInputC av envv fs0 stdin0))) eqn:Hr; [left | right];
      unfold kn_termT, kn_termF, know_ok;
      repeat apply Forall_cons; try apply Forall_nil;
      [ apply (kauxv_word 52 27) | apply (kauxv_word 54 28) | apply (kauxv_word 56 0)
      | apply (kauxv_word 52 0) ];
      first [ unfold auxv_count; rewrite Hr; cbv beta iota; lia
            | generalize (eq_refl : la_rseq (launch_auxv (mkProcInputC av envv fs0 stdin0) sp0 mbase)
                                    = kb_rseq (in_kernel (mkProcInputC av envv fs0 stdin0)));
              rewrite Hr; destruct (launch_auxv (mkProcInputC av envv fs0 stdin0) sp0 mbase) as [la_e la_c la_m la_r];
              cbn [la_rseq]; intros ->; vm_compute; reflexivity ].
  Qed.

  Lemma auxvp_w : auxvp sp0 a0s path envv = auxv_w (mkProcInputC av envv fs0 stdin0) sp0.
  Proof. reflexivity. Qed.

  Lemma kimg_ok : forall lo hi, D_main_missb lo (Z.to_nat (hi - lo)) = true -> (lo <= hi)%Z -> (hi <= 0x124000)%Z ->
    kentry_ok RSEGS E mem (KImg lo hi).
  Proof.
    intros lo hi Hb Hle Hhi. pose proof kp_lo as HLO. pose proof kp_hi as HHI.
    destruct (missb_parts lo _ Hb) as (_ & _ & Hlo0 & _).
    cbn [kentry_ok]. split; [lia|]. split; [lia|]. intros i Hi.
    rewrite (main_entry_mem_data _ _ _ _ _ _ _ ME) by (rewrite u_small by lia; unfold stack_max_size; lia).
    apply (D_main_none sp0 (mkProcInputC av envv fs0 stdin0) tid rdraw Hva).
    apply (missb_sub lo (Z.to_nat (hi - lo))); [exact Hb | lia | rewrite Z2Nat.id by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia].
  Qed.

  Ltac kimg := apply kimg_ok; [vm_compute; reflexivity | lia | lia].

  Ltac kw_pre :=
    split; [lia|]; split; [lia|];
    unfold adenot; cbn [a_base a_off edenot]; unfold v_addi; rewrite u_small by lia; rewrite Z.add_0_l.
  (* Every image word goes through [D_main1] ([main_entry_rdn_data]); the tid and guard
     words used to go through S1StartupFacts' ME-lemmas, which take the same route. *)
  Ltac kw_data L :=
    kw_pre;
    rewrite (main_entry_rdn_data _ _ _ _ _ _ _ ME) by (rewrite u_small by lia; unfold stack_max_size; lia);
    rewrite (L RSEGS); try reflexivity.

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
    - kw_data (D_main_self sp0 (mkProcInputC av envv fs0 stdin0) tid rdraw Hva).
    - kw_data (D_main_tid sp0 (mkProcInputC av envv fs0 stdin0) tid rdraw Hva).
    - kw_data (D_main_canary sp0 (mkProcInputC av envv fs0 stdin0) tid rdraw Hva).
    - kw_data (D_main_guard sp0 (mkProcInputC av envv fs0 stdin0) tid rdraw Hva).
    - rewrite auxvp_w. kw_data (D_main_auxv sp0 (mkProcInputC av envv fs0 stdin0) tid rdraw Hva).
    - kw_data (D_main_pagesize sp0 (mkProcInputC av envv fs0 stdin0) tid rdraw Hva).
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
    rewrite (main_entry_rdn_data _ _ _ _ _ _ _ ME) by (rewrite u_small by lia; unfold stack_max_size; lia).
    rewrite (D_main_cxx sp0 (mkProcInputC av envv fs0 stdin0) tid rdraw RSEGS a w zs) by (try exact HLK; lia).
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
      rewrite (main_entry_rdn_data _ _ _ _ _ _ _ ME) by (rewrite u_small by lia; unfold stack_max_size; lia).
      erewrite (D_main_cxx sp0 (mkProcInputC av envv fs0 stdin0) tid rdraw RSEGS); [ | lia | cbn; lia | reflexivity].
      f_equal. apply byte_list_eq2. vm_compute. reflexivity.
  Qed.

  Theorem main_know_ok : know_ok RSEGS E mem kn_main.
  Proof.
    unfold kn_main, know_ok.
    apply Forall_app; split; [apply know_stack|].
    apply Forall_app; split; [apply know_auxv | apply know_image].
  Qed.

  (* [main_know_ok] plus the [kb_rseq]-split terminator rows, and the fact that the auxv
     sits above sp0 (so the rows survive every store below it). *)
  Theorem main_know_term : (bv_unsigned sp0 <= bv_unsigned (auxvp sp0 a0s path envv))%Z /\
    (know_ok RSEGS E mem (kn_main ++ kn_termT) \/ know_ok RSEGS E mem (kn_main ++ kn_termF)).
  Proof.
    split; [pose proof kp_lo; destruct auxvp_u as [Hau _]; rewrite Hau; lia|].
    pose proof main_know_ok as HK.
    destruct know_auxv_term as [HT|HT]; [left | right];
      unfold know_ok in *; apply Forall_app; split; assumption.
  Qed.

  Theorem main_know_sx : know_ok RSEGS E mem kn_sx.
  Proof.
    apply know_sx.
    - unfold E, E0, blobs0. apply blobs_sx_ok_app. reflexivity.
    - eapply main_entry_pins_sx; [exact (proj1 Hvsp) | exact ME].
  Qed.

  (* #38: argv string [k] is at [cat_argv_ptr (ed_top rdraw) av envv a_execfn k], in the
     string block below [ed_top], not at a fixed offset from sp0. *)
  Lemma main_str : forall k, (k < 2)%nat ->
    rdn RSEGS mem (cat_argv_ptr (ed_top rdraw) av envv a_execfn k) (length (nth k av []) + 1) = Some (nth k av [] ++ [Z_to_bv 8 0])
    /\ (bv_unsigned sp0 <= bv_unsigned (cat_argv_ptr (ed_top rdraw) av envv a_execfn k))%Z
    /\ (bv_unsigned (cat_argv_ptr (ed_top rdraw) av envv a_execfn k) <= bv_unsigned sp0 + 2107576)%Z
    /\ (Z.of_nat (length (nth k av [])) <= 131071)%Z.
  Proof.
    intros k Hk. me_prep. pose proof kp_lo as Hlo. pose proof kp_hi as Hhi.
    assert (Hka : (k < length av)%nat) by (subst av; cbn; lia).
    assert (Hk' : (k < length (in_argv (mkProcInputC av envv fs0 stdin0)))%nat) by (rewrite me38_argv; exact Hka).
    destruct (argv_ptr_bounds Sv48 (mkProcInputC av envv fs0 stdin0) mbase sp0 brk rdraw k Hlau Hk') as [B1 B2].
    assert (Hu : bv_unsigned (cat_argv_ptr (ed_top rdraw) (in_argv (mkProcInputC av envv fs0 stdin0))
                                (in_envp (mkProcInputC av envv fs0 stdin0)) (in_execfn (mkProcInputC av envv fs0 stdin0)) k)
                 = (bv_unsigned sp0
                    + Z.of_nat (cat_string_off (kb_rseq (in_kernel (mkProcInputC av envv fs0 stdin0))) sp0 (ed_top rdraw)
                                  (in_argv (mkProcInputC av envv fs0 stdin0)) (in_envp (mkProcInputC av envv fs0 stdin0))
                                  (in_execfn (mkProcInputC av envv fs0 stdin0))
                                + total_arg_bytes_nat (firstn k (in_argv (mkProcInputC av envv fs0 stdin0)))))%Z)
      by (eapply (u_cat_argv_ptr Sv48 (mkProcInputC av envv fs0 stdin0) mbase RPH (0x656f0 : word) sp0 brk rdraw);
          try eassumption; first [unfold sp_window_lo; lia | unfold sp_window_hi; lia]).
    pose proof (struct_av_bound (mkProcInputC av envv fs0 stdin0) mbase RPH (0x656f0 : word) sp0 brk rdraw) as Hsb.
    pose proof (lay_bsb_len Sv48 (mkProcInputC av envv fs0 stdin0) mbase RPH (0x656f0 : word) sp0 brk rdraw Hvl Hlau) as Hl.
    pose proof (total_arg_bytes_firstn_le k av) as Hf.
    pose proof (valid_argv_str_len av k Hva Hka) as Hlen.
    inp_norm B1. inp_norm B2. inp_norm Hu. inp_norm Hsb.
    repeat split.
    - rewrite (main_entry_rdn_above _ _ _ _ _ _ _ ME) by lia.
      pose proof (rdn_wmem_stack RSEGS (mkProcInputC av envv fs0 stdin0) mbase RPH (0x656f0 : word) sp0 rdraw) as Hw.
      unfold wmem in Hw. rewrite Hw by lia.
      exact (read_argv_cstr_k Sv48 RSEGS (mkProcInputC av envv fs0 stdin0) mbase RPH (0x656f0 : word) sp0 brk rdraw k Hlau Hk').
    - exact B1.
    - lia.
    - exact Hlen.
  Qed.
End KnowProofs.
