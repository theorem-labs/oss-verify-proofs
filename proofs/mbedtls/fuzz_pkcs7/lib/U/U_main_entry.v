(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.mbedtls.fuzz_pkcs7.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import PropExec.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BB Require Import Amb CatExec CatSim SeqExec StoreOk FileSim ArgvEnv SymExec SymExec2 SymExec2Sound SymRun SymDrive MemSplit Layout StartupTac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import U_startup_defs U_startup U_startup_facts.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.
#[local] Existing Instance PropExec.fx0.

Abbreviation RSEGS := Ubsan.M.loaded_segments.
Abbreviation RPH := Ubsan.M.phdrs.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
Ltac2 gd_tbl_P_main_entry () : Init.string Init.list := ["stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.list"; "LinuxProcessSemantics.LinuxProcessSem.StackLayout.EntryDraw"; "Corelib.Numbers.BinNums.Z"; "LinuxProcessSemantics.LinuxProcessSem.Run.valid_argv"; "Stdlib.ZArith.BinInt.Z.le"; "stdpp.bitvector.definitions.bv_unsigned"; "Corelib.Init.Logic.eq"; "Corelib.Init.Datatypes.bool"; "RocqVerifyHarness.AgentSubmission.U.U_startup_facts.D_main_missb"; "Corelib.Init.Datatypes.true"; "Corelib.Init.Datatypes.option"; "RocqVerifyHarness.AgentSubmission.U.U_startup_defs.D_main"; "stdpp.bitvector.definitions.Z_to_bv"; "Corelib.Init.Datatypes.None"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.expr"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.ELit"; "MainEntry.spx"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.EVar"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.kentry"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.KAlign"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.KRange"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.KWr"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.SA"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.KWord"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.KDisj"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.KImg"; "stdpp.bitvector.definitions.BV"; "Corelib.Init.Logic.I"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.env"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Corelib.Init.Datatypes.nat"; "Corelib.Init.Peano.lt"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.getr"; "Corelib.Lists.ListDef.nth"; "all_regs"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.edenot"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2Sound.SX2S.regs_ok"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.ev"; "Corelib.Init.Datatypes.app"; "p0"; "p1"; "auxvp"; "rnd"; "RocqVerifyHarness.AgentSubmission.U.U_startup_defs.canary_w"; "RocqVerifyHarness.AgentSubmission.BB.Amb.a_hwcap"; "junk_vals2"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.of_nat"; "RocqVerifyHarness.AgentSubmission.BB.Layout.auxv_off"; "Stdlib.ZArith.BinInt.Z.modulo"; "Corelib.Init.Peano.le"; "Corelib.Init.Nat.add"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.rdn"; "LinuxProcessSemantics.LinuxProcessSem.MemImageType.Segment"; "LinuxProcessSemantics.LinuxProcessSem.StackLayout.stack_to_mem"; "LinuxProcessSemantics.LinuxProcessSem.Run.entry_stack_image"; "RocqVerifyHarness.ProcessOversight.Tgt_fuzz_pkcs7_ubsan.M.phdrs"; "RocqVerifyHarness.AgentSubmission.BB.Amb.a_uid"; "Corelib.Init.Datatypes.Some"; "Corelib.Lists.ListDef.firstn"; "Corelib.Lists.ListDef.skipn"; "RocqVerifyHarness.AgentSubmission.U.U_startup_defs.rnd_bytes"; "RocqVerifyHarness.ProcessOversight.Tgt_fuzz_pkcs7_ubsan.M.loaded_segments"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.word_to_le_bytes"; "RocqVerifyHarness.AgentSubmission.U.U_startup_defs.secret_w"; "Stdlib.ZArith.BinInt.Z.mul"; "RocqVerifyHarness.AgentSubmission.BB.Layout.auxv_words"; "Corelib.Init.Datatypes.prod"; "RocqVerifyHarness.AgentSubmission.U.U_startup_facts.range_disjoint_b"; "Stdlib.ZArith.BinInt.Z.to_nat"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2Sound.SX2S.kentry_ok"; "RocqVerifyHarness.AgentSubmission.BB.CatExec.cat_argv_ptr"; "Corelib.Init.Datatypes.length"].


Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
Lemma D_main_none : ltac2:(CDefT.buildp (gd_tbl_P_main_entry ()) "Psp0,(0.&40.)Pav,(1.(1.(0.&8.)))Pev,(1.(1.(0.&8.)))Phw,(0.&40.)Prd,$2.Ptid,(0.&40.)Pi,$3.P,(4.R6.)P,(5.+7???80000000.(6.&40.R8.))P,(5.(6.&40.R9.)+800000000000.)P,(7.$8.(9.R4.#1.)$:.)(7.(;.(0.&8.))(<.R;.R:.R9.R8.R7.R6.(=.&40.R5.))(>.(0.&8.)))")
(* [comment removed for export] *).
Proof.
  intros sp0 av ev hw rd tid i Hva Hlo Hhi Hb.
  pose proof (u64_range tid) as Ht.
  unfold D_main_missb, D_main_cells in Hb. cbn [forallb] in Hb.
  repeat match goal with
         | H : (_ && _)%bool = true |- _ => apply andb_true_iff in H; destruct H as [? ?]
         end.
  repeat match goal with
         | H : range_disjoint_b _ _ _ = true |- _ =>
             apply range_disjoint_djw in H; cbn [fst snd] in H
         | H : (_ <=? _)%Z = true |- _ => apply Z.leb_le in H
         | H : true = true |- _ => clear H
         end.
  assert (Hui : bv_unsigned (Z_to_bv 64 i) = i) by (apply u_small; lia).
  unfold D_main, D_fd, D_ssp, D_tls, D_tlsB, D_tlsA, D_libc.
  repeat (rewrite MemSplit.wbytes_outside;
    [ | rewrite ?length_N_to_le_bytes; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; rewrite u_small by (cbn; lia); cbn; lia
      | rewrite ?length_N_to_le_bytes; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; rewrite Hui; rewrite u_small by (cbn; lia);
        match goal with H : djw _ |- _ => unfold djw in H; clear -H; lia end ]).
  reflexivity.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L19939001730.2000006S1a2Ha". (* [comment removed for export] *)
Lemma seg_rom_high : forall (a : word), (0x7e000 <= bv_unsigned a)%Z -> seg_rom RSEGS a = None.
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
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)

Section MainEntry.
  Context {AMB : Amb}.
  Variable sp0 : word.
  Variables a0s path : list byte.
  Variable ev : list (list byte).
  Variable tid : word.
  Variable rd : EntryDraw.
  Variable regs : bvmap 5 word.
  Variable mem : word -> option byte.
  Let av := [a0s; path].
  Hypothesis Hva : valid_argv av.
  Hypothesis Hve : valid_envp ev.
  Hypothesis Hvsp : valid_sp sp0.
  Hypothesis Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z.
  Hypothesis ME : main_entry sp0 av ev tid rd regs mem.

  Let Hlo : (0x7fff80000000 <= bv_unsigned sp0)%Z := proj1 Hvsp.
  Let Hhi : (bv_unsigned sp0 <= 0x800000000000)%Z := proj1 (proj2 Hvsp).
  Let Hal : (bv_unsigned sp0 mod 16 = 0)%Z := proj2 (proj2 Hvsp).

  Definition p0 : word := cat_argv_ptr sp0 av ev 0.
  Definition p1 : word := cat_argv_ptr sp0 av ev 1.
  Definition auxvp : word := auxv_w sp0 av ev.
  Definition rnd : word := at_random_ptr sp0 av ev.

  (* [comment removed for export] *)
  Definition junk_vals2 (R : bvmap 5 word) : list word :=
    map (fun i => getr R (Z_to_bv 5 (Z.of_nat i))) (seq 2 30).
  Definition vals0 : list word := [sp0; p0; p1; auxvp; rnd; tid; canary_w rd; a_hwcap] ++ junk_vals2 regs.
  Definition blobs0 : list (list byte) := [a0s ++ [Z_to_bv 8 0]; path ++ [Z_to_bv 8 0]].
  Definition E0 : env := Env (vals_ev vals0) (blobs_ev blobs0).

  Definition spx (k : Z) : expr := EAlu ALU_ADD (EVar 0) (ELit k).

  Definition sr_main : list expr := ltac2:(CDefT.buildp (gd_tbl_P_main_entry ()) "(?.$10.(11.=)(?.$10.(11.+3?2:8.)(?.$10.(12.-30.)(?.$10.(11.+10800.)(?.$10.(11.+5=0<8.)(?.$10.(13.#;.)(?.$10.(13.#<.)(?.$10.(13.#=.)(?.$10.(12.+8.)(?.$10.(11.+2.)(?.$10.(11.+2.)(?.$10.(12.+8.)(?.$10.(12.+20.)(?.$10.(13.#13.)(?.$10.(13.#14.)(?.$10.(13.#15.)(?.$10.(13.#16.)(?.$10.(13.#17.)(?.$10.(11.+1=24<.)(?.$10.(12.+20.)(?.$10.(11.=)(?.$10.(11.=)(?.$10.(11.=)(?.$10.(11.=)(?.$10.(11.=)(?.$10.(11.=)(?.$10.(11.=)(?.$10.(11.=)(?.$10.(13.#22.)(?.$10.(13.#23.)(?.$10.(13.#24.)(?.$10.(13.#25.)(14.$10.)))))))))))))))))))))))))))))))))")
(* [comment removed for export] *).

  Definition kn_stack : list kentry := ltac2:(CDefT.buildp (gd_tbl_P_main_entry ()) "(?.$15.(16.(13.#0.)+10.)(?.$15.(17.(13.#0.)+7???80000000.+800000000000.)(?.$15.(18.(19.(13.#0.)-800000.)+800000.)(?.$15.(1:.(19.(13.#0.)=)#8.(11.+2.))(?.$15.(1:.(19.(13.#0.)+8.)#8.(13.#1.))(?.$15.(1:.(19.(13.#0.)+10.)#8.(13.#2.))(?.$15.(1:.(19.(13.#0.)+18.)#8.(11.=))(14.$15.))))))))")
(* [comment removed for export] *).

  Definition kn_auxv : list kentry := ltac2:(CDefT.buildp (gd_tbl_P_main_entry ()) "(?.$15.(17.(13.#3.)+7???80000000.+800000400000.)(?.$15.(17.(13.#4.)+7???80000000.+800000400000.)(?.$15.(1;.(19.(13.#0.)-800000.)+800000.(19.(13.#3.)=)+:0.)(?.$15.(1;.(19.(13.#0.)-800000.)+800000.(19.(13.#4.)=)+10.)(?.$15.(16.(13.#3.)+8.)(?.$15.(16.(13.#4.)+8.)(?.$15.(1:.(19.(13.#3.)=)#8.(11.+3.))(?.$15.(1:.(19.(13.#3.)+8.)#8.(11.+10040.))(?.$15.(1:.(19.(13.#3.)+10.)#8.(11.+4.))(?.$15.(1:.(19.(13.#3.)+18.)#8.(11.+38.))(?.$15.(1:.(19.(13.#3.)+20.)#8.(11.+5.))(?.$15.(1:.(19.(13.#3.)+28.)#8.(11.+:.))(?.$15.(1:.(19.(13.#3.)+30.)#8.(11.+10.))(?.$15.(1:.(19.(13.#3.)+38.)#8.(13.#7.))(?.$15.(1:.(19.(13.#3.)+40.)#8.(11.+6.))(?.$15.(1:.(19.(13.#3.)+48.)#8.(11.+1000.))(?.$15.(1:.(19.(13.#3.)+50.)#8.(11.+;.))(?.$15.(1:.(19.(13.#3.)+60.)#8.(11.+<.))(?.$15.(1:.(19.(13.#3.)+70.)#8.(11.+17.))(?.$15.(1:.(19.(13.#3.)+78.)#8.(11.=))(?.$15.(1:.(19.(13.#3.)+80.)#8.(11.+19.))(?.$15.(1:.(19.(13.#3.)+88.)#8.(13.#4.))(?.$15.(1:.(19.(13.#3.)+90.)#8.(11.=))(?.$15.(1:.(19.(13.#3.)+98.)#8.(11.=))(14.$15.)))))))))))))))))))))))))")
(* [comment removed for export] *).
    (* [comment removed for export] *)

  Definition kn_image : list kentry := ltac2:(CDefT.buildp (gd_tbl_P_main_entry ()) "(?.$15.(18.(19.(11.=)+4<000.)+32000.)(?.$15.(1<.+10000.+4<?20.)(?.$15.(1<.+4<?21.+5<??8.)(?.$15.(1<.+7=0=0.+7=0?0.)(?.$15.(1:.(19.(11.=)+5=000.)#8.(11.+5=000.))(?.$15.(1:.(19.(11.=)+5=020.)#4.(13.#5.))(?.$15.(1<.+5=02<.+5=078.)(?.$15.(1<.+5=080.+5=098.)(?.$15.(1<.+5=0:0.+5=0;8.)(?.$15.(1:.(19.(11.=)+5=0;8.)#8.(13.#6.))(?.$15.(1<.+5=0<8.+5=0=8.)(?.$15.(1<.+5=0>0.+5=150.)(?.$15.(1<.+7=108.+7=330.)(?.$15.(1:.(19.(11.=)+7=330.)#8.(13.#6.))(?.$15.(1<.+7=338.+7=340.)(?.$15.(1<.+7=351.+7=358.)(?.$15.(1:.(19.(11.=)+7=358.)#8.(13.#3.))(?.$15.(1<.+7=360.+7=368.)(?.$15.(1<.+7=378.+7=380.)(?.$15.(1:.(19.(11.=)+7=380.)#8.(11.+1000.))(?.$15.(1<.+7=388.+7=3;8.)(?.$15.(1:.(19.(11.=)+7=3;8.)#8.(13.#7.))(?.$15.(1<.+7=3<0.+7>000.)(?.$15.(17.(13.#5.)+1.+3?????.)(?.$15.(1<.=+1000.)(14.$15.))))))))))))))))))))))))))")
(* [comment removed for export] *).

  (* [comment removed for export] *)
  Definition kn_main : list kentry := kn_stack ++ kn_auxv ++ kn_image.
End MainEntry.

Definition all_regs : list reg := ltac2:(CDefT.buildp (gd_tbl_P_main_entry ()) "(?.(0.&5.)(1=.&5.=$1>.)(?.(0.&5.)(1=.&5.+1.$1>.)(?.(0.&5.)(1=.&5.+2.$1>.)(?.(0.&5.)(1=.&5.+3.$1>.)(?.(0.&5.)(1=.&5.+4.$1>.)(?.(0.&5.)(1=.&5.+5.$1>.)(?.(0.&5.)(1=.&5.+6.$1>.)(?.(0.&5.)(1=.&5.+7.$1>.)(?.(0.&5.)(1=.&5.+8.$1>.)(?.(0.&5.)(1=.&5.+9.$1>.)(?.(0.&5.)(1=.&5.+:.$1>.)(?.(0.&5.)(1=.&5.+;.$1>.)(?.(0.&5.)(1=.&5.+<.$1>.)(?.(0.&5.)(1=.&5.+=.$1>.)(?.(0.&5.)(1=.&5.+>.$1>.)(?.(0.&5.)(1=.&5.+?.$1>.)(?.(0.&5.)(1=.&5.+10.$1>.)(?.(0.&5.)(1=.&5.+11.$1>.)(?.(0.&5.)(1=.&5.+12.$1>.)(?.(0.&5.)(1=.&5.+13.$1>.)(?.(0.&5.)(1=.&5.+14.$1>.)(?.(0.&5.)(1=.&5.+15.$1>.)(?.(0.&5.)(1=.&5.+16.$1>.)(?.(0.&5.)(1=.&5.+17.$1>.)(?.(0.&5.)(1=.&5.+18.$1>.)(?.(0.&5.)(1=.&5.+19.$1>.)(?.(0.&5.)(1=.&5.+1:.$1>.)(?.(0.&5.)(1=.&5.+1;.$1>.)(?.(0.&5.)(1=.&5.+1<.$1>.)(?.(0.&5.)(1=.&5.+1=.$1>.)(?.(0.&5.)(1=.&5.+1>.$1>.)(?.(0.&5.)(1=.&5.+1?.$1>.)(14.(0.&5.))))))))))))))))))))))))))))))))))")
(* [comment removed for export] *).

Local Ltac2 Set LiaOrc.tbl := fun () => "0010=L1649687558.2000006S1n2Hn". (* [comment removed for export] *)
Lemma nth_all_regs : forall n, (n < 32)%nat -> nth n all_regs 0%bv = Z_to_bv 5 (Z.of_nat n).
Proof.
  intros n Hn.
  destruct n as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|n]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]; [ .. | lia]; apply bv_eq; reflexivity.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Local Ltac2 Set LiaOrc.tbl := fun () => "0010=L8912114872.6000007S1r3Hr0". (* [comment removed for export] *)
Lemma regs_ok_by_index : ltac2:(CDefT.buildp (gd_tbl_P_main_entry ()) "PE,$1?.Psr,(1.$10.)PR,(20.&5.(0.&40.))P,Pi,$21.P,(22.R1.#20.)(7.(0.&40.)(23.R3.(24.(0.&5.)R2.$25.(1=.&5.=$1>.)))(26.R5.(24.$10.R2.R4.(11.=))))(27.R4.R3.R2.)")
(* [comment removed for export] *).
Proof.
  intros E sr R H r. unfold sr_get. destruct (bv_eqb r 0) eqn:Hr0.
  - assert (r = 0%bv) by (apply bv_eq; unfold bv_eqb in Hr0; lia). subst r. cbn [edenot].
    reflexivity.
  - pose proof (H (ridx r) (ridx_range r)) as Hx. rewrite nth_all_regs in Hx by apply ridx_range.
    rewrite ridx_roundtrip in Hx. exact Hx.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Section MainEntryProofs.
  Context {AMB : Amb}.
  Variable sp0 : word.
  Variables a0s path : list byte.
  Variable envv : list (list byte).
  Variable tid : word.
  Variable rd : EntryDraw.
  Variable regs : bvmap 5 word.
  Variable mem : word -> option byte.
  Let av := [a0s; path].
  Hypothesis Hva : valid_argv av.
  Hypothesis Hve : valid_envp envv.
  Hypothesis Hvsp : valid_sp sp0.
  Hypothesis Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z.
  Hypothesis ME : main_entry sp0 av envv tid rd regs mem.

  Let E := E0 sp0 a0s path envv tid rd regs.

      
  #[using="Type"] Lemma ev_vals : ltac2:(CDefT.buildp (gd_tbl_P_main_entry ()) "Pn,$21.(7.(0.&40.)(28.VE,R1.)(24.(0.&40.)R1.(29.(0.&40.)(?.(0.&40.)Vsp0,(?.(0.&40.)(2:.Vsp0,Va0s,Vpath,Venvv,)(?.(0.&40.)(2;.Vsp0,Va0s,Vpath,Venvv,)(?.(0.&40.)(2<.Vsp0,Va0s,Vpath,Venvv,)(?.(0.&40.)(2=.Vsp0,Va0s,Vpath,Venvv,)(?.(0.&40.)Vtid,(?.(0.&40.)(2>.Vrd,)(?.(0.&40.)(2?.VAMB,)(14.(0.&40.))))))))))(30.Vregs,))(=.&40.=)))")
(* [comment removed for export] *).
  Proof. intros n. reflexivity. Qed.

  #[using="Type"] Lemma junk_vals2_length : length (junk_vals2 regs) = 30%nat.
  Proof. unfold junk_vals2. rewrite length_map, length_seq. reflexivity. Qed.

  #[using="Type"] Lemma vals0_length : length (vals0 sp0 a0s path envv tid rd regs) = 38%nat.
  Proof. unfold vals0. rewrite length_app, junk_vals2_length. reflexivity. Qed.

  Local Ltac2 Set LiaOrc.tbl := fun () => "0030?L34802164351.18L60049107488.18L63213442206.1800000600<00BS1i2HiS1i2HiS1i2Hi". (* [comment removed for export] *)
  #[using="Type"] Lemma ev_junk : forall i, (2 <= i < 32)%nat -> ev E (6 + i) = getr regs (Z_to_bv 5 (Z.of_nat i)).
  Proof.
    intros i Hi. rewrite ev_vals.
    replace (6 + i)%nat with (length [sp0; p0 sp0 a0s path envv; p1 sp0 a0s path envv; auxvp sp0 a0s path envv; rnd sp0 a0s path envv; tid; canary_w rd; a_hwcap] + (i - 2))%nat by (cbn [length]; lia).
    rewrite app_nth2_plus. unfold junk_vals2. rewrite (nth_map_seq_gen (fun i => getr regs (Z_to_bv 5 (Z.of_nat i)))) by lia.
    f_equal. f_equal. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

    
  #[using="Type"] Lemma spx_val : forall k, edenot E (spx k) = Z_to_bv 64 (bv_unsigned sp0 + k).
  Proof. intros k. cbn [spx edenot]. rewrite alu_add. unfold v_add. change (ev E 0) with sp0.
    apply bv_eq. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod. rewrite Zplus_mod_idemp_r. reflexivity. Qed.

End MainEntryProofs.

Section MainRegs.
  Context {AMB : Amb}.
  Variable sp0 : word.
  Variables a0s path : list byte.
  Variable envv : list (list byte).
  Variable tid : word.
  Variable rd : EntryDraw.
  Variable regs : bvmap 5 word.
  Variable mem : word -> option byte.
  Let av := [a0s; path].
  Hypothesis Hva : valid_argv av.
  Hypothesis Hve : valid_envp envv.
  Hypothesis Hvsp : valid_sp sp0.
  Hypothesis Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z.
  Hypothesis ME : main_entry sp0 av envv tid rd regs mem.
  Let E := E0 sp0 a0s path envv tid rd regs.

  Ltac reg_case :=
    cbn [nth sr_main all_regs];
          first [ lazymatch goal with |- _ = edenot _ (spx ?k) => rewrite (spx_val sp0 a0s path envv tid rd regs k) end
                | lazymatch goal with |- _ = edenot _ (EVar ?n) =>
                    change (edenot E (EVar n)) with (ev E n);
                    first [ rewrite (ev_junk sp0 a0s path envv tid rd regs (n - 6)) by lia; reflexivity | idtac ]
                  | |- _ => cbn [edenot] end ];
          first [ reflexivity
                | exact (me_ra _ _ _ _ _ _ _ ME) | exact (me_gp _ _ _ _ _ _ _ ME) | exact (me_tp _ _ _ _ _ _ _ ME)
                | exact (me_s2 _ _ _ _ _ _ _ ME)
                | rewrite (me_sp _ _ _ _ _ _ _ ME); apply bv_eq; rewrite !u_small by lia; lia
                | rewrite (me_s0 _ _ _ _ _ _ _ ME); reflexivity
                | rewrite (me_a1 _ _ _ _ _ _ _ ME); reflexivity
                | rewrite (me_a2 _ _ _ _ _ _ _ ME); f_equal; subst av; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ Pos.mul Z.mul Pos.add]; lia
                | rewrite (me_s3 _ _ _ _ _ _ _ ME); f_equal; subst av; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ Pos.mul Z.mul Pos.add]; lia
                | rewrite (me_s1 _ _ _ _ _ _ _ ME); unfold argcN, len_word; reflexivity
                | rewrite (me_a0 _ _ _ _ _ _ _ ME); unfold argcN, len_word; reflexivity
                | apply (me_szero _ _ _ _ _ _ _ ME); cbn; tauto
                | idtac ].

  Local Ltac2 Set LiaOrc.tbl := fun () => "0060?L14793095917.19L23381421869.20L26359469379.19L35020285785.19L48837324397.18L55566975531.1900000@00M00Q00a00i011S3sp03Hlo3Hhi2HiS4regs1E1i2HiS2HiS3sp03Hlo3Hhi2HiS3sp02HiS3sp02Hi". (* [comment removed for export] *)
  #[using="mem av Hvsp Htid ME"] Theorem main_regs_ok : regs_ok E sr_main regs.
  Proof.
    pose proof (proj1 Hvsp) as Hlo. pose proof (proj1 (proj2 Hvsp)) as Hhi. unfold sp_window_lo, sp_window_hi in *.
    apply regs_ok_by_index.
    intros i Hi.
    destruct i as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|i]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]; [ .. | lia]; reg_case.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End MainRegs.

Section KnowProofs.
  Context {AMB : Amb}.
  Variable sp0 : word.
  Variables a0s path : list byte.
  Variable envv : list (list byte).
  Variable tid : word.
  Variable rd : EntryDraw.
  Variable regs : bvmap 5 word.
  Variable mem : word -> option byte.
  Let av := [a0s; path].
  Hypothesis Hva : valid_argv av.
  Hypothesis Hve : valid_envp envv.
  Hypothesis Hvsp : valid_sp sp0.
  Hypothesis Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z.
  Hypothesis ME : main_entry sp0 av envv tid rd regs mem.
  Let E := E0 sp0 a0s path envv tid rd regs.

  #[using="Hvsp"] Lemma kp_lo : (0x7fff80000000 <= bv_unsigned sp0)%Z. Proof. exact (proj1 Hvsp). Qed.
  #[using="Hvsp"] Lemma kp_hi : (bv_unsigned sp0 <= 0x800000000000)%Z. Proof. exact (proj1 (proj2 Hvsp)). Qed.
  #[using="Hvsp"] Lemma kp_al : (bv_unsigned sp0 mod 16 = 0)%Z. Proof. exact (proj2 (proj2 Hvsp)). Qed.
  #[using="Type"] Lemma ke0 : ev E 0 = sp0. Proof. reflexivity. Qed.
  #[using="Type"] Lemma ke1 : ev E 1 = p0 sp0 a0s path envv. Proof. reflexivity. Qed.
  #[using="Type"] Lemma ke2 : ev E 2 = p1 sp0 a0s path envv. Proof. reflexivity. Qed.
  #[using="Type"] Lemma ke3 : ev E 3 = auxvp sp0 a0s path envv. Proof. reflexivity. Qed.
  #[using="Type"] Lemma ke4 : ev E 4 = rnd sp0 a0s path envv. Proof. reflexivity. Qed.
  #[using="Type"] Lemma ke5 : ev E 5 = tid. Proof. reflexivity. Qed.
  #[using="Type"] Lemma ke6 : ev E 6 = canary_w rd. Proof. reflexivity. Qed.
  #[using="Type"] Lemma ke7 : ev E 7 = a_hwcap. Proof. reflexivity. Qed.

  Local Ltac2 Set LiaOrc.tbl := fun () => "00K0?L10820775366.19L11938902141.19L11941001443.20L14054083309.23L15526844254.19L21148992303.23L21821278179.19L22307106469.18L23146052690.19L25273903627.19L27271135070.19L27892021168.19L29784725349.19L3124517214.19 L33678089694.19L37987918546.19L43937998686.19L45219286238.19L4794965574.19 L5007054517.19 L52109955984.18L54919312656.19L565246302.19  L64205780885.23L65500324722.19L67487084742.19L8319121362.19 00000500>00G00^00k01701@01E01R01W01d02102:02G02P02]02j03303803E03J03O03X03d03i03n04;S3sp0S3sp03HhiS3sp03HhiS3sp03Hlo3Hhi1d1m2Hd2HmS3sp03Hlo3HhiS3sp01d1m2HmS3sp03HloS3sp0S3sp03Hlo3HhiS3sp0S3sp03Hlo3HhiS3sp03Hlo3HhiS3sp03HhiS3sp03Hlo3HhiS3sp03HhiS3sp03Hlo3HhiS3sp03Hlo3HhiS3sp03HhiS3sp0S3sp03Hlo3HhiS3sp0S3sp0S3sp03HhiS3sp01d1m2HdS3sp0S3sp0S3sp03Hlo3Hhi". (* [comment removed for export] *)
  #[using="av Hva Hve Hvsp ME"] Lemma know_stack : know_ok RSEGS E mem kn_stack.
  Proof.
    pose proof kp_lo as Hlo. pose proof kp_hi as Hhi. pose proof kp_al as Hal.
    unfold kn_stack, know_ok.
    repeat apply Forall_cons; try apply Forall_nil; cbn [kentry_ok a_base a_off edenot]; rewrite ?ke0, ?ke1, ?ke2;
      unfold flat, estart; cbn [a_base a_off edenot]; rewrite ?ke0.
    - split; [lia | exact Hal].
    - lia.
    - split; [lia|]. intros d m Hd Hm.
      apply (main_entry_store_ok_win sp0 av envv tid rd regs mem ME); rewrite u_small by lia; unfold stack_max_size; lia.
    - split; [lia|]. split; [lia|].
      unfold adenot. cbn [a_base a_off edenot]. rewrite ke0. unfold v_addi. rewrite Z.add_0_r, Z_to_bv_bv_unsigned.
      rewrite (main_entry_rdn_above sp0 av envv tid rd regs mem ME) by lia.
      pose proof (read_argc_w RSEGS RPH sp0 av envv a_uid a_hwcap rd Hva) as Hr. unfold wmem in Hr.
      rewrite (Hr Hve) by (unfold sp_window_hi; lia).
      rewrite n_to_le_8_spec. reflexivity.
    - split; [lia|]. split; [lia|].
      unfold adenot. cbn [a_base a_off edenot]. rewrite ke0. unfold v_addi.
      rewrite (main_entry_rdn_above sp0 av envv tid rd regs mem ME) by (rewrite u_small by lia; lia).
      pose proof (read_argv_ptr_w RSEGS RPH sp0 av envv a_uid a_hwcap rd Hva Hve ltac:(unfold sp_window_lo; lia) ltac:(unfold sp_window_hi; lia) 0%nat ltac:(subst av; cbn; lia)) as Hr.
      unfold wmem in Hr. rewrite w_add_nat in Hr. change (Z.of_nat (8 + 8 * 0)) with 8%Z in Hr.
      rewrite Hr. rewrite n_to_le_8_spec. reflexivity.
    - split; [lia|]. split; [lia|].
      unfold adenot. cbn [a_base a_off edenot]. rewrite ke0. unfold v_addi.
      rewrite (main_entry_rdn_above sp0 av envv tid rd regs mem ME) by (rewrite u_small by lia; lia).
      pose proof (read_argv_ptr_w RSEGS RPH sp0 av envv a_uid a_hwcap rd Hva Hve ltac:(unfold sp_window_lo; lia) ltac:(unfold sp_window_hi; lia) 1%nat ltac:(subst av; cbn; lia)) as Hr.
      unfold wmem in Hr. rewrite w_add_nat in Hr. change (Z.of_nat (8 + 8 * 1)) with 16%Z in Hr.
      rewrite Hr. rewrite n_to_le_8_spec. reflexivity.
    - split; [lia|]. split; [lia|].
      unfold adenot. cbn [a_base a_off edenot]. rewrite ke0. unfold v_addi.
      rewrite (main_entry_rdn_above sp0 av envv tid rd regs mem ME) by (rewrite u_small by lia; lia).
      pose proof (read_argv_null [] RPH sp0 rd av envv a_uid a_hwcap Hva Hve ltac:(unfold sp_window_hi; lia)) as Hr.
      rewrite w_add_nat in Hr. subst av. change (Z.of_nat (8 + 8 * length [a0s; path])) with 24%Z in Hr.
      apply (rdn_wmem_stack RSEGS RPH sp0 [a0s; path] envv a_uid a_hwcap rd) in Hr. (* [comment removed for export] *)
      unfold wmem in Hr. rewrite n_to_le_8_spec in Hr. exact Hr.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L8171826243.1500000:S3sp04envv". (* [comment removed for export] *)
  #[using="Type"] Lemma auxvp_eq : auxvp sp0 a0s path envv = Z_to_bv 64 (bv_unsigned sp0 + Z.of_nat (auxv_off av envv)).
  Proof. unfold auxvp, auxv_w, auxv_off. subst av. cbn [length]. f_equal. lia. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "0020?L67177967488.20L8929206910.20 00000J00iS3AMB3sp04envv2rd2av2Hb2HlS3AMB3sp04envv2rd2av1H2H02Hb2Hl". (* [comment removed for export] *)
  #[using="AMB rd Hva Hve Hvsp"] Lemma auxvp_u : ltac2:(CDefT.buildp (gd_tbl_P_main_entry ()) "(31.(7.$3.(6.&40.(2<.Vsp0,Va0s,Vpath,Venvv,))(32.(6.&40.Vsp0,)(33.(34.Vav,Venvv,))))(5.(32.(33.(34.Vav,Venvv,))+:0.)+222>00.))")
(* [comment removed for export] *).
  Proof.
    pose proof kp_lo. pose proof kp_hi.
    pose proof (auxv_off_bound RPH sp0 rd av envv a_uid a_hwcap) as Hb.
    pose proof (lay_bsb_len RPH sp0 rd av envv a_uid a_hwcap Hva Hve) as Hl.
    rewrite auxvp_eq. rewrite u_small by lia. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "0030?L11941001213.19L21819179107.19L7501436360.23 00000H00`01CS3AMB3sp04envv2rd2av3HHIS3AMB3sp04envv2rd2av3HLOS3AMB3sp03a0s4path4envv2rd3HLO2Hl1B". (* [comment removed for export] *)
  #[using="Hva Hve Hvsp"] Lemma rnd_u : ltac2:(CDefT.buildp (gd_tbl_P_main_entry ()) "(31.(5.(6.&40.Vsp0,)(6.&40.(2=.Vsp0,Va0s,Vpath,Venvv,)))(31.(5.(32.(6.&40.(2=.Vsp0,Va0s,Vpath,Venvv,))+10.)(32.(6.&40.Vsp0,)+222>00.))(31.(7.$3.(35.(6.&40.(2=.Vsp0,Va0s,Vpath,Venvv,))+8.)=)Pj,$21.Pn,$21.P,(36.(37.R2.R1.)#10.)(7.(;.(1.(0.&8.)))(38.(14.$39.)(3:.Vsp0,(3;.$3<.Vsp0,Vav,Venvv,(3=.VAMB,)(2?.VAMB,)Vrd,))(=.&40.(32.(6.&40.(2=.Vsp0,Va0s,Vpath,Venvv,))(33.R3.)))R2.)(3>.(1.(0.&8.))(3?.(0.&8.)R2.(40.(0.&8.)R3.(41.Vrd,))))))))")
(* [comment removed for export] *).
  Proof.
    pose proof kp_lo as HLO. pose proof kp_hi as HHI.
    pose proof (lay_bsb_len RPH sp0 rd av envv a_uid a_hwcap Hva Hve) as Hl.
    ddestruct (rnd_facts [] RPH sp0 rd av envv a_uid a_hwcap Hva Hve ltac:(unfold sp_window_lo; lia) ltac:(unfold sp_window_hi; lia) kp_al)
      as (A & B & C & D & F).
    unfold rnd, rnd_bytes. subst av. repeat split; try assumption; try lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0040?L2124253248.22 L43938000774.22L45219283974.22L54463725982.2300000G00j01E01XS3sp03a0s4path4envv3Hr1S3sp03a0s4path4envv3HLO3HHI3Hr13Hr2S3sp03a0s4path4envv3HHI3Hr2S3sp03a0s4path4envv". (* [comment removed for export] *)
  #[using="AMB tid regs av Hva Hve Hvsp ME"] Lemma main_entry_secret : ltac2:(CDefT.buildp (gd_tbl_P_main_entry ()) "(7.(;.(1.(0.&8.)))(38.$42.Vmem,(=.&40.(32.(6.&40.(2=.Vsp0,Va0s,Vpath,Venvv,))+8.))#8.)(3>.(1.(0.&8.))(43.#8.(44.Vrd,))))")
(* [comment removed for export] *).
  Proof.
    pose proof kp_lo as HLO. pose proof kp_hi as HHI. ddestruct rnd_u as (Hr1 & Hr2 & Hr3 & Hr4).
    rewrite (main_entry_rdn_above sp0 av envv tid rd regs mem ME) by (rewrite u_small by lia; lia).
    pose proof (rdn_wmem_stack RSEGS RPH sp0 av envv a_uid a_hwcap rd) as Hw. unfold wmem in Hw. apply Hw.
    rewrite secret_store. unfold secret_bytes. change 8%Z with (Z.of_nat 8) at 1. apply (Hr4 8%nat 8%nat). lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "0050?L11941002600.23L13247467432.23L16626617217.22L49704876920.22L8929207664.22 00000F00d01B01g02PS3sp04envv2av1j2Hj3HHIS3sp03a0s4path4envv2av1j2Hj2HuS3sp03a0s4path4envv2av1j2Hj2HuS3sp03a0s4path4envv2av1j2Hj3HHI2Hu2HbS3sp03a0s4path4envv2av1j2Hj3HLO3HHI2Hu2Hb". (* [comment removed for export] *)
  #[using="tid rd regs av Hva Hve Hvsp ME"] Lemma auxv_word_at : ltac2:(CDefT.buildp (gd_tbl_P_main_entry ()) "Pj,$21.P,(22.R1.#14.)(7.(;.(1.(0.&8.)))(38.$42.Vmem,(=.&40.(32.(6.&40.(2<.Vsp0,Va0s,Vpath,Venvv,))(45.+8.(33.R2.))))#8.)(3>.(1.(0.&8.))(43.#8.(24.(0.&40.)R2.(46.$3<.(2=.Vsp0,Va0s,Vpath,Venvv,)(3=.VAMB,)(2?.VAMB,))(=.&40.=)))))")
(* [comment removed for export] *).
  Proof.
    intros j Hj. pose proof kp_lo as HLO. pose proof kp_hi as HHI.
    destruct auxvp_u as [Hu Hb].
    rewrite (main_entry_rdn_above sp0 av envv tid rd regs mem ME) by (rewrite u_small by lia; lia).
    pose proof (rdn_wmem_stack RSEGS RPH sp0 av envv a_uid a_hwcap rd) as Hw. unfold wmem in Hw.
    apply Hw. (* [comment removed for export] *)
    replace (Z_to_bv 64 (bv_unsigned (auxvp sp0 a0s path envv) + 8 * Z.of_nat j))
      with (sp0 + nat_to_word (auxv_off av envv + 8 * j)) by (rewrite w_add_nat; f_equal; lia).
    rewrite (read_auxv_word [] RPH sp0 rd av envv a_uid a_hwcap Hva Hve ltac:(unfold sp_window_hi; lia) j Hj).
    rewrite n_to_le_8_spec. unfold rnd. reflexivity.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Ltac kw_auxv j :=
    split; [lia|]; split; [lia|];
    unfold adenot; cbn [a_base a_off edenot]; rewrite ke3; unfold v_addi;
    lazymatch goal with |- rdn _ _ (Z_to_bv 64 (?u + ?k)) 8 = _ =>
      replace k with (8 * Z.of_nat j)%Z by reflexivity end;
    rewrite (auxv_word_at j) by lia; unfold auxv_words; cbn [nth]; try reflexivity.

  Local Ltac2 Set LiaOrc.tbl := fun () => "00P0?L11800015230.25L13781474954.25L15200873443.25L19185762953.25L23146050698.25L24102061194.25L24692314506.25L24892955888.25L25273901779.25L25378044438.26L26641192841.25L27271133062.25L28608664586.25L30224812301.25L34071574410.25L37987920394.25L38869727075.25L39519508234.25L43452894602.25L4402247818.25 L44771709187.25L485605898.25  L52815373194.25L54363212938.25L54438951020.25L58277987082.25L63370421802.25L63742468746.25L64160617967.25L67659340042.25L8319123210.25 L9850181642.25 00000F00l00m01G01m02O03503K03a04A04W05=05c06906_07E07k08Q09709]0:C0:i0;O0<50<K0=10=G0=m0>C0>i0?O0@5S3sp03a0s4path4envv2avS3sp03a0s4path4envv2av3Hlo3Hhi3Hab3Hr1FS3sp03a0s4path4envv2av3Hr1S3sp03a0s4path4envv2av3Hlo3Hhi3Hab3Hr1S3sp03a0s4path4envv2av3Hlo3Hr13Hr3S3sp03a0s4path4envv2av3Hlo3Hhi3Hab3Hr1S3sp03a0s4path4envv2avS3sp03a0s4path4envv2avS3sp03a0s4path4envv3Hlo3Hr11q2HqS3sp03a0s4path4envv2avS3sp03a0s4path4envv2av3Hlo3Hhi3Hab3Hr1S3sp03a0s4path4envv2av3Hlo3Hhi3Hab3Hr1S3sp03a0s4path4envv2avS3sp03a0s4path4envv2av3Hlo3Hhi3Hab3Hr1S3sp03a0s4path4envv2av3Hlo3Hhi3Hab3Hr1S3sp03a0s4path4envv2av3Hlo3Hhi3Hab3Hr1S3sp03a0s4path4envv2av3Hlo3Hhi3Hab3Hr1S3sp03a0s4path4envv2av3Hlo3Hhi3Hab3Hr1S3sp03a0s4path4envv2av3Hlo3Hhi3Hab3Hr1S3sp03a0s4path4envv2av3Hlo3Hhi3Hr13Hr2S3sp03a0s4path4envv2av3Hlo3Hhi3Hab3Hr1S3sp03a0s4path4envv2av3Hlo3Hhi3Hab3Hr1S3sp03a0s4path4envv2av3Hlo3Hhi3Hab3Hr1S3sp03a0s4path4envv2avS3sp03a0s4path4envv2av3Hlo3Hhi3Hab3Hr1S3sp03a0s4path4envv2avS3sp03a0s4path4envv2av3Hlo3Hhi3Hab3Hr1S3sp03a0s4path4envv2avS3sp03a0s4path4envv2av3Hlo3Hhi3Hab3Hr1S3sp03a0s4path4envv2av3Hlo3Hhi3Hab3Hr1S3sp03a0s4path4envv2av3Hlo3Hhi3Hab3Hr1". (* [comment removed for export] *)
  #[using="av Hva Hve Hvsp ME"] Lemma know_auxv : know_ok RSEGS E mem kn_auxv.
  Proof.
    pose proof kp_lo as Hlo. pose proof kp_hi as Hhi. pose proof kp_al as Hal.
    destruct auxvp_u as [Hau Hab]. ddestruct rnd_u as (Hr1 & Hr2 & Hr3 & Hr4).
    unfold kn_auxv, know_ok.
    repeat apply Forall_cons; try apply Forall_nil; cbn [kentry_ok a_base a_off edenot];
      rewrite ?ke0, ?ke3, ?ke4, ?ke7; unfold flat, estart, elenZ; cbn [a_base a_off edenot]; rewrite ?ke0, ?ke3, ?ke4, ?ke7;
      try rewrite Hau; try lia.
    - (* [comment removed for export] *) split; [lia|].
      destruct (proj1 (Z.mod_divide (bv_unsigned sp0) 16 ltac:(lia)) Hal) as [q Hq].
      replace (bv_unsigned sp0 + Z.of_nat (auxv_off av envv))%Z with ((2 * q + 5 + Z.of_nat (length envv)) * 8)%Z
        by (unfold auxv_off; subst av; cbn [length]; lia).
      apply Z_mod_mult.
    - kw_auxv 0%nat. - kw_auxv 1%nat. - kw_auxv 2%nat. - kw_auxv 3%nat. - kw_auxv 4%nat. - kw_auxv 5%nat.
    - kw_auxv 6%nat. - kw_auxv 7%nat. - kw_auxv 8%nat. - kw_auxv 9%nat. - kw_auxv 10%nat.
    - kw_auxv 12%nat. - kw_auxv 14%nat. - kw_auxv 15%nat. - kw_auxv 16%nat. - kw_auxv 17%nat.
    - kw_auxv 18%nat. - kw_auxv 19%nat.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0050?L12629059976.20L29588573869.20L3980174806.20 L40359575923.20L43855241437.20000001002003004005FSSSS". (* [comment removed for export] *)
  #[using="Hvsp"] Lemma D_main_auxvp : ltac2:(CDefT.buildp (gd_tbl_P_main_entry ()) "Psegs,(1.$39.)(7.(;.(1.(0.&8.)))(38.R1.(<.Vsp0,Vav,Venvv,(2?.VAMB,)Vrd,Vtid,)(=.&40.+7=358.)#8.)(3>.(1.(0.&8.))(43.#8.(2<.Vsp0,Va0s,Vpath,Venvv,))))")
(* [comment removed for export] *).
  Proof.
    intros segs. pose proof (u64_range tid). pose proof kp_lo. pose proof kp_hi.
    unfold auxvp, D_main, D_fd, D_ssp, D_tls, D_tlsB, D_tlsA, D_libc. peel.
    apply rdn_wbytes_hit8. unorm; lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)

  #[using="Type"] Lemma wseg_data : wseg_ok RSEGS (Z_to_bv 64 0x4c000) 0x32000 = true.
  Proof. vm_compute. reflexivity. Qed.

  Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L68474595396.2400000FS2lo1n1c1w1i1H3Hlo3Hhi". (* [comment removed for export] *)
  #[using="Type"] Lemma range_disjoint_sub : ltac2:(CDefT.buildp (gd_tbl_P_main_entry ()) "Plo,$3.Pn,$21.Pc,(47.$3.$21.)Pi,$3.P,(7.$8.(48.R4.R3.R2.)$:.)P,(5.R5.R2.)P,(5.(32.R3.+1.)(32.R6.(33.R5.)))(7.$8.(48.R4.#1.R5.)$:.)")
(* [comment removed for export] *).
  Proof.
    intros lo n [c w] i H Hlo Hhi. unfold range_disjoint_b in *. cbn [fst snd] in *.
    apply orb_true_iff in H. apply orb_true_iff. rewrite !Z.leb_le in *. cbn [Z.of_nat Pos.of_succ_nat]. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "0040?L10353693098.24L23830564072.24L32278067313.26L42007348611.2600000?00N00Z00fS2lo1n1i2H23HloS2lo1n1i2H33HhiS2lo1n1i3HhiS2lo1n1i3Hlo". (* [comment removed for export] *)
  #[using="Type"] Lemma missb_sub : ltac2:(CDefT.buildp (gd_tbl_P_main_entry ()) "Plo,$3.Pn,$21.Pi,$3.P,(7.$8.(9.R3.R2.)$:.)P,(5.R4.R2.)P,(5.(32.R3.+1.)(32.R5.(33.R4.)))(7.$8.(9.R4.#1.)$:.)")
(* [comment removed for export] *).
  Proof.
    intros lo n i H Hlo Hhi. unfold D_main_missb in *.
    apply andb_true_iff in H as [H H3]. apply andb_true_iff in H as [H1 H2].
    apply Z.leb_le in H2. apply Z.leb_le in H3.
    apply andb_true_iff; split; [apply andb_true_iff; split|]; [| apply Z.leb_le; lia | apply Z.leb_le; cbn [Z.of_nat Pos.of_succ_nat]; lia].
    apply forallb_forall. intros c Hc. apply (range_disjoint_sub lo n); [|lia|lia].
    apply (proj1 (forallb_forall _ _) H1). exact Hc.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0090?L11941000314.26L17749049106.26L18914900186.26L21819180004.26L29443145835.24L42007347853.26L52371396776.24L66253720165.26L8785596558.26 00000900Q00]00f00o01;01C01X01cS3sp03HHIS3sp02lo2hi3Hhi3HLO1i2HiS2lo2hi1i2HiS3sp03HLOS2lo4Hlo0S2lo2hi1i2HiS2hi3HhiS2lo2hi3Hhi4Hlo01i2HiS2lo2hi3Hle". (* [comment removed for export] *)
  #[using="av Hva Hvsp ME"] Lemma kimg_ok : ltac2:(CDefT.buildp (gd_tbl_P_main_entry ()) "Plo,$3.Phi,$3.P,(7.$8.(9.R2.(49.(4:.R1.R2.)))$:.)P,(5.R3.R2.)P,(5.R3.+7>000.)(4;.$42.VE,Vmem,(1<.R5.R4.))")
(* [comment removed for export] *).
  Proof.
    intros lo hi Hb Hle Hhi. pose proof kp_lo as HLO. pose proof kp_hi as HHI.
    assert (Hlo0 : (0 <= lo)%Z).
    { unfold D_main_missb in Hb. apply andb_true_iff in Hb as [Hb _]. apply andb_true_iff in Hb as [_ Hb].
      apply Z.leb_le in Hb. exact Hb. }
    cbn [kentry_ok]. split; [lia|]. split; [lia|]. intros i Hi.
    rewrite (main_entry_mem_data sp0 av envv tid rd regs mem ME) by (rewrite u_small by lia; unfold stack_max_size; lia).
    apply (D_main_none sp0 av envv a_hwcap rd tid i Hva); [lia | lia |].
    apply (missb_sub lo (Z.to_nat (hi - lo))); [exact Hb | lia | rewrite Z2Nat.id by lia; lia].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Ltac kimg := apply kimg_ok; [vm_compute; reflexivity | lia | lia].

  Ltac kw_pre :=
    split; [lia|]; split; [lia|];
    unfold adenot; cbn [a_base a_off edenot]; unfold v_addi; rewrite u_small by lia; rewrite Z.add_0_l.
  Ltac kw_data L :=
    kw_pre;
    rewrite (main_entry_rdn_data sp0 av envv tid rd regs mem ME) by (rewrite u_small by lia; unfold stack_max_size; lia);
    rewrite (L RSEGS); try reflexivity.
  Ltac kw_mem L := kw_pre; rewrite (L RSEGS); try reflexivity.

  Local Ltac2 Set LiaOrc.tbl := fun () => "00c0?L1000284608.19 L10724054094.19L1083249694.19 L13485667150.19L14291479502.19L14424637262.19L16697688782.19L18501395702.19L18833241560.19L18928853482.19L20435208654.19L21823471390.19L2457917272.19 L25271804307.19L25654141262.19L27118011854.19L28043817678.19L29290475342.19L30283716302.19L31262883904.19L31289823704.19L32155950670.19L32538124622.19L35860693326.19L37859791438.19L39505559628.23L41011215822.19L43056431448.19L44593532046.19L49858991606.19L51852962894.19L52094160630.19L52723532366.19L53519161302.19L56415728974.19L57220884790.23L58884595790.19L59429660632.19L60705177601.23L60844916302.19L61604292160.19L63448934734.19L63691814390.19L64514089525.19L65070153166.19L65499172032.19L67436825038.19L67969894744.19L68075130122.23L68458866126.19L7927117016.19 00000900:00;00<00=00>00?00@00A00B00C00D00E00F00G00H00I00J00K00T00U00V00W00X00Y00a00b00c00d00e00f00g00h00i00j01201301401?01@01I01J01K01U01V01_01`01a01d01e01fS3sp03HloSSSSSSSSSSSSSSSSSSS3sp03HloSSSSSS1d1m2HmSSSSSSSSSS1d1m2HdSSS1d1m2Hd2HmSS3sp03HloSSS3tid4HtidSS3sp03HloSSS1mSS". (* [comment removed for export] *)
  #[using="av Hva Hvsp Htid ME"] Lemma know_image : know_ok RSEGS E mem kn_image.
  Proof.
    pose proof kp_lo as Hlo. pose proof kp_hi as Hhi. pose proof (u64_range tid) as Ht.
    unfold kn_image, know_ok.
    repeat apply Forall_cons; try apply Forall_nil;
      try kimg;
      cbn [kentry_ok a_base a_off edenot]; rewrite ?ke3, ?ke5, ?ke6, ?ke7; unfold flat, estart, elenZ; cbn [a_base a_off edenot];
      rewrite ?(u_small 0) by lia; cbn [Z.add].
    - (* [comment removed for export] *) split; [lia|]. intros d m Hd Hm.
      eapply (store_ok_window RSEGS mem (Z_to_bv 64 0x4c000) (Z_to_bv 64 (0x4c000 + d)) 0x32000 m 0x4c000 0x7e000);
        [reflexivity | reflexivity | cbn; lia | apply wseg_data | rewrite u_small by lia; lia | rewrite u_small by lia; lia].
    - kw_data (D_main_self sp0 av envv tid rd).
    - kw_mem (main_entry_tid sp0 av envv tid rd Hlo regs mem ME).
    - kw_data (D_main_canary sp0 av envv tid rd).
    - kw_mem (main_entry_guard sp0 av envv tid rd Hlo regs mem ME). rewrite canary_store. reflexivity.
    - kw_data D_main_auxvp.
    - kw_data (D_main_pagesize sp0 av envv tid rd Hva).
    - kw_data (D_main_hwcap sp0 av envv tid rd Hva).
    - (* [comment removed for export] *) lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)


  #[using="av Hva Hve Hvsp Htid ME"] Theorem main_know_ok : know_ok RSEGS E mem kn_main.
  Proof.
    unfold kn_main, know_ok.
    apply Forall_app; split; [apply know_stack|].
    apply Forall_app; split; [apply know_auxv | apply know_image].
  Qed.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0080?L11938903546.20L11938903864.22L11941157027.24L21819092797.24L29676460282.28L30216703632.28L55805207106.28L57518446966.2000000>00_01@01a02K03503\04;S3sp01k2Hk3HhiS3AMB3sp04envv2rd2av1k2Hk3Hhi3Hk'S3AMB3sp04envv2rd2av1k2Hk3Hhi3Hk'S3AMB3sp04envv2rd2av1k2Hk3Hlo3Hk'S3AMB3sp04envv2rd2av1k2Hk3Hk'2B22Hu3Hsb2HfS3AMB3sp04envv2rd2av1k2Hk3Hk'2B12Hu3Hsb2HfS3AMB3sp04envv2rd2av1k2Hk3Hk'2Hu3Hsb2HfS3AMB3sp03a0s4path4envv2rd1k2Hk". (* [comment removed for export] *)
  #[using="AMB tid rd regs Hva Hve Hvsp ME"] Lemma main_str : ltac2:(CDefT.buildp (gd_tbl_P_main_entry ()) "Pk,$21.P,(22.R1.#2.)(31.(7.(;.(1.(0.&8.)))(38.$42.Vmem,(4<.Vsp0,Vav,Venvv,R2.)(37.(4=.(0.&8.)(24.(1.(0.&8.))R2.Vav,(14.(0.&8.))))#1.))(3>.(1.(0.&8.))(29.(0.&8.)(24.(1.(0.&8.))R2.Vav,(14.(0.&8.)))(?.(0.&8.)(=.&8.=)(14.(0.&8.))))))(31.(5.(6.&40.Vsp0,)(6.&40.(4<.Vsp0,Vav,Venvv,R2.)))(31.(5.(6.&40.(4<.Vsp0,Vav,Venvv,R2.))(32.(6.&40.Vsp0,)+2028;8.))(5.(33.(4=.(0.&8.)(24.(1.(0.&8.))R2.Vav,(14.(0.&8.)))))+1????.))))")
(* [comment removed for export] *).
  Proof.
    intros k Hk. pose proof kp_lo as Hlo. pose proof kp_hi as Hhi.
    pose proof (lay_bsb_nw RPH sp0 rd av envv a_uid a_hwcap Hva Hve ltac:(unfold sp_window_hi; lia)) as Hnw.
    assert (Hk' : (k < length av)%nat) by (subst av; cbn; lia).
    destruct (argv_ptr_bounds_at sp0 av envv Hva Hve ltac:(unfold sp_window_hi; lia) k Hk') as [B1 B2].
    pose proof (u_cat_argv_ptr sp0 av envv Hva Hve ltac:(unfold sp_window_lo; lia) ltac:(unfold sp_window_hi; lia) k Hk') as Hu.
    pose proof (struct_av_bound av envv Hva Hve) as Hsb.
    pose proof (total_arg_bytes_firstn_le k av) as Hf.
    pose proof (argv_str_len av Hva k Hk') as Hlen.
    repeat split.
    - rewrite (main_entry_rdn_above sp0 av envv tid rd regs mem ME) by lia.
      pose proof (rdn_wmem_stack RSEGS RPH sp0 av envv a_uid a_hwcap rd) as Hw. unfold wmem in Hw. apply Hw. (* [comment removed for export] *)
      apply read_argv_cstr_k; [exact Hk' | exact Hnw].
    - exact B1.
    - lia.
    - exact Hlen.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0040?L11940998021.22L21819186203.22L57518447204.19L6412697092.28 00000Q01201801lS3AMB3sp04envv2rd2av1k2Hk3Hhi3Hk'S3AMB3sp04envv2rd2av1k2Hk3Hlo3Hk'S1k2HkS3AMB3sp04envv2rd2av1k2Hk3Hk'2HT2Hu3pre4post4Hpre2HL". (* [comment removed for export] *)
  #[using="AMB tid rd regs mem Hva Hve Hvsp ME"] Lemma main_str_top : ltac2:(CDefT.buildp (gd_tbl_P_main_entry ()) "Pk,$21.P,(22.R1.#2.)(5.(32.(32.(6.&40.(4<.Vsp0,Vav,Venvv,R2.))(33.(4=.(0.&8.)(24.(1.(0.&8.))R2.Vav,(14.(0.&8.))))))+1.)+800000000000.)")
(* [comment removed for export] *).
  Proof.
    intros k Hk. pose proof kp_lo as Hlo. pose proof kp_hi as Hhi.
    assert (Hk' : (k < length av)%nat) by (subst av; cbn; lia).
    pose proof (main_entry_block_top sp0 av envv tid rd regs mem ME) as HT. unfold sp_window_hi in HT.
    pose proof (u_cat_argv_ptr sp0 av envv Hva Hve ltac:(unfold sp_window_lo; lia) ltac:(unfold sp_window_hi; lia) k Hk') as Hu.
    ddestruct (bsb_byte_k RPH sp0 av envv k a_uid a_hwcap rd Hk') as (pre & post & EB & Hpre).
    pose proof (f_equal (@length byte) EB) as HL. rewrite !length_app in HL. cbn [length] in HL.
    rewrite Hu, <- Hpre. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End KnowProofs.
