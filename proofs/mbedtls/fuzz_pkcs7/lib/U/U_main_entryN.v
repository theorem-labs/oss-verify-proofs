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
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BB Require Import Amb CatExec CatSim SeqExec StoreOk FileSim ArgvEnv MuslStrlen SymExec SymExec2 SymExec2Sound SymRun SymDrive MemSplit Layout StartupTac SymDriveX.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import U_startup_defs U_startup U_startup_facts U_main_entry.
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
Ltac2 gd_tbl_P_main_entryN () : Init.string Init.list := ["Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.expr"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.ELit"; "RocqVerifyHarness.AgentSubmission.U.U_main_entry.spx"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.EVar"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.kentry"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.KAlign"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.KRange"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.KWr"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.SA"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.KWord"; "Corelib.Init.Datatypes.nat"; "Corelib.Init.Peano.lt"; "Corelib.Init.Datatypes.length"; "Corelib.Init.Datatypes.list"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "Corelib.Init.Datatypes.option"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.rdn"; "RocqVerifyHarness.ProcessOversight.Tgt_fuzz_pkcs7_ubsan.M.loaded_segments"; "RocqVerifyHarness.AgentSubmission.BB.CatExec.cat_argv_ptr"; "Corelib.Init.Nat.add"; "Corelib.Lists.ListDef.nth"; "Corelib.Init.Datatypes.Some"; "Corelib.Init.Datatypes.app"; "stdpp.bitvector.definitions.Z_to_bv"; "Stdlib.ZArith.BinInt.Z.le"; "stdpp.bitvector.definitions.bv_unsigned"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Logic.ex"; "LinuxProcessSemantics.LinuxProcessSem.MemImageType.Segment"; "RocqVerifyHarness.AgentSubmission.U.U_startup_defs.D_main"; "RocqVerifyHarness.AgentSubmission.BB.Amb.a_hwcap"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.word_to_le_bytes"; "MainEntryN.auxvpN"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.bool"; "RocqVerifyHarness.AgentSubmission.U.U_startup_facts.range_disjoint_b"; "Corelib.Init.Datatypes.true"; "RocqVerifyHarness.AgentSubmission.U.U_startup_facts.D_main_missb"; "Stdlib.ZArith.BinInt.Z.to_nat"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2Sound.SX2S.kentry_ok"; "MainEntryN.EN"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.KImg"].


Section MainEntryN.
  Context {AMB : Amb}.
  Variable sp0 : word.
  Variables av envv : list (list byte).
  Variable tid : word.
  Variable rd : EntryDraw.
  Variable regs : bvmap 5 word.
  Variable mem : word -> option byte.
  Hypothesis Hva : valid_argv av.
  Hypothesis Hve : valid_envp envv.
  Hypothesis Hvsp : valid_sp sp0.
  Hypothesis Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z.
  Hypothesis ME : main_entry sp0 av envv tid rd regs mem.

  Definition p0N : word := cat_argv_ptr sp0 av envv 0.
  Definition auxvpN : word := auxv_w sp0 av envv.
  Definition rndN : word := at_random_ptr sp0 av envv.

  Definition valsN : list word := [sp0; p0N; p0N; auxvpN; rndN; tid; canary_w rd; a_hwcap] ++ junk_vals2 regs.
  Definition EN : env := Env (vals_ev valsN) (blobs_ev []).

  Definition sr_mainN : list expr := ltac2:(CDefT.buildp (gd_tbl_P_main_entryN ()) "(0.$1.(2.=)(0.$1.(2.+3?2:8.)(0.$1.(3.-30.)(0.$1.(2.+10800.)(0.$1.(2.+5=0<8.)(0.$1.(4.#;.)(0.$1.(4.#<.)(0.$1.(4.#=.)(0.$1.(3.+8.)(0.$1.(4.#?.)(0.$1.(4.#10.)(0.$1.(3.+8.)(0.$1.(4.#12.)(0.$1.(4.#13.)(0.$1.(4.#14.)(0.$1.(4.#15.)(0.$1.(4.#16.)(0.$1.(4.#17.)(0.$1.(2.+1=24<.)(0.$1.(4.#19.)(0.$1.(2.=)(0.$1.(2.=)(0.$1.(2.=)(0.$1.(2.=)(0.$1.(2.=)(0.$1.(2.=)(0.$1.(2.=)(0.$1.(2.=)(0.$1.(4.#22.)(0.$1.(4.#23.)(0.$1.(4.#24.)(0.$1.(4.#25.)(5.$1.)))))))))))))))))))))))))))))))))")
(* [comment removed for export] *).

  Definition kn_stackN : list kentry := ltac2:(CDefT.buildp (gd_tbl_P_main_entryN ()) "(0.$6.(7.(4.#0.)+10.)(0.$6.(8.(4.#0.)+7???80000000.+800000000000.)(0.$6.(9.(:.(4.#0.)-800000.)+800000.)(0.$6.(;.(:.(4.#0.)+8.)#8.(4.#1.))(0.$6.(8.(4.#1.)+7???80000000.+800000400000.)(5.$6.))))))")
(* [comment removed for export] *).

  Definition kn_mainN : list kentry := kn_stackN ++ kn_image.

  Let Hlo : (0x7fff80000000 <= bv_unsigned sp0)%Z := proj1 Hvsp.
  Let Hhi : (bv_unsigned sp0 <= 0x800000000000)%Z := proj1 (proj2 Hvsp).
  Let Hal : (bv_unsigned sp0 mod 16 = 0)%Z := proj2 (proj2 Hvsp).

  Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L59328887778.1800000>S3sp02av2H12H2". (* [comment removed for export] *)
  #[using="sp0 Hva"] Lemma len_avN : (1 <= length av <= 1024)%nat.
  Proof. destruct Hva as [[H1 H2] _]. lia. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "0030?L34802164351.18L60049107488.18L63213442206.1800000>00L00ZS3sp03Hlo1i2HiS3sp03Hlo1i2HiS3sp03Hlo1i2Hi". (* [comment removed for export] *)
  #[using="Hvsp Hlo"] Lemma evN_junk : forall i, (2 <= i < 32)%nat -> ev EN (6 + i) = getr regs (Z_to_bv 5 (Z.of_nat i)).
  Proof.
    intros i Hi. unfold EN. cbn [ev]. unfold valsN.
    replace (6 + i)%nat with (length [sp0; p0N; p0N; auxvpN; rndN; tid; canary_w rd; a_hwcap] + (i - 2))%nat by (cbn [length]; lia).
    unfold vals_ev. rewrite app_nth2_plus. unfold junk_vals2.
    rewrite (nth_map_seq_gen (fun i => getr regs (Z_to_bv 5 (Z.of_nat i)))) by lia. f_equal. f_equal. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  #[using="Type"] Lemma spxN_val : forall k, edenot EN (spx k) = Z_to_bv 64 (bv_unsigned sp0 + k).
  Proof. intros k. cbn [spx edenot]. rewrite alu_add. unfold v_add. change (ev EN 0) with sp0.
    apply bv_eq. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod. rewrite Zplus_mod_idemp_r. reflexivity. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Ltac reg_caseN :=
    cbn [nth sr_mainN all_regs];
    first [ rewrite spxN_val
          | lazymatch goal with |- _ = edenot _ (EVar ?n) =>
              change (edenot EN (EVar n)) with (ev EN n);
              first [ rewrite (evN_junk (n - 6)) by lia; reflexivity | idtac ]
            | |- _ => cbn [edenot] end ];
    first [ reflexivity
          | exact (me_ra _ _ _ _ _ _ _ ME) | exact (me_gp _ _ _ _ _ _ _ ME) | exact (me_tp _ _ _ _ _ _ _ ME)
          | exact (me_s2 _ _ _ _ _ _ _ ME)
          | rewrite (me_sp _ _ _ _ _ _ _ ME); apply bv_eq; rewrite !u_small by lia; lia
          | rewrite (me_s0 _ _ _ _ _ _ _ ME); reflexivity
          | rewrite (me_a1 _ _ _ _ _ _ _ ME); reflexivity
          | apply (me_szero _ _ _ _ _ _ _ ME); cbn; tauto
          | idtac ].

  Local Ltac2 Set LiaOrc.tbl := fun () => "0040?L14793095917.19L35020285785.19L55566975531.19L62272581616.2000000@00P00X00gS3sp03Hlo3Hhi2HiS3sp03Hlo3Hhi2HiS3sp02HiS3sp04regs1i2Hi". (* [comment removed for export] *)
  #[using="mem Hvsp Htid ME Hlo Hhi"] Theorem main_regs_okN : regs_ok EN sr_mainN regs.
  Proof.
    pose proof Hlo. pose proof Hhi.
    apply regs_ok_by_index.
    intros i Hi.
    destruct i as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|i]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]; [ .. | lia]; reg_caseN.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "00;0?L11938903784.21L11940993441.20L11941157027.23L21819092797.23L28898766558.31L29663877101.28L30229283207.28L49702777634.31L52039821598.28L55817792853.28L8927112490.31 00000N00`01>01\02N03503\04S05705_06SS3AMB3sp02av4envv2rd3Hhi1k3Hk'S3sp02av3Hhi1k3Hk'S3AMB3sp02av4envv2rd3Hhi1k3Hk'S3AMB3sp02av4envv2rd3Hlo1k3Hk'S3AMB3sp02av4envv2rd3Hlo1k3Hk'2B12Hu3Hsb2Hf2t83Hl8S3AMB3sp02av4envv2rd1k3Hk'2B22Hu3Hsb2HfS3AMB3sp02av4envv2rd1k3Hk'2B12Hu3Hsb2HfS3AMB3sp02av4envv2rd3Hlo1k3Hk'2H02Hu3Hsb2Hf4Hlen2t83Hl8S3AMB3sp02av4envv2rd1k3Hk'2Hu3Hsb2HfS3AMB3sp02av4envv2rd3Hlo1k3Hk'2Hu3Hsb2HfS3AMB3sp02av4envv2rd3Hlo1k3Hk'1H2B22Hu3Hsb2Hf2t83Hl8". (* [comment removed for export] *)
  #[using="AMB tid rd regs Hva Hve Hvsp ME Hlo Hhi"] Lemma main_strN : ltac2:(CDefT.buildp (gd_tbl_P_main_entryN ()) "Pk,$<.P,(=.R1.(>.(?.(10.&8.))Vav,))(11.(12.(13.(?.(10.&8.)))(14.$15.Vmem,(16.Vsp0,Vav,Venvv,R2.)(17.(>.(10.&8.)(18.(?.(10.&8.))R2.Vav,(5.(10.&8.))))#1.))(19.(?.(10.&8.))(1:.(10.&8.)(18.(?.(10.&8.))R2.Vav,(5.(10.&8.)))(0.(10.&8.)(1;.&8.=)(5.(10.&8.))))))(11.(1<.(1=.&40.Vsp0,)(1=.&40.(16.Vsp0,Vav,Venvv,R2.)))(11.(1<.(1=.&40.(16.Vsp0,Vav,Venvv,R2.))(1>.(1=.&40.Vsp0,)+2028;8.))(11.(1<.(1?.(>.(10.&8.)(18.(?.(10.&8.))R2.Vav,(5.(10.&8.)))))+1????.)(20.(?.(10.&8.))Lt8,(?.(10.&8.))(12.(13.(?.(10.&8.)))(14.$15.Vmem,(1;.&40.(1>.(1=.&40.(16.Vsp0,Vav,Venvv,R3.))(1?.(>.(10.&8.)(18.(?.(10.&8.))R3.Vav,(5.(10.&8.)))))))#8.)(19.(?.(10.&8.))R1.)))))))")
(* [comment removed for export] *).
  Proof.
    intros k Hk'. pose proof Hlo. pose proof Hhi.
    pose proof (lay_bsb_nw RPH sp0 rd av envv a_uid a_hwcap Hva Hve ltac:(unfold sp_window_hi; lia)) as Hnw.
    destruct (argv_ptr_bounds_at sp0 av envv Hva Hve ltac:(unfold sp_window_hi; lia) k Hk') as [B1 B2].
    pose proof (u_cat_argv_ptr sp0 av envv Hva Hve ltac:(unfold sp_window_lo; lia) ltac:(unfold sp_window_hi; lia) k Hk') as Hu.
    pose proof (struct_av_bound av envv Hva Hve) as Hsb.
    pose proof (total_arg_bytes_firstn_le k av) as Hf.
    pose proof (argv_str_len av Hva k Hk') as Hlen.
    pose proof (rdn_wmem_stack RSEGS RPH sp0 av envv a_uid a_hwcap rd) as Hw. unfold wmem in Hw.
    repeat split.
    - rewrite (main_entry_rdn_above sp0 av envv tid rd regs mem ME) by lia.
      apply Hw. (* [comment removed for export] *) apply read_argv_cstr_k; [exact Hk' | exact Hnw].
    - exact B1.
    - lia.
    - exact Hlen.
    - ddestruct (read_word_stack RPH [] sp0 av envv k (length (nth k av [])) a_uid a_hwcap rd Hk' ltac:(lia) Hnw) as (t8 & Hl8 & Hr8).
      exists t8. rewrite w_add_nat in Hr8.
      rewrite (main_entry_rdn_above sp0 av envv tid rd regs mem ME) by (rewrite u_small by lia; lia).
      apply Hw. (* [comment removed for export] *) exact Hr8.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  #[using="Type"] Lemma keN0 : ev EN 0 = sp0. Proof. reflexivity. Qed.
  #[using="Type"] Lemma keN1 : ev EN 1 = p0N. Proof. reflexivity. Qed.
  #[using="Type"] Lemma keN3 : ev EN 3 = auxvpN. Proof. reflexivity. Qed.
  #[using="Type"] Lemma keN5 : ev EN 5 = tid. Proof. reflexivity. Qed.
  #[using="Type"] Lemma keN6 : ev EN 6 = canary_w rd. Proof. reflexivity. Qed.
  #[using="Type"] Lemma keN7 : ev EN 7 = a_hwcap. Proof. reflexivity. Qed.

  Local Ltac2 Set LiaOrc.tbl := fun () => "00@0?L11941157027.22L13156172523.20L13168666679.22L14054083309.26L21148992303.26L21819092797.22L25271960277.22L27889819502.22L43935993728.22L44773716229.22L45221225472.22L5005065835.22 L64205780885.26L65502251948.22L67489077272.22L8321048332.22 00000A00N00[01;01O01`01m02B02W03803I03^04204?04L04aS3sp02av3Hhi4HlenS3sp02av4HlenS3sp02av4HlenS3sp02av3Hlo1H2H04Hlen1d1m2Hd2HmS3sp02av4Hlen1d1m2HmS3sp02av3Hlo4HlenS3sp02av4HlenS3sp02av3Hlo3Hhi4HlenS3sp02av3Hlo3Hhi4HlenS3sp02av4envv3Hlo1H2H04Hlen2B12B2S3sp02av3Hhi4HlenS3sp02av3Hlo3Hhi4HlenS3sp02av4Hlen1d1m2HdS3sp02av4HlenS3sp02av4HlenS3sp02av3Hlo3Hhi4Hlen". (* [comment removed for export] *)
  #[using="Hva Hve Hvsp ME Hlo Hhi Hal"] Lemma know_stackN : know_ok RSEGS EN mem kn_stackN.
  Proof.
    pose proof Hlo. pose proof Hhi. pose proof Hal. pose proof len_avN as Hlen.
    ddestruct (main_strN 0%nat ltac:(lia)) as (_ & B1 & B2 & _ & _).
    unfold kn_stackN, know_ok.
    repeat apply Forall_cons; try apply Forall_nil; cbn [kentry_ok a_base a_off edenot]; rewrite ?keN0, ?keN1;
      unfold flat, estart; cbn [a_base a_off edenot]; rewrite ?keN0.
    - split; [lia | exact Hal].
    - lia.
    - split; [lia|]. intros d m Hd Hm.
      apply (main_entry_store_ok_win sp0 av envv tid rd regs mem ME); rewrite u_small by lia; unfold stack_max_size; lia.
    - split; [lia|]. split; [lia|].
      unfold adenot. cbn [a_base a_off edenot]. rewrite keN0. unfold v_addi.
      rewrite (main_entry_rdn_above sp0 av envv tid rd regs mem ME) by (rewrite u_small by lia; lia).
      pose proof (read_argv_ptr_w RSEGS RPH sp0 av envv a_uid a_hwcap rd Hva Hve ltac:(unfold sp_window_lo; lia) ltac:(unfold sp_window_hi; lia) 0%nat ltac:(lia)) as Hr.
      unfold wmem in Hr. rewrite w_add_nat in Hr. change (Z.of_nat (8 + 8 * 0)) with 8%Z in Hr.
      rewrite Hr. rewrite n_to_le_8_spec. reflexivity.
    - unfold p0N. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0050?L12629059976.20L29588573869.20L3980174806.20 L40359575923.20L43855241437.2000000100600;00@00EFS3sp0S3sp0S3sp0S3sp0". (* [comment removed for export] *)
  #[using="Hvsp Hlo Hhi"] Lemma D_main_auxvpN : ltac2:(CDefT.buildp (gd_tbl_P_main_entryN ()) "Psegs,(?.$21.)(12.(13.(?.(10.&8.)))(14.R1.(22.Vsp0,Vav,Venvv,(23.VAMB,)Vrd,Vtid,)(1;.&40.+7=358.)#8.)(19.(?.(10.&8.))(24.#8.$25.)))")
(* [comment removed for export] *).
  Proof.
    intros segs. pose proof (u64_range tid). pose proof Hlo. pose proof Hhi.
    unfold auxvpN, D_main, D_fd, D_ssp, D_tls, D_tlsB, D_tlsA, D_libc. peel.
    apply rdn_wbytes_hit8. unorm; lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)

  #[using="Type"] Lemma wseg_dataN : wseg_ok RSEGS (Z_to_bv 64 0x4c000) 0x32000 = true.
  Proof. vm_compute. reflexivity. Qed.

  Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L68476692870.2400000PS3sp03Hlo2lo1n1c1w1i1H4Hlo'4Hhi'". (* [comment removed for export] *)
  #[using="sp0 Hvsp Hlo"] Lemma range_disjoint_subN : ltac2:(CDefT.buildp (gd_tbl_P_main_entryN ()) "Plo,$26.Pn,$<.Pc,(27.$26.$<.)Pi,$26.P,(12.$28.(29.R4.R3.R2.)$2:.)P,(1<.R5.R2.)P,(1<.(1>.R3.+1.)(1>.R6.(1?.R5.)))(12.$28.(29.R4.#1.R5.)$2:.)")
(* [comment removed for export] *).
  Proof.
    intros lo n [c w] i H Hlo' Hhi'. unfold range_disjoint_b in *. cbn [fst snd] in *.
    apply orb_true_iff in H. apply orb_true_iff. rewrite !Z.leb_le in *. cbn [Z.of_nat Pos.of_succ_nat]. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "0040?L10364178536.24L23832661290.24L32278067313.26L42007348611.2600000H00`01101BS3sp03Hlo2lo1n1i2H24Hlo'S3sp03Hlo2lo1n1i2H34Hhi'S3sp02lo1n1i4Hhi'S3sp02lo1n1i4Hlo'". (* [comment removed for export] *)
  #[using="sp0 Hvsp Hlo"] Lemma missb_subN : ltac2:(CDefT.buildp (gd_tbl_P_main_entryN ()) "Plo,$26.Pn,$<.Pi,$26.P,(12.$28.(2;.R3.R2.)$2:.)P,(1<.R4.R2.)P,(1<.(1>.R3.+1.)(1>.R5.(1?.R4.)))(12.$28.(2;.R4.#1.)$2:.)")
(* [comment removed for export] *).
  Proof.
    intros lo n i H Hlo' Hhi'. unfold D_main_missb in *.
    apply andb_true_iff in H as [H H3]. apply andb_true_iff in H as [H1 H2].
    apply Z.leb_le in H2. apply Z.leb_le in H3.
    apply andb_true_iff; split; [apply andb_true_iff; split|]; [| apply Z.leb_le; lia | apply Z.leb_le; cbn [Z.of_nat Pos.of_succ_nat]; lia].
    apply forallb_forall. intros c Hc. apply (range_disjoint_subN lo n); [|lia|lia].
    apply (proj1 (forallb_forall _ _) H1). exact Hc.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "0090?L11941000314.26L17749049106.26L18914900186.26L21819180004.26L29443145835.24L42007347853.26L52371396776.24L66253720165.26L8785596558.26 00000900V00f00o01<01L01Y02702FS3sp03HhiS3sp03Hlo2lo2hi4Hhi'3HLO1i2HiS3sp02lo2hi1i2HiS3sp03HloS3sp02lo4Hlo0S3sp02lo2hi1i2HiS3sp02hi4Hhi'S3sp03Hlo2lo2hi4Hhi'4Hlo01i2HiS3sp02lo2hi3Hle". (* [comment removed for export] *)
  #[using="Hva Hvsp ME Hlo Hhi"] Lemma kimg_okN : ltac2:(CDefT.buildp (gd_tbl_P_main_entryN ()) "Plo,$26.Phi,$26.P,(12.$28.(2;.R2.(2<.(2=.R1.R2.)))$2:.)P,(1<.R3.R2.)P,(1<.R3.+7>000.)(2>.$15.$2?.Vmem,(30.R5.R4.))")
(* [comment removed for export] *).
  Proof.
    intros lo hi Hb Hle Hhi'. pose proof Hlo as HLO. pose proof Hhi as HHI.
    assert (Hlo0 : (0 <= lo)%Z).
    { unfold D_main_missb in Hb. apply andb_true_iff in Hb as [Hb _]. apply andb_true_iff in Hb as [_ Hb].
      apply Z.leb_le in Hb. exact Hb. }
    cbn [kentry_ok]. split; [lia|]. split; [lia|]. intros i Hi.
    rewrite (main_entry_mem_data sp0 av envv tid rd regs mem ME) by (rewrite u_small by lia; unfold stack_max_size; lia).
    apply (D_main_none sp0 av envv a_hwcap rd tid i Hva); [lia | lia |].
    apply (missb_subN lo (Z.to_nat (hi - lo))); [exact Hb | lia | rewrite Z2Nat.id by lia; lia].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Ltac kimgN := apply kimg_okN; [vm_compute; reflexivity | lia | lia].

  Ltac kw_preN :=
    split; [lia|]; split; [lia|];
    unfold adenot; cbn [a_base a_off edenot]; unfold v_addi; rewrite u_small by lia; rewrite Z.add_0_l.
  Ltac kw_dataN L :=
    kw_preN;
    rewrite (main_entry_rdn_data sp0 av envv tid rd regs mem ME) by (rewrite u_small by lia; unfold stack_max_size; lia);
    rewrite (L RSEGS); try reflexivity.
  Ltac kw_memN L := kw_preN; rewrite (L RSEGS); try reflexivity.

  Local Ltac2 Set LiaOrc.tbl := fun () => "00c0?L1000284608.19 L10724054094.19L1083249694.19 L13485667150.19L14291479502.19L14424637262.19L16697688782.19L18501395702.19L18833241560.19L18928853482.19L20435208654.19L21823471390.19L2457917272.19 L25271804307.19L25654141262.19L27118011854.19L28043817678.19L29290475342.19L30283716302.19L31262883904.19L31289823704.19L32155950670.19L32538124622.19L35860693326.19L37859791438.19L39505559628.23L41011215822.19L43056431448.19L44593532046.19L49858991606.19L51852962894.19L52094160630.19L52723532366.19L53519161302.19L56415728974.19L57220884790.23L58884595790.19L59429660632.19L60705177601.23L60844916302.19L61604292160.19L63448934734.19L63691814390.19L64514089525.19L65070153166.19L65499172032.19L67436825038.19L67969894744.19L68075130122.23L68458866126.19L7927117016.19 00000900>00C00H00M00R00W00\00a00f00k01001501:01?01D01I01N01S01\01a01f01k02002502A02F02K02P02U02Z02_02d02i02n03:03?03D03W03\03e03j03o04=04B04K04P04U04\04a04fS3sp03HloS3sp0S3sp0S3sp0S3sp0S3sp0S3sp0S3sp0S3sp0S3sp0S3sp0S3sp0S3sp0S3sp0S3sp0S3sp0S3sp0S3sp0S3sp0S3sp03HloS3sp0S3sp0S3sp0S3sp0S3sp0S3sp01d1m2HmS3sp0S3sp0S3sp0S3sp0S3sp0S3sp0S3sp0S3sp0S3sp0S3sp01d1m2HdS3sp0S3sp0S3sp03Hlo1d1m2Hd2HmS3sp0S3sp03HloS3sp0S3sp0S3sp03tid4HtidS3sp0S3sp03HloS3sp0S3sp0S3sp01mS3sp0S3sp0". (* [comment removed for export] *)
  #[using="Hva Hvsp Htid ME Hlo Hhi"] Lemma know_imageN : know_ok RSEGS EN mem kn_image.
  Proof.
    pose proof Hlo as HLO. pose proof Hhi as HHI. pose proof (u64_range tid) as Ht.
    unfold kn_image, know_ok.
    repeat apply Forall_cons; try apply Forall_nil;
      try kimgN;
      cbn [kentry_ok a_base a_off edenot]; rewrite ?keN3, ?keN5, ?keN6, ?keN7; unfold flat, estart, elenZ; cbn [a_base a_off edenot];
      rewrite ?(u_small 0) by lia; cbn [Z.add].
    - (* [comment removed for export] *) split; [lia|]. intros d m Hd Hm.
      eapply (store_ok_window RSEGS mem (Z_to_bv 64 0x4c000) (Z_to_bv 64 (0x4c000 + d)) 0x32000 m 0x4c000 0x7e000);
        [reflexivity | reflexivity | cbn; lia | apply wseg_dataN | rewrite u_small by lia; lia | rewrite u_small by lia; lia].
    - kw_dataN (D_main_self sp0 av envv tid rd).
    - kw_memN (main_entry_tid sp0 av envv tid rd HLO regs mem ME).
    - kw_dataN (D_main_canary sp0 av envv tid rd).
    - kw_memN (main_entry_guard sp0 av envv tid rd HLO regs mem ME). rewrite canary_store. reflexivity.
    - kw_dataN D_main_auxvpN.
    - kw_dataN (D_main_pagesize sp0 av envv tid rd Hva).
    - kw_dataN (D_main_hwcap sp0 av envv tid rd Hva).
    - (* [comment removed for export] *) lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  #[using="Hva Hve Hvsp Htid ME Hlo Hhi Hal"] Theorem main_know_okN : know_ok RSEGS EN mem kn_mainN.
  Proof.
    unfold kn_mainN, know_ok. apply Forall_app; split; [apply know_stackN | apply know_imageN].
  Qed.

  #[using="Type"] Lemma valsN_length : length valsN = 38%nat.
  Proof. unfold valsN, junk_vals2. rewrite length_app, length_map, length_seq. reflexivity. Qed.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0030?L11940998021.21L21819186203.21L6412697092.27 00000N00l01aS3AMB3sp02av4envv2rd3Hhi1k3Hk'S3AMB3sp02av4envv2rd3Hlo1k3Hk'S3AMB3sp02av4envv2rd3Hlo1k3Hk'2HT2Hu3pre4post4Hpre2HL". (* [comment removed for export] *)
  #[using="AMB tid rd regs mem Hva Hve Hvsp ME Hlo Hhi"] Lemma main_strN_top : ltac2:(CDefT.buildp (gd_tbl_P_main_entryN ()) "Pk,$<.P,(=.R1.(>.(?.(10.&8.))Vav,))(1<.(1>.(1>.(1=.&40.(16.Vsp0,Vav,Venvv,R2.))(1?.(>.(10.&8.)(18.(?.(10.&8.))R2.Vav,(5.(10.&8.))))))+1.)+800000000000.)")
(* [comment removed for export] *).
  Proof.
    intros k Hk'. pose proof Hlo. pose proof Hhi.
    pose proof (main_entry_block_top sp0 av envv tid rd regs mem ME) as HT. unfold sp_window_hi in HT.
    pose proof (u_cat_argv_ptr sp0 av envv Hva Hve ltac:(unfold sp_window_lo; lia) ltac:(unfold sp_window_hi; lia) k Hk') as Hu.
    ddestruct (bsb_byte_k RPH sp0 av envv k a_uid a_hwcap rd Hk') as (pre & post & EB & Hpre).
    pose proof (f_equal (@length byte) EB) as HL. rewrite !length_app in HL. cbn [length] in HL.
    rewrite Hu, <- Hpre. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L5373760964.16000005S3sp0". (* [comment removed for export] *)
  #[using="mem Hvsp ME Hlo"] Lemma evN_argc : ev EN 16 = argcN av.
  Proof. change 16%nat with (6 + 10)%nat. rewrite (evN_junk 10) by lia. exact (me_a0 _ _ _ _ _ _ _ ME). Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End MainEntryN.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
