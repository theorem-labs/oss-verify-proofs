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
From OSSVerify.boost_json.fuzz_parse.images Require Import AsanUbsan.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import
  PropExec CatExec CatSim SeqExec StoreOk ShapeAlg Nodes AgentLib SpecConsts Frame StreamSim FileSim
  SymExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX LibKnowFrame SymAux Hoare RefPrintfLib LibTail Spec
  LazyRestrict LazySR LazyFdNodes LazySym.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Bs Require Import RefExitBase RefStdioDefs AsLazyRun AsStdioWrite AsStdioCall AsScLib
  AsPrintfFirst AsExitCas AsExitDefs AsExit.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums04Npos01Z35stdpp9bitvectorbdefinitionsi22bv37Corelib4Init9Datatypesk44listk44prodk44consk44pairi27Z_to_bvk43nil46Stdlib6ZArith6BinInt1Zo83subi2bbv_unsignedo82le37Corelib4Init5Logicr93andr92or79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs0d1A1s1P1r1i1n1t1f1F1i1r1s1t~~~~~~t86ASP_LO89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2BsaAsTailExit8TailExit~~~~~~hj2ctail_regions69OSSVerify6Proofsaboost_jsonafuzz_parse3lib5Frame~~~~~~hob7outsideo83addo82ltk46optionr92eq69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8PropExec~~~~~~hu73rdn69OSSVerifyaboost_jsonafuzz_parse6images9AsanUbsan1M~~~~~~ii9floaded_segmentso86of_natk43nathob9frame_modk44Nonet88cells_ok37Corelib5Lists7ListDefiq46Forall79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2BsaAsExitDefs~~~~~~is5cax_lit_cellsk43appiq46firstniq45skipnk44Some3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticsjj5h0word_to_le_bytesr91Ihu74getri22BVi24BvWfjj5dmachine_state3h5LinuxProcessSemanticsfLinuxProcessSem3Runjqa5mkCfg3h5LinuxProcessSemanticsfLinuxProcessSem5Statejtf5Modeljtf4m_fs3h5LinuxProcessSemantics5Riscv7Preludekhe5bvmapis55AEXITt86ASP_HIhj25exitH69OSSVerify6Proofsaboost_jsonafuzz_parse3libcLazyRestrict~~~~~~km88restrict69OSSVerify6Proofsaboost_jsonafuzz_parse3lib6LazySR~~~~~~kr34lzokhu74mksthu77seg_rom69OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Scfg~~~~~~lg7dhunspell_scfg69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8ShapeAlg~~~~~~lkf8realizeslkf6t_exit69OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec~~~~~~lq09exit_code69OSSVerify6Proofsaboost_jsonafuzz_parse3lib6SymRun~~~~~~lu46stk_oko86moduloo83pow" s.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Abbreviation RSEGS := AsanUbsan.M.loaded_segments.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section TailExit.
  Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
  Variables (L S Zr : list (word * word)).

  Record exitH (mem : word -> option byte) (sp : word) (tid : Z) (ro wpw : word) : Prop := EXH {
    Etid  : (0 < tid < 2147483648)%Z;
    Etidc : rdn RSEGS mem (Z_to_bv 64 0x6f1270) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 tid));
    Euse2 : forall i, (0x1b6e08 <= i < 0x1b6e10)%Z -> mem (Z_to_bv 64 i) = None;
    Eglb  : forall i, (0x1b6ef8 <= i < 0x1b9ac0)%Z -> mem (Z_to_bv 64 i) = None;
    Eor1  : rdn RSEGS mem (Z_to_bv 64 0x1b6e18) 8 = Some (word_to_le_bytes 8 ro);
    Eor2  : rdn RSEGS mem (Z_to_bv 64 0x1b6e20) 8 = Some (word_to_le_bytes 8 ro);
    Eow1  : rdn RSEGS mem (Z_to_bv 64 0x1b6e38) 8 = Some (word_to_le_bytes 8 wpw);
    Eow2  : rdn RSEGS mem (Z_to_bv 64 0x1b6e48) 8 = Some (word_to_le_bytes 8 wpw);
    Ecells : cells_ok mem ax_lit_cells;
    Eshw  : forall (a : word) (n : nat), (0x7fffa000 <= bv_unsigned a)%Z -> (bv_unsigned a + Z.of_nat n <= 0x7fffa000 + 0xe0600)%Z ->
              store_ok RSEGS mem a n = true }.

  (* [comment removed for export] *)
  Definition tail_regions : ltac2:(zQ "50!h9!hf!jf!lc!m3>2sp@1$2@1$0#k0>2FR$1@1$3@2$4@1$2@1$0#k0$1") := ltac2:(zQ "a0!h9!hf!jf!m3!ma!n1!n8!o2!q0!q6\2sp@1$2@1$0#k0\2FR$1@3$4@2$3@1$2@1$0#k0$1@4$5@1$2@1$0#k0$1@2$6@1$0#k0@2$8@2$9@1$0#k0^2^1^1@3$4@2$3@1$2@1$0#k0$1@4$5@1$2@1$0#k0$1@2$6@1$0#k0+hrmti0+u8@1$7@2$3@1$2@1$0#k0$1").

  Lemma outside_tail : ltac2:(zQ "d0!r4!h9!hf!sd!t3!hi9!hnb!hs3!hse!ht4!n8!jf!q6>2sp@1$b@1$1#k0>2FR$2>1x$2>0@2$0$5@2$c@1$1#k0^3>0@2$3@2$0+hp0^3@2$0^3+ogggg0>0@2$0Z^3>0@2$4@2$0@2$8^4+1+hrmti0@2$0+hrmug8^4>0@2$9^5+nvvvggggggg0@2$7@2$a@1$1#k0^6@2$6^8^7").
  Proof.
    intros sp FR x Hlo HFR Hx H1 H2. unfold ASP_LO in Hlo. pose proof (u64_range sp).
    unfold tail_regions. cbn [outside]. unfold in_rng. rewrite !u64_lit by lia. lia.
  Qed.

  Lemma rdn_tail : ltac2:(zQ "h41!h9!jf!r4!ht9!lc!hu2!hf!ii2!im3!hse!in6!n8!inf!sd!t3!hi9!hnb!io5!ht4!q6&>0@1$1@1$0#k0@1$3@1$1@1$0#8>3mem~0>4mem'~0>2sp@1$1@1$0#k0>2FR$6>1a$6>1n$c>1v@1$3@1$4@1$1@1$0#8>0@3$h1^7^6@2$h0^5^4>0@2$2$f@2$h3@1$0#k0^6>0@2$d@2$2+hp0^6@2$2^6+ogggg0>0@2$2Z^6>0@2$e@2$2@2$9^7@1$a^6+hrmti0@2$2+hrmug8^7>0@2$h2@2$9^8@1$a^7+nvvvggggggg0>0@3$5@1$3@1$4@1$1@1$0#8@4$7$8^d@2$b@1$0#k0^9^8^7@3$5@1$3@1$4@1$1@1$0#8@4$7$8^d@2$b@1$0#k0^a^9^8").
  Proof.
    intros mem mem' sp FR a n v FM Hlo HFR Ha H1 H2 Hr. rewrite <- Hr.
    apply (frame_mod_rdn RSEGS mem mem' _ n (Z_to_bv 64 a) FM); rewrite u64_lit by lia; [|lia].
    intros i Hi. apply outside_tail; try assumption; lia.
  Qed.

  Lemma none_tail : ltac2:(zQ "f2!h9!jf!r4!hf!ht9!sd!ht4!ip2!hu2!n8!t3!hi9!hnb!io5!q6&>0@1$1@1$0#k0@1$4@1$1@1$0#8&@3$8@1$4@1$1@1$0#8@1^e@2$9@1$0#k0^2@1$7@1$1@1$0#8>3mem~0>4mem'~0>2sp@1$1@1$0#k0>2FR$3>2lo$3>2hi$3>0@3$d^6^5@2$c^4^3>0@2$2$b@2$e@1$0#k0^5>0@2$5@2$2+hp0^5@2$2^5+ogggg0>0@2$2Z^5>0@2$a@2$2^5+hrmti0@2$2+hrmug8^6>0@2$6^6+nvvvggggggg0>0>1i$3>0@2$5@2$2^9^1@2$6^1^8~1>1i$3>0@2$5@2$2^a^1@2$6^1^9~1").
  Proof.
    intros mem mem' sp FR lo hi FM Hlo HFR H0 H1 H2 Hn i Hi.
    rewrite (frame_mod_byte mem mem' _ (Z_to_bv 64 i) FM); [apply Hn; exact Hi|].
    apply outside_tail; try assumption; lia.
  Qed.

  Lemma cells_tail : ltac2:(zQ "h31!hf!m3!inf!h9!r4!jf!sd!ht9!ip9!hse!in6!lc!t3!irb!hi9!hnb!io5!ht4!q6&>0@1$5@1$3#k0@1$7@1$5@1$3#8>3mem~0>4mem'~0>2sp@1$5@1$3#k0>2FR$0>2cs@1$b@2$1@2$1$0$2$0>0@3$h0^5^4@2$f^3^2>0@2$4$e@2$h2@1$3#k0^4>0@2$6@2$4+hp0^4@2$4^4+ogggg0>0@3$d@2$1@2$1$0$2$0\1c@2$1@2$1$0$2$0M1\1c@2$1@2$1$0$2$0P^1\1y@2$1$0$2\2y0$0M1\1y@2$1$0$2P^2\1a$0\1w$2@2$6@2$4Z^2@2$6@2$c@2$4@2$9^2@1$a^1+hrmti0@2$4+hrmug8^2@2$h1@2$9^2@1$a^1+nvvvggggggg0^4>0@2$8^9^5@2$8^9^6").
  Proof.
    intros mem mem' sp FR cs FM Hlo HFR Hcs Hc. unfold cells_ok in *.
    induction cs as [|[[a w] v] cs IH]; [constructor|].
    inversion Hcs as [|c cs' Hc1 Hcs']; subst. inversion Hc as [|c cs'' Hok Hc']; subst.
    constructor; [| apply IH; assumption].
    unfold cell_ok in *. ndestruct Hc1 as (A1 & A2 & A3).
    apply (rdn_tail mem mem' sp FR a w _ FM Hlo HFR A1 A2 A3 Hok).
  Qed.

  (* [comment removed for export] *)
  Lemma ax_lit_cells_split : ltac2:(zQ "c0!hf!m3!inf!jg5!jh5!n1!ma!lc!o2!hu2!jhb!ji5@3$9@1$7@2$1@2$1$0$2$0$3@3$4@2$1@2$1$0$2$0@3$a@2$1@2$1$0$2$0Nh4$3@3$4@2$1@2$1$0$2$0@3$6@2$1@2$1$0$2$0@4$5@2$1$0$2$0@4$5$0$2+hrmtqcN4+vvvvvvvf@1$8@2$1@2$1$0$2$0@3$b@2$1@2$1$0$2$0Nh5$3").
  Proof. reflexivity. Qed.

  Lemma ax_lit_cells_apart : ltac2:(zQ "e0!m3!hf!inf!r4!sd!jg5!hse!in6!jh5!t3!irb!jhb!ji5!ht4@3$a@2$0@2$0$1$2$1\1c@2$0@2$0$1$2$1M0\1c@2$0@2$0$1$2$1P^1\1p@2$0$1$2\1z$1M0\1p@2$0$1$2P^2\1a$1\1w$2@2$4@2$3Z^2@2$4@2$9@2$3@2$6^2@1$7^1+hrmti0@2$3+hrmug8^2@2$d@2$6^2@1$7^1+nvvvggggggg0@3$8@2$0@2$0$1$2$1@3$b@2$0@2$0$1$2$1Nh4$5@3$c@2$0@2$0$1$2$1Nh5$5").
  Proof. cbn. repeat (apply Forall_cons; [cbn; lia|]). apply Forall_nil. Qed.

  Theorem tail_exit2 : ltac2:(zQ "ia2!h9!jf!hu2!n8!lc!ht9!im3!r4!jie!hf!jmc!ii2!sd!jo1!jo5!ht4!jod!jp2!q6!ip2!jp9!jt6!kgd!kh6!kk4!kkd!kl6!hi9!klf!hnb!io5!kq7!kuc!kv4!kvc!lje!loa!lp6!lt7!mhd!mi7!mj0&>0@1$1@1$0#k0@1$5@1$1@1$0#8&@2$8@1$4@1$1@1$0#8@2$aN8^e>4regs@2$h8@1$0#5@1$1@1$0#k0>3mem~0>4mem'~0>3msF$h4>2mo$h6>2sp@1$1@1$0#k0>2FR$9>3tid$9>3can$9>2ro@1$1@1$0#k0>3wpw@1$1@1$0#k0>2we@1$1@1$0#k0>2re@1$1@1$0#k0>0@5$hc^c^8^6^4^3>0@3$2$9@2$i8@2$h2@1$0#k0^9+h0Z>0@2$7$hb@2$h2@1$0#k0^a>0@2$7@2$h2@1$0#k0^b$ha>0>1i$9>0@2$c@2$7+hggg0^1@2$f^1+mngg0@3$2@1$5@1$1@1$0#8@1^h2@2$3@1$0#k0^2@1$h3@1$1@1$0#8>0>1i$9>0@2$c@2$7+hqqgg0^1@2$f^1+hrkgg0@3$2@1$5@1$1@1$0#8@1^h3@2$3@1$0#k0^2@1$h3@1$1@1$0#8>0@3$he^h2^h1@2$hd^e^d>0@2$c@2$7+hp0^e@2$7^e+ogggg0>0@4$i7$6^h3^h0+hp0>0@2$c@2$7Z^e@2$f^e@2$i9+2+k0>0@3$2@1$5@1$4@1$1@1$0#8@4$b$6^h5@2$3@1$0#k0+nhhjl8N8@2$8@1$4@1$1@1$0#8@2$aN8@2$3@1$0#k0^f>0@3$2@1$5@1$4@1$1@1$0#8@4$b$6^h6@2$3@1$0#k0+hrmtk8N8@2$8@1$4@1$1@1$0#8@2$aN8^d>0@3$2@1$5@1$4@1$1@1$0#8@4$b$6^h7@2$3@1$0#k0+hrmtl8N8~1>0@3$2@1$5@1$4@1$1@1$0#8@4$b$6^h8@2$3@1$0#k0+hrmti8N8~1>0@3$2@1$5@1$4@1$1@1$0#8@4$b$6^h9@2$3@1$0#k0+hrmtj0N8@2$8@1$4@1$1@1$0#8@2$aN8^f>0@3$2@1$5@1$4@1$1@1$0#8@4$b$6^ha@2$3@1$0#k0+hrmtqcN4@2$8@1$4@1$1@1$0#8@2$aN4@2$3@1$0#k0+vvvvvvvf>0@3$2@1$1@1$0#k0@2$e^hd@3$h0@1$0#5+2Kv$d@2$h1@1$0#5+2^h8>0@3$2@1$1@1$0#k0@2$e^he@3$h0@1$0#5+4Kv$d@2$h1@1$0#5+4@2$3@1$0#k0+mvhjh8>0@3$2@1$1@1$0#k0@2$e^hf@3$h0@1$0#5+aKv$d@2$h1@1$0#5+a@2$3@1$0#k0+2>0@5$i0$6?1L?1S?2Zr@2$h5^hd^hc>0@3$2$h4@3$hf?1L?1S^he@5$i1?2fx^i1@2$3@1$0#k0$h9^hf@1$i2$6@4$i4$6$i3@2$h5^hf^he@2$i5@1$i6+2@1$h7^he").
  Proof.
    intros regs mem mem' msF mo sp FR tid can ro wpw we re XH Hal Hlo Hhi Himg Hgot FM HFR Hstk Hcan64 Hcan
           Hwe1 Hwe2 Hre1 Hre2 Hlock R2 R4 R10 OK RS.
    destruct XH.
    replace (exit_code 2) with (bv_and (Z_to_bv 64 2) (Z_to_bv 64 255)) by (apply bv_eq; reflexivity).
    apply (as_exit_clean L S Zr regs mem' msF mo sp (Z_to_bv 64 2) we re ro wpw tid can); try assumption.
    - split; try assumption.
      + apply (rdn_tail mem mem' sp FR 0x6f1270 4 _ FM Hlo HFR); [lia | lia | lia | exact Etidc0].
      + apply (none_tail mem mem' sp FR 0x10000 0x67000 FM Hlo HFR); [lia | lia | lia | exact Himg].
      + apply (none_tail mem mem' sp FR 0x1aa000 0x1b4000 FM Hlo HFR); [lia | lia | lia | exact Hgot].
      + apply (none_tail mem mem' sp FR 0x1b6e08 0x1b6e10 FM Hlo HFR); [lia | lia | lia | exact Euse3].
      + apply (none_tail mem mem' sp FR 0x1b6ef8 0x1b9ac0 FM Hlo HFR); [lia | lia | lia | exact Eglb0].
      + apply (rdn_tail mem mem' sp FR 0x1b6e18 8 _ FM Hlo HFR); [lia | lia | lia | exact Eor3].
      + apply (rdn_tail mem mem' sp FR 0x1b6e20 8 _ FM Hlo HFR); [lia | lia | lia | exact Eor4].
      + rewrite ax_lit_cells_split in Ecells0 |- *. unfold cells_ok in *.
        apply Forall_app in Ecells0 as [C1 C23]. apply Forall_app in C23 as [_ C3].
        pose proof (cells_tail mem mem' sp FR _ FM Hlo HFR ax_lit_cells_apart) as CT. unfold cells_ok in CT.
        assert (C13 : Forall (cell_ok mem) (firstn 20 ax_lit_cells ++ skipn 21 ax_lit_cells)) by (apply Forall_app; split; assumption).
        apply CT in C13. apply Forall_app in C13 as [C1' C3'].
        apply Forall_app; split; [exact C1'|]. constructor; [exact Hlock | exact C3'].
      + intros a n Ha Hn. eapply frame_mod_store_ok; [exact FM|]. apply Eshw0; assumption.
    - apply (rdn_tail mem mem' sp FR 0x1b6e38 8 _ FM Hlo HFR); [lia | lia | lia | exact Eow3].
    - apply (rdn_tail mem mem' sp FR 0x1b6e48 8 _ FM Hlo HFR); [lia | lia | lia | exact Eow4].
  Qed.
End TailExit.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
