(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk AStep CellsX Image Asn1Aux Asn1AuxA X509Aux X509AuxB.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts RepName.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg U_string U_asn1_get_tag U_asn1_get_len U_asn1_sequence_free U_asn1_free_named_data_list_shallow U_asn1_get_sequence_of_A U_x509_get_name_A U_x509_parse_san_A U_x509_parse_san U_x509_get_san_ext_A U_x509_get_san_ext_B U_x509_get_san_ext_C U_x509_get_san_ext_D.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX Require Import LxExpr LxDec LxMem LxStep LxRun LxDenot LxSoundRun LxSum LxSoundSum LxTac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXP Require Import LxPTac.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Import OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.LxhSyntax. #[local] Instance lxh_tab : OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lx_hints := OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lxh_parse "P004afa2b03b378c3 0 4 0 1 24 1 25 1 32 1P022c5ffb340d2c5b 2 15 1 1 8 3 2 1 38 1 39 1 6 0 1 22 1 29 1 37 1 40 1 41 8 1 1 8 3 1 1 37 1 40 1 4 0 1 38 1 39 1 41 8P0472c4b6addd6783 2 13 0 6 0 1 3 1 23 1 30 1 38 1 39 1 0 4 0 1 2 1 38 1 39 1P0501753e0dba17d7 2 15 1 1 8 3 2 1 38 1 39 1 6 0 1 22 1 29 1 37 1 40 1 41 8 1 1 8 3 1 1 37 1 40 1 4 0 1 38 1 39 1 41 8P0812841294ba7302 2 15 1 1 8 3 2 1 38 1 39 1 6 0 1 22 1 29 1 37 1 40 1 41 8 1 1 8 3 1 1 37 1 40 1 4 0 1 38 1 39 1 41 8P0a24c51bfc4c9128 2 13 0 6 0 1 3 1 23 1 30 1 38 1 39 1 0 4 0 1 2 1 38 1 39 1P0bb0c8d19d82d8aa 2 14 1 1 8 3 2 1 38 1 39 1 6 0 1 22 1 29 1 37 1 40 1 41 8 1 1 8 3 1 1 37 1 40 1 4 0 1 38 1 39 1 41 8P0bb8357f65a07b19 2 13 0 6 0 1 3 1 23 1 30 1 38 1 39 1 0 4 0 1 2 1 38 1 39 1P0f5ff4bb40ba3062 2 15 1 1 8 3 2 1 38 1 39 1 6 0 1 22 1 29 1 37 1 40 1 41 8 1 1 8 3 1 1 37 1 40 1 4 0 1 38 1 39 1 41 8P104f0ab6fa6ceb0e 2 13 0 6 0 1 3 1 23 1 30 1 38 1 39 1 0 4 0 1 2 1 38 1 39 1P13404a6b9a953c86 2 14 1 1 8 3 2 1 38 1 39 1 6 0 1 22 1 29 1 37 1 40 1 41 8 1 1 8 3 1 1 37 1 40 1 4 0 1 38 1 39 1 41 8P142e3171383c2daa 2 14 1 1 8 3 2 1 38 1 39 1 6 0 1 22 1 29 1 37 1 40 1 41 8 1 1 8 3 1 1 37 1 40 1 4 0 1 38 1 39 1 41 8P17cd15a2e180e1cc 2 14 1 1 8 3 2 1 38 1 39 1 6 0 1 22 1 29 1 37 1 40 1 41 8 1 1 8 3 1 1 37 1 40 1 4 0 1 38 1 39 1 41 8P17ff60f7db7eda68 2 13 0 6 0 1 3 1 23 1 30 1 38 1 39 1 0 4 0 1 2 1 38 1 39 1P1ae647d84ac58aa7 0 3 0 1 24 1 25 1P1b32fa8942712602 2 15 1 1 8 3 2 1 38 1 39 1 6 0 1 22 1 29 1 37 1 40 1 41 8 1 1 8 3 1 1 37 1 40 1 4 0 1 38 1 39 1 41 8P1bd8daa19a2814da 2 15 1 1 8 3 2 1 38 1 39 1 6 0 1 22 1 29 1 37 1 40 1 41 8 1 1 8 3 1 1 37 1 40 1 4 0 1 38 1 39 1 41 8P1c9f797b7c303e16 2 14 1 1 8 3 2 1 38 1 39 1 6 0 1 22 1 29 1 37 1 40 1 41 8 1 1 8 3 1 1 37 1 40 1 4 0 1 38 1 39 1 41 8P1da97f6b001dfbb1 2 15 1 1 8 3 2 1 38 1 39 1 6 0 1 22 1 29 1 37 1 40 1 41 8 1 1 8 3 1 1 37 1 40 1 4 0 1 38 1 39 1 41 8P1fd99cd996db0bd1 0 3 0 1 21 1 26 1P21eebd7733436bf7 2 13 0 6 0 1 3 1 23 1 30 1 38 1 39 1 0 4 0 1 2 1 38 1 39 1P21f8382680d0971b 2 14 1 1 8 3 2 1 38 1 39 1 6 0 1 22 1 29 1 37 1 40 1 41 8 1 1 8 3 1 1 37 1 40 1 4 0 1 38 1 39 1 41 8P26770c12c8559bf1 2 15 1 1 8 3 2 1 38 1 39 1 6 0 1 22 1 29 1 37 1 40 1 41 8 1 1 8 3 1 1 37 1 40 1 4 0 1 38 1 39 1 41 8P2873a699e5471328 2 13 0 6 0 1 3 1 23 1 30 1 38 1 39 1 0 4 0 1 2 1 38 1 39 1P2af591f6a94736c0 2 14 1 1 8 3 2 1 38 1 39 1 6 0 1 22 1 29 1 37 1 40 1 41 8 1 1 8 3 1 1 37 1 40 1 4 0 1 38 1 39 1 41 8P2b127834e4aad841 0 4 0 1 21 1 26 1 32 1P2bcb71351d336f5f 2 15 1 1 8 3 2 1 38 1 39 1 6 0 1 22 1 29 1 37 1 40 1 41 8 1 1 8 3 1 1 37 1 40 1 4 0 1 38 1 39 1 41 8P2ea6fbe0c74bf593 2 14 1 1 8 3 2 1 38 1 39 1 6 0 1 22 1 29 1 37 1 40 1 41 8 1 1 8 3 1 1 37 1 40 1 4 0 1 38 1 39 1 41 8P2fca83092ec47dc3 2 13 0 6 0 1 3 1 23 1 30 1 38 1 39 1 0 4 0 1 2 1 38 1 39 1P2ffc0887a99aafed 2 13 0 6 0 1 3 1 23 1 30 1 38 1 39 1 0 4 0 1 2 1 38 1 39 1P30e3bb4c1e661ae9 2 14 1 1 8 3 2 1 38 1 39 1 6 0 1 22 1 29 1 37 1 40 1 41 8 1 1 8 3 1 1 37 1 40 1 4 0 1 38 1 39 1 41 8P324d59e38f660364 2 14 1 1 8 3 2 1 38 1 39 1 6 0 1 22 1 29 1 37 1 40 1 41 8 1 1 8 3 1 1 37 1 40 1 4 0 1 38 1 39 1 41 8P3295d8785ef9a9e3 2 15 1 1 8 3 2 1 38 1 39 1 6 0 1 22 1 29 1 37 1 40 1 41 8 1 1 8 3 1 1 37 1 40 1 4 0 1 38 1 39 1 41 8P32fc3db9288fd08e 2 15 1 1 8 3 2 1 38 1 39 1 6 0 1 22 1 29 1 37 1 40 1 41 8 1 1 8 3 1 1 37 1 40 1 4 0 1 38 1 39 1 41 8P366a665b7101460f 2 13 0 6 0 1 3 1 23 1 30 1 38 1 39 1 0 4 0 1 2 1 38 1 39 1P36ad062bb5f4ed06 2 14 1 1 8 3 2 1 38 1 39 1 6 0 1 22 1 29 1 37 1 40 1 41 8 1 1 8 3 1 1 37 1 40 1 4 0 1 38 1 39 1 41 8P37c59b6c6b80427f 2 15 1 1 8 3 2 1 38 1 39 1 6 0 1 22 1 29 1 37 1 40 1 41 8 1 1 8 3 1 1 37 1 40 1 4 0 1 38 1 39 1 41 8P39c0877cacbabb05 2 13 0 6 0 1 3 1 23 1 30 1 38 1 39 1 0 4 0 1 2 1 38 1 39 1P3ade6a89d4537e9f 2 13 0 6 0 1 3 1 23 1 30 1 38 1 39 1 0 4 0 1 2 1 38 1 39 1P3b5f0953d18cade3 2 13 0 6 0 1 3 1 23 1 30 1 38 1 39 1 0 4 0 1 2 1 38 1 39 1P3b78fb8f0bac9074 2 14 1 1 8 3 2 1 38 1 39 1 6 0 1 22 1 29 1 37 1 40 1 41 8 1 1 8 3 1 1 37 1 40 1 4 0 1 38 1 39 1 41 8P3c5938fc27847568 2 15 1 1 8 3 2 1 38 1 39 1 6 0 1 22 1 29 1 37 1 40 1 41 8 1 1 8 3 1 1 37 1 40 1 4 0 1 38 1 39 1 41 8P3e42c317fbc3e108 2 14 1 1 8 3 2 1 38 1 39 1 6 0 1 22 1 29 1 37 1 40 1 41 8 1 1 8 3 1 1 37 1 40 1 4 0 1 38 1 39 1 41 8N00b6e04393dbfc6bN019b3bce3c3582d1N039fe80b31d771e6N04e6e2b0bb4d8981N05dc626695641358N076ec51689ec60d6N080f56e6df1fd0baN084679c09b80dda8N08a97c8ffc7f73dcN0b572eab6a900e53N0c19679d350e1785N161c2d9688c430d9N1917ab06721955cfN22e3a58c9287e6b7N2454933c7ee63ee4N261f3809a9a514a6N28c1550bebc81b6eN2aa527fce82da1eeN2b4fa26da29ce9e0N2b84153a30e0af07N2d6ca4bc300072ceN35c1c200cec51b4fN36d61a3157cc65fdN370bf02b397a6983N3b697c41c10b4b7eN3fb31b1f143c8f8f"%lxh.
Ltac2 gd_tbl_P_x509_get_san_ext () : Init.string Init.list := ["Corelib.Init.Datatypes.list"; "Corelib.Numbers.BinNums.Z"; "stdpp.bitvector.definitions.bv"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "Corelib.Init.Datatypes.option"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.HST"; "RocqVerifyHarness.AgentSubmission.U.UImg.usegs"; "RocqVerifyHarness.AgentSubmission.U.U_x509_get_san_ext_A.ninv"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.Spec.RepFacts.seq_cells"; "Corelib.Init.Logic.or"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "Corelib.Init.Datatypes.nil"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.add"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "stdpp.bitvector.definitions.Z_to_bv"; "Stdlib.ZArith.BinInt.Z.lt"; "RocqVerifyHarness.AgentSubmission.Lib.AEvt.aevtM"; "RocqVerifyHarness.AgentSubmission.U.U_x509_get_san_ext_A.x509_get_san_ext_post"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "stdpp.bitvector.definitions.bv_unsigned"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.HEAP"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.bytes_at"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.heap_layout"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.heap_iface"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_calloc"; "RocqVerifyHarness.AgentSubmission.U.U_x509_get_name_A.U_CALLOC"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_free"; "RocqVerifyHarness.AgentSubmission.U.U_asn1_free_named_data_list_shallow.U_FREE"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_stack"; "RocqVerifyHarness.AgentSubmission.U.U_x509_get_san_ext_A.x509_get_san_ext_stmt"; "RocqVerifyHarness.AgentSubmission.U.U_x509_get_san_ext_A.U_X509_GET_SAN_EXT"].


Section Walk.
  Variable L : heap_layout.
  Variable HI : heap_iface usegs L.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model)
            (h : HST usegs L HI) (LB : list blk) (PP CUR P END BUF lo : Z) (bs : list byte).
  Notation CTX := (ext_ctx usegs L HI U_CALLOC U_FREE sp tp h LB PP CUR P END BUF lo bs).
  Hypothesis HC : CTX.

  Notation X := [(PP, PP + 8); (CUR, CUR + 32)].
  Notation POST := (x509_get_san_ext_post usegs L HI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc h LB PP CUR P END BUF lo m mo).
  Notation SPF := (Z_to_bv 64 (bv_unsigned sp + -224)).
  Notation INV := (ninv L HI ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m mo h LB PP CUR END BUF lo bs).
  Notation K4W := (Z_to_bv 64 (-9570)) (only parsing).
  Notation K7W := (Z_to_bv 64 (-9472)) (only parsing).
  Notation K8W := (Z_to_bv 64 (-8320)) (only parsing).
  Notation K9W := (Z_to_bv 64 (-9578)) (only parsing).
  Let sync_W' := sync_W L HI sp tp m h LB PP CUR P END BUF lo bs HC.
  Let presx_W' := presx_W L HI sp tp m h LB PP CUR P END BUF lo bs HC.
  Let heap_W' := heap_W L HI sp tp h LB PP CUR P END BUF lo bs HC.
  Let snoc_facts' := snoc_facts L HI sp tp h LB PP CUR P END BUF lo bs HC.
  Let others_apart' := others_apart L HI sp tp h LB PP CUR P END BUF lo bs HC.
  Let cur_wrange' := cur_wrange L HI sp tp h LB PP CUR P END BUF lo bs HC.
  Let headrep_pres' := headrep_pres L HI sp tp h LB PP CUR P END BUF lo bs HC.
  Let headrep_presx' := headrep_presx L HI sp tp h LB PP CUR P END BUF lo bs HC.
  Let presx_call' := presx_call L HI sp tp h LB PP CUR P END BUF lo bs HC.
  Let cur_cases' := cur_cases L HI sp tp h LB PP CUR P END BUF lo bs HC.
  Let in_block_below' := in_block_below L HI sp tp h LB PP CUR P END BUF lo bs HC.
  Let close_nodes' := close_nodes sp LB PP CUR END BUF lo bs.
  Let headrep_snoc' := headrep_snoc sp PP CUR END BUF lo bs.
  Let presx_munch' := presx_munch L sp LB PP CUR.

  (* [comment removed for export] *)
  Ltac flia := first [clear_disj; lia | lia].
  Lemma zbv_mod64 : forall a b, (a - b) mod 18446744073709551616 = 0 -> (Z_to_bv 64 a : word) = Z_to_bv 64 b.
  Proof.
    intros a b H. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with 18446744073709551616.
    apply Z.mod_divide in H; [| lia]. destruct H as [k Hk]. replace a with (b + k * 18446744073709551616) by lia. apply Z.mod_add. lia.
  Qed.
  Ltac spine_firstn k cs :=
    let k := eval cbv in k in
    lazymatch k with
    | Datatypes.O => eval lazy beta iota delta [firstn] in (firstn Datatypes.O cs)
    | Datatypes.S ?k' => lazymatch cs with
               | ?c :: ?cs' => let r := spine_firstn k' cs' in constr:(c :: r)
               | _ => eval cbv beta iota delta [firstn] in (firstn k cs)
               end
    end.
  Ltac spine_skipn k cs :=
    let k := eval cbv in k in
    lazymatch k with
    | Datatypes.O => cs
    | Datatypes.S ?k' => lazymatch cs with
               | _ :: ?cs' => spine_skipn k' cs'
               | _ => eval cbv beta iota delta [skipn] in (skipn k cs)
               end
    end.
  Ltac zofnat H := cbn [cells_size csize Nat.add length] in H;
    repeat match type of H with context [Z.of_nat (Datatypes.S ?k)] => let v := eval vm_compute in (Z.of_nat (Datatypes.S k)) in change (Z.of_nat (Datatypes.S k)) with v in H end;
    repeat match type of H with context [Z.add (Z.add ?a ?b) ?c] => is_Zlit b; is_Zlit c; let v := eval vm_compute in (Z.add b c) in replace (Z.add (Z.add a b) c) with (Z.add a v) in H by lia end.
  Ltac splitat H k H2 :=
    lazymatch type of H with rw_cells ?sg ?mm ?A0 ?cs =>
      let l1 := spine_firstn k cs in
      let l2 := spine_skipn k cs in
      change (rw_cells sg mm A0 (l1 ++ l2)) in H;
      let H1 := fresh "SP" in
      destruct (proj1 (rw_cells_app sg mm A0 l1 l2) H) as [H1 H2]; clear H; rename H1 into H; zofnat H2
    end.

  (* [comment removed for export] *)
  Definition BodyOb (p : Z) : Prop :=
    forall (nodes : list Z) (cur : Z) (ct cpad : word) (cl cp : Z) (j0 : list byte) (fb fs : list cell) (tl : word)
      (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) (mm : mem) (moc : Model) (hc : HST usegs L HI),
    INV mm moc hc nodes cur j0 fb fs tl -> rw_cells usegs mm cur (seq_cells ct cpad cl cp 0) ->
    (cp = 0 /\ cl = 0 /\ nodes = []) \/ (BUF <= cp /\ 0 <= cl /\ cp + cl <= END) ->
    rw_cells usegs mm PP [C8 (Z_to_bv 64 p)] -> P <= p -> p < END ->
    aevtM usegs moc POST
      (MS (mkR x1 SPF gp tp x5 x6 x7 (Z_to_bv 64 CUR) (Z_to_bv 64 END) x10 x11 x12 x13 x14 x15 x16 x17
             (Z_to_bv 64 (-9570)) (Z_to_bv 64 PP) (Z_to_bv 64 (-1)) (Z_to_bv 64 cur) (Z_to_bv 64 128) (Z_to_bv 64 4)
             (Z_to_bv 64 (-9472)) (Z_to_bv 64 (-8320)) (Z_to_bv 64 (-9578)) (Z_to_bv 64 p) x28 x29 x30 x31)
          F (Z_to_bv 64 0x2880c) fc None mm (seg_rom usegs))
(* [comment removed for export] *).
  Let exit_walk' := exit_walk L HI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo h LB PP CUR P END BUF lo bs HC.
  Let body_walk' := body_walk L HI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo h LB PP CUR P END BUF lo bs HC.

  Lemma loops : forall (k : nat) (p : Z), END - p < Z.of_nat k -> BodyOb p.
  Proof.
    induction k as [|k IH]; intros p Hk.
    - unfold BodyOb. intros. exfalso. clear -Hk H4. lia.
    - apply body_walk'. intros p' Hp'. apply IH. clear -Hk Hp'. lia.
  Qed.

  Lemma body_start : forall p, BodyOb p.
  Proof. intros p. apply (loops (Z.to_nat (END - p + 1))). clear. lia. Qed.

  Lemma main_walk : ltac2:(CDefT.buildp (gd_tbl_P_x509_get_san_ext ()) "Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)Pct,(2.&40.)Pcpad,(2.&40.)P,(1<.$7.VL,VHI,Vh,VLB,Vm,Vmo,)P,(9.$7.Vm,VPP,(11.$3.(12.(13.&40.VP,))(>.$3.)))P,(9.$7.Vm,VCUR,(:.R4.R3.===))P,(1=.$7.Vm,VBUF,Vbs,)P,(1>.$7.Vm,Vlo,(19.&40.Vsp,))P,(1?.$7.Vm,)P,(?.VP,VEND,)(15.$7.Vmo,(16.$7.VL,VHI,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VPP,VCUR,VP,VEND,VBUF,Vlo,Vm,Vmo,)(17.(18.Vra,Vsp,Vgp,Vtp,R15.R14.R13.Vs0,Vs1,(13.&40.VPP,)(13.&40.VEND,)(13.&40.VCUR,)R12.R11.R10.R?.R>.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R=.R<.R;.R:.)VF,(13.&40.+28790.)Vfc,(1:.(2.&40.))Vm,(1;.$7.)))")
(* [comment removed for export] *).
  Proof.
    intros t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 ct cpad HH HPP HCUR HBUF ST MI HPE.
    open_ectx HC. pose proof (heap_mok _ _ HI _ _ _ _ HH) as MK. unfold seq_cells in HCUR.
    pose proof (bytes_at_bound _ _ _ _ HBUF) as BB.
    assert (HCF0 : curF sp PP CUR BUF lo bs [] CUR).
    { unfold curF. split; [exact AL2|]. split; [exact NZ2|]. split; [clear -CURB; lia|]. split; [exact D1|]. split; [exact D3|].
      split; [exact DS2|]. left; split; reflexivity. }
    assert (HFR0 : nfresh L LB []) by (intros y Hy; destruct Hy).
    (* [comment removed for export] *)
    carve_frame 224%nat ST.
    lazymatch type of FR with rw_cells ?sg ?mx ?A [CB 224 ?j] =>
      set (JJ := j) in FR; clearbody JJ;
      change (rw_cells sg mx A ([] ++ CB 224 JJ :: [])) in FR;
      apply (rw_cells_split_CB sg mx A [] 224 JJ [] [8; 24; 80; 8; 104]%nat) in FR; [| reflexivity]; cbn [mk_CB_cells app] in FR
    end.
    lazymatch type of FR with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: _) => cb8_to_c8 FR [c0; c1; c2] end.
    lazymatch type of FR with rw_cells _ _ _ [?c0; ?c1; ?c2; C8 ?w; ?c4] => set (tl0 := w) in FR; clearbody tl0 end.
    (* [comment removed for export] *)
    assert (LXSUMS : forall AL, Forall (summary_okG usegs AL []) (@nil summary)) by (intros AL; constructor).
    rewrite TP. apply (lxp_aevtM_of_evt usegs mo _ _ MK).
    lx_run_tac (PLANS [0x2880c; 0x2890c] [] 60%N (@nil summary)); lx_tree.
    all: apply evt_done; cbv beta; rewrite <- TP.
    (* [comment removed for export] *)
    all: repeat match goal with |- context [Z_to_bv 64 (Zpos ?p)] =>
           let z := constr:(Zpos p) in
           lazymatch eval compute in (Z.leb (2^63) z) with
           | true => let z' := eval compute in (z - 2^64)%Z in replace (Z_to_bv 64 z : word) with (Z_to_bv 64 z' : word) by (apply zbv_mod64; reflexivity)
           end end.
    all: lazymatch goal with |- aevtM _ _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ ?mx _) =>
         lazymatch goal with Hm1 : munch ?W1 m mx, Hw1 : wmono _ m mx, HF : rw_cells _ mx (bv_unsigned sp + -224) _, HP : rw_cells _ mx PP _,
                             HC0 : rw_cells _ mx CUR _, STx : stk _ mx lo _, MIx : mem_inv _ mx, HB : bytes_at _ mx BUF bs |- _ =>
           let MUW := fresh "MUW" in
           assert (MUW : munch (W sp PP CUR) m mx) by (eapply munch_weaken; [| exact Hm1]; intros xw Hxw; clear - Hxw; cbn [outside W] in Hxw |- *; lia);
           pose proof (heap_W' [] CUR h (nLBof LB []) _ _ mo HFR0 HCF0 HH eq_refl ltac:(intros b Hb; exact Hb) MUW Hw1) as HH1;
           pose proof (presx_W' [] CUR _ _ HFR0 HCF0 MUW Hw1 (heap_presx_refl usegs L LB (bv_unsigned sp) X m)) as HPX1;
           let HB2 := fresh "FB" in let HS2 := fresh "FS" in let HT2 := fresh "FT" in let HR2 := fresh "FRH" in
           splitat HF 1%nat HB2; splitat HB2 1%nat HS2; splitat HS2 1%nat HT2; splitat HT2 1%nat HR2;
           lazymatch type of HF with rw_cells _ _ _ [CB 8 ?j0] =>
           lazymatch type of HB2 with rw_cells _ _ _ ?fb =>
           lazymatch type of HS2 with rw_cells _ _ _ ?fs =>
           lazymatch type of HT2 with rw_cells _ _ _ [C8 ?tl] =>
             assert (INV1 : INV mx mo h [] CUR j0 fb fs tl);
             [ unfold ninv; repeat match goal with |- _ /\ _ => split end; try assumption; try reflexivity;
               solve [constructor | left; reflexivity | exact I | apply mo_frame_refl | unfold frame_hi; exact HR2]
             | lazymatch pc with
               | 166156 => eapply exit_walk'; [exact INV1| exact HC0| left; split; [reflexivity|]; split; reflexivity| exact HP| clear - HPE B1; flia]
               | _ => eapply (body_start P); [exact INV1| exact HC0| left; split; [reflexivity|]; split; reflexivity| exact HP| clear; lia| flia]
               end ]
           end end end end
         end end.
  Qed.
End Walk.

Lemma U_x509_get_san_ext_spec : ltac2:(CDefT.buildp (gd_tbl_P_x509_get_san_ext ()) "PL,$20.PHI,(21.$7.R1.)P,(=.$1.(22.R2.)$23.)P,(=.$1.(24.R3.)$25.)P,(?.=(26.R4.))(27.$7.R5.R4.$28.)")
(* [comment removed for export] *).
Proof.
  intros L HI HCALLOC HFREE HLS. unfold x509_get_san_ext_stmt, U_X509_GET_SAN_EXT.
  intros until cpad. intros HH HPP HCUR HBUF B1 B2 B3 B4 D1 D2 D3 AL1 AL2 NZ1 NZ2 NZ3 ST SLO ACL HTOP SPA DHI DIM1 DIM2 DS1 DS2 DS3
    CWPP CWCUR CRBUF TP MI -> -> ->.
  pose proof alloc_ceiling_pos as ACP.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof (rw_cells_bound _ _ _ _ HPP) as PPB. pose proof (rw_cells_bound _ _ _ _ HCUR) as CURB.
  cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ seq_cells] in PPB, CURB.
  change (Z.of_nat 8) with 8 in PPB. change (Z.of_nat 32) with 32 in CURB.
  destruct (heap_blocks _ _ HI _ _ _ _ HH) as [HBR0 _].
  eapply main_walk; try eassumption.
  unfold ext_ctx. repeat match goal with |- _ /\ _ => split end; try assumption; try eassumption; dlia.
Qed.

