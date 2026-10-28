(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk AStep CellsX Image Asn1Aux Asn1AuxA X509Aux X509AuxB.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts RepName.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg U_string U_oid U_asn1_get_tag U_asn1_get_len U_asn1_free_named_data_list_shallow U_asn1_get_sequence_of_A U_x509_get_name_A U_x509_get_name U_x509_parse_san_A.
Import ListNotations.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
Local Ltac dlia ::= orc_dlia. (* [comment removed for export] *)
Local Ltac plia ::= orc_plia. (* [comment removed for export] *)
Local Ltac lia_nodisj ::= orc_dlia. (* [comment removed for export] *)
Local Ltac clear_disj ::= fc_clear_disj. (* [comment removed for export] *)
Local Ltac prune_disj ::= fc_prune_disj. (* [comment removed for export] *)
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section Walk.
  Variable L : heap_layout.
  Variable HI : heap_iface usegs L.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model)
            (h : HST usegs L HI) (LB : list blk) (SB SAN BUF sp0 slen lo : Z) (bs : list byte).
  Notation CTX := (san_ctx usegs L HI U_CALLOC U_FREE sp tp h LB SB SAN BUF sp0 slen lo bs).
  Hypothesis HC : CTX.

  Notation X := [(SAN, SAN + 80)].
  Notation W := [(SAN, SAN + 80); (bv_unsigned sp - 80, bv_unsigned sp)].
  Notation POST := (x509_parse_san_post usegs L HI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc h LB SAN lo m mo).
  Notation SPF := (Z_to_bv 64 (bv_unsigned sp + -80)).
  Let epi_walk' := epi_walk L HI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo h LB SB SAN BUF sp0 slen lo bs HC.
  Let IBB := in_block_below' L HI sp tp h LB SB SAN BUF sp0 slen lo bs HC.
  Let heap_W' := heap_W L HI sp tp mo h LB SB SAN BUF sp0 slen lo bs HC.
  Let presx_W' := presx_W L HI sp tp m h LB SB SAN BUF sp0 slen lo bs HC.
  (* [comment removed for export] *)
  Ltac call_memset :=
    let SPM := fresh "SPM" in
    pose proof U_memset_spec as SPM; unfold memset_stmt in SPM;
    lazymatch goal with
    | |- aevtM ?segs _ _ (MS _ _ _ _ _ ?mx _) =>
        eapply aevtM_cut_evt;
        [ eassumption
        | eapply SPM; rewrite ?(unsigned_lit SAN) by dlia; rewrite ?(unsigned_lit 80) by (clear; lia); try eassumption
        | unfold memset_post; rewrite ?(unsigned_lit SAN) by dlia; rewrite ?(unsigned_lit 80) by (clear; lia);
          rewrite ?(unsigned_lit 0) by (clear; lia); post_call segs mx ]
    end;
    clear SPM;
    match goal with H : rw_cells _ _ SAN _ |- _ => change (Z.to_nat 80) with 80%nat in H; change (0 mod 256) with 0 in H end.


  (* [comment removed for export] *)
  Ltac ro_const A n RO :=
    lazymatch goal with |- context [MS _ _ _ _ _ ?mx (seg_rom ?sg)] =>
      let bs := eval vm_compute in (match image_bytes sg A n with Some bs => bs | None => [] end) in
      match goal with MI : mem_inv sg mx |- _ =>
        pose proof (ro_image_bytes_at sg mx A bs MI ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia)) as RO end
    end.

  (* [comment removed for export] *)
  Ltac san_t0 HSAN :=
    lazymatch type of HSAN with rw_cells ?sg ?mx ?A _ =>
      apply (rw_cells_zeros sg mx A 80 [C4 (Z_to_bv 64 0); CB 76 (repeat (Z_to_bv 8 0) 76)]) in HSAN;
        [| cbn; repeat split; reflexivity | reflexivity] end.
  Ltac chk :=
    let K := fresh "K" in if_cases K; zify_cond K;
    [ exfalso; rewrite ?land_7_mod in K; first [ clear_disj; lia | lia ] | clear K ].

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00<0@D11834415701.107D22528871402.105D31913816407.105D34576298468.105D45644163930.107D8602834927.105 L11834415701.103L34603895532.0  L44422694039.100L45644163930.103L46932555819.100L9219470451.100 00000100G00\01101201C02K02L02Z03H03V03dFS2sp2SB3SAN2bs4SANB2HBS2sp2SB3SAN2bs3NZS2HBS2sp2SB3SAN2bs3NZS2HBFS2sp2SB3SAN2bs2HBS1L2sp2SB3SAN2lo2bs1t3HLS4NZSB3NZS3SLO2HD3SPR2HB5Ha_st5Hl_st2w04slen3sp0SS2sp2SB3SAN2bsS2sp2SB3SAN2bs1t2HD2HB5Ha_st5Hl_st2w04slen3sp0S2sp2SB3SAN2bsS2sp2SB3SAN2bs". (* [comment removed for export] *)
  #[using="BUF bs HC epi_walk'"] Lemma copy_walk : forall (t : Z) (junk : list byte) (w0 pw lw : word)
                           (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x28 x29 x30 x31 : word) mm,
    rw_cells usegs mm (bv_unsigned sp + -80) [C8 pw; C8 lw; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    rw_cells usegs mm SB [C8 w0; C8 (Z_to_bv 64 slen); C8 (Z_to_bv 64 sp0)] ->
    rw_cells usegs mm SAN [CB 80 junk] ->
    stk usegs mm lo (bv_unsigned sp + -80) -> mem_inv usegs mm ->
    munch W m mm -> wmono usegs m mm -> HEAP usegs L HI h LB m mo ->
    0 <= t <= 7 -> t <> 4 ->
    aevtM usegs mo POST
      (MS (mkR x1 SPF gp tp x5 x6 x7 (Z_to_bv 64 SAN) (Z_to_bv 64 SB) (Z_to_bv 64 t) x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x28c20) fc None mm (seg_rom usegs)).
  Proof.
    intros t junk w0 pw lw x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x28 x29 x30 x31 mm FR HSB HSAN ST MI MU WM HH Ht0 Ht.
    open_sctx HC. pose proof (heap_mok _ _ HI _ _ _ _ HH) as MK.
    zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    eapply epi_walk'; try eassumption. { clear; lia. } { cbn. reflexivity. }
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00C0@D12172635341.121D27154541347.123D43989901677.103D46043887455.121D57732555186.121L12172635341.117L18248671187.0  L32027975233.0  L35765468590.0  L43878674222.0  L45412166038.117L46043887455.117L46368229782.117L4832059926.117 L57732555186.117L58909126211.0  L6645327278.0   L66642082819.0  L68714284705.0  00000100E00\00]00^01201301401501601D01U01c02102\02]02^02_02`FS2sp2SB3SAN2bs3x331HS2sp2SB3SAN2bs3NZS4SANBFFS2sp2SB3SAN2lo2bs2HDSSSSS2sp2SB3SAN2bsS2sp2SB3SAN2bs2HDS2sp2SB3SAN2bsS2sp2SB3SAN2bsS1L2sp2SB3SAN2lo2bs3HLS4NZSB3NZS3SLO2HD3SPRSSSS". (* [comment removed for export] *)
  #[using="BUF bs HC epi_walk'"] Lemma ms_walk : forall (k : Z) (junk : list byte) (w0 pw lw : word)
                         (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x28 x29 x30 x31 : word) mm,
    rw_cells usegs mm (bv_unsigned sp + -80) [C8 pw; C8 lw; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    rw_cells usegs mm SB [C8 w0; C8 (Z_to_bv 64 slen); C8 (Z_to_bv 64 sp0)] ->
    rw_cells usegs mm SAN [CB 80 junk] ->
    stk usegs mm lo (bv_unsigned sp + -80) -> mem_inv usegs mm ->
    munch W m mm -> wmono usegs m mm -> HEAP usegs L HI h LB m mo ->
    (k = 0x28b4c \/ k = 0x28ad4 \/ k = 0x28c00) ->
    aevtM usegs mo POST
      (MS (mkR x1 SPF gp tp x5 x6 x7 (Z_to_bv 64 SAN) (Z_to_bv 64 SB) x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 k) fc None mm (seg_rom usegs)).
  Proof.
    intros k junk w0 pw lw x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x28 x29 x30 x31 mm FR HSB HSAN ST MI MU WM HH Hk.
    open_sctx HC. pose proof (heap_mok _ _ HI _ _ _ _ HH) as MK.
    destruct Hk as [-> | [-> | ->]].
    - zstep. zstep. zstep. zstep. call_memset. zstep. chk. zstep. zstep. chk. zstep. zstep. eapply copy_walk; try eassumption; clear; lia.
    - zstep. zstep. zstep. zstep. call_memset. zstep. chk. zstep. zstep. chk. zstep. zstep. eapply copy_walk; try eassumption; clear; lia.
    - zstep. zstep. zstep. zstep. call_memset. zstep. chk. zstep. zstep. chk. zstep. eapply copy_walk; try eassumption; clear; lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00Z0@D11834415701.119D11834415701.120D11834415701.121D12172635341.121D22528871402.117D22528871402.118D22528871402.119D27154541347.123D31913816407.117D34576298468.118D34576298468.119D43989901677.103D45644163930.119D45644163930.120D45644163930.121D46043887455.121D57732555186.121D8602834927.117 D8602834927.118 D8602834927.119 L11834415701.115L11834415701.116L11834415701.117L12172635341.117L32027975233.0  L34603895532.0  L38957038742.113L38959136532.112L40156088366.0  L44422694039.112L45644163930.115L45644163930.116L45644163930.117L46043887455.117L46932555819.112L57732555186.117L68533714012.0  L68621752726.117L68714284705.0  L7232946611.0   L9219470451.113 L9219470451.114 00000100200300400J00`01601J01_02402I02`02a02b02c02d02e03603G03X04R05X06^07207307407l08d08e09309S0:?0:k0;<0;J0<50<60<D0<E0<F0<T0<bFFFFS2sp2SB3SAN2bs4SANB2HBS2sp2SB3SAN2bs4SANB2HBS2sp2SB3SAN2bs4SANB2HBS2sp2SB3SAN2bs3x331HS2sp2SB3SAN2bs3NZS2HBS2sp2SB3SAN2bs3NZS2HBS2sp2SB3SAN2bs3NZS2HBS2sp2SB3SAN2bs3NZS4SANBFFFFFS2sp2SB3SAN2bs2HBS2sp2SB3SAN2bs2HBS2sp2SB3SAN2bs2HBS1L2sp2SB3SAN2lo2bs3HLS4NZSB3NZS3SLO2HD3SPR2HB5Ha_st5Hl_stS1L2sp2SB3SAN3sp02lo2bs3HLS4NZSB3NZS3SLO2HD3SPR2HB5Ha_st5Hl_st4slen2w0S1L2sp2SB3SAN3sp02lo2bs3HLS4NZSB3NZS3SLO2HD3SPR2HB5Ha_st5Hl_st4slen2w0S2sp2SB3SAN2lo2bs2HDSSS2sp2SB3SAN3BUF3sp04slen2bs2B12B22B32B44NZSB3NZS3NZB3SPRS2sp2SB3SAN3BUF3sp04slen2bs2B12B22B32B44NZSB3NZS3NZB3SPRSS2sp2SB3SAN2bsS2sp2SB3SAN2bs2HD2HB5Ha_st5Hl_stS2sp2SB3SAN3sp02bs2HD2HB5Ha_st5Hl_st4slen2w0S2sp2SB3SAN3sp02bs2HD2HB5Ha_st5Hl_st4slen2w0S2sp2SB3SAN2bs2HDS2sp2SB3SAN2bsS1L2sp2SB3SAN2lo2bs3HLS4NZSB3NZS3SLO2HD3SPRSS2sp2SB3SAN2bsSSS2sp2SB3SAN2bsS2sp2SB3SAN2bs". (* [comment removed for export] *)
  #[using="BUF bs HC epi_walk'"] Lemma ip_walk : forall (junk : list byte) (w0 pw lw : word)
                         (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x28 x29 x30 x31 : word) mm,
    rw_cells usegs mm (bv_unsigned sp + -80) [C8 pw; C8 lw; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    rw_cells usegs mm SB [C8 w0; C8 (Z_to_bv 64 slen); C8 (Z_to_bv 64 sp0)] ->
    rw_cells usegs mm SAN [CB 80 junk] ->
    stk usegs mm lo (bv_unsigned sp + -80) -> mem_inv usegs mm ->
    munch W m mm -> wmono usegs m mm -> HEAP usegs L HI h LB m mo ->
    aevtM usegs mo POST
      (MS (mkR x1 SPF gp tp x5 x6 x7 (Z_to_bv 64 SAN) (Z_to_bv 64 SB) x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x28af8) fc None mm (seg_rom usegs)).
  Proof.
    intros junk w0 pw lw x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x28 x29 x30 x31 mm FR HSB HSAN ST MI MU WM HH.
    open_sctx HC. pose proof (heap_mok _ _ HI _ _ _ _ HH) as MK.
    zstep. zstep. zstep. zstep. call_memset. zstep. chk. zstep. zstep. chk.
    zstep. zstep. zstep. zstep. zstep. if_cases K16; zify_cond K16.
    - (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
      eapply epi_walk'; try eassumption. { clear; lia. } { cbn. reflexivity. } { clear; lia. } { clear; lia. }
    - zstep. zstep. if_cases K4; zify_cond K4.
      { (* [comment removed for export] *)
        zstep. zstep. zstep.
        try replace (Z_to_bv 64 18446744073709541376) with (Z_to_bv 64 (-10240)) by (apply bv_eq; reflexivity).
        eapply epi_walk'; try eassumption. { clear; lia. } { cbn. reflexivity. } { clear; lia. } { clear; lia. } }
      zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
      eapply epi_walk'; try eassumption. { clear; lia. } { cbn. reflexivity. } { clear; lia. } { clear; lia. }
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End Walk.
