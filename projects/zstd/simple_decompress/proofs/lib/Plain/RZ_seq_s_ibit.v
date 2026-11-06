(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdFrameThm ZdDCtx ZdSeqTable.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit MemRange ZdWalkKit ZdDctxRep ZdSeqW ZdTbl KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXPost.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import KXLean KXLeanAll.   (* [comment removed for export] *)
From OSSVerify.Proofs.zstd.simple_decompress.lib.Plain Require Import PImg F_memcpy F_memmove RZ_seq_iface RZ_seq_kit RZ_seq_gkit RZ_seq_s_base RZ_seq_s_lbase RZ_seq_s_lkit RZ_seq_s_ibase RZ_seq_s_iexit.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma zbv_mod : forall z, Z_to_bv 64 z = Z_to_bv 64 (z mod 2^64).
Proof. intros z. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2^64). rewrite Z.mod_mod by lia. reflexivity. Qed.

Lemma seqs_bitinit : forall P OEND LLO LEND LOCV, seqs_static P OEND LLO LEND LOCV -> seqs_ranges P -> ai_i1 P OEND LLO LEND LOCV -> ai_i0 P OEND LLO LEND LOCV.
Proof.
  intros P OEND LLO LEND LOCV ST RG0 CONT. unfold ai_i0.
  intros m1 p0 p1 p2 w_c0 w_c8 w_c16 w_c24 w_c32 w_c40 w_c48 w_c88 w_c96 w_c104 w_c112 w_c120 w_c128 w_c136 w_c144 w_c152 w_c160 w_c168 jpad jseq x1 x5 x6 x7 x8 x9 x10 x11 x12 x15 x16 x17 x19 x21 x22 x27 x28 x29 x31 INV.
  pose proof (seqs_iinv_frame P OEND LLO LEND LOCV m1 _ ST INV) as TRANS.
  pose proof (seqs_iexit P OEND LLO LEND LOCV) as IEXIT.
  pose proof (seqs_iinv_mi _ _ _ _ _ _ _ INV) as MI.
  unfold ai_i1 in CONT.
  destruct INV as (FR & _ & _ & _ & _ & SQB & _).
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws].
  cbn [seqs_static seqs_post v_ra v_gp v_tp v_s0 v_s1 v_s2 v_s3 v_s4 v_s5 v_s6 v_s7 v_s8 v_s9 v_s10 v_s11 v_F v_fc v_m v_SPV v_lo v_DCTX v_DST v_CAP v_B0 v_B1 v_SEQ v_nbSeq v_LLT v_MLT v_OFT v_PFX v_LITP v_LBE v_LITB v_LOC v_sq v_tLL v_tOF v_tML v_huf v_r0 v_r1 v_r2 v_pde v_dend v_expd v_pcs v_dsz v_bt v_stg v_le v_fe v_ws] in ST, FR, SQB, CONT, TRANS |- *.
  sd_static_open ST.
  remember (map (Z_to_bv 8) sq) as sqb eqn:Esqb. remember (zlen sq) as n eqn:En.
  assert (LSQ : Z.of_nat (length sqb) = n) by (subst sqb n; rewrite length_map; reflexivity).
  assert (MUL : munch [(SPV - 336, SPV)] m1 m1) by apply munch_refl. assert (WMl : wmono psegs m1 m1) by apply wmono_refl.
  assert (DJ : SPV - 336 + 336 <= SEQ \/ SEQ + n <= SPV - 336) by (unfold held in S25; clear - S25 S18; lia).
  assert (RG : 4096 <= OEND < 2^47 /\ 4096 <= DCTX < 2^47) by (clear - S1 S2 S3 S4 S5 S6 S7 S19 S20; lia).
  assert (CASES : 8 <= n \/ n = 1 \/ n = 2 \/ n = 3 \/ n = 4 \/ n = 5 \/ n = 6 \/ n = 7) by (clear - S15; lia).
  destruct CASES as [C|[C|[C|[C|[C|[C|[C|C]]]]]]].
  - try hold TRANS. try hold CONT. try hold IEXIT. try hold RG0. try hold Esqb. try hold S1. try hold S2. try hold S3. try hold S4. try hold S5. try hold S6. try hold S7. try hold S8. try hold S9. try hold S10. try hold S11. try hold S12. try hold S15. try hold S16. try hold S18. try hold S19. try hold S20. try hold S21. try hold S22. try hold S23. try hold S24. try hold S25. try hold S26. try hold S27. try hold S28. try hold S29. try hold S30. try hold S31. try hold S32. try hold S33. try hold S34. try hold S35. try hold S36. try hold S37. try hold S38. try hold S39. try hold S40. try hold S41. try hold S42. try hold OKLL. try hold OKOF. try hold OKML.
    kx_autoLx [0x19afc; 0x1a5ec] 120%nat
    [KZRange SPV 544 (2^47); KZRange SEQ 4096 (2^47); KZRange n 8 (2^47); KZRange (SEQ + n) 4096 (2^47); KZRange OEND 4096 (2^47); KZRange DCTX 4096 (2^47);
     KZWr (SPV - 336) 336; KZDisj (SPV - 336) 336 SEQ n; KZImg 0x10000 0x14000]
    [(SEQ, n)].
    all: kx_mem.
    all: (try unfold held in TRANS; try unfold held in CONT; try unfold held in IEXIT; try unfold held in RG0; try unfold held in Esqb; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S15; try unfold held in S16; try unfold held in S18; try unfold held in S19; try unfold held in S20; try unfold held in S21; try unfold held in S22; try unfold held in S23; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in S36; try unfold held in S37; try unfold held in S38; try unfold held in S39; try unfold held in S40; try unfold held in S41; try unfold held in S42; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end).
    all: lazymatch goal with
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1a5ec) _ _ _ _) =>
          eapply IEXIT; [exact RG0 | eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR] | reflexivity | reflexivity | lia | left; reflexivity]
      | |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 (bv_unsigned (edenot ?E ?e))) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ (Z_to_bv 64 0x19afc) _ _ _ _) =>
          let BCE := fresh "BCE" in let B1 := fresh "B1" in let B2 := fresh "B2" in
          kx_read_ranges;
          lazymatch e with context [EVar ?j] => kx_enum BCE E e j 1 255%nat (fun v => (1 <=? v) && (v <=? 64))%bool end;
          cbv beta in BCE; apply andb_prop in BCE as [B1 B2]; apply Z.leb_le in B1, B2;
          eapply CONT with (d := (n - 8));
          [ first [ eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR] | eapply seqs_iinv_eq; [eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR] | repeat f_equal; lia] ]
          | split; [split; [lia | exact B2] | unfold bit_ok; cbn [v_SEQ v_sq]; rewrite <- En; intros; lia]
          | cbn [v_SEQ]; lia ]
      | |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 (-1 * Z.lxor (bv_unsigned (edenot ?E ?e)) 31 + 8)) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ (Z_to_bv 64 0x19afc) _ _ _ _) =>
          let BCE := fresh "BCE" in let B1 := fresh "B1" in let B2 := fresh "B2" in
          kx_read_ranges;
          lazymatch e with context [EVar ?j] => kx_enum BCE E e j 1 255%nat (fun v => (1 <=? -1 * Z.lxor v 31 + 8) && (-1 * Z.lxor v 31 + 8 <=? 8))%bool end;
          cbv beta in BCE; apply andb_prop in BCE as [B1 B2]; apply Z.leb_le in B1, B2;
          eapply CONT with (d := (n - 8));
          [ first [ eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR] | eapply seqs_iinv_eq; [eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR] | repeat f_equal; lia] ]
          | split; [split; [lia | lia] | unfold bit_ok; cbn [v_SEQ v_sq]; rewrite <- En; intros; lia]
          | cbn [v_SEQ]; lia ]
      | |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 (bv_unsigned (edenot ?E ?e) + 41)) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ (Z_to_bv 64 0x19afc) _ _ _ _) =>
          let BCE := fresh "BCE" in let B1 := fresh "B1" in let B2 := fresh "B2" in
          kx_read_ranges;
          lazymatch e with context [EVar ?j] => kx_enum BCE E e j 1 255%nat (fun v => (1 <=? (v + 41) mod 2^64) && ((v + 41) mod 2^64 <=? 64))%bool end;
          cbv beta in BCE; apply andb_prop in BCE as [B1 B2]; apply Z.leb_le in B1, B2;
          rewrite (zbv_mod (bv_unsigned (edenot E e) + 41));
          eapply CONT with (d := (n - 8));
          [ first [ eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR] | eapply seqs_iinv_eq; [eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR] | repeat f_equal; lia] ]
          | split; [split; [lia | exact B2] | unfold bit_ok; cbn [v_SEQ v_sq]; rewrite <- En; intros; lia]
          | cbn [v_SEQ]; lia ]
      end.
  - rewrite C in *; clear C.
    try hold TRANS. try hold CONT. try hold IEXIT. try hold RG0. try hold Esqb. try hold S1. try hold S2. try hold S3. try hold S4. try hold S5. try hold S6. try hold S7. try hold S8. try hold S9. try hold S10. try hold S11. try hold S12. try hold S15. try hold S16. try hold S18. try hold S19. try hold S20. try hold S21. try hold S22. try hold S23. try hold S24. try hold S25. try hold S26. try hold S27. try hold S28. try hold S29. try hold S30. try hold S31. try hold S32. try hold S33. try hold S34. try hold S35. try hold S36. try hold S37. try hold S38. try hold S39. try hold S40. try hold S41. try hold S42. try hold OKLL. try hold OKOF. try hold OKML.
    kx_autoLx [0x19afc; 0x1a5ec] 120%nat
    [KZRange SPV 544 (2^47); KZRange SEQ 4096 (2^47);  KZRange (SEQ + 1) 4096 (2^47); KZRange OEND 4096 (2^47); KZRange DCTX 4096 (2^47);
     KZWr (SPV - 336) 336; KZDisj (SPV - 336) 336 SEQ 1; KZImg 0x10000 0x14000]
    [(SEQ, 1)].
    all: kx_mem.
    all: (try unfold held in TRANS; try unfold held in CONT; try unfold held in IEXIT; try unfold held in RG0; try unfold held in Esqb; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S15; try unfold held in S16; try unfold held in S18; try unfold held in S19; try unfold held in S20; try unfold held in S21; try unfold held in S22; try unfold held in S23; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in S36; try unfold held in S37; try unfold held in S38; try unfold held in S39; try unfold held in S40; try unfold held in S41; try unfold held in S42; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end).
    all: lazymatch goal with
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1a5ec) _ _ _ _) =>
          eapply IEXIT; [exact RG0 | eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR] | reflexivity | reflexivity | lia | left; reflexivity]
      | |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 (bv_unsigned (edenot ?E ?e))) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ (Z_to_bv 64 0x19afc) _ _ _ _) =>
          let BCE := fresh "BCE" in let B1 := fresh "B1" in let B2 := fresh "B2" in
          kx_read_ranges;
          lazymatch e with context [EVar ?j] => kx_enum BCE E e j 1 255%nat (fun v => (1 <=? v) && (v <=? 64))%bool end;
          cbv beta in BCE; apply andb_prop in BCE as [B1 B2]; apply Z.leb_le in B1, B2;
          eapply CONT with (d := 0);
          [ first [ eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR] | eapply seqs_iinv_eq; [eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR] | repeat f_equal; lia] ]
          | split; [split; [lia | exact B2] | unfold bit_ok; cbn [v_SEQ v_sq]; rewrite <- En; intros; lia]
          | cbn [v_SEQ]; lia ]
      | |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 (-1 * Z.lxor (bv_unsigned (edenot ?E ?e)) 31 + 8)) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ (Z_to_bv 64 0x19afc) _ _ _ _) =>
          let BCE := fresh "BCE" in let B1 := fresh "B1" in let B2 := fresh "B2" in
          kx_read_ranges;
          lazymatch e with context [EVar ?j] => kx_enum BCE E e j 1 255%nat (fun v => (1 <=? -1 * Z.lxor v 31 + 8) && (-1 * Z.lxor v 31 + 8 <=? 8))%bool end;
          cbv beta in BCE; apply andb_prop in BCE as [B1 B2]; apply Z.leb_le in B1, B2;
          eapply CONT with (d := 0);
          [ first [ eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR] | eapply seqs_iinv_eq; [eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR] | repeat f_equal; lia] ]
          | split; [split; [lia | lia] | unfold bit_ok; cbn [v_SEQ v_sq]; rewrite <- En; intros; lia]
          | cbn [v_SEQ]; lia ]
      | |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 (bv_unsigned (edenot ?E ?e) + 41)) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ (Z_to_bv 64 0x19afc) _ _ _ _) =>
          let BCE := fresh "BCE" in let B1 := fresh "B1" in let B2 := fresh "B2" in
          kx_read_ranges;
          lazymatch e with context [EVar ?j] => kx_enum BCE E e j 1 255%nat (fun v => (1 <=? (v + 41) mod 2^64) && ((v + 41) mod 2^64 <=? 64))%bool end;
          cbv beta in BCE; apply andb_prop in BCE as [B1 B2]; apply Z.leb_le in B1, B2;
          rewrite (zbv_mod (bv_unsigned (edenot E e) + 41));
          eapply CONT with (d := 0);
          [ first [ eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR] | eapply seqs_iinv_eq; [eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR] | repeat f_equal; lia] ]
          | split; [split; [lia | exact B2] | unfold bit_ok; cbn [v_SEQ v_sq]; rewrite <- En; intros; lia]
          | cbn [v_SEQ]; lia ]
      end.
  - rewrite C in *; clear C.
    try hold TRANS. try hold CONT. try hold IEXIT. try hold RG0. try hold Esqb. try hold S1. try hold S2. try hold S3. try hold S4. try hold S5. try hold S6. try hold S7. try hold S8. try hold S9. try hold S10. try hold S11. try hold S12. try hold S15. try hold S16. try hold S18. try hold S19. try hold S20. try hold S21. try hold S22. try hold S23. try hold S24. try hold S25. try hold S26. try hold S27. try hold S28. try hold S29. try hold S30. try hold S31. try hold S32. try hold S33. try hold S34. try hold S35. try hold S36. try hold S37. try hold S38. try hold S39. try hold S40. try hold S41. try hold S42. try hold OKLL. try hold OKOF. try hold OKML.
    kx_autoLx [0x19afc; 0x1a5ec] 120%nat
    [KZRange SPV 544 (2^47); KZRange SEQ 4096 (2^47);  KZRange (SEQ + 2) 4096 (2^47); KZRange OEND 4096 (2^47); KZRange DCTX 4096 (2^47);
     KZWr (SPV - 336) 336; KZDisj (SPV - 336) 336 SEQ 2; KZImg 0x10000 0x14000]
    [(SEQ, 2)].
    all: kx_mem.
    all: (try unfold held in TRANS; try unfold held in CONT; try unfold held in IEXIT; try unfold held in RG0; try unfold held in Esqb; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S15; try unfold held in S16; try unfold held in S18; try unfold held in S19; try unfold held in S20; try unfold held in S21; try unfold held in S22; try unfold held in S23; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in S36; try unfold held in S37; try unfold held in S38; try unfold held in S39; try unfold held in S40; try unfold held in S41; try unfold held in S42; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end).
    all: lazymatch goal with
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1a5ec) _ _ _ _) =>
          eapply IEXIT; [exact RG0 | eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR] | reflexivity | reflexivity | lia | left; reflexivity]
      | |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 (bv_unsigned (edenot ?E ?e))) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ (Z_to_bv 64 0x19afc) _ _ _ _) =>
          let BCE := fresh "BCE" in let B1 := fresh "B1" in let B2 := fresh "B2" in
          kx_read_ranges;
          lazymatch e with context [EVar ?j] => kx_enum BCE E e j 1 255%nat (fun v => (1 <=? v) && (v <=? 64))%bool end;
          cbv beta in BCE; apply andb_prop in BCE as [B1 B2]; apply Z.leb_le in B1, B2;
          eapply CONT with (d := 0);
          [ first [ eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR] | eapply seqs_iinv_eq; [eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR] | repeat f_equal; lia] ]
          | split; [split; [lia | exact B2] | unfold bit_ok; cbn [v_SEQ v_sq]; rewrite <- En; intros; lia]
          | cbn [v_SEQ]; lia ]
      | |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 (-1 * Z.lxor (bv_unsigned (edenot ?E ?e)) 31 + 8)) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ (Z_to_bv 64 0x19afc) _ _ _ _) =>
          let BCE := fresh "BCE" in let B1 := fresh "B1" in let B2 := fresh "B2" in
          kx_read_ranges;
          lazymatch e with context [EVar ?j] => kx_enum BCE E e j 1 255%nat (fun v => (1 <=? -1 * Z.lxor v 31 + 8) && (-1 * Z.lxor v 31 + 8 <=? 8))%bool end;
          cbv beta in BCE; apply andb_prop in BCE as [B1 B2]; apply Z.leb_le in B1, B2;
          eapply CONT with (d := 0);
          [ first [ eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR] | eapply seqs_iinv_eq; [eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR] | repeat f_equal; lia] ]
          | split; [split; [lia | lia] | unfold bit_ok; cbn [v_SEQ v_sq]; rewrite <- En; intros; lia]
          | cbn [v_SEQ]; lia ]
      | |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 (bv_unsigned (edenot ?E ?e) + 41)) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ (Z_to_bv 64 0x19afc) _ _ _ _) =>
          let BCE := fresh "BCE" in let B1 := fresh "B1" in let B2 := fresh "B2" in
          kx_read_ranges;
          lazymatch e with context [EVar ?j] => kx_enum BCE E e j 1 255%nat (fun v => (1 <=? (v + 41) mod 2^64) && ((v + 41) mod 2^64 <=? 64))%bool end;
          cbv beta in BCE; apply andb_prop in BCE as [B1 B2]; apply Z.leb_le in B1, B2;
          rewrite (zbv_mod (bv_unsigned (edenot E e) + 41));
          eapply CONT with (d := 0);
          [ first [ eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR] | eapply seqs_iinv_eq; [eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR] | repeat f_equal; lia] ]
          | split; [split; [lia | exact B2] | unfold bit_ok; cbn [v_SEQ v_sq]; rewrite <- En; intros; lia]
          | cbn [v_SEQ]; lia ]
      end.
  - rewrite C in *; clear C.
    try hold TRANS. try hold CONT. try hold IEXIT. try hold RG0. try hold Esqb. try hold S1. try hold S2. try hold S3. try hold S4. try hold S5. try hold S6. try hold S7. try hold S8. try hold S9. try hold S10. try hold S11. try hold S12. try hold S15. try hold S16. try hold S18. try hold S19. try hold S20. try hold S21. try hold S22. try hold S23. try hold S24. try hold S25. try hold S26. try hold S27. try hold S28. try hold S29. try hold S30. try hold S31. try hold S32. try hold S33. try hold S34. try hold S35. try hold S36. try hold S37. try hold S38. try hold S39. try hold S40. try hold S41. try hold S42. try hold OKLL. try hold OKOF. try hold OKML.
    kx_autoLx [0x19afc; 0x1a5ec] 120%nat
    [KZRange SPV 544 (2^47); KZRange SEQ 4096 (2^47);  KZRange (SEQ + 3) 4096 (2^47); KZRange OEND 4096 (2^47); KZRange DCTX 4096 (2^47);
     KZWr (SPV - 336) 336; KZDisj (SPV - 336) 336 SEQ 3; KZImg 0x10000 0x14000]
    [(SEQ, 3)].
    all: kx_mem.
    all: (try unfold held in TRANS; try unfold held in CONT; try unfold held in IEXIT; try unfold held in RG0; try unfold held in Esqb; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S15; try unfold held in S16; try unfold held in S18; try unfold held in S19; try unfold held in S20; try unfold held in S21; try unfold held in S22; try unfold held in S23; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in S36; try unfold held in S37; try unfold held in S38; try unfold held in S39; try unfold held in S40; try unfold held in S41; try unfold held in S42; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end).
    all: lazymatch goal with
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1a5ec) _ _ _ _) =>
          eapply IEXIT; [exact RG0 | eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR] | reflexivity | reflexivity | lia | left; reflexivity]
      | |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 (bv_unsigned (edenot ?E ?e))) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ (Z_to_bv 64 0x19afc) _ _ _ _) =>
          let BCE := fresh "BCE" in let B1 := fresh "B1" in let B2 := fresh "B2" in
          kx_read_ranges;
          lazymatch e with context [EVar ?j] => kx_enum BCE E e j 1 255%nat (fun v => (1 <=? v) && (v <=? 64))%bool end;
          cbv beta in BCE; apply andb_prop in BCE as [B1 B2]; apply Z.leb_le in B1, B2;
          eapply CONT with (d := 0);
          [ first [ eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR] | eapply seqs_iinv_eq; [eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR] | repeat f_equal; lia] ]
          | split; [split; [lia | exact B2] | unfold bit_ok; cbn [v_SEQ v_sq]; rewrite <- En; intros; lia]
          | cbn [v_SEQ]; lia ]
      | |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 (-1 * Z.lxor (bv_unsigned (edenot ?E ?e)) 31 + 8)) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ (Z_to_bv 64 0x19afc) _ _ _ _) =>
          let BCE := fresh "BCE" in let B1 := fresh "B1" in let B2 := fresh "B2" in
          kx_read_ranges;
          lazymatch e with context [EVar ?j] => kx_enum BCE E e j 1 255%nat (fun v => (1 <=? -1 * Z.lxor v 31 + 8) && (-1 * Z.lxor v 31 + 8 <=? 8))%bool end;
          cbv beta in BCE; apply andb_prop in BCE as [B1 B2]; apply Z.leb_le in B1, B2;
          eapply CONT with (d := 0);
          [ first [ eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR] | eapply seqs_iinv_eq; [eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR] | repeat f_equal; lia] ]
          | split; [split; [lia | lia] | unfold bit_ok; cbn [v_SEQ v_sq]; rewrite <- En; intros; lia]
          | cbn [v_SEQ]; lia ]
      | |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 (bv_unsigned (edenot ?E ?e) + 41)) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ (Z_to_bv 64 0x19afc) _ _ _ _) =>
          let BCE := fresh "BCE" in let B1 := fresh "B1" in let B2 := fresh "B2" in
          kx_read_ranges;
          lazymatch e with context [EVar ?j] => kx_enum BCE E e j 1 255%nat (fun v => (1 <=? (v + 41) mod 2^64) && ((v + 41) mod 2^64 <=? 64))%bool end;
          cbv beta in BCE; apply andb_prop in BCE as [B1 B2]; apply Z.leb_le in B1, B2;
          rewrite (zbv_mod (bv_unsigned (edenot E e) + 41));
          eapply CONT with (d := 0);
          [ first [ eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR] | eapply seqs_iinv_eq; [eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR] | repeat f_equal; lia] ]
          | split; [split; [lia | exact B2] | unfold bit_ok; cbn [v_SEQ v_sq]; rewrite <- En; intros; lia]
          | cbn [v_SEQ]; lia ]
      end.
  - rewrite C in *; clear C.
    try hold TRANS. try hold CONT. try hold IEXIT. try hold RG0. try hold Esqb. try hold S1. try hold S2. try hold S3. try hold S4. try hold S5. try hold S6. try hold S7. try hold S8. try hold S9. try hold S10. try hold S11. try hold S12. try hold S15. try hold S16. try hold S18. try hold S19. try hold S20. try hold S21. try hold S22. try hold S23. try hold S24. try hold S25. try hold S26. try hold S27. try hold S28. try hold S29. try hold S30. try hold S31. try hold S32. try hold S33. try hold S34. try hold S35. try hold S36. try hold S37. try hold S38. try hold S39. try hold S40. try hold S41. try hold S42. try hold OKLL. try hold OKOF. try hold OKML.
    kx_autoLx [0x19afc; 0x1a5ec] 120%nat
    [KZRange SPV 544 (2^47); KZRange SEQ 4096 (2^47);  KZRange (SEQ + 4) 4096 (2^47); KZRange OEND 4096 (2^47); KZRange DCTX 4096 (2^47);
     KZWr (SPV - 336) 336; KZDisj (SPV - 336) 336 SEQ 4; KZImg 0x10000 0x14000]
    [(SEQ, 4)].
    all: kx_mem.
    all: (try unfold held in TRANS; try unfold held in CONT; try unfold held in IEXIT; try unfold held in RG0; try unfold held in Esqb; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S15; try unfold held in S16; try unfold held in S18; try unfold held in S19; try unfold held in S20; try unfold held in S21; try unfold held in S22; try unfold held in S23; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in S36; try unfold held in S37; try unfold held in S38; try unfold held in S39; try unfold held in S40; try unfold held in S41; try unfold held in S42; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end).
    all: lazymatch goal with
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1a5ec) _ _ _ _) =>
          eapply IEXIT; [exact RG0 | eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR] | reflexivity | reflexivity | lia | left; reflexivity]
      | |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 (bv_unsigned (edenot ?E ?e))) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ (Z_to_bv 64 0x19afc) _ _ _ _) =>
          let BCE := fresh "BCE" in let B1 := fresh "B1" in let B2 := fresh "B2" in
          kx_read_ranges;
          lazymatch e with context [EVar ?j] => kx_enum BCE E e j 1 255%nat (fun v => (1 <=? v) && (v <=? 64))%bool end;
          cbv beta in BCE; apply andb_prop in BCE as [B1 B2]; apply Z.leb_le in B1, B2;
          eapply CONT with (d := 0);
          [ first [ eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR] | eapply seqs_iinv_eq; [eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR] | repeat f_equal; lia] ]
          | split; [split; [lia | exact B2] | unfold bit_ok; cbn [v_SEQ v_sq]; rewrite <- En; intros; lia]
          | cbn [v_SEQ]; lia ]
      | |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 (-1 * Z.lxor (bv_unsigned (edenot ?E ?e)) 31 + 8)) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ (Z_to_bv 64 0x19afc) _ _ _ _) =>
          let BCE := fresh "BCE" in let B1 := fresh "B1" in let B2 := fresh "B2" in
          kx_read_ranges;
          lazymatch e with context [EVar ?j] => kx_enum BCE E e j 1 255%nat (fun v => (1 <=? -1 * Z.lxor v 31 + 8) && (-1 * Z.lxor v 31 + 8 <=? 8))%bool end;
          cbv beta in BCE; apply andb_prop in BCE as [B1 B2]; apply Z.leb_le in B1, B2;
          eapply CONT with (d := 0);
          [ first [ eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR] | eapply seqs_iinv_eq; [eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR] | repeat f_equal; lia] ]
          | split; [split; [lia | lia] | unfold bit_ok; cbn [v_SEQ v_sq]; rewrite <- En; intros; lia]
          | cbn [v_SEQ]; lia ]
      | |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 (bv_unsigned (edenot ?E ?e) + 41)) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ (Z_to_bv 64 0x19afc) _ _ _ _) =>
          let BCE := fresh "BCE" in let B1 := fresh "B1" in let B2 := fresh "B2" in
          kx_read_ranges;
          lazymatch e with context [EVar ?j] => kx_enum BCE E e j 1 255%nat (fun v => (1 <=? (v + 41) mod 2^64) && ((v + 41) mod 2^64 <=? 64))%bool end;
          cbv beta in BCE; apply andb_prop in BCE as [B1 B2]; apply Z.leb_le in B1, B2;
          rewrite (zbv_mod (bv_unsigned (edenot E e) + 41));
          eapply CONT with (d := 0);
          [ first [ eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR] | eapply seqs_iinv_eq; [eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR] | repeat f_equal; lia] ]
          | split; [split; [lia | exact B2] | unfold bit_ok; cbn [v_SEQ v_sq]; rewrite <- En; intros; lia]
          | cbn [v_SEQ]; lia ]
      end.
  - rewrite C in *; clear C.
    try hold TRANS. try hold CONT. try hold IEXIT. try hold RG0. try hold Esqb. try hold S1. try hold S2. try hold S3. try hold S4. try hold S5. try hold S6. try hold S7. try hold S8. try hold S9. try hold S10. try hold S11. try hold S12. try hold S15. try hold S16. try hold S18. try hold S19. try hold S20. try hold S21. try hold S22. try hold S23. try hold S24. try hold S25. try hold S26. try hold S27. try hold S28. try hold S29. try hold S30. try hold S31. try hold S32. try hold S33. try hold S34. try hold S35. try hold S36. try hold S37. try hold S38. try hold S39. try hold S40. try hold S41. try hold S42. try hold OKLL. try hold OKOF. try hold OKML.
    kx_autoLx [0x19afc; 0x1a5ec] 120%nat
    [KZRange SPV 544 (2^47); KZRange SEQ 4096 (2^47);  KZRange (SEQ + 5) 4096 (2^47); KZRange OEND 4096 (2^47); KZRange DCTX 4096 (2^47);
     KZWr (SPV - 336) 336; KZDisj (SPV - 336) 336 SEQ 5; KZImg 0x10000 0x14000]
    [(SEQ, 5)].
    all: kx_mem.
    all: (try unfold held in TRANS; try unfold held in CONT; try unfold held in IEXIT; try unfold held in RG0; try unfold held in Esqb; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S15; try unfold held in S16; try unfold held in S18; try unfold held in S19; try unfold held in S20; try unfold held in S21; try unfold held in S22; try unfold held in S23; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in S36; try unfold held in S37; try unfold held in S38; try unfold held in S39; try unfold held in S40; try unfold held in S41; try unfold held in S42; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end).
    all: lazymatch goal with
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1a5ec) _ _ _ _) =>
          eapply IEXIT; [exact RG0 | eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR] | reflexivity | reflexivity | lia | left; reflexivity]
      | |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 (bv_unsigned (edenot ?E ?e))) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ (Z_to_bv 64 0x19afc) _ _ _ _) =>
          let BCE := fresh "BCE" in let B1 := fresh "B1" in let B2 := fresh "B2" in
          kx_read_ranges;
          lazymatch e with context [EVar ?j] => kx_enum BCE E e j 1 255%nat (fun v => (1 <=? v) && (v <=? 64))%bool end;
          cbv beta in BCE; apply andb_prop in BCE as [B1 B2]; apply Z.leb_le in B1, B2;
          eapply CONT with (d := 0);
          [ first [ eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR] | eapply seqs_iinv_eq; [eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR] | repeat f_equal; lia] ]
          | split; [split; [lia | exact B2] | unfold bit_ok; cbn [v_SEQ v_sq]; rewrite <- En; intros; lia]
          | cbn [v_SEQ]; lia ]
      | |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 (-1 * Z.lxor (bv_unsigned (edenot ?E ?e)) 31 + 8)) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ (Z_to_bv 64 0x19afc) _ _ _ _) =>
          let BCE := fresh "BCE" in let B1 := fresh "B1" in let B2 := fresh "B2" in
          kx_read_ranges;
          lazymatch e with context [EVar ?j] => kx_enum BCE E e j 1 255%nat (fun v => (1 <=? -1 * Z.lxor v 31 + 8) && (-1 * Z.lxor v 31 + 8 <=? 8))%bool end;
          cbv beta in BCE; apply andb_prop in BCE as [B1 B2]; apply Z.leb_le in B1, B2;
          eapply CONT with (d := 0);
          [ first [ eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR] | eapply seqs_iinv_eq; [eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR] | repeat f_equal; lia] ]
          | split; [split; [lia | lia] | unfold bit_ok; cbn [v_SEQ v_sq]; rewrite <- En; intros; lia]
          | cbn [v_SEQ]; lia ]
      | |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 (bv_unsigned (edenot ?E ?e) + 41)) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ (Z_to_bv 64 0x19afc) _ _ _ _) =>
          let BCE := fresh "BCE" in let B1 := fresh "B1" in let B2 := fresh "B2" in
          kx_read_ranges;
          lazymatch e with context [EVar ?j] => kx_enum BCE E e j 1 255%nat (fun v => (1 <=? (v + 41) mod 2^64) && ((v + 41) mod 2^64 <=? 64))%bool end;
          cbv beta in BCE; apply andb_prop in BCE as [B1 B2]; apply Z.leb_le in B1, B2;
          rewrite (zbv_mod (bv_unsigned (edenot E e) + 41));
          eapply CONT with (d := 0);
          [ first [ eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR] | eapply seqs_iinv_eq; [eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR] | repeat f_equal; lia] ]
          | split; [split; [lia | exact B2] | unfold bit_ok; cbn [v_SEQ v_sq]; rewrite <- En; intros; lia]
          | cbn [v_SEQ]; lia ]
      end.
  - rewrite C in *; clear C.
    try hold TRANS. try hold CONT. try hold IEXIT. try hold RG0. try hold Esqb. try hold S1. try hold S2. try hold S3. try hold S4. try hold S5. try hold S6. try hold S7. try hold S8. try hold S9. try hold S10. try hold S11. try hold S12. try hold S15. try hold S16. try hold S18. try hold S19. try hold S20. try hold S21. try hold S22. try hold S23. try hold S24. try hold S25. try hold S26. try hold S27. try hold S28. try hold S29. try hold S30. try hold S31. try hold S32. try hold S33. try hold S34. try hold S35. try hold S36. try hold S37. try hold S38. try hold S39. try hold S40. try hold S41. try hold S42. try hold OKLL. try hold OKOF. try hold OKML.
    kx_autoLx [0x19afc; 0x1a5ec] 120%nat
    [KZRange SPV 544 (2^47); KZRange SEQ 4096 (2^47);  KZRange (SEQ + 6) 4096 (2^47); KZRange OEND 4096 (2^47); KZRange DCTX 4096 (2^47);
     KZWr (SPV - 336) 336; KZDisj (SPV - 336) 336 SEQ 6; KZImg 0x10000 0x14000]
    [(SEQ, 6)].
    all: kx_mem.
    all: (try unfold held in TRANS; try unfold held in CONT; try unfold held in IEXIT; try unfold held in RG0; try unfold held in Esqb; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S15; try unfold held in S16; try unfold held in S18; try unfold held in S19; try unfold held in S20; try unfold held in S21; try unfold held in S22; try unfold held in S23; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in S36; try unfold held in S37; try unfold held in S38; try unfold held in S39; try unfold held in S40; try unfold held in S41; try unfold held in S42; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end).
    all: lazymatch goal with
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1a5ec) _ _ _ _) =>
          eapply IEXIT; [exact RG0 | eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR] | reflexivity | reflexivity | lia | left; reflexivity]
      | |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 (bv_unsigned (edenot ?E ?e))) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ (Z_to_bv 64 0x19afc) _ _ _ _) =>
          let BCE := fresh "BCE" in let B1 := fresh "B1" in let B2 := fresh "B2" in
          kx_read_ranges;
          lazymatch e with context [EVar ?j] => kx_enum BCE E e j 1 255%nat (fun v => (1 <=? v) && (v <=? 64))%bool end;
          cbv beta in BCE; apply andb_prop in BCE as [B1 B2]; apply Z.leb_le in B1, B2;
          eapply CONT with (d := 0);
          [ first [ eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR] | eapply seqs_iinv_eq; [eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR] | repeat f_equal; lia] ]
          | split; [split; [lia | exact B2] | unfold bit_ok; cbn [v_SEQ v_sq]; rewrite <- En; intros; lia]
          | cbn [v_SEQ]; lia ]
      | |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 (-1 * Z.lxor (bv_unsigned (edenot ?E ?e)) 31 + 8)) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ (Z_to_bv 64 0x19afc) _ _ _ _) =>
          let BCE := fresh "BCE" in let B1 := fresh "B1" in let B2 := fresh "B2" in
          kx_read_ranges;
          lazymatch e with context [EVar ?j] => kx_enum BCE E e j 1 255%nat (fun v => (1 <=? -1 * Z.lxor v 31 + 8) && (-1 * Z.lxor v 31 + 8 <=? 8))%bool end;
          cbv beta in BCE; apply andb_prop in BCE as [B1 B2]; apply Z.leb_le in B1, B2;
          eapply CONT with (d := 0);
          [ first [ eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR] | eapply seqs_iinv_eq; [eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR] | repeat f_equal; lia] ]
          | split; [split; [lia | lia] | unfold bit_ok; cbn [v_SEQ v_sq]; rewrite <- En; intros; lia]
          | cbn [v_SEQ]; lia ]
      | |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 (bv_unsigned (edenot ?E ?e) + 41)) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ (Z_to_bv 64 0x19afc) _ _ _ _) =>
          let BCE := fresh "BCE" in let B1 := fresh "B1" in let B2 := fresh "B2" in
          kx_read_ranges;
          lazymatch e with context [EVar ?j] => kx_enum BCE E e j 1 255%nat (fun v => (1 <=? (v + 41) mod 2^64) && ((v + 41) mod 2^64 <=? 64))%bool end;
          cbv beta in BCE; apply andb_prop in BCE as [B1 B2]; apply Z.leb_le in B1, B2;
          rewrite (zbv_mod (bv_unsigned (edenot E e) + 41));
          eapply CONT with (d := 0);
          [ first [ eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR] | eapply seqs_iinv_eq; [eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR] | repeat f_equal; lia] ]
          | split; [split; [lia | exact B2] | unfold bit_ok; cbn [v_SEQ v_sq]; rewrite <- En; intros; lia]
          | cbn [v_SEQ]; lia ]
      end.
  - rewrite C in *; clear C.
    try hold TRANS. try hold CONT. try hold IEXIT. try hold RG0. try hold Esqb. try hold S1. try hold S2. try hold S3. try hold S4. try hold S5. try hold S6. try hold S7. try hold S8. try hold S9. try hold S10. try hold S11. try hold S12. try hold S15. try hold S16. try hold S18. try hold S19. try hold S20. try hold S21. try hold S22. try hold S23. try hold S24. try hold S25. try hold S26. try hold S27. try hold S28. try hold S29. try hold S30. try hold S31. try hold S32. try hold S33. try hold S34. try hold S35. try hold S36. try hold S37. try hold S38. try hold S39. try hold S40. try hold S41. try hold S42. try hold OKLL. try hold OKOF. try hold OKML.
    kx_autoLx [0x19afc; 0x1a5ec] 120%nat
    [KZRange SPV 544 (2^47); KZRange SEQ 4096 (2^47);  KZRange (SEQ + 7) 4096 (2^47); KZRange OEND 4096 (2^47); KZRange DCTX 4096 (2^47);
     KZWr (SPV - 336) 336; KZDisj (SPV - 336) 336 SEQ 7; KZImg 0x10000 0x14000]
    [(SEQ, 7)].
    all: kx_mem.
    all: (try unfold held in TRANS; try unfold held in CONT; try unfold held in IEXIT; try unfold held in RG0; try unfold held in Esqb; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S15; try unfold held in S16; try unfold held in S18; try unfold held in S19; try unfold held in S20; try unfold held in S21; try unfold held in S22; try unfold held in S23; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in S36; try unfold held in S37; try unfold held in S38; try unfold held in S39; try unfold held in S40; try unfold held in S41; try unfold held in S42; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end).
    all: lazymatch goal with
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1a5ec) _ _ _ _) =>
          eapply IEXIT; [exact RG0 | eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR] | reflexivity | reflexivity | lia | left; reflexivity]
      | |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 (bv_unsigned (edenot ?E ?e))) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ (Z_to_bv 64 0x19afc) _ _ _ _) =>
          let BCE := fresh "BCE" in let B1 := fresh "B1" in let B2 := fresh "B2" in
          kx_read_ranges;
          lazymatch e with context [EVar ?j] => kx_enum BCE E e j 1 255%nat (fun v => (1 <=? v) && (v <=? 64))%bool end;
          cbv beta in BCE; apply andb_prop in BCE as [B1 B2]; apply Z.leb_le in B1, B2;
          eapply CONT with (d := 0);
          [ first [ eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR] | eapply seqs_iinv_eq; [eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR] | repeat f_equal; lia] ]
          | split; [split; [lia | exact B2] | unfold bit_ok; cbn [v_SEQ v_sq]; rewrite <- En; intros; lia]
          | cbn [v_SEQ]; lia ]
      | |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 (-1 * Z.lxor (bv_unsigned (edenot ?E ?e)) 31 + 8)) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ (Z_to_bv 64 0x19afc) _ _ _ _) =>
          let BCE := fresh "BCE" in let B1 := fresh "B1" in let B2 := fresh "B2" in
          kx_read_ranges;
          lazymatch e with context [EVar ?j] => kx_enum BCE E e j 1 255%nat (fun v => (1 <=? -1 * Z.lxor v 31 + 8) && (-1 * Z.lxor v 31 + 8 <=? 8))%bool end;
          cbv beta in BCE; apply andb_prop in BCE as [B1 B2]; apply Z.leb_le in B1, B2;
          eapply CONT with (d := 0);
          [ first [ eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR] | eapply seqs_iinv_eq; [eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR] | repeat f_equal; lia] ]
          | split; [split; [lia | lia] | unfold bit_ok; cbn [v_SEQ v_sq]; rewrite <- En; intros; lia]
          | cbn [v_SEQ]; lia ]
      | |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 (bv_unsigned (edenot ?E ?e) + 41)) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ (Z_to_bv 64 0x19afc) _ _ _ _) =>
          let BCE := fresh "BCE" in let B1 := fresh "B1" in let B2 := fresh "B2" in
          kx_read_ranges;
          lazymatch e with context [EVar ?j] => kx_enum BCE E e j 1 255%nat (fun v => (1 <=? (v + 41) mod 2^64) && ((v + 41) mod 2^64 <=? 64))%bool end;
          cbv beta in BCE; apply andb_prop in BCE as [B1 B2]; apply Z.leb_le in B1, B2;
          rewrite (zbv_mod (bv_unsigned (edenot E e) + 41));
          eapply CONT with (d := 0);
          [ first [ eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR] | eapply seqs_iinv_eq; [eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR] | repeat f_equal; lia] ]
          | split; [split; [lia | exact B2] | unfold bit_ok; cbn [v_SEQ v_sq]; rewrite <- En; intros; lia]
          | cbn [v_SEQ]; lia ]
      end.
Qed.
