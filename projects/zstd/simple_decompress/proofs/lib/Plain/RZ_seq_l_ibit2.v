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
From OSSVerify.Proofs.zstd.simple_decompress.lib.Plain Require Import PImg F_memcpy F_memmove RZ_seq_iface RZ_seq_kit RZ_seq_gkit RZ_seq_l_base RZ_seq_l_lbase RZ_seq_l_lkit RZ_seq_l_ibase RZ_seq_l_iexit RZ_seq_l_ibit.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma seql_bitinit_b : forall P OEND LLO LEND LOCV, seql_static P OEND LLO LEND LOCV -> seql_ranges P -> 4 <= zlen (y_sq P) <= 7 -> ai_i1 P OEND LLO LEND LOCV -> ai_i0 P OEND LLO LEND LOCV.
Proof.
  intros P OEND LLO LEND LOCV ST RG0 HN CONT. unfold ai_i0.
  intros m1 p0 p1 p2 w_c0 w_c8 w_c16 w_c24 w_c32 w_c40 w_c48 w_c56 w_c64 w_c72 w_c96 w_c104 w_c112 w_c128 w_c144 w_c152 w_c160 w_c168 w_c176 w_c184 w_c192 w_c200 w_c208 w_c216 w_c224 w_c232 w_c240 w_c248 jpad jseq rl rm ro x1 x5 x6 x7 x12 x15 x16 x17 x21 x22 x23 x25 x27 x28 x29 x31 INV.
  pose proof (seql_iinv_frame P OEND LLO LEND LOCV m1 _ ST INV) as TRANS.
  pose proof (seql_iexit P OEND LLO LEND LOCV) as IEXIT.
  pose proof (seql_iinv_mi _ _ _ _ _ _ _ INV) as MI.
  unfold ai_i1 in CONT.
  destruct INV as (FR & _ & _ & _ & _ & SQB & _).
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws].
  cbn [seql_static seql_post y_ra y_gp y_tp y_s0 y_s1 y_s2 y_s3 y_s4 y_s5 y_s6 y_s7 y_s8 y_s9 y_s10 y_s11 y_F y_fc y_m y_SPV y_lo y_DCTX y_DST y_CAP y_B0 y_B1 y_SEQ y_nbSeq y_LLT y_MLT y_OFT y_PFX y_LITP y_LBE y_LITB y_LOC y_sq y_tLL y_tOF y_tML y_huf y_r0 y_r1 y_r2 y_pde y_dend y_expd y_pcs y_dsz y_bt y_stg y_le y_fe y_ws] in ST, FR, SQB, CONT, TRANS, HN |- *.
  sd_static_open ST.
  remember (map (Z_to_bv 8) sq) as sqb eqn:Esqb. remember (zlen sq) as n eqn:En.
  assert (LSQ : Z.of_nat (length sqb) = n) by (subst sqb n; rewrite length_map; reflexivity).
  assert (MUL : munch [(SPV - 608, SPV)] m1 m1) by apply munch_refl. assert (WMl : wmono psegs m1 m1) by apply wmono_refl.
  assert (DJ : SPV - 608 + 608 <= SEQ \/ SEQ + n <= SPV - 608) by (unfold held in S25; clear - S25 S18; lia).
  assert (RG : 4096 <= OEND < 2^47 /\ 4096 <= DCTX < 2^47) by (clear - S1 S2 S3 S4 S5 S6 S7 S19 S20; lia).
  assert (CASES : n = 4 \/ n = 5 \/ n = 6 \/ n = 7) by (unfold held in HN; clear - S15 HN; lia).
  destruct CASES as [C|[C|[C|C]]].
  - rewrite C in *; clear C.
    try hold TRANS. try hold CONT. try hold IEXIT. try hold RG0. try hold Esqb. try hold S1. try hold S2. try hold S3. try hold S4. try hold S5. try hold S6. try hold S7. try hold S8. try hold S9. try hold S10. try hold S11. try hold S12. try hold S15. try hold S16. try hold S18. try hold S19. try hold S20. try hold S21. try hold S22. try hold S23. try hold S24. try hold S25. try hold S26. try hold S27. try hold S28. try hold S29. try hold S30. try hold S31. try hold S32. try hold S33. try hold S34. try hold S35. try hold S36. try hold S37. try hold S38. try hold S39. try hold S40. try hold S41. try hold S42. try hold OKLL. try hold OKOF. try hold OKML.
    kx_autoLx [0x17560; 0x18c10] 120%nat
    [KZRange SPV 816 (2^47); KZRange SEQ 4096 (2^47);  KZRange (SEQ + 4) 4096 (2^47); KZRange OEND 4096 (2^47); KZRange DCTX 4096 (2^47);
     KZWr (SPV - 608) 608; KZDisj (SPV - 608) 608 SEQ 4; KZImg 0x10000 0x14000]
    [(SEQ, 4)].
    all: kx_mem.
    all: (try unfold held in TRANS; try unfold held in CONT; try unfold held in IEXIT; try unfold held in RG0; try unfold held in Esqb; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S15; try unfold held in S16; try unfold held in S18; try unfold held in S19; try unfold held in S20; try unfold held in S21; try unfold held in S22; try unfold held in S23; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in S36; try unfold held in S37; try unfold held in S38; try unfold held in S39; try unfold held in S40; try unfold held in S41; try unfold held in S42; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end).
    all: lazymatch goal with
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x18c10) _ _ _ _) =>
          eapply IEXIT; [exact RG0 | eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR] | reflexivity | reflexivity | lia | left; reflexivity]
      | |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 (bv_unsigned (edenot ?E ?e))) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ (Z_to_bv 64 0x17560) _ _ _ _) =>
          let BCE := fresh "BCE" in let B1 := fresh "B1" in let B2 := fresh "B2" in
          kx_read_ranges;
          lazymatch e with context [EVar ?j] => kx_enum BCE E e j 1 255%nat (fun v => (1 <=? v) && (v <=? 64))%bool end;
          cbv beta in BCE; apply andb_prop in BCE as [B1 B2]; apply Z.leb_le in B1, B2;
          eapply CONT with (d := 0);
          [ first [ eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR] | eapply seql_iinv_eq; [eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR] | repeat f_equal; lia] ]
          | split; [split; [lia | exact B2] | unfold bit_ok; cbn [y_SEQ y_sq]; rewrite <- En; intros; lia]
          | cbn [y_SEQ]; lia ]
      | |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 (-1 * Z.lxor (bv_unsigned (edenot ?E ?e)) 31 + 8)) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ (Z_to_bv 64 0x17560) _ _ _ _) =>
          let BCE := fresh "BCE" in let B1 := fresh "B1" in let B2 := fresh "B2" in
          kx_read_ranges;
          lazymatch e with context [EVar ?j] => kx_enum BCE E e j 1 255%nat (fun v => (1 <=? -1 * Z.lxor v 31 + 8) && (-1 * Z.lxor v 31 + 8 <=? 8))%bool end;
          cbv beta in BCE; apply andb_prop in BCE as [B1 B2]; apply Z.leb_le in B1, B2;
          eapply CONT with (d := 0);
          [ first [ eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR] | eapply seql_iinv_eq; [eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR] | repeat f_equal; lia] ]
          | split; [split; [lia | lia] | unfold bit_ok; cbn [y_SEQ y_sq]; rewrite <- En; intros; lia]
          | cbn [y_SEQ]; lia ]
      | |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 (bv_unsigned (edenot ?E ?e) + 41)) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ (Z_to_bv 64 0x17560) _ _ _ _) =>
          let BCE := fresh "BCE" in let B1 := fresh "B1" in let B2 := fresh "B2" in
          kx_read_ranges;
          lazymatch e with context [EVar ?j] => kx_enum BCE E e j 1 255%nat (fun v => (1 <=? (v + 41) mod 2^64) && ((v + 41) mod 2^64 <=? 64))%bool end;
          cbv beta in BCE; apply andb_prop in BCE as [B1 B2]; apply Z.leb_le in B1, B2;
          rewrite (zbv_mod (bv_unsigned (edenot E e) + 41));
          eapply CONT with (d := 0);
          [ first [ eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR] | eapply seql_iinv_eq; [eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR] | repeat f_equal; lia] ]
          | split; [split; [lia | exact B2] | unfold bit_ok; cbn [y_SEQ y_sq]; rewrite <- En; intros; lia]
          | cbn [y_SEQ]; lia ]
      end.
  - rewrite C in *; clear C.
    try hold TRANS. try hold CONT. try hold IEXIT. try hold RG0. try hold Esqb. try hold S1. try hold S2. try hold S3. try hold S4. try hold S5. try hold S6. try hold S7. try hold S8. try hold S9. try hold S10. try hold S11. try hold S12. try hold S15. try hold S16. try hold S18. try hold S19. try hold S20. try hold S21. try hold S22. try hold S23. try hold S24. try hold S25. try hold S26. try hold S27. try hold S28. try hold S29. try hold S30. try hold S31. try hold S32. try hold S33. try hold S34. try hold S35. try hold S36. try hold S37. try hold S38. try hold S39. try hold S40. try hold S41. try hold S42. try hold OKLL. try hold OKOF. try hold OKML.
    kx_autoLx [0x17560; 0x18c10] 120%nat
    [KZRange SPV 816 (2^47); KZRange SEQ 4096 (2^47);  KZRange (SEQ + 5) 4096 (2^47); KZRange OEND 4096 (2^47); KZRange DCTX 4096 (2^47);
     KZWr (SPV - 608) 608; KZDisj (SPV - 608) 608 SEQ 5; KZImg 0x10000 0x14000]
    [(SEQ, 5)].
    all: kx_mem.
    all: (try unfold held in TRANS; try unfold held in CONT; try unfold held in IEXIT; try unfold held in RG0; try unfold held in Esqb; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S15; try unfold held in S16; try unfold held in S18; try unfold held in S19; try unfold held in S20; try unfold held in S21; try unfold held in S22; try unfold held in S23; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in S36; try unfold held in S37; try unfold held in S38; try unfold held in S39; try unfold held in S40; try unfold held in S41; try unfold held in S42; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end).
    all: lazymatch goal with
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x18c10) _ _ _ _) =>
          eapply IEXIT; [exact RG0 | eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR] | reflexivity | reflexivity | lia | left; reflexivity]
      | |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 (bv_unsigned (edenot ?E ?e))) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ (Z_to_bv 64 0x17560) _ _ _ _) =>
          let BCE := fresh "BCE" in let B1 := fresh "B1" in let B2 := fresh "B2" in
          kx_read_ranges;
          lazymatch e with context [EVar ?j] => kx_enum BCE E e j 1 255%nat (fun v => (1 <=? v) && (v <=? 64))%bool end;
          cbv beta in BCE; apply andb_prop in BCE as [B1 B2]; apply Z.leb_le in B1, B2;
          eapply CONT with (d := 0);
          [ first [ eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR] | eapply seql_iinv_eq; [eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR] | repeat f_equal; lia] ]
          | split; [split; [lia | exact B2] | unfold bit_ok; cbn [y_SEQ y_sq]; rewrite <- En; intros; lia]
          | cbn [y_SEQ]; lia ]
      | |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 (-1 * Z.lxor (bv_unsigned (edenot ?E ?e)) 31 + 8)) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ (Z_to_bv 64 0x17560) _ _ _ _) =>
          let BCE := fresh "BCE" in let B1 := fresh "B1" in let B2 := fresh "B2" in
          kx_read_ranges;
          lazymatch e with context [EVar ?j] => kx_enum BCE E e j 1 255%nat (fun v => (1 <=? -1 * Z.lxor v 31 + 8) && (-1 * Z.lxor v 31 + 8 <=? 8))%bool end;
          cbv beta in BCE; apply andb_prop in BCE as [B1 B2]; apply Z.leb_le in B1, B2;
          eapply CONT with (d := 0);
          [ first [ eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR] | eapply seql_iinv_eq; [eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR] | repeat f_equal; lia] ]
          | split; [split; [lia | lia] | unfold bit_ok; cbn [y_SEQ y_sq]; rewrite <- En; intros; lia]
          | cbn [y_SEQ]; lia ]
      | |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 (bv_unsigned (edenot ?E ?e) + 41)) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ (Z_to_bv 64 0x17560) _ _ _ _) =>
          let BCE := fresh "BCE" in let B1 := fresh "B1" in let B2 := fresh "B2" in
          kx_read_ranges;
          lazymatch e with context [EVar ?j] => kx_enum BCE E e j 1 255%nat (fun v => (1 <=? (v + 41) mod 2^64) && ((v + 41) mod 2^64 <=? 64))%bool end;
          cbv beta in BCE; apply andb_prop in BCE as [B1 B2]; apply Z.leb_le in B1, B2;
          rewrite (zbv_mod (bv_unsigned (edenot E e) + 41));
          eapply CONT with (d := 0);
          [ first [ eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR] | eapply seql_iinv_eq; [eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR] | repeat f_equal; lia] ]
          | split; [split; [lia | exact B2] | unfold bit_ok; cbn [y_SEQ y_sq]; rewrite <- En; intros; lia]
          | cbn [y_SEQ]; lia ]
      end.
  - rewrite C in *; clear C.
    try hold TRANS. try hold CONT. try hold IEXIT. try hold RG0. try hold Esqb. try hold S1. try hold S2. try hold S3. try hold S4. try hold S5. try hold S6. try hold S7. try hold S8. try hold S9. try hold S10. try hold S11. try hold S12. try hold S15. try hold S16. try hold S18. try hold S19. try hold S20. try hold S21. try hold S22. try hold S23. try hold S24. try hold S25. try hold S26. try hold S27. try hold S28. try hold S29. try hold S30. try hold S31. try hold S32. try hold S33. try hold S34. try hold S35. try hold S36. try hold S37. try hold S38. try hold S39. try hold S40. try hold S41. try hold S42. try hold OKLL. try hold OKOF. try hold OKML.
    kx_autoLx [0x17560; 0x18c10] 120%nat
    [KZRange SPV 816 (2^47); KZRange SEQ 4096 (2^47);  KZRange (SEQ + 6) 4096 (2^47); KZRange OEND 4096 (2^47); KZRange DCTX 4096 (2^47);
     KZWr (SPV - 608) 608; KZDisj (SPV - 608) 608 SEQ 6; KZImg 0x10000 0x14000]
    [(SEQ, 6)].
    all: kx_mem.
    all: (try unfold held in TRANS; try unfold held in CONT; try unfold held in IEXIT; try unfold held in RG0; try unfold held in Esqb; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S15; try unfold held in S16; try unfold held in S18; try unfold held in S19; try unfold held in S20; try unfold held in S21; try unfold held in S22; try unfold held in S23; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in S36; try unfold held in S37; try unfold held in S38; try unfold held in S39; try unfold held in S40; try unfold held in S41; try unfold held in S42; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end).
    all: lazymatch goal with
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x18c10) _ _ _ _) =>
          eapply IEXIT; [exact RG0 | eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR] | reflexivity | reflexivity | lia | left; reflexivity]
      | |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 (bv_unsigned (edenot ?E ?e))) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ (Z_to_bv 64 0x17560) _ _ _ _) =>
          let BCE := fresh "BCE" in let B1 := fresh "B1" in let B2 := fresh "B2" in
          kx_read_ranges;
          lazymatch e with context [EVar ?j] => kx_enum BCE E e j 1 255%nat (fun v => (1 <=? v) && (v <=? 64))%bool end;
          cbv beta in BCE; apply andb_prop in BCE as [B1 B2]; apply Z.leb_le in B1, B2;
          eapply CONT with (d := 0);
          [ first [ eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR] | eapply seql_iinv_eq; [eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR] | repeat f_equal; lia] ]
          | split; [split; [lia | exact B2] | unfold bit_ok; cbn [y_SEQ y_sq]; rewrite <- En; intros; lia]
          | cbn [y_SEQ]; lia ]
      | |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 (-1 * Z.lxor (bv_unsigned (edenot ?E ?e)) 31 + 8)) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ (Z_to_bv 64 0x17560) _ _ _ _) =>
          let BCE := fresh "BCE" in let B1 := fresh "B1" in let B2 := fresh "B2" in
          kx_read_ranges;
          lazymatch e with context [EVar ?j] => kx_enum BCE E e j 1 255%nat (fun v => (1 <=? -1 * Z.lxor v 31 + 8) && (-1 * Z.lxor v 31 + 8 <=? 8))%bool end;
          cbv beta in BCE; apply andb_prop in BCE as [B1 B2]; apply Z.leb_le in B1, B2;
          eapply CONT with (d := 0);
          [ first [ eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR] | eapply seql_iinv_eq; [eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR] | repeat f_equal; lia] ]
          | split; [split; [lia | lia] | unfold bit_ok; cbn [y_SEQ y_sq]; rewrite <- En; intros; lia]
          | cbn [y_SEQ]; lia ]
      | |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 (bv_unsigned (edenot ?E ?e) + 41)) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ (Z_to_bv 64 0x17560) _ _ _ _) =>
          let BCE := fresh "BCE" in let B1 := fresh "B1" in let B2 := fresh "B2" in
          kx_read_ranges;
          lazymatch e with context [EVar ?j] => kx_enum BCE E e j 1 255%nat (fun v => (1 <=? (v + 41) mod 2^64) && ((v + 41) mod 2^64 <=? 64))%bool end;
          cbv beta in BCE; apply andb_prop in BCE as [B1 B2]; apply Z.leb_le in B1, B2;
          rewrite (zbv_mod (bv_unsigned (edenot E e) + 41));
          eapply CONT with (d := 0);
          [ first [ eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR] | eapply seql_iinv_eq; [eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR] | repeat f_equal; lia] ]
          | split; [split; [lia | exact B2] | unfold bit_ok; cbn [y_SEQ y_sq]; rewrite <- En; intros; lia]
          | cbn [y_SEQ]; lia ]
      end.
  - rewrite C in *; clear C.
    try hold TRANS. try hold CONT. try hold IEXIT. try hold RG0. try hold Esqb. try hold S1. try hold S2. try hold S3. try hold S4. try hold S5. try hold S6. try hold S7. try hold S8. try hold S9. try hold S10. try hold S11. try hold S12. try hold S15. try hold S16. try hold S18. try hold S19. try hold S20. try hold S21. try hold S22. try hold S23. try hold S24. try hold S25. try hold S26. try hold S27. try hold S28. try hold S29. try hold S30. try hold S31. try hold S32. try hold S33. try hold S34. try hold S35. try hold S36. try hold S37. try hold S38. try hold S39. try hold S40. try hold S41. try hold S42. try hold OKLL. try hold OKOF. try hold OKML.
    kx_autoLx [0x17560; 0x18c10] 120%nat
    [KZRange SPV 816 (2^47); KZRange SEQ 4096 (2^47);  KZRange (SEQ + 7) 4096 (2^47); KZRange OEND 4096 (2^47); KZRange DCTX 4096 (2^47);
     KZWr (SPV - 608) 608; KZDisj (SPV - 608) 608 SEQ 7; KZImg 0x10000 0x14000]
    [(SEQ, 7)].
    all: kx_mem.
    all: (try unfold held in TRANS; try unfold held in CONT; try unfold held in IEXIT; try unfold held in RG0; try unfold held in Esqb; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S15; try unfold held in S16; try unfold held in S18; try unfold held in S19; try unfold held in S20; try unfold held in S21; try unfold held in S22; try unfold held in S23; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in S36; try unfold held in S37; try unfold held in S38; try unfold held in S39; try unfold held in S40; try unfold held in S41; try unfold held in S42; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end).
    all: lazymatch goal with
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x18c10) _ _ _ _) =>
          eapply IEXIT; [exact RG0 | eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR] | reflexivity | reflexivity | lia | left; reflexivity]
      | |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 (bv_unsigned (edenot ?E ?e))) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ (Z_to_bv 64 0x17560) _ _ _ _) =>
          let BCE := fresh "BCE" in let B1 := fresh "B1" in let B2 := fresh "B2" in
          kx_read_ranges;
          lazymatch e with context [EVar ?j] => kx_enum BCE E e j 1 255%nat (fun v => (1 <=? v) && (v <=? 64))%bool end;
          cbv beta in BCE; apply andb_prop in BCE as [B1 B2]; apply Z.leb_le in B1, B2;
          eapply CONT with (d := 0);
          [ first [ eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR] | eapply seql_iinv_eq; [eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR] | repeat f_equal; lia] ]
          | split; [split; [lia | exact B2] | unfold bit_ok; cbn [y_SEQ y_sq]; rewrite <- En; intros; lia]
          | cbn [y_SEQ]; lia ]
      | |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 (-1 * Z.lxor (bv_unsigned (edenot ?E ?e)) 31 + 8)) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ (Z_to_bv 64 0x17560) _ _ _ _) =>
          let BCE := fresh "BCE" in let B1 := fresh "B1" in let B2 := fresh "B2" in
          kx_read_ranges;
          lazymatch e with context [EVar ?j] => kx_enum BCE E e j 1 255%nat (fun v => (1 <=? -1 * Z.lxor v 31 + 8) && (-1 * Z.lxor v 31 + 8 <=? 8))%bool end;
          cbv beta in BCE; apply andb_prop in BCE as [B1 B2]; apply Z.leb_le in B1, B2;
          eapply CONT with (d := 0);
          [ first [ eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR] | eapply seql_iinv_eq; [eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR] | repeat f_equal; lia] ]
          | split; [split; [lia | lia] | unfold bit_ok; cbn [y_SEQ y_sq]; rewrite <- En; intros; lia]
          | cbn [y_SEQ]; lia ]
      | |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 (bv_unsigned (edenot ?E ?e) + 41)) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ (Z_to_bv 64 0x17560) _ _ _ _) =>
          let BCE := fresh "BCE" in let B1 := fresh "B1" in let B2 := fresh "B2" in
          kx_read_ranges;
          lazymatch e with context [EVar ?j] => kx_enum BCE E e j 1 255%nat (fun v => (1 <=? (v + 41) mod 2^64) && ((v + 41) mod 2^64 <=? 64))%bool end;
          cbv beta in BCE; apply andb_prop in BCE as [B1 B2]; apply Z.leb_le in B1, B2;
          rewrite (zbv_mod (bv_unsigned (edenot E e) + 41));
          eapply CONT with (d := 0);
          [ first [ eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR] | eapply seql_iinv_eq; [eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR] | repeat f_equal; lia] ]
          | split; [split; [lia | exact B2] | unfold bit_ok; cbn [y_SEQ y_sq]; rewrite <- En; intros; lia]
          | cbn [y_SEQ]; lia ]
      end.
Qed.
