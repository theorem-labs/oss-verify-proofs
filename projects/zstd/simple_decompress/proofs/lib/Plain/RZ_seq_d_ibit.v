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
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit MemRange ZdWalkKit ZdDctxRep ZdSeqW KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXPost.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import KXLean KXLeanAll.   (* [comment removed for export] *)
From OSSVerify.Proofs.zstd.simple_decompress.lib.Plain Require Import PImg F_memcpy F_memmove RZ_seq_iface RZ_seq_kit RZ_seq_d_base RZ_seq_d_lbase RZ_seq_d_lkit RZ_seq_d_ibase RZ_seq_d_ient.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma seqd_iinv_eq2 : forall P LEND m1 fr fr', seqd_iinv P LEND m1 fr -> fr = fr' -> seqd_iinv P LEND m1 fr'.
Proof. intros P LEND m1 fr fr' H E. subst fr'. exact H. Qed.

Lemma zbv_mod : forall z, Z_to_bv 64 z = Z_to_bv 64 (z mod 2^64).
Proof. intros z. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2^64). rewrite Z.mod_mod by lia. reflexivity. Qed.

Lemma seqd_bitinit : forall P OEND LEND, seqd_static P OEND LEND -> seqd_ranges P -> ai_408 P OEND LEND -> ai_1ac P OEND LEND.
Proof.
  intros P OEND LEND ST RG0 CONT. unfold ai_1ac.
  intros m1 p0 p1 p2 j0 jpad jseq j_c8 j_c16 j_c24 j_c48 j_cw j_cbc j_cptr j_c80 j_c88 j_c96 j_c104 j_c112 j_c120 j_c128 j_c136 t5v r10 x1 x5 x6 x7 x11 x12 x15 x16 x17 x19 x20 x21 x22 x23 x25 x28 x31 INV ET5 ER10.
  pose proof (seqd_iinv_frame P OEND LEND m1 _ ST INV) as TRANS.
  pose proof (seqd_iexit P LEND) as IEXIT.
  pose proof (seqd_iinv_mi _ _ _ _ INV) as MI.
  unfold ai_408 in CONT.
  destruct INV as (FR & _ & _ & _ & _ & SQB & _).
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LITSZ LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws].
  cbn [seqd_static seqd_post q_ra q_gp q_tp q_s0 q_s1 q_s2 q_s3 q_s4 q_s5 q_s6 q_s7 q_s8 q_s9 q_s10 q_s11 q_F q_fc q_m q_SPV q_lo q_DCTX q_DST q_CAP q_B0 q_B1 q_SEQ q_nbSeq q_LLT q_MLT q_OFT q_PFX q_LITP q_LITSZ q_LITB q_LOC q_sq q_tLL q_tOF q_tML q_huf q_r0 q_r1 q_r2 q_pde q_dend q_expd q_pcs q_dsz q_bt q_stg q_le q_fe q_ws] in ST, FR, SQB, CONT, TRANS, ET5 |- *.
  sd_static_open ST.
  remember (map (Z_to_bv 8) sq) as sqb eqn:Esqb. remember (zlen sq) as n eqn:En.
  assert (LSQ : Z.of_nat (length sqb) = n) by (subst sqb n; rewrite length_map; reflexivity).
  subst t5v r10.
  assert (MUL : munch [(SPV - 304, SPV)] m1 m1) by apply munch_refl. assert (WMl : wmono psegs m1 m1) by apply wmono_refl.
  assert (DJ : SPV - 304 + 304 <= SEQ \/ SEQ + n <= SPV - 304) by (unfold held in S25; clear - S25 S18; lia).
  assert (RG : 4096 <= OEND < 2^47 /\ 4096 <= DCTX < 2^47) by (clear - S1 S2 S3 S4 S5 S6 S7 S19 S20; lia).
  assert (CASES : 8 <= n \/ n = 1 \/ n = 2 \/ n = 3 \/ n = 4 \/ n = 5 \/ n = 6 \/ n = 7) by (clear - S15; lia).
  destruct CASES as [C|[C|[C|[C|[C|[C|[C|C]]]]]]].
  - try hold TRANS. try hold CONT. try hold IEXIT. try hold RG0. try hold Esqb. try hold S1. try hold S2. try hold S3. try hold S4. try hold S5. try hold S6. try hold S7. try hold S8. try hold S9. try hold S10. try hold S11. try hold S12. try hold S15. try hold S16. try hold S18. try hold S19. try hold S20. try hold S21. try hold S22. try hold S23. try hold S24. try hold S25. try hold S26. try hold S27. try hold S28. try hold S29. try hold S30. try hold S31. try hold S32. try hold S33. try hold S34. try hold S35. try hold OKLL. try hold OKOF. try hold OKML.
    kx_autoLx [0x1b4d4; 0x1c070] 120%nat
    [KZRange SPV 496 (2^47); KZRange SEQ 4096 (2^47); KZRange n 8 (2^47); KZRange (SEQ + n) 4096 (2^47); KZRange OEND 4096 (2^47); KZRange DCTX 4096 (2^47);
     KZWr (SPV - 304) 304; KZDisj (SPV - 304) 304 SEQ n; KZImg 0x10000 0x14000]
    [(SEQ, n)].
    all: kx_mem.
    all: (try unfold held in TRANS; try unfold held in CONT; try unfold held in IEXIT; try unfold held in RG0; try unfold held in Esqb; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S15; try unfold held in S16; try unfold held in S18; try unfold held in S19; try unfold held in S20; try unfold held in S21; try unfold held in S22; try unfold held in S23; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end).
    all: lazymatch goal with
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1c070) _ _ _ _) =>
          eapply IEXIT; [exact RG0 | eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR] | reflexivity | reflexivity | lia | left; reflexivity]
      | |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 (bv_unsigned (edenot ?E ?e))) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ (Z_to_bv 64 0x1b4d4) _ _ _ _) =>
          let BCE := fresh "BCE" in let B1 := fresh "B1" in let B2 := fresh "B2" in
          kx_read_ranges;
          lazymatch e with context [EVar ?j] => kx_enum BCE E e j 1 255%nat (fun v => (1 <=? v) && (v <=? 64))%bool end;
          cbv beta in BCE; apply andb_prop in BCE as [B1 B2]; apply Z.leb_le in B1, B2;
          eapply CONT with (d := (n - 8));
          [ first [ eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR] | eapply seqd_iinv_eq2; [eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR] | repeat f_equal; lia] ]
          | split; [split; [lia | exact B2] | unfold bit_ok; cbn [q_SEQ q_sq]; rewrite <- En; intros; lia]
          | cbn [q_SEQ]; lia ]
      | |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 (-1 * Z.lxor (bv_unsigned (edenot ?E ?e)) 31 + 8)) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ (Z_to_bv 64 0x1b4d4) _ _ _ _) =>
          let BCE := fresh "BCE" in let B1 := fresh "B1" in let B2 := fresh "B2" in
          kx_read_ranges;
          lazymatch e with context [EVar ?j] => kx_enum BCE E e j 1 255%nat (fun v => (1 <=? -1 * Z.lxor v 31 + 8) && (-1 * Z.lxor v 31 + 8 <=? 8))%bool end;
          cbv beta in BCE; apply andb_prop in BCE as [B1 B2]; apply Z.leb_le in B1, B2;
          eapply CONT with (d := (n - 8));
          [ first [ eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR] | eapply seqd_iinv_eq2; [eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR] | repeat f_equal; lia] ]
          | split; [split; [lia | lia] | unfold bit_ok; cbn [q_SEQ q_sq]; rewrite <- En; intros; lia]
          | cbn [q_SEQ]; lia ]
      | |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 (bv_unsigned (edenot ?E ?e) + 41)) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ (Z_to_bv 64 0x1b4d4) _ _ _ _) =>
          let BCE := fresh "BCE" in let B1 := fresh "B1" in let B2 := fresh "B2" in
          kx_read_ranges;
          lazymatch e with context [EVar ?j] => kx_enum BCE E e j 1 255%nat (fun v => (1 <=? (v + 41) mod 2^64) && ((v + 41) mod 2^64 <=? 64))%bool end;
          cbv beta in BCE; apply andb_prop in BCE as [B1 B2]; apply Z.leb_le in B1, B2;
          rewrite (zbv_mod (bv_unsigned (edenot E e) + 41));
          eapply CONT with (d := (n - 8));
          [ first [ eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR] | eapply seqd_iinv_eq2; [eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR] | repeat f_equal; lia] ]
          | split; [split; [lia | exact B2] | unfold bit_ok; cbn [q_SEQ q_sq]; rewrite <- En; intros; lia]
          | cbn [q_SEQ]; lia ]
      end.
  - rewrite C in *; clear C.
    try hold TRANS. try hold CONT. try hold IEXIT. try hold RG0. try hold Esqb. try hold S1. try hold S2. try hold S3. try hold S4. try hold S5. try hold S6. try hold S7. try hold S8. try hold S9. try hold S10. try hold S11. try hold S12. try hold S15. try hold S16. try hold S18. try hold S19. try hold S20. try hold S21. try hold S22. try hold S23. try hold S24. try hold S25. try hold S26. try hold S27. try hold S28. try hold S29. try hold S30. try hold S31. try hold S32. try hold S33. try hold S34. try hold S35. try hold OKLL. try hold OKOF. try hold OKML.
    kx_autoLx [0x1b4d4; 0x1c070] 120%nat
    [KZRange SPV 496 (2^47); KZRange SEQ 4096 (2^47);  KZRange (SEQ + 1) 4096 (2^47); KZRange OEND 4096 (2^47); KZRange DCTX 4096 (2^47);
     KZWr (SPV - 304) 304; KZDisj (SPV - 304) 304 SEQ 1; KZImg 0x10000 0x14000]
    [(SEQ, 1)].
    all: kx_mem.
    all: (try unfold held in TRANS; try unfold held in CONT; try unfold held in IEXIT; try unfold held in RG0; try unfold held in Esqb; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S15; try unfold held in S16; try unfold held in S18; try unfold held in S19; try unfold held in S20; try unfold held in S21; try unfold held in S22; try unfold held in S23; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end).
    all: lazymatch goal with
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1c070) _ _ _ _) =>
          eapply IEXIT; [exact RG0 | eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR] | reflexivity | reflexivity | lia | left; reflexivity]
      | |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 (bv_unsigned (edenot ?E ?e))) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ (Z_to_bv 64 0x1b4d4) _ _ _ _) =>
          let BCE := fresh "BCE" in let B1 := fresh "B1" in let B2 := fresh "B2" in
          kx_read_ranges;
          lazymatch e with context [EVar ?j] => kx_enum BCE E e j 1 255%nat (fun v => (1 <=? v) && (v <=? 64))%bool end;
          cbv beta in BCE; apply andb_prop in BCE as [B1 B2]; apply Z.leb_le in B1, B2;
          eapply CONT with (d := 0);
          [ first [ eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR] | eapply seqd_iinv_eq2; [eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR] | repeat f_equal; lia] ]
          | split; [split; [lia | exact B2] | unfold bit_ok; cbn [q_SEQ q_sq]; rewrite <- En; intros; lia]
          | cbn [q_SEQ]; lia ]
      | |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 (-1 * Z.lxor (bv_unsigned (edenot ?E ?e)) 31 + 8)) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ (Z_to_bv 64 0x1b4d4) _ _ _ _) =>
          let BCE := fresh "BCE" in let B1 := fresh "B1" in let B2 := fresh "B2" in
          kx_read_ranges;
          lazymatch e with context [EVar ?j] => kx_enum BCE E e j 1 255%nat (fun v => (1 <=? -1 * Z.lxor v 31 + 8) && (-1 * Z.lxor v 31 + 8 <=? 8))%bool end;
          cbv beta in BCE; apply andb_prop in BCE as [B1 B2]; apply Z.leb_le in B1, B2;
          eapply CONT with (d := 0);
          [ first [ eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR] | eapply seqd_iinv_eq2; [eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR] | repeat f_equal; lia] ]
          | split; [split; [lia | lia] | unfold bit_ok; cbn [q_SEQ q_sq]; rewrite <- En; intros; lia]
          | cbn [q_SEQ]; lia ]
      | |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 (bv_unsigned (edenot ?E ?e) + 41)) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ (Z_to_bv 64 0x1b4d4) _ _ _ _) =>
          let BCE := fresh "BCE" in let B1 := fresh "B1" in let B2 := fresh "B2" in
          kx_read_ranges;
          lazymatch e with context [EVar ?j] => kx_enum BCE E e j 1 255%nat (fun v => (1 <=? (v + 41) mod 2^64) && ((v + 41) mod 2^64 <=? 64))%bool end;
          cbv beta in BCE; apply andb_prop in BCE as [B1 B2]; apply Z.leb_le in B1, B2;
          rewrite (zbv_mod (bv_unsigned (edenot E e) + 41));
          eapply CONT with (d := 0);
          [ first [ eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR] | eapply seqd_iinv_eq2; [eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR] | repeat f_equal; lia] ]
          | split; [split; [lia | exact B2] | unfold bit_ok; cbn [q_SEQ q_sq]; rewrite <- En; intros; lia]
          | cbn [q_SEQ]; lia ]
      end.
  - rewrite C in *; clear C.
    try hold TRANS. try hold CONT. try hold IEXIT. try hold RG0. try hold Esqb. try hold S1. try hold S2. try hold S3. try hold S4. try hold S5. try hold S6. try hold S7. try hold S8. try hold S9. try hold S10. try hold S11. try hold S12. try hold S15. try hold S16. try hold S18. try hold S19. try hold S20. try hold S21. try hold S22. try hold S23. try hold S24. try hold S25. try hold S26. try hold S27. try hold S28. try hold S29. try hold S30. try hold S31. try hold S32. try hold S33. try hold S34. try hold S35. try hold OKLL. try hold OKOF. try hold OKML.
    kx_autoLx [0x1b4d4; 0x1c070] 120%nat
    [KZRange SPV 496 (2^47); KZRange SEQ 4096 (2^47);  KZRange (SEQ + 2) 4096 (2^47); KZRange OEND 4096 (2^47); KZRange DCTX 4096 (2^47);
     KZWr (SPV - 304) 304; KZDisj (SPV - 304) 304 SEQ 2; KZImg 0x10000 0x14000]
    [(SEQ, 2)].
    all: kx_mem.
    all: (try unfold held in TRANS; try unfold held in CONT; try unfold held in IEXIT; try unfold held in RG0; try unfold held in Esqb; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S15; try unfold held in S16; try unfold held in S18; try unfold held in S19; try unfold held in S20; try unfold held in S21; try unfold held in S22; try unfold held in S23; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end).
    all: lazymatch goal with
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1c070) _ _ _ _) =>
          eapply IEXIT; [exact RG0 | eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR] | reflexivity | reflexivity | lia | left; reflexivity]
      | |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 (bv_unsigned (edenot ?E ?e))) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ (Z_to_bv 64 0x1b4d4) _ _ _ _) =>
          let BCE := fresh "BCE" in let B1 := fresh "B1" in let B2 := fresh "B2" in
          kx_read_ranges;
          lazymatch e with context [EVar ?j] => kx_enum BCE E e j 1 255%nat (fun v => (1 <=? v) && (v <=? 64))%bool end;
          cbv beta in BCE; apply andb_prop in BCE as [B1 B2]; apply Z.leb_le in B1, B2;
          eapply CONT with (d := 0);
          [ first [ eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR] | eapply seqd_iinv_eq2; [eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR] | repeat f_equal; lia] ]
          | split; [split; [lia | exact B2] | unfold bit_ok; cbn [q_SEQ q_sq]; rewrite <- En; intros; lia]
          | cbn [q_SEQ]; lia ]
      | |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 (-1 * Z.lxor (bv_unsigned (edenot ?E ?e)) 31 + 8)) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ (Z_to_bv 64 0x1b4d4) _ _ _ _) =>
          let BCE := fresh "BCE" in let B1 := fresh "B1" in let B2 := fresh "B2" in
          kx_read_ranges;
          lazymatch e with context [EVar ?j] => kx_enum BCE E e j 1 255%nat (fun v => (1 <=? -1 * Z.lxor v 31 + 8) && (-1 * Z.lxor v 31 + 8 <=? 8))%bool end;
          cbv beta in BCE; apply andb_prop in BCE as [B1 B2]; apply Z.leb_le in B1, B2;
          eapply CONT with (d := 0);
          [ first [ eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR] | eapply seqd_iinv_eq2; [eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR] | repeat f_equal; lia] ]
          | split; [split; [lia | lia] | unfold bit_ok; cbn [q_SEQ q_sq]; rewrite <- En; intros; lia]
          | cbn [q_SEQ]; lia ]
      | |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 (bv_unsigned (edenot ?E ?e) + 41)) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ (Z_to_bv 64 0x1b4d4) _ _ _ _) =>
          let BCE := fresh "BCE" in let B1 := fresh "B1" in let B2 := fresh "B2" in
          kx_read_ranges;
          lazymatch e with context [EVar ?j] => kx_enum BCE E e j 1 255%nat (fun v => (1 <=? (v + 41) mod 2^64) && ((v + 41) mod 2^64 <=? 64))%bool end;
          cbv beta in BCE; apply andb_prop in BCE as [B1 B2]; apply Z.leb_le in B1, B2;
          rewrite (zbv_mod (bv_unsigned (edenot E e) + 41));
          eapply CONT with (d := 0);
          [ first [ eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR] | eapply seqd_iinv_eq2; [eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR] | repeat f_equal; lia] ]
          | split; [split; [lia | exact B2] | unfold bit_ok; cbn [q_SEQ q_sq]; rewrite <- En; intros; lia]
          | cbn [q_SEQ]; lia ]
      end.
  - rewrite C in *; clear C.
    try hold TRANS. try hold CONT. try hold IEXIT. try hold RG0. try hold Esqb. try hold S1. try hold S2. try hold S3. try hold S4. try hold S5. try hold S6. try hold S7. try hold S8. try hold S9. try hold S10. try hold S11. try hold S12. try hold S15. try hold S16. try hold S18. try hold S19. try hold S20. try hold S21. try hold S22. try hold S23. try hold S24. try hold S25. try hold S26. try hold S27. try hold S28. try hold S29. try hold S30. try hold S31. try hold S32. try hold S33. try hold S34. try hold S35. try hold OKLL. try hold OKOF. try hold OKML.
    kx_autoLx [0x1b4d4; 0x1c070] 120%nat
    [KZRange SPV 496 (2^47); KZRange SEQ 4096 (2^47);  KZRange (SEQ + 3) 4096 (2^47); KZRange OEND 4096 (2^47); KZRange DCTX 4096 (2^47);
     KZWr (SPV - 304) 304; KZDisj (SPV - 304) 304 SEQ 3; KZImg 0x10000 0x14000]
    [(SEQ, 3)].
    all: kx_mem.
    all: (try unfold held in TRANS; try unfold held in CONT; try unfold held in IEXIT; try unfold held in RG0; try unfold held in Esqb; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S15; try unfold held in S16; try unfold held in S18; try unfold held in S19; try unfold held in S20; try unfold held in S21; try unfold held in S22; try unfold held in S23; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end).
    all: lazymatch goal with
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1c070) _ _ _ _) =>
          eapply IEXIT; [exact RG0 | eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR] | reflexivity | reflexivity | lia | left; reflexivity]
      | |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 (bv_unsigned (edenot ?E ?e))) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ (Z_to_bv 64 0x1b4d4) _ _ _ _) =>
          let BCE := fresh "BCE" in let B1 := fresh "B1" in let B2 := fresh "B2" in
          kx_read_ranges;
          lazymatch e with context [EVar ?j] => kx_enum BCE E e j 1 255%nat (fun v => (1 <=? v) && (v <=? 64))%bool end;
          cbv beta in BCE; apply andb_prop in BCE as [B1 B2]; apply Z.leb_le in B1, B2;
          eapply CONT with (d := 0);
          [ first [ eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR] | eapply seqd_iinv_eq2; [eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR] | repeat f_equal; lia] ]
          | split; [split; [lia | exact B2] | unfold bit_ok; cbn [q_SEQ q_sq]; rewrite <- En; intros; lia]
          | cbn [q_SEQ]; lia ]
      | |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 (-1 * Z.lxor (bv_unsigned (edenot ?E ?e)) 31 + 8)) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ (Z_to_bv 64 0x1b4d4) _ _ _ _) =>
          let BCE := fresh "BCE" in let B1 := fresh "B1" in let B2 := fresh "B2" in
          kx_read_ranges;
          lazymatch e with context [EVar ?j] => kx_enum BCE E e j 1 255%nat (fun v => (1 <=? -1 * Z.lxor v 31 + 8) && (-1 * Z.lxor v 31 + 8 <=? 8))%bool end;
          cbv beta in BCE; apply andb_prop in BCE as [B1 B2]; apply Z.leb_le in B1, B2;
          eapply CONT with (d := 0);
          [ first [ eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR] | eapply seqd_iinv_eq2; [eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR] | repeat f_equal; lia] ]
          | split; [split; [lia | lia] | unfold bit_ok; cbn [q_SEQ q_sq]; rewrite <- En; intros; lia]
          | cbn [q_SEQ]; lia ]
      | |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 (bv_unsigned (edenot ?E ?e) + 41)) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ (Z_to_bv 64 0x1b4d4) _ _ _ _) =>
          let BCE := fresh "BCE" in let B1 := fresh "B1" in let B2 := fresh "B2" in
          kx_read_ranges;
          lazymatch e with context [EVar ?j] => kx_enum BCE E e j 1 255%nat (fun v => (1 <=? (v + 41) mod 2^64) && ((v + 41) mod 2^64 <=? 64))%bool end;
          cbv beta in BCE; apply andb_prop in BCE as [B1 B2]; apply Z.leb_le in B1, B2;
          rewrite (zbv_mod (bv_unsigned (edenot E e) + 41));
          eapply CONT with (d := 0);
          [ first [ eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR] | eapply seqd_iinv_eq2; [eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR] | repeat f_equal; lia] ]
          | split; [split; [lia | exact B2] | unfold bit_ok; cbn [q_SEQ q_sq]; rewrite <- En; intros; lia]
          | cbn [q_SEQ]; lia ]
      end.
  - rewrite C in *; clear C.
    try hold TRANS. try hold CONT. try hold IEXIT. try hold RG0. try hold Esqb. try hold S1. try hold S2. try hold S3. try hold S4. try hold S5. try hold S6. try hold S7. try hold S8. try hold S9. try hold S10. try hold S11. try hold S12. try hold S15. try hold S16. try hold S18. try hold S19. try hold S20. try hold S21. try hold S22. try hold S23. try hold S24. try hold S25. try hold S26. try hold S27. try hold S28. try hold S29. try hold S30. try hold S31. try hold S32. try hold S33. try hold S34. try hold S35. try hold OKLL. try hold OKOF. try hold OKML.
    kx_autoLx [0x1b4d4; 0x1c070] 120%nat
    [KZRange SPV 496 (2^47); KZRange SEQ 4096 (2^47);  KZRange (SEQ + 4) 4096 (2^47); KZRange OEND 4096 (2^47); KZRange DCTX 4096 (2^47);
     KZWr (SPV - 304) 304; KZDisj (SPV - 304) 304 SEQ 4; KZImg 0x10000 0x14000]
    [(SEQ, 4)].
    all: kx_mem.
    all: (try unfold held in TRANS; try unfold held in CONT; try unfold held in IEXIT; try unfold held in RG0; try unfold held in Esqb; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S15; try unfold held in S16; try unfold held in S18; try unfold held in S19; try unfold held in S20; try unfold held in S21; try unfold held in S22; try unfold held in S23; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end).
    all: lazymatch goal with
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1c070) _ _ _ _) =>
          eapply IEXIT; [exact RG0 | eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR] | reflexivity | reflexivity | lia | left; reflexivity]
      | |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 (bv_unsigned (edenot ?E ?e))) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ (Z_to_bv 64 0x1b4d4) _ _ _ _) =>
          let BCE := fresh "BCE" in let B1 := fresh "B1" in let B2 := fresh "B2" in
          kx_read_ranges;
          lazymatch e with context [EVar ?j] => kx_enum BCE E e j 1 255%nat (fun v => (1 <=? v) && (v <=? 64))%bool end;
          cbv beta in BCE; apply andb_prop in BCE as [B1 B2]; apply Z.leb_le in B1, B2;
          eapply CONT with (d := 0);
          [ first [ eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR] | eapply seqd_iinv_eq2; [eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR] | repeat f_equal; lia] ]
          | split; [split; [lia | exact B2] | unfold bit_ok; cbn [q_SEQ q_sq]; rewrite <- En; intros; lia]
          | cbn [q_SEQ]; lia ]
      | |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 (-1 * Z.lxor (bv_unsigned (edenot ?E ?e)) 31 + 8)) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ (Z_to_bv 64 0x1b4d4) _ _ _ _) =>
          let BCE := fresh "BCE" in let B1 := fresh "B1" in let B2 := fresh "B2" in
          kx_read_ranges;
          lazymatch e with context [EVar ?j] => kx_enum BCE E e j 1 255%nat (fun v => (1 <=? -1 * Z.lxor v 31 + 8) && (-1 * Z.lxor v 31 + 8 <=? 8))%bool end;
          cbv beta in BCE; apply andb_prop in BCE as [B1 B2]; apply Z.leb_le in B1, B2;
          eapply CONT with (d := 0);
          [ first [ eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR] | eapply seqd_iinv_eq2; [eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR] | repeat f_equal; lia] ]
          | split; [split; [lia | lia] | unfold bit_ok; cbn [q_SEQ q_sq]; rewrite <- En; intros; lia]
          | cbn [q_SEQ]; lia ]
      | |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 (bv_unsigned (edenot ?E ?e) + 41)) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ (Z_to_bv 64 0x1b4d4) _ _ _ _) =>
          let BCE := fresh "BCE" in let B1 := fresh "B1" in let B2 := fresh "B2" in
          kx_read_ranges;
          lazymatch e with context [EVar ?j] => kx_enum BCE E e j 1 255%nat (fun v => (1 <=? (v + 41) mod 2^64) && ((v + 41) mod 2^64 <=? 64))%bool end;
          cbv beta in BCE; apply andb_prop in BCE as [B1 B2]; apply Z.leb_le in B1, B2;
          rewrite (zbv_mod (bv_unsigned (edenot E e) + 41));
          eapply CONT with (d := 0);
          [ first [ eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR] | eapply seqd_iinv_eq2; [eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR] | repeat f_equal; lia] ]
          | split; [split; [lia | exact B2] | unfold bit_ok; cbn [q_SEQ q_sq]; rewrite <- En; intros; lia]
          | cbn [q_SEQ]; lia ]
      end.
  - rewrite C in *; clear C.
    try hold TRANS. try hold CONT. try hold IEXIT. try hold RG0. try hold Esqb. try hold S1. try hold S2. try hold S3. try hold S4. try hold S5. try hold S6. try hold S7. try hold S8. try hold S9. try hold S10. try hold S11. try hold S12. try hold S15. try hold S16. try hold S18. try hold S19. try hold S20. try hold S21. try hold S22. try hold S23. try hold S24. try hold S25. try hold S26. try hold S27. try hold S28. try hold S29. try hold S30. try hold S31. try hold S32. try hold S33. try hold S34. try hold S35. try hold OKLL. try hold OKOF. try hold OKML.
    kx_autoLx [0x1b4d4; 0x1c070] 120%nat
    [KZRange SPV 496 (2^47); KZRange SEQ 4096 (2^47);  KZRange (SEQ + 5) 4096 (2^47); KZRange OEND 4096 (2^47); KZRange DCTX 4096 (2^47);
     KZWr (SPV - 304) 304; KZDisj (SPV - 304) 304 SEQ 5; KZImg 0x10000 0x14000]
    [(SEQ, 5)].
    all: kx_mem.
    all: (try unfold held in TRANS; try unfold held in CONT; try unfold held in IEXIT; try unfold held in RG0; try unfold held in Esqb; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S15; try unfold held in S16; try unfold held in S18; try unfold held in S19; try unfold held in S20; try unfold held in S21; try unfold held in S22; try unfold held in S23; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end).
    all: lazymatch goal with
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1c070) _ _ _ _) =>
          eapply IEXIT; [exact RG0 | eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR] | reflexivity | reflexivity | lia | left; reflexivity]
      | |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 (bv_unsigned (edenot ?E ?e))) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ (Z_to_bv 64 0x1b4d4) _ _ _ _) =>
          let BCE := fresh "BCE" in let B1 := fresh "B1" in let B2 := fresh "B2" in
          kx_read_ranges;
          lazymatch e with context [EVar ?j] => kx_enum BCE E e j 1 255%nat (fun v => (1 <=? v) && (v <=? 64))%bool end;
          cbv beta in BCE; apply andb_prop in BCE as [B1 B2]; apply Z.leb_le in B1, B2;
          eapply CONT with (d := 0);
          [ first [ eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR] | eapply seqd_iinv_eq2; [eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR] | repeat f_equal; lia] ]
          | split; [split; [lia | exact B2] | unfold bit_ok; cbn [q_SEQ q_sq]; rewrite <- En; intros; lia]
          | cbn [q_SEQ]; lia ]
      | |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 (-1 * Z.lxor (bv_unsigned (edenot ?E ?e)) 31 + 8)) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ (Z_to_bv 64 0x1b4d4) _ _ _ _) =>
          let BCE := fresh "BCE" in let B1 := fresh "B1" in let B2 := fresh "B2" in
          kx_read_ranges;
          lazymatch e with context [EVar ?j] => kx_enum BCE E e j 1 255%nat (fun v => (1 <=? -1 * Z.lxor v 31 + 8) && (-1 * Z.lxor v 31 + 8 <=? 8))%bool end;
          cbv beta in BCE; apply andb_prop in BCE as [B1 B2]; apply Z.leb_le in B1, B2;
          eapply CONT with (d := 0);
          [ first [ eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR] | eapply seqd_iinv_eq2; [eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR] | repeat f_equal; lia] ]
          | split; [split; [lia | lia] | unfold bit_ok; cbn [q_SEQ q_sq]; rewrite <- En; intros; lia]
          | cbn [q_SEQ]; lia ]
      | |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 (bv_unsigned (edenot ?E ?e) + 41)) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ (Z_to_bv 64 0x1b4d4) _ _ _ _) =>
          let BCE := fresh "BCE" in let B1 := fresh "B1" in let B2 := fresh "B2" in
          kx_read_ranges;
          lazymatch e with context [EVar ?j] => kx_enum BCE E e j 1 255%nat (fun v => (1 <=? (v + 41) mod 2^64) && ((v + 41) mod 2^64 <=? 64))%bool end;
          cbv beta in BCE; apply andb_prop in BCE as [B1 B2]; apply Z.leb_le in B1, B2;
          rewrite (zbv_mod (bv_unsigned (edenot E e) + 41));
          eapply CONT with (d := 0);
          [ first [ eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR] | eapply seqd_iinv_eq2; [eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR] | repeat f_equal; lia] ]
          | split; [split; [lia | exact B2] | unfold bit_ok; cbn [q_SEQ q_sq]; rewrite <- En; intros; lia]
          | cbn [q_SEQ]; lia ]
      end.
  - rewrite C in *; clear C.
    try hold TRANS. try hold CONT. try hold IEXIT. try hold RG0. try hold Esqb. try hold S1. try hold S2. try hold S3. try hold S4. try hold S5. try hold S6. try hold S7. try hold S8. try hold S9. try hold S10. try hold S11. try hold S12. try hold S15. try hold S16. try hold S18. try hold S19. try hold S20. try hold S21. try hold S22. try hold S23. try hold S24. try hold S25. try hold S26. try hold S27. try hold S28. try hold S29. try hold S30. try hold S31. try hold S32. try hold S33. try hold S34. try hold S35. try hold OKLL. try hold OKOF. try hold OKML.
    kx_autoLx [0x1b4d4; 0x1c070] 120%nat
    [KZRange SPV 496 (2^47); KZRange SEQ 4096 (2^47);  KZRange (SEQ + 6) 4096 (2^47); KZRange OEND 4096 (2^47); KZRange DCTX 4096 (2^47);
     KZWr (SPV - 304) 304; KZDisj (SPV - 304) 304 SEQ 6; KZImg 0x10000 0x14000]
    [(SEQ, 6)].
    all: kx_mem.
    all: (try unfold held in TRANS; try unfold held in CONT; try unfold held in IEXIT; try unfold held in RG0; try unfold held in Esqb; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S15; try unfold held in S16; try unfold held in S18; try unfold held in S19; try unfold held in S20; try unfold held in S21; try unfold held in S22; try unfold held in S23; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end).
    all: lazymatch goal with
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1c070) _ _ _ _) =>
          eapply IEXIT; [exact RG0 | eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR] | reflexivity | reflexivity | lia | left; reflexivity]
      | |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 (bv_unsigned (edenot ?E ?e))) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ (Z_to_bv 64 0x1b4d4) _ _ _ _) =>
          let BCE := fresh "BCE" in let B1 := fresh "B1" in let B2 := fresh "B2" in
          kx_read_ranges;
          lazymatch e with context [EVar ?j] => kx_enum BCE E e j 1 255%nat (fun v => (1 <=? v) && (v <=? 64))%bool end;
          cbv beta in BCE; apply andb_prop in BCE as [B1 B2]; apply Z.leb_le in B1, B2;
          eapply CONT with (d := 0);
          [ first [ eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR] | eapply seqd_iinv_eq2; [eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR] | repeat f_equal; lia] ]
          | split; [split; [lia | exact B2] | unfold bit_ok; cbn [q_SEQ q_sq]; rewrite <- En; intros; lia]
          | cbn [q_SEQ]; lia ]
      | |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 (-1 * Z.lxor (bv_unsigned (edenot ?E ?e)) 31 + 8)) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ (Z_to_bv 64 0x1b4d4) _ _ _ _) =>
          let BCE := fresh "BCE" in let B1 := fresh "B1" in let B2 := fresh "B2" in
          kx_read_ranges;
          lazymatch e with context [EVar ?j] => kx_enum BCE E e j 1 255%nat (fun v => (1 <=? -1 * Z.lxor v 31 + 8) && (-1 * Z.lxor v 31 + 8 <=? 8))%bool end;
          cbv beta in BCE; apply andb_prop in BCE as [B1 B2]; apply Z.leb_le in B1, B2;
          eapply CONT with (d := 0);
          [ first [ eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR] | eapply seqd_iinv_eq2; [eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR] | repeat f_equal; lia] ]
          | split; [split; [lia | lia] | unfold bit_ok; cbn [q_SEQ q_sq]; rewrite <- En; intros; lia]
          | cbn [q_SEQ]; lia ]
      | |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 (bv_unsigned (edenot ?E ?e) + 41)) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ (Z_to_bv 64 0x1b4d4) _ _ _ _) =>
          let BCE := fresh "BCE" in let B1 := fresh "B1" in let B2 := fresh "B2" in
          kx_read_ranges;
          lazymatch e with context [EVar ?j] => kx_enum BCE E e j 1 255%nat (fun v => (1 <=? (v + 41) mod 2^64) && ((v + 41) mod 2^64 <=? 64))%bool end;
          cbv beta in BCE; apply andb_prop in BCE as [B1 B2]; apply Z.leb_le in B1, B2;
          rewrite (zbv_mod (bv_unsigned (edenot E e) + 41));
          eapply CONT with (d := 0);
          [ first [ eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR] | eapply seqd_iinv_eq2; [eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR] | repeat f_equal; lia] ]
          | split; [split; [lia | exact B2] | unfold bit_ok; cbn [q_SEQ q_sq]; rewrite <- En; intros; lia]
          | cbn [q_SEQ]; lia ]
      end.
  - rewrite C in *; clear C.
    try hold TRANS. try hold CONT. try hold IEXIT. try hold RG0. try hold Esqb. try hold S1. try hold S2. try hold S3. try hold S4. try hold S5. try hold S6. try hold S7. try hold S8. try hold S9. try hold S10. try hold S11. try hold S12. try hold S15. try hold S16. try hold S18. try hold S19. try hold S20. try hold S21. try hold S22. try hold S23. try hold S24. try hold S25. try hold S26. try hold S27. try hold S28. try hold S29. try hold S30. try hold S31. try hold S32. try hold S33. try hold S34. try hold S35. try hold OKLL. try hold OKOF. try hold OKML.
    kx_autoLx [0x1b4d4; 0x1c070] 120%nat
    [KZRange SPV 496 (2^47); KZRange SEQ 4096 (2^47);  KZRange (SEQ + 7) 4096 (2^47); KZRange OEND 4096 (2^47); KZRange DCTX 4096 (2^47);
     KZWr (SPV - 304) 304; KZDisj (SPV - 304) 304 SEQ 7; KZImg 0x10000 0x14000]
    [(SEQ, 7)].
    all: kx_mem.
    all: (try unfold held in TRANS; try unfold held in CONT; try unfold held in IEXIT; try unfold held in RG0; try unfold held in Esqb; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S15; try unfold held in S16; try unfold held in S18; try unfold held in S19; try unfold held in S20; try unfold held in S21; try unfold held in S22; try unfold held in S23; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end).
    all: lazymatch goal with
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1c070) _ _ _ _) =>
          eapply IEXIT; [exact RG0 | eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR] | reflexivity | reflexivity | lia | left; reflexivity]
      | |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 (bv_unsigned (edenot ?E ?e))) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ (Z_to_bv 64 0x1b4d4) _ _ _ _) =>
          let BCE := fresh "BCE" in let B1 := fresh "B1" in let B2 := fresh "B2" in
          kx_read_ranges;
          lazymatch e with context [EVar ?j] => kx_enum BCE E e j 1 255%nat (fun v => (1 <=? v) && (v <=? 64))%bool end;
          cbv beta in BCE; apply andb_prop in BCE as [B1 B2]; apply Z.leb_le in B1, B2;
          eapply CONT with (d := 0);
          [ first [ eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR] | eapply seqd_iinv_eq2; [eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR] | repeat f_equal; lia] ]
          | split; [split; [lia | exact B2] | unfold bit_ok; cbn [q_SEQ q_sq]; rewrite <- En; intros; lia]
          | cbn [q_SEQ]; lia ]
      | |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 (-1 * Z.lxor (bv_unsigned (edenot ?E ?e)) 31 + 8)) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ (Z_to_bv 64 0x1b4d4) _ _ _ _) =>
          let BCE := fresh "BCE" in let B1 := fresh "B1" in let B2 := fresh "B2" in
          kx_read_ranges;
          lazymatch e with context [EVar ?j] => kx_enum BCE E e j 1 255%nat (fun v => (1 <=? -1 * Z.lxor v 31 + 8) && (-1 * Z.lxor v 31 + 8 <=? 8))%bool end;
          cbv beta in BCE; apply andb_prop in BCE as [B1 B2]; apply Z.leb_le in B1, B2;
          eapply CONT with (d := 0);
          [ first [ eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR] | eapply seqd_iinv_eq2; [eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR] | repeat f_equal; lia] ]
          | split; [split; [lia | lia] | unfold bit_ok; cbn [q_SEQ q_sq]; rewrite <- En; intros; lia]
          | cbn [q_SEQ]; lia ]
      | |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 (bv_unsigned (edenot ?E ?e) + 41)) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ (Z_to_bv 64 0x1b4d4) _ _ _ _) =>
          let BCE := fresh "BCE" in let B1 := fresh "B1" in let B2 := fresh "B2" in
          kx_read_ranges;
          lazymatch e with context [EVar ?j] => kx_enum BCE E e j 1 255%nat (fun v => (1 <=? (v + 41) mod 2^64) && ((v + 41) mod 2^64 <=? 64))%bool end;
          cbv beta in BCE; apply andb_prop in BCE as [B1 B2]; apply Z.leb_le in B1, B2;
          rewrite (zbv_mod (bv_unsigned (edenot E e) + 41));
          eapply CONT with (d := 0);
          [ first [ eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR] | eapply seqd_iinv_eq2; [eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR] | repeat f_equal; lia] ]
          | split; [split; [lia | exact B2] | unfold bit_ok; cbn [q_SEQ q_sq]; rewrite <- En; intros; lia]
          | cbn [q_SEQ]; lia ]
      end.
Qed.
