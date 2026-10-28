(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)


From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib Require CodeAt StepGen GwInst GwEq GwApply. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6nq.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q91D.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Lib.SepCache.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.SepCache.StrFun. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QWxq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWxq.Mq0.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UEQM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UEQM.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QgoP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QgoP.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q3CA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q3CA.
Import ListNotations. Unset Keyed Unification. Local Ltac OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_idioms ::= OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_idioms_3. Local Ltac OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_idioms_in H ::= OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_idioms_in_4 H. Local Ltac OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_wrap e ::= OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_wrap_1 e. Local Ltac OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_wrap_in e H ::= OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_wrap_in_2 e H.
Open Scope bv_scope.

From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib Require CodeAt StepGen GwInst GwApply.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition intscan_entry := 0x5e4f0%Z.
Lemma gw_eq_intscan_entry : @intscan_entry = ltac:(GwInst.gw_term (@Q91D.Mq1.intscan_entry 0x5e4f0) (@intscan_entry)). Proof. unfold intscan_entry, Q91D.Mq1.intscan_entry; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_intscan_entry : gw_eqs.
Definition ISTAB : Z := 0x16cd4.

Module GwI.
Definition segs := rsegs.
Definition base := 0x5e4f0%Z.
Definition w_23 := 0x92cfd0ef%Z.
Definition w_56 := 0x8a8fd0ef%Z.
Definition w_79 := 0xfffb8597%Z.
Definition w_80 := 0x6a858593%Z.
Definition w_91 := 0xfe5fc0ef%Z.
Definition w_92 := 0xd00f20ef%Z.
Definition w_98 := 0x800fd0ef%Z.
Definition w_114 := 0xfc1fc0ef%Z.
Definition w_133 := 0xfffb5517%Z.
Definition w_134 := 0xce453b03%Z.
Definition w_149 := 0xf35fc0ef%Z.
Definition w_160 := 0xf09fc0ef%Z.
Definition w_161 := 0xfffb8597%Z.
Definition w_162 := 0x56058593%Z.
Definition w_182 := 0xfffb8617%Z.
Definition w_183 := 0xfffb8697%Z.
Definition w_185 := 0x60d60613%Z.
Definition w_186 := 0x50868a93%Z.
Definition w_197 := 0xe75fc0ef%Z.
Definition w_224 := 0xe09fc0ef%Z.
Definition w_243 := 0xfffb8597%Z.
Definition w_244 := 0x41858a93%Z.
Definition w_253 := 0xd95fc0ef%Z.
Definition w_281 := 0xd25fc0ef%Z.
Definition w_305 := 0xfffb8597%Z.
Definition w_306 := 0x32058a93%Z.
Definition w_320 := 0xc89fc0ef%Z.
Definition w_333 := 0x93cf20ef%Z.
Definition w_346 := 0x908f20ef%Z.
Definition w_352 := 0x8f0f20ef%Z.
Definition w_359 := 0xbb5fc0ef%Z.
Definition hi_79 := (Z_to_bv 20 1048504).
Definition hi_133 := (Z_to_bv 20 1048501).
Definition hi_161 := (Z_to_bv 20 1048504).
Definition hi_182 := (Z_to_bv 20 1048504).
Definition hi_183 := (Z_to_bv 20 1048504).
Definition hi_243 := (Z_to_bv 20 1048504).
Definition hi_305 := (Z_to_bv 20 1048504).
Definition lo_80 := (Z_to_bv 12 1704).
Definition lo_134 := (Z_to_bv 12 3300).
Definition lo_162 := (Z_to_bv 12 1376).
Definition lo_185 := (Z_to_bv 12 1549).
Definition lo_186 := (Z_to_bv 12 1288).
Definition lo_244 := (Z_to_bv 12 1048).
Definition lo_306 := (Z_to_bv 12 800).
Definition joff_23 := (Z_to_bv 21 2085164).
Definition joff_56 := (Z_to_bv 21 2085032).
Definition joff_91 := (Z_to_bv 21 2084836).
Definition joff_92 := (Z_to_bv 21 2041088).
Definition joff_98 := (Z_to_bv 21 2084864).
Definition joff_114 := (Z_to_bv 21 2084800).
Definition joff_149 := (Z_to_bv 21 2084660).
Definition joff_160 := (Z_to_bv 21 2084616).
Definition joff_197 := (Z_to_bv 21 2084468).
Definition joff_224 := (Z_to_bv 21 2084360).
Definition joff_253 := (Z_to_bv 21 2084244).
Definition joff_281 := (Z_to_bv 21 2084132).
Definition joff_320 := (Z_to_bv 21 2083976).
Definition joff_333 := (Z_to_bv 21 2040124).
Definition joff_346 := (Z_to_bv 21 2040072).
Definition joff_352 := (Z_to_bv 21 2040048).
Definition joff_359 := (Z_to_bv 21 2083764).
Definition G_10760 := 0x133e8%Z.
Definition ISTAB := ISTAB.
Definition G_11b9d := 0x16dd5%Z.
Definition RATP := 0x77c00%Z.
Definition RGLOBALS_TOP := 0x99000%Z.
Definition e_errno_loc := 0x50b60%Z.
Definition e_shlim := 0x5b640%Z.
Definition e_21e74 := 0x5b678%Z.
Lemma CODE : CodeAt.code_at rsegs 0x5e4f0 (Q91D.Mq1.intscan_code 0x92cfd0ef%Z 0x8a8fd0ef%Z 0xfffb8597%Z 0x6a858593%Z 0xfe5fc0ef%Z 0xd00f20ef%Z 0x800fd0ef%Z 0xfc1fc0ef%Z 0xfffb5517%Z 0xce453b03%Z 0xf35fc0ef%Z 0xf09fc0ef%Z 0xfffb8597%Z 0x56058593%Z 0xfffb8617%Z 0xfffb8697%Z 0x60d60613%Z 0x50868a93%Z 0xe75fc0ef%Z 0xe09fc0ef%Z 0xfffb8597%Z 0x41858a93%Z 0xd95fc0ef%Z 0xd25fc0ef%Z 0xfffb8597%Z 0x32058a93%Z 0xc89fc0ef%Z 0x93cf20ef%Z 0x908f20ef%Z 0x8f0f20ef%Z 0xbb5fc0ef%Z).  Proof. StepGen.code_at_vm. Qed.
Lemma BASE4 : (0x5e4f0 mod 4 = 0)%Z.  Proof. reflexivity. Qed.
Lemma BASER : (0 <= 0x5e4f0 /\ 0x5e4f0 + 1496 <= 2^40)%Z.  Proof. vm_compute. split; discriminate. Qed.
Lemma CODE_e_errno_loc : CodeAt.code_at rsegs e_errno_loc Q91D.Mq1.errno_loc_code.  Proof. StepGen.code_at_vm. Qed.
Lemma CODE_e_shlim : CodeAt.code_at rsegs e_shlim Q91D.Mq1.shlim_code.  Proof. StepGen.code_at_vm. Qed.
Lemma D_305 : ltac2:(GwEq.gw_fact_ty 'segs '(@Q91D.Mq1.gw_all) @D_305). Proof. GwApply.gw_side. Qed.
Lemma E_305 : ltac2:(GwEq.gw_fact_ty 'segs '(@Q91D.Mq1.gw_all) @E_305). Proof. GwApply.gw_side. Qed.
Lemma D_306 : ltac2:(GwEq.gw_fact_ty 'segs '(@Q91D.Mq1.gw_all) @D_306). Proof. GwApply.gw_side. Qed.
Lemma E_306 : ltac2:(GwEq.gw_fact_ty 'segs '(@Q91D.Mq1.gw_all) @E_306). Proof. GwApply.gw_side. Qed.
Lemma D_333 : ltac2:(GwEq.gw_fact_ty 'segs '(@Q91D.Mq1.gw_all) @D_333). Proof. GwApply.gw_side. Qed.
Lemma E_333 : ltac2:(GwEq.gw_fact_ty 'segs '(@Q91D.Mq1.gw_all) @E_333). Proof. GwApply.gw_side. Qed.
Lemma D_346 : ltac2:(GwEq.gw_fact_ty 'segs '(@Q91D.Mq1.gw_all) @D_346). Proof. GwApply.gw_side. Qed.
Lemma E_346 : ltac2:(GwEq.gw_fact_ty 'segs '(@Q91D.Mq1.gw_all) @E_346). Proof. GwApply.gw_side. Qed.
Lemma D_352 : ltac2:(GwEq.gw_fact_ty 'segs '(@Q91D.Mq1.gw_all) @D_352). Proof. GwApply.gw_side. Qed.
Lemma E_352 : ltac2:(GwEq.gw_fact_ty 'segs '(@Q91D.Mq1.gw_all) @E_352). Proof. GwApply.gw_side. Qed.
Lemma ANCH_306 : ltac2:(GwEq.gw_fact_ty 'segs '(@Q91D.Mq1.gw_all) @ANCH_306). Proof. GwApply.gw_side. Qed.
Lemma LINK_333 : ltac2:(GwEq.gw_fact_ty 'segs '(@Q91D.Mq1.gw_all) @LINK_333). Proof. GwApply.gw_side. Qed.
Lemma LINK_346 : ltac2:(GwEq.gw_fact_ty 'segs '(@Q91D.Mq1.gw_all) @LINK_346). Proof. GwApply.gw_side. Qed.
Lemma LINK_352 : ltac2:(GwEq.gw_fact_ty 'segs '(@Q91D.Mq1.gw_all) @LINK_352). Proof. GwApply.gw_side. Qed.
Lemma LAY_lo_ISTAB : ltac2:(GwEq.gw_fact_ty 'segs '(@Q91D.Mq1.gw_all) @LAY_lo_ISTAB). Proof. GwApply.gw_side. Qed.
Lemma RNG_RATP : ltac2:(GwEq.gw_fact_ty 'segs '(@Q91D.Mq1.gw_all) @RNG_RATP). Proof. GwApply.gw_side. Qed.
Lemma LAY_lo_RATP : ltac2:(GwEq.gw_fact_ty 'segs '(@Q91D.Mq1.gw_all) @LAY_lo_RATP). Proof. GwApply.gw_side. Qed.
Lemma RNG_RGLOBALS_TOP : ltac2:(GwEq.gw_fact_ty 'segs '(@Q91D.Mq1.gw_all) @RNG_RGLOBALS_TOP). Proof. GwApply.gw_side. Qed.
Lemma LAY_ISTAB_RATP : ltac2:(GwEq.gw_fact_ty 'segs '(@Q91D.Mq1.gw_all) @LAY_ISTAB_RATP). Proof. GwApply.gw_side. Qed.
Lemma LAY_RATP_RGLOBALS_TOP : ltac2:(GwEq.gw_fact_ty 'segs '(@Q91D.Mq1.gw_all) @LAY_RATP_RGLOBALS_TOP). Proof. GwApply.gw_side. Qed.
Lemma ROM_ISTAB : ltac2:(GwEq.gw_fact_ty 'segs '(@Q91D.Mq1.gw_all) @ROM_ISTAB). Proof. first [ apply QWxq.Mq0.ro_bytes_b_sound; vm_compute; reflexivity | GwApply.gw_side ]. Qed.
Lemma ROM_G_10760 : ltac2:(GwEq.gw_fact_ty 'segs '(@Q91D.Mq1.gw_all) @ROM_G_10760). Proof. first [ apply QWxq.Mq0.ro_bytes_b_sound; vm_compute; reflexivity | GwApply.gw_side ]. Qed.
End GwI.

Definition M64m1 : Z := 18446744073709551615.
Lemma gw_eq_M64m1 : @M64m1 = ltac:(GwInst.gw_term (@Q91D.Mq1.M64m1) (@M64m1)). Proof. unfold M64m1, Q91D.Mq1.M64m1; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_M64m1 : gw_eqs.

Definition intscan_table_Z : list Z := [255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 255; 255; 255; 255; 255; 255; 255; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31; 32; 33; 34; 35; 255; 255; 255; 255; 255; 255; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31; 32; 33; 34; 35; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255]%Z.
Lemma gw_eq_intscan_table_Z : @intscan_table_Z = ltac:(GwInst.gw_term (@Q91D.Mq1.intscan_table_Z) (@intscan_table_Z)). Proof. unfold intscan_table_Z, Q91D.Mq1.intscan_table_Z; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_intscan_table_Z : gw_eqs.
Definition intscan_table : list byte := map (Z_to_bv 8) intscan_table_Z.
Lemma gw_eq_intscan_table : @intscan_table = ltac:(GwInst.gw_term (@Q91D.Mq1.intscan_table) (@intscan_table)). Proof. unfold intscan_table, Q91D.Mq1.intscan_table; rewrite ?gw_eq_intscan_table_Z; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_intscan_table : gw_eqs.
Definition itab (c : Z) : Z :=
(if (48 <=? c) && (c <=? 57) then c - 48
else if (65 <=? c) && (c <=? 90) then c - 55
else if (97 <=? c) && (c <=? 122) then c - 87 else 255)%Z%bool.
Lemma gw_eq_itab : @itab = ltac:(GwInst.gw_term (@Q91D.Mq1.itab) (@itab)). Proof. unfold itab, Q91D.Mq1.itab; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_itab : gw_eqs.

Lemma itab_range : forall c, (0 <= itab c < 256)%Z.
Proof. rewrite ?gw_eq_itab; first [GwInst.gw_exact (@Q91D.Mq1.itab_range) | autorewrite with gw_eqs; GwInst.gw_exact (@Q91D.Mq1.itab_range)]. Qed.

Lemma intscan_table_nth : forall c, (0 <= c < 256)%Z ->
nth_error intscan_table (Z.to_nat (c + 1)) = Some (Z_to_bv 8 (itab c)).
Proof. rewrite ?gw_eq_intscan_table, ?gw_eq_itab; first [GwInst.gw_exact (@Q91D.Mq1.intscan_table_nth) | autorewrite with gw_eqs; GwInst.gw_exact (@Q91D.Mq1.intscan_table_nth)]. Qed.

Lemma itab_lt10 : forall c, (0 <= c < 256)%Z -> (itab c < 10 <-> 48 <= c <= 57)%Z.
Proof. rewrite ?gw_eq_itab; first [GwInst.gw_exact (@Q91D.Mq1.itab_lt10) | autorewrite with gw_eqs; GwInst.gw_exact (@Q91D.Mq1.itab_lt10)]. Qed.

Lemma intscan_table_ro : forall m, mem_inv rsegs m -> ro_cells rsegs m 0x16cd4 [CB 257 intscan_table].
Proof. rewrite ?gw_eq_intscan_table; first [GwApply.gw_by_name GwI.segs (@Q91D.Mq1.intscan_table_ro) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@Q91D.Mq1.intscan_table_ro)]. Qed.

Lemma swrap32_byte_off : forall c k, (0 <= c < 256)%Z -> (-256 <= k <= 0)%Z -> bv_swrap 32 (c + k) = (c + k)%Z.
Proof. first [GwInst.gw_exact (@Q91D.Mq1.swrap32_byte_off) | autorewrite with gw_eqs; GwInst.gw_exact (@Q91D.Mq1.swrap32_byte_off)]. Qed.

Lemma digit_test : forall c, (0 <= c < 256)%Z ->
(((c + -48) mod 18446744073709551616 <= 9)%Z <-> (48 <= c <= 57)%Z).
Proof. first [GwInst.gw_exact (@Q91D.Mq1.digit_test) | autorewrite with gw_eqs; GwInst.gw_exact (@Q91D.Mq1.digit_test)]. Qed.

Lemma itab_unsigned : forall c, bv_unsigned (Z_to_bv 8 (itab c)) = itab c.
Proof. rewrite ?gw_eq_itab; first [GwInst.gw_exact (@Q91D.Mq1.itab_unsigned) | autorewrite with gw_eqs; GwInst.gw_exact (@Q91D.Mq1.itab_unsigned)]. Qed.

Definition file_cells (j0 j1 j2 j3 : list byte) (rp A shcnt : Z) : list cell :=
[CB 8 j0; C8 (Z_to_bv 64 rp); C8 (Z_to_bv 64 M64m1); CB 64 j1; C8 (Z_to_bv 64 A); CB 88 j2;
C8 (Z_to_bv 64 M64m1); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 shcnt); CB 24 j3].
Lemma gw_eq_file_cells : @file_cells = ltac:(GwInst.gw_term (@Q91D.Mq1.file_cells) (@file_cells)). Proof. unfold file_cells, Q91D.Mq1.file_cells; rewrite ?gw_eq_M64m1; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_file_cells : gw_eqs.

Definition intscan_W (SP F0 : Z) : list ivl :=
[(SP - 80, SP); (F0, F0 + 232); (0x77c00 - 164, 0x77c00 - 160)]%Z.
Lemma gw_eq_intscan_W : @intscan_W = ltac:(GwInst.gw_term (@Q91D.Mq1.intscan_W 0x77c00%Z) (@intscan_W)). Proof. unfold intscan_W, Q91D.Mq1.intscan_W; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_intscan_W : gw_eqs.

Definition intscan_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(SP F0 A : Z) (str : list byte) (j0 j1 j2 j3 : list byte) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists x5 x6 x7 a0' a1' a2' a3' a4' a5' a6' a7' x28 x29 x30 x31 m' (k sc : Z) (e' : word),
ms' = MS (mkR ra sp gp tp x5 x6 x7 s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
F (ret_pc ra) fc None m' (seg_rom rsegs)
/\ munch (intscan_W SP F0) m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ rw_cells rsegs m' F0 (file_cells j0 j1 j2 j3 (A + k) A sc)
/\ (0 <= k <= Z.of_nat (length str))%Z /\ (0 <= sc + k <= Z.of_nat (length str))%Z
/\ bytes_at rsegs m' A (str ++ [b0])
/\ rw_cells rsegs m' (0x77c00 - 164) [C4 e']
/\ stk rsegs m' lo SP.
Lemma gw_eq_intscan_post : @intscan_post = ltac:(GwInst.gw_term (@Q91D.Mq1.intscan_post rsegs 0x77c00%Z) (@intscan_post)). Proof. unfold intscan_post, Q91D.Mq1.intscan_post; rewrite ?gw_eq_file_cells, ?gw_eq_intscan_W; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_intscan_post : gw_eqs.

Definition intscan_stmt : Prop :=
forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (str j0 j1 j2 j3 : list byte) (A lo SP F0 : Z) (e : word),
a1 = Z_to_bv 64 10 -> a2 = Z_to_bv 64 1 ->
bv_unsigned sp = SP -> bv_unsigned a0 = F0 ->
rw_cells rsegs m F0 (file_cells j0 j1 j2 j3 A A 0) ->
bytes_at rsegs m A (str ++ [b0]) -> ~ In b0 str -> (A + Z.of_nat (length str) + 2 <= 2^64)%Z ->
rw_cells rsegs m (0x77c00 - 164) [C4 e] ->
tp = Z_to_bv 64 0x77c00 ->
stk rsegs m lo SP -> (0x99000 <= lo)%Z -> (lo <= SP - 80)%Z ->

(F0 + 232 <= SP - 80 \/ SP <= F0)%Z ->
(0x99000 <= F0)%Z ->
(A + Z.of_nat (length str) + 1 <= SP - 80 \/ SP <= A)%Z ->
(A + Z.of_nat (length str) + 1 <= F0 \/ F0 + 232 <= A)%Z ->
(A + Z.of_nat (length str) + 1 <= 0x77c00 - 164 \/ 0x77c00 - 160 <= A)%Z ->
mem_inv rsegs m ->
evt rsegs (intscan_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SP F0 A str j0 j1 j2 j3 lo m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x5e4f0) fc None m (seg_rom rsegs)).
Lemma gw_eq_intscan_stmt : @intscan_stmt = ltac:(GwInst.gw_term (@Q91D.Mq1.intscan_stmt rsegs 0x5e4f0 0x77c00%Z 0x99000%Z) (@intscan_stmt)). Proof. unfold intscan_stmt, Q91D.Mq1.intscan_stmt; rewrite ?gw_eq_file_cells, ?gw_eq_intscan_post; ltac2:(GwEq.gw_rw [[@gw_eq_frame__3; @gw_eq_frame__2; @gw_eq_frame]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_intscan_stmt : gw_eqs.

Section Proofs.
Variables (ra sp gp tp t0 t1 t2 s0 s1 f0 lim a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m0 : word -> option byte) (str j0 j1 j2 j3 : list byte) (A lo : Z).
Notation F0 := (bv_unsigned f0).
Notation len := (Z.of_nat (length str)).
Notation W := (intscan_W (bv_unsigned sp) F0).
Notation FRC := [C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
Hypothesis NONUL : ~ In b0 str.
Hypothesis BND : (0 <= A /\ A + len + 2 <= 2^64 /\ 0x99000 <= lo /\ lo <= bv_unsigned sp - 80 /\ bv_unsigned sp <= 2^64
/\ 0x99000 <= F0 /\ F0 + 232 <= 2^64
/\ (F0 + 232 <= bv_unsigned sp - 80 \/ bv_unsigned sp <= F0)
/\ (A + len + 1 <= bv_unsigned sp - 80 \/ bv_unsigned sp <= A)
/\ (A + len + 1 <= F0 \/ F0 + 232 <= A)
/\ (A + len + 1 <= 0x77c00 - 164 \/ 0x77c00 - 160 <= A))%Z.
Hypothesis TPV : bv_unsigned tp = 0x77c00%Z.
Notation ERRA := (bv_unsigned tp + -164)%Z.

Definition ISI (m1 : word -> option byte) (rp : Z) (e : word) : Prop :=
rw_cells rsegs m1 F0 (file_cells j0 j1 j2 j3 rp A 0) /\
bytes_at rsegs m1 A (str ++ [b0]) /\
rw_cells rsegs m1 (bv_unsigned sp + -80) FRC /\
rw_cells rsegs m1 ERRA [C4 e] /\
ro_cells rsegs m1 0x16cd4 [CB 257 intscan_table] /\
stk rsegs m1 lo (bv_unsigned sp + -80) /\
mem_inv rsegs m1 /\ munch W m0 m1 /\ wmono rsegs m0 m1.
Lemma gw_eq_ISI : @ISI = ltac:(GwInst.gw_term (@Q91D.Mq1.ISI rsegs ISTAB 0x77c00%Z) (@ISI)). Proof. unfold ISI, Q91D.Mq1.ISI; rewrite ?gw_eq_intscan_table, ?gw_eq_file_cells; ltac2:(GwEq.gw_rw [[@gw_eq_W__3; @gw_eq_W__2; @gw_eq_W]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_ISI : gw_eqs.

#[using="NONUL"] Lemma str_nth : ltac2:(Q6nq.ty1 'GwI.segs '(@Q91D.Mq1.str_nth) [[@gw_eq_intscan_entry__3; @gw_eq_intscan_entry__2; @gw_eq_intscan_entry]; [@gw_eq_M64m1__3; @gw_eq_M64m1__2; @gw_eq_M64m1]; [@gw_eq_intscan_table_Z__3; @gw_eq_intscan_table_Z__2; @gw_eq_intscan_table_Z]; [@gw_eq_intscan_table__3; @gw_eq_intscan_table__2; @gw_eq_intscan_table]; [@gw_eq_itab__3; @gw_eq_itab__2; @gw_eq_itab]; [@gw_eq_file_cells__3; @gw_eq_file_cells__2; @gw_eq_file_cells]; [@gw_eq_intscan_W__3; @gw_eq_intscan_W__2; @gw_eq_intscan_W]; [@gw_eq_intscan_post__3; @gw_eq_intscan_post__2; @gw_eq_intscan_post]; [@gw_eq_intscan_stmt__3; @gw_eq_intscan_stmt__2; @gw_eq_intscan_stmt]; [@gw_eq_ISI__3; @gw_eq_ISI__2; @gw_eq_ISI]] '(@nil Z) 'Q6nq.gwt_nil).
Proof. first [GwApply.gw_by_name GwI.segs (@Q91D.Mq1.str_nth) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@Q91D.Mq1.str_nth)]. Qed.

#[using="BND TPV"] Lemma is_ret : ltac2:(Q6nq.ty1 'GwI.segs '(@Q91D.Mq1.is_ret) [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]; [@gw_eq_W__3; @gw_eq_W__2; @gw_eq_W]; [@gw_eq_file_cells]; [@gw_eq_intscan_entry__3; @gw_eq_intscan_entry__2; @gw_eq_intscan_entry]; [@gw_eq_M64m1__3; @gw_eq_M64m1__2; @gw_eq_M64m1]; [@gw_eq_intscan_table_Z__3; @gw_eq_intscan_table_Z__2; @gw_eq_intscan_table_Z]; [@gw_eq_intscan_table__3; @gw_eq_intscan_table__2; @gw_eq_intscan_table]; [@gw_eq_itab__3; @gw_eq_itab__2; @gw_eq_itab]; [@gw_eq_intscan_W__3; @gw_eq_intscan_W__2; @gw_eq_intscan_W]; [@gw_eq_intscan_post__3; @gw_eq_intscan_post__2; @gw_eq_intscan_post]; [@gw_eq_intscan_stmt__3; @gw_eq_intscan_stmt__2; @gw_eq_intscan_stmt]; [@gw_eq_ISI__3; @gw_eq_ISI__2; @gw_eq_ISI]] '([(-80); 387732]%Z : list Z) 'Q6nq.gwt_nil).
Proof. rewrite ?gw_eq_file_cells; ltac2:(GwEq.gw_rw [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]; [@gw_eq_W__3; @gw_eq_W__2; @gw_eq_W]]); first [GwApply.gw_by_name GwI.segs (@Q91D.Mq1.is_ret) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@Q91D.Mq1.is_ret)]. Qed.

#[using="BND TPV"] Lemma is_tail : ltac2:(Q6nq.ty1 'GwI.segs '(@Q91D.Mq1.is_tail) [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]; [@gw_eq_W__3; @gw_eq_W__2; @gw_eq_W]; [@gw_eq_file_cells]; [@gw_eq_intscan_entry__3; @gw_eq_intscan_entry__2; @gw_eq_intscan_entry]; [@gw_eq_M64m1__3; @gw_eq_M64m1__2; @gw_eq_M64m1]; [@gw_eq_intscan_table_Z__3; @gw_eq_intscan_table_Z__2; @gw_eq_intscan_table_Z]; [@gw_eq_intscan_table__3; @gw_eq_intscan_table__2; @gw_eq_intscan_table]; [@gw_eq_itab__3; @gw_eq_itab__2; @gw_eq_itab]; [@gw_eq_intscan_W__3; @gw_eq_intscan_W__2; @gw_eq_intscan_W]; [@gw_eq_intscan_post__3; @gw_eq_intscan_post__2; @gw_eq_intscan_post]; [@gw_eq_intscan_stmt__3; @gw_eq_intscan_stmt__2; @gw_eq_intscan_stmt]; [@gw_eq_ISI__3; @gw_eq_ISI__2; @gw_eq_ISI]] '([(-80); 387548]%Z : list Z) 'Q6nq.gwt_nil).
Proof. rewrite ?gw_eq_file_cells; ltac2:(GwEq.gw_rw [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]; [@gw_eq_W__3; @gw_eq_W__2; @gw_eq_W]]); first [GwApply.gw_by_name GwI.segs (@Q91D.Mq1.is_tail) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@Q91D.Mq1.is_tail)]. Qed.

#[using="Type"] Lemma tab_read : ltac2:(Q6nq.ty1 'GwI.segs '(@Q91D.Mq1.tab_read) [[@gw_eq_intscan_table]; [@gw_eq_itab]; [@gw_eq_intscan_entry__3; @gw_eq_intscan_entry__2; @gw_eq_intscan_entry]; [@gw_eq_M64m1__3; @gw_eq_M64m1__2; @gw_eq_M64m1]; [@gw_eq_intscan_table_Z__3; @gw_eq_intscan_table_Z__2; @gw_eq_intscan_table_Z]; [@gw_eq_file_cells__3; @gw_eq_file_cells__2; @gw_eq_file_cells]; [@gw_eq_intscan_W__3; @gw_eq_intscan_W__2; @gw_eq_intscan_W]; [@gw_eq_intscan_post__3; @gw_eq_intscan_post__2; @gw_eq_intscan_post]; [@gw_eq_intscan_stmt__3; @gw_eq_intscan_stmt__2; @gw_eq_intscan_stmt]; [@gw_eq_ISI__3; @gw_eq_ISI__2; @gw_eq_ISI]] '([257; 93396]%Z : list Z) '(Q6nq.gwt_unf (@ISTAB) (Q6nq.gwt_pat (@ISTAB) (@ISTAB) (Q6nq.gwt_hdr GwI.ISTAB (@ISTAB) Q6nq.gwt_nil)))).
Proof. rewrite ?gw_eq_intscan_table, ?gw_eq_itab; first [GwApply.gw_by_name GwI.segs (@Q91D.Mq1.tab_read) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@Q91D.Mq1.tab_read)]. Qed.

#[using="BND TPV"] Lemma is_einval : ltac2:(Q6nq.ty1 'GwI.segs '(@Q91D.Mq1.is_einval) [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]; [@gw_eq_ISI]; [@gw_eq_intscan_entry__3; @gw_eq_intscan_entry__2; @gw_eq_intscan_entry]; [@gw_eq_M64m1__3; @gw_eq_M64m1__2; @gw_eq_M64m1]; [@gw_eq_intscan_table_Z__3; @gw_eq_intscan_table_Z__2; @gw_eq_intscan_table_Z]; [@gw_eq_intscan_table__3; @gw_eq_intscan_table__2; @gw_eq_intscan_table]; [@gw_eq_itab__3; @gw_eq_itab__2; @gw_eq_itab]; [@gw_eq_file_cells__3; @gw_eq_file_cells__2; @gw_eq_file_cells]; [@gw_eq_intscan_W__3; @gw_eq_intscan_W__2; @gw_eq_intscan_W]; [@gw_eq_intscan_post__3; @gw_eq_intscan_post__2; @gw_eq_intscan_post]; [@gw_eq_intscan_stmt__3; @gw_eq_intscan_stmt__2; @gw_eq_intscan_stmt]] '([386624]%Z : list Z) 'Q6nq.gwt_nil).
Proof. rewrite ?gw_eq_ISI; ltac2:(GwEq.gw_rw [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]]); first [GwApply.gw_by_name GwI.segs (@Q91D.Mq1.is_einval) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@Q91D.Mq1.is_einval)]. Qed.

#[using="BND TPV"] Lemma is_done : ltac2:(Q6nq.ty1 'GwI.segs '(@Q91D.Mq1.is_done) [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]; [@gw_eq_ISI]; [@gw_eq_intscan_entry__3; @gw_eq_intscan_entry__2; @gw_eq_intscan_entry]; [@gw_eq_M64m1__3; @gw_eq_M64m1__2; @gw_eq_M64m1]; [@gw_eq_intscan_table_Z__3; @gw_eq_intscan_table_Z__2; @gw_eq_intscan_table_Z]; [@gw_eq_intscan_table__3; @gw_eq_intscan_table__2; @gw_eq_intscan_table]; [@gw_eq_itab__3; @gw_eq_itab__2; @gw_eq_itab]; [@gw_eq_file_cells__3; @gw_eq_file_cells__2; @gw_eq_file_cells]; [@gw_eq_intscan_W__3; @gw_eq_intscan_W__2; @gw_eq_intscan_W]; [@gw_eq_intscan_post__3; @gw_eq_intscan_post__2; @gw_eq_intscan_post]; [@gw_eq_intscan_stmt__3; @gw_eq_intscan_stmt__2; @gw_eq_intscan_stmt]] '([387528]%Z : list Z) 'Q6nq.gwt_nil).
Proof. rewrite ?gw_eq_ISI; ltac2:(GwEq.gw_rw [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]]); first [GwApply.gw_by_name GwI.segs (@Q91D.Mq1.is_done) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@Q91D.Mq1.is_done)]. Qed.

#[using="NONUL BND TPV"] Lemma is_ovf_loop : ltac2:(Q6nq.ty1 'GwI.segs '(@Q91D.Mq1.is_ovf_loop) [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]; [@gw_eq_ISI]; [@gw_eq_intscan_entry__3; @gw_eq_intscan_entry__2; @gw_eq_intscan_entry]; [@gw_eq_M64m1__3; @gw_eq_M64m1__2; @gw_eq_M64m1]; [@gw_eq_intscan_table_Z__3; @gw_eq_intscan_table_Z__2; @gw_eq_intscan_table_Z]; [@gw_eq_intscan_table__3; @gw_eq_intscan_table__2; @gw_eq_intscan_table]; [@gw_eq_itab__3; @gw_eq_itab__2; @gw_eq_itab]; [@gw_eq_file_cells__3; @gw_eq_file_cells__2; @gw_eq_file_cells]; [@gw_eq_intscan_W__3; @gw_eq_intscan_W__2; @gw_eq_intscan_W]; [@gw_eq_intscan_post__3; @gw_eq_intscan_post__2; @gw_eq_intscan_post]; [@gw_eq_intscan_stmt__3; @gw_eq_intscan_stmt__2; @gw_eq_intscan_stmt]] '([93396; 387584]%Z : list Z) '(Q6nq.gwt_unf (@ISTAB) (Q6nq.gwt_pat (@ISTAB) (@ISTAB) (Q6nq.gwt_hdr GwI.ISTAB (@ISTAB) Q6nq.gwt_nil)))).
Proof. rewrite ?gw_eq_ISI; ltac2:(GwEq.gw_rw [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]]); first [GwApply.gw_by_name GwI.segs (@Q91D.Mq1.is_ovf_loop) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@Q91D.Mq1.is_ovf_loop)]. Qed.

#[using="NONUL BND TPV"] Lemma is_ovf : ltac2:(Q6nq.ty1 'GwI.segs '(@Q91D.Mq1.is_ovf) [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]; [@gw_eq_ISI]; [@gw_eq_intscan_entry__3; @gw_eq_intscan_entry__2; @gw_eq_intscan_entry]; [@gw_eq_M64m1__3; @gw_eq_M64m1__2; @gw_eq_M64m1]; [@gw_eq_intscan_table_Z__3; @gw_eq_intscan_table_Z__2; @gw_eq_intscan_table_Z]; [@gw_eq_intscan_table__3; @gw_eq_intscan_table__2; @gw_eq_intscan_table]; [@gw_eq_itab__3; @gw_eq_itab__2; @gw_eq_itab]; [@gw_eq_file_cells__3; @gw_eq_file_cells__2; @gw_eq_file_cells]; [@gw_eq_intscan_W__3; @gw_eq_intscan_W__2; @gw_eq_intscan_W]; [@gw_eq_intscan_post__3; @gw_eq_intscan_post__2; @gw_eq_intscan_post]; [@gw_eq_intscan_stmt__3; @gw_eq_intscan_stmt__2; @gw_eq_intscan_stmt]] '([387508]%Z : list Z) 'Q6nq.gwt_nil).
Proof. rewrite ?gw_eq_ISI; ltac2:(GwEq.gw_rw [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]]); first [GwApply.gw_by_name GwI.segs (@Q91D.Mq1.is_ovf) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@Q91D.Mq1.is_ovf)]. Qed.

#[using="NONUL BND TPV"] Lemma is_l2 : ltac2:(Q6nq.ty1 'GwI.segs '(@Q91D.Mq1.is_l2) [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]; [@gw_eq_ISI]; [@gw_eq_intscan_entry__3; @gw_eq_intscan_entry__2; @gw_eq_intscan_entry]; [@gw_eq_M64m1__3; @gw_eq_M64m1__2; @gw_eq_M64m1]; [@gw_eq_intscan_table_Z__3; @gw_eq_intscan_table_Z__2; @gw_eq_intscan_table_Z]; [@gw_eq_intscan_table__3; @gw_eq_intscan_table__2; @gw_eq_intscan_table]; [@gw_eq_itab__3; @gw_eq_itab__2; @gw_eq_itab]; [@gw_eq_file_cells__3; @gw_eq_file_cells__2; @gw_eq_file_cells]; [@gw_eq_intscan_W__3; @gw_eq_intscan_W__2; @gw_eq_intscan_W]; [@gw_eq_intscan_post__3; @gw_eq_intscan_post__2; @gw_eq_intscan_post]; [@gw_eq_intscan_stmt__3; @gw_eq_intscan_stmt__2; @gw_eq_intscan_stmt]] '([386840; 1844674407370955162]%Z : list Z) 'Q6nq.gwt_nil).
Proof. rewrite ?gw_eq_ISI; ltac2:(GwEq.gw_rw [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]]); first [GwApply.gw_by_name GwI.segs (@Q91D.Mq1.is_l2) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@Q91D.Mq1.is_l2)]. Qed.

#[using="NONUL BND TPV"] Lemma is_l2_entry : ltac2:(Q6nq.ty1 'GwI.segs '(@Q91D.Mq1.is_l2_entry) [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]; [@gw_eq_ISI]; [@gw_eq_intscan_entry__3; @gw_eq_intscan_entry__2; @gw_eq_intscan_entry]; [@gw_eq_M64m1__3; @gw_eq_M64m1__2; @gw_eq_M64m1]; [@gw_eq_intscan_table_Z__3; @gw_eq_intscan_table_Z__2; @gw_eq_intscan_table_Z]; [@gw_eq_intscan_table__3; @gw_eq_intscan_table__2; @gw_eq_intscan_table]; [@gw_eq_itab__3; @gw_eq_itab__2; @gw_eq_itab]; [@gw_eq_file_cells__3; @gw_eq_file_cells__2; @gw_eq_file_cells]; [@gw_eq_intscan_W__3; @gw_eq_intscan_W__2; @gw_eq_intscan_W]; [@gw_eq_intscan_post__3; @gw_eq_intscan_post__2; @gw_eq_intscan_post]; [@gw_eq_intscan_stmt__3; @gw_eq_intscan_stmt__2; @gw_eq_intscan_stmt]] '([386820]%Z : list Z) 'Q6nq.gwt_nil).
Proof. rewrite ?gw_eq_ISI; ltac2:(GwEq.gw_rw [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]]); first [GwApply.gw_by_name GwI.segs (@Q91D.Mq1.is_l2_entry) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@Q91D.Mq1.is_l2_entry)]. Qed.

#[using="NONUL BND TPV"] Lemma is_l1 : ltac2:(Q6nq.ty1 'GwI.segs '(@Q91D.Mq1.is_l1) [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]; [@gw_eq_ISI]; [@gw_eq_intscan_entry__3; @gw_eq_intscan_entry__2; @gw_eq_intscan_entry]; [@gw_eq_M64m1__3; @gw_eq_M64m1__2; @gw_eq_M64m1]; [@gw_eq_intscan_table_Z__3; @gw_eq_intscan_table_Z__2; @gw_eq_intscan_table_Z]; [@gw_eq_intscan_table__3; @gw_eq_intscan_table__2; @gw_eq_intscan_table]; [@gw_eq_itab__3; @gw_eq_itab__2; @gw_eq_itab]; [@gw_eq_file_cells__3; @gw_eq_file_cells__2; @gw_eq_file_cells]; [@gw_eq_intscan_W__3; @gw_eq_intscan_W__2; @gw_eq_intscan_W]; [@gw_eq_intscan_post__3; @gw_eq_intscan_post__2; @gw_eq_intscan_post]; [@gw_eq_intscan_stmt__3; @gw_eq_intscan_stmt__2; @gw_eq_intscan_stmt]] '([386768; 429496729]%Z : list Z) 'Q6nq.gwt_nil).
Proof. rewrite ?gw_eq_ISI; ltac2:(GwEq.gw_rw [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]]); first [GwApply.gw_by_name GwI.segs (@Q91D.Mq1.is_l1) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@Q91D.Mq1.is_l1)]. Qed.

#[using="NONUL BND TPV"] Lemma is_dig : ltac2:(Q6nq.ty1 'GwI.segs '(@Q91D.Mq1.is_dig) [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]; [@gw_eq_ISI]; [@gw_eq_intscan_entry__3; @gw_eq_intscan_entry__2; @gw_eq_intscan_entry]; [@gw_eq_M64m1__3; @gw_eq_M64m1__2; @gw_eq_M64m1]; [@gw_eq_intscan_table_Z__3; @gw_eq_intscan_table_Z__2; @gw_eq_intscan_table_Z]; [@gw_eq_intscan_table__3; @gw_eq_intscan_table__2; @gw_eq_intscan_table]; [@gw_eq_itab__3; @gw_eq_itab__2; @gw_eq_itab]; [@gw_eq_file_cells__3; @gw_eq_file_cells__2; @gw_eq_file_cells]; [@gw_eq_intscan_W__3; @gw_eq_intscan_W__2; @gw_eq_intscan_W]; [@gw_eq_intscan_post__3; @gw_eq_intscan_post__2; @gw_eq_intscan_post]; [@gw_eq_intscan_stmt__3; @gw_eq_intscan_stmt__2; @gw_eq_intscan_stmt]] '([386700]%Z : list Z) 'Q6nq.gwt_nil).
Proof. rewrite ?gw_eq_ISI; ltac2:(GwEq.gw_rw [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]]); first [GwApply.gw_by_name GwI.segs (@Q91D.Mq1.is_dig) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@Q91D.Mq1.is_dig)]. Qed.

#[using="NONUL BND TPV"] Lemma is_chk : ltac2:(Q6nq.ty1 'GwI.segs '(@Q91D.Mq1.is_chk) [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]; [@gw_eq_ISI]; [@gw_eq_intscan_entry__3; @gw_eq_intscan_entry__2; @gw_eq_intscan_entry]; [@gw_eq_M64m1__3; @gw_eq_M64m1__2; @gw_eq_M64m1]; [@gw_eq_intscan_table_Z__3; @gw_eq_intscan_table_Z__2; @gw_eq_intscan_table_Z]; [@gw_eq_intscan_table__3; @gw_eq_intscan_table__2; @gw_eq_intscan_table]; [@gw_eq_itab__3; @gw_eq_itab__2; @gw_eq_itab]; [@gw_eq_file_cells__3; @gw_eq_file_cells__2; @gw_eq_file_cells]; [@gw_eq_intscan_W__3; @gw_eq_intscan_W__2; @gw_eq_intscan_W]; [@gw_eq_intscan_post__3; @gw_eq_intscan_post__2; @gw_eq_intscan_post]; [@gw_eq_intscan_stmt__3; @gw_eq_intscan_stmt__2; @gw_eq_intscan_stmt]] '([386596]%Z : list Z) 'Q6nq.gwt_nil).
Proof. rewrite ?gw_eq_ISI; ltac2:(GwEq.gw_rw [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]]); first [GwApply.gw_by_name GwI.segs (@Q91D.Mq1.is_chk) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@Q91D.Mq1.is_chk)]. Qed.

#[using="NONUL BND TPV"] Lemma is_sign : ltac2:(Q6nq.ty1 'GwI.segs '(@Q91D.Mq1.is_sign) [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]; [@gw_eq_ISI]; [@gw_eq_intscan_entry__3; @gw_eq_intscan_entry__2; @gw_eq_intscan_entry]; [@gw_eq_M64m1__3; @gw_eq_M64m1__2; @gw_eq_M64m1]; [@gw_eq_intscan_table_Z__3; @gw_eq_intscan_table_Z__2; @gw_eq_intscan_table_Z]; [@gw_eq_intscan_table__3; @gw_eq_intscan_table__2; @gw_eq_intscan_table]; [@gw_eq_itab__3; @gw_eq_itab__2; @gw_eq_itab]; [@gw_eq_file_cells__3; @gw_eq_file_cells__2; @gw_eq_file_cells]; [@gw_eq_intscan_W__3; @gw_eq_intscan_W__2; @gw_eq_intscan_W]; [@gw_eq_intscan_post__3; @gw_eq_intscan_post__2; @gw_eq_intscan_post]; [@gw_eq_intscan_stmt__3; @gw_eq_intscan_stmt__2; @gw_eq_intscan_stmt]] '([386428]%Z : list Z) 'Q6nq.gwt_nil).
Proof. rewrite ?gw_eq_ISI; ltac2:(GwEq.gw_rw [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]]); first [GwApply.gw_by_name GwI.segs (@Q91D.Mq1.is_sign) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@Q91D.Mq1.is_sign)]. Qed.

#[using="NONUL BND TPV"] Lemma is_ws : ltac2:(Q6nq.ty1 'GwI.segs '(@Q91D.Mq1.is_ws) [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]; [@gw_eq_ISI]; [@gw_eq_intscan_entry__3; @gw_eq_intscan_entry__2; @gw_eq_intscan_entry]; [@gw_eq_M64m1__3; @gw_eq_M64m1__2; @gw_eq_M64m1]; [@gw_eq_intscan_table_Z__3; @gw_eq_intscan_table_Z__2; @gw_eq_intscan_table_Z]; [@gw_eq_intscan_table__3; @gw_eq_intscan_table__2; @gw_eq_intscan_table]; [@gw_eq_itab__3; @gw_eq_itab__2; @gw_eq_itab]; [@gw_eq_file_cells__3; @gw_eq_file_cells__2; @gw_eq_file_cells]; [@gw_eq_intscan_W__3; @gw_eq_intscan_W__2; @gw_eq_intscan_W]; [@gw_eq_intscan_post__3; @gw_eq_intscan_post__2; @gw_eq_intscan_post]; [@gw_eq_intscan_stmt__3; @gw_eq_intscan_stmt__2; @gw_eq_intscan_stmt]] '([386392]%Z : list Z) 'Q6nq.gwt_nil).
Proof. rewrite ?gw_eq_ISI; ltac2:(GwEq.gw_rw [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]]); first [GwApply.gw_by_name GwI.segs (@Q91D.Mq1.is_ws) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@Q91D.Mq1.is_ws)]. Qed.
End Proofs.
Lemma gw_eq_ISI__2 : @ISI = ltac:(GwInst.gw_term (@Q91D.Mq1.ISI rsegs ISTAB 0x77c00%Z) (@ISI)). Proof. unfold ISI, Q91D.Mq1.ISI; rewrite ?gw_eq_intscan_table, ?gw_eq_file_cells; ltac2:(GwEq.gw_rw [[@gw_eq_W__3; @gw_eq_W__2; @gw_eq_W]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_ISI__2 : gw_eqs.

Lemma intscan_spec : intscan_stmt.
Proof. rewrite ?gw_eq_intscan_stmt; first [GwApply.gw_by_name GwI.segs (@Q91D.Mq1.intscan_spec) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@Q91D.Mq1.intscan_spec)]. Qed.
