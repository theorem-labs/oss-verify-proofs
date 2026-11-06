(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: proofs/libreac/fuzz_knock/lib/A/APgRt.v (rt_hand, fs_roF / fs_rwF) and
   APgStep.v (same_io_wvb) at 6ebe35ba632; adapted to the class-0 frame and the exit of reac_box_pin_parse. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_pin/lib/A/PPgParse4.v, with its module paths and module names changed; 262 of its 291 lines of code are new or changed and 251 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_codec/lib/A/Prog/check_personality_A.v, with its module names changed; 691 of its 735 lines of code are new or changed and 247 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_codec/lib/A/Prog/diginet_meter_encode_A.v, with its module paths and module names changed; 887 of its 941 lines of code are new or changed and 681 lines of the source are left out. *)
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YN3v YI04 YI09 YI08.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YI16 YM05 YI00.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU Require Import AWalkFw0 YCef YF0l YCej YCeh YCem YCep.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU Require Import AWalkFw1 AWalkFw2 YCfm.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU Require YF0x YFl3.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require YCeo.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import CodecCJ CPgBase.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import CPgBaseU CPgChkU CPgWalkU CPgWalkIntrU.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* text_arg at image B (fuzz_codec.asan-ubsan, 0x83ba0): the paths, invariants and arithmetic of the image-A walk
   lib/A/Prog/text_arg_A.v at image B's addresses. Image B adds the UBSan checks of the cursor: its alignment
   (0x83bb4, ip mod 8 = 0), the pointer increments p + 1 / p + 2 (0x83c14, 0x83c54, 0 < p), the end p + header +
   length (0x83cdc, 0x83cec) and text + length after the copy (0x83d1c); each trap (`unimp` at 0x83d50) is shown
   not taken. The engine decides the checks it can from the atom facts (ip 8-aligned, 1 <= p); the walk splits the
   others (ta_to_join, the branch at 0x83d1c) and refutes the trap side. The paths join at 0x83d0c, before the
   copy's argument moves, where a2 = n - used and a6 = p + used. *)

Definition TA_B : Z := 0x83ba0.
Definition ta_cur : YP09.region :=
YP09.mkRegion (Some 10%nat) 0 16 0 16 [YP09.mkChunk 0 (CVal 8 (SOff 33 0)); YP09.mkChunk 8 (CVal 8 (SOff 34 0))].
Definition ta_af : list (nat * afact) :=
[(10%nat, mkAF (2 ^ 46) (2 ^ 47 - 16) 3); (33%nat, mkAF 1 (2 ^ 47 - 1) 0); (34%nat, mkAF 0 (2 ^ 47) 0);
 (35%nat, mkAF 0 255 0); (36%nat, mkAF 0 255 0)].
Definition ta_ss0 : sstate := mkSS TA_B sr_atoms (cw_regs 32 ++ [ta_cur]) None (mkFacts (cw_atoms ++ ta_af) [] []).
Definition ta_SH : list shent := [mkSHE 10 0 16].
Definition ta_xs (p : Z) (data : list Z) : list Z := [p; Z.of_nat (length data); nth 0 data 0; nth 1 data 0].

(* the cursor's first and second byte, read-only, added once the run knows they exist *)
Definition ta_d0 : YP09.region := YP09.mkRegion (Some 33%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 35 0))].
Definition ta_d1 : YP09.region := YP09.mkRegion (Some 33%nat) 1 2 1 1 [YP09.mkChunk 1 (CVal 1 (SOff 36 0))].
Lemma ta_garr8_nth : forall segs m a l j, garr8 segs m a l -> 0 <= nth j l 0 < 256.
Proof.
intros segs m a l j H. destruct (Nat.lt_ge_cases j (length l)) as [Hj|Hj].
- exact (proj2 (H j Hj)).
- rewrite nth_overflow by exact Hj. lia.
Qed.

(* ---- the arithmetic of the length (fuzz_codec.c:526, 0x83c90 - 0x83cbc), over the engine's symbolic values ---- *)
(* the compiler's `v % 65` for a 16-bit v: q = (v * 4033) >> 18 is v / 65 *)
Lemma ta_mod65_magic : forall v, 0 <= v < 65536 -> (v * 4033) / 2 ^ 18 = v / 65.
Proof.
intros v Hv.
pose proof (Z.div_mod v 65 ltac:(lia)) as Hd. pose proof (Z.mod_pos_bound v 65 ltac:(lia)) as Hr.
assert (Hq : 0 <= v / 65 <= 1008) by lia.
symmetry. apply (Z.div_unique (v * 4033) (2 ^ 18) (v / 65) (v / 65 + 4033 * (v mod 65))).
- left. change (2 ^ 18) with 262144. lia.
- change (2 ^ 18) with 262144. lia.
Qed.
(* q = (v * 4033) >> 18, then ((v - q) - (q << 6)) << 48 >> 48, as the engine leaves `v % 65` *)
Lemma ta_U_m65 : forall E e v, U E e = v -> 0 <= v < 65536 ->
  U E (SAlu ALU_SRL (SAlu ALU_SLL (SAlu ALU_SUB (SAlu ALU_SUB e (SAlu ALU_SRL (SMd M_MUL e (SLit 4033)) (SLit 18)))
        (SAlu ALU_SLL (SAlu ALU_SRL (SMd M_MUL e (SLit 4033)) (SLit 18)) (SLit 6))) (SLit 48)) (SLit 48)) = v mod 65.
Proof.
intros E e v He Hv.
pose proof (ta_mod65_magic v Hv) as Hq.
pose proof (Z.div_mod v 65 ltac:(lia)) as Hd. pose proof (Z.mod_pos_bound v 65 ltac:(lia)) as Hr.
assert (UQ : U E (SAlu ALU_SRL (SMd M_MUL e (SLit 4033)) (SLit 18)) = v / 65).
{ rewrite U_SAlu, U_SMd. cbn [zalu_raw zmd_raw]. rewrite !U_SLit, He.
  change (Z.land (zcanon 18) 63) with 18. change (zcanon 4033) with 4033.
  rewrite (zcanon_id (v * 4033)) by (unfold M64; lia).
  rewrite Z.shiftr_div_pow2 by lia. rewrite Hq. apply zcanon_id. unfold M64. lia. }
assert (UA : U E (SAlu ALU_SUB e (SAlu ALU_SRL (SMd M_MUL e (SLit 4033)) (SLit 18))) = v - v / 65).
{ rewrite U_SAlu. cbn [zalu_raw]. rewrite He, UQ. apply zcanon_id. unfold M64. lia. }
assert (UB : U E (SAlu ALU_SLL (SAlu ALU_SRL (SMd M_MUL e (SLit 4033)) (SLit 18)) (SLit 6)) = v / 65 * 64).
{ rewrite U_SAlu. cbn [zalu_raw]. rewrite UQ, U_SLit. change (Z.land (zcanon 6) 63) with 6.
  rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 6) with 64. apply zcanon_id. unfold M64. lia. }
assert (UC : U E (SAlu ALU_SUB (SAlu ALU_SUB e (SAlu ALU_SRL (SMd M_MUL e (SLit 4033)) (SLit 18)))
        (SAlu ALU_SLL (SAlu ALU_SRL (SMd M_MUL e (SLit 4033)) (SLit 18)) (SLit 6))) = v mod 65).
{ rewrite U_SAlu. cbn [zalu_raw]. rewrite UA, UB. replace (v - v / 65 - v / 65 * 64) with (v mod 65) by lia.
  apply zcanon_id. unfold M64. lia. }
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw]. rewrite UC, !U_SLit.
change (Z.land (zcanon 48) 63) with 48.
rewrite Z.shiftl_mul_pow2 by lia. rewrite (zcanon_id (v mod 65 * 2 ^ 48)) by (unfold M64; lia).
rewrite Z.shiftr_div_pow2 by lia. rewrite Z.div_mul by lia. apply zcanon_id. unfold M64. lia.
Qed.
Lemma ta_lor_byte : forall hib lo, 0 <= hib < 256 -> 0 <= lo < 256 -> Z.lor (hib * 256) lo = lo + 256 * hib.
Proof.
intros hib lo Hh Hl.
assert (Hd : Z.land (hib * 256) lo = 0).
{ apply Z.bits_inj_0. intros i. rewrite Z.land_spec. destruct (Z_lt_le_dec i 8) as [Hi|Hi].
  - destruct (Z_lt_le_dec i 0) as [Hn|Hn]; [rewrite Z.testbit_neg_r by exact Hn; reflexivity|].
    replace (hib * 256) with (Z.shiftl hib 8) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
    rewrite Z.shiftl_spec_low by exact Hi. reflexivity.
  - rewrite <- (Z.mod_small lo 256) by exact Hl. change 256 with (2 ^ 8). rewrite Z.mod_pow2_bits_high by lia.
    apply Bool.andb_false_r. }
rewrite <- (Z.lxor_lor _ _ Hd). rewrite <- (Z.add_nocarry_lxor _ _ Hd). lia.
Qed.
(* the two cursor bytes as the code combines them (0x83c90 - 0x83c98): lo | hi << 8 *)
Lemma ta_U_v2 : forall E x0 x1, ew E 35 = Z_to_bv 64 x0 -> ew E 36 = Z_to_bv 64 x1 -> 0 <= x0 < 256 -> 0 <= x1 < 256 ->
  U E (SAlu ALU_OR (SAlu ALU_SLL (SOff 36 0) (SLit 8)) (SOff 35 0)) = x0 + 256 * x1.
Proof.
intros E x0 x1 H0 H1 R0 R1. rewrite !U_SAlu. cbn [zalu_raw].
rewrite (U_atom E 35 x0 H0), (U_atom E 36 x1 H1), U_SLit by lia.
change (Z.land (zcanon 8) 63) with 8. unfold zcanon, M64.
rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 8) with 256.
rewrite (Z.mod_small (x1 * 256)) by lia. rewrite ta_lor_byte by lia. apply Z.mod_small. lia.
Qed.
Lemma ta_U_v1 : forall E x0, ew E 35 = Z_to_bv 64 x0 -> 0 <= x0 < 256 ->
  U E (SAlu ALU_OR (SLit 0) (SOff 35 0)) = x0.
Proof.
intros E x0 H0 R0. rewrite U_SAlu. cbn [zalu_raw]. rewrite (U_atom E 35 x0 H0), U_SLit by lia.
change (zcanon 0) with 0. rewrite Z.lor_0_l. apply zcanon_id. unfold M64. lia.
Qed.
(* the length the spec takes, in the three header cases *)
Lemma ta_len_cases : forall data,
  Z.of_nat (text_lenZ data) = Z.min (text_u16Z data mod 65) (Z.of_nat (length data) - Z.of_nat (text_hdrZ data)).
Proof.
intros data. unfold text_lenZ, text_hdrZ.
pose proof (Z.mod_pos_bound (text_u16Z data) 65 ltac:(lia)). lia.
Qed.

(* ---- the state every path reaches at 0x83d0c (after the store of n - used at 0x83d08) ----
   Atoms 60.. hold, in order, t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 at that point: s1 = the length, a1 = p + the
   header, a2 = n - used, a6 = p + used. The cursor holds a6 and a2; the input regions are dropped. *)
Definition TA_J : nat := 60.
Definition ta_clob : list (bv 5) := [5; 6; 7; 9; 10; 11; 12; 13; 14; 15; 16; 17]%bv.
Definition ta_curJ : YP09.region :=
YP09.mkRegion (Some 10%nat) 0 16 0 16 [YP09.mkChunk 0 (CVal 8 (SOff 70 0)); YP09.mkChunk 8 (CVal 8 (SOff 66 0))].
Definition ta_stkJ : YP09.region :=
YP09.mkRegion (Some 2%nat) (-32) 0 (-32) 0
  [YP09.mkChunk (-32) (CVal 8 (SOff 18 0)); YP09.mkChunk (-24) (CVal 8 (SOff 9 0));
   YP09.mkChunk (-16) (CVal 8 (SOff 8 0)); YP09.mkChunk (-8) (CVal 8 (SOff 1 0))].
Definition ta_afJ : list (nat * afact) := cw_atoms ++ [(10%nat, mkAF (2 ^ 46) (2 ^ 47 - 16) 3)].
Definition ta_ssJ : sstate :=
mkSS 0x83d0c
  [SLit 0; SOff 1 0; SOff 2 (-32); SOff 3 0; SOff 4 0; SOff 60 0; SOff 61 0; SOff 62 0; SOff 11 0; SOff 63 0;
   SOff 64 0; SOff 65 0; SOff 66 0; SOff 67 0; SOff 68 0; SOff 69 0; SOff 70 0; SOff 71 0; SOff 32 0;
   SOff 19 0; SOff 20 0; SOff 21 0; SOff 22 0; SOff 23 0; SOff 24 0; SOff 25 0; SOff 26 0; SOff 27 0;
   SOff 28 0; SOff 29 0; SOff 30 0; SOff 31 0]
  [ta_curJ; ta_stkJ] None (mkFacts ta_afJ [] []).

(* lia without the disjunctions of the context (lia splits each one) *)
Ltac ta_lia := repeat match goal with H : _ \/ _ |- _ => clear H end; lia.
Ltac ta_nlia := clear; lia.
(* the engine's atoms below 37 are the entry atoms in every later env *)
Ltac ta_ev :=
repeat match goal with
| AG : forall n, (n < 37)%nat -> ew ?Ev n = ew ?E0 n |- context [ew ?Ev ?n] =>
  lazymatch Ev with E0 => fail | _ => rewrite (AG n) by ta_nlia end
end;
repeat match goal with H : bv_unsigned (ew ?E0 ?n) = _ |- context [bv_unsigned (ew ?E0 ?n)] => rewrite H end;
repeat match goal with H : ew ?E0 ?n = Z_to_bv 64 _ |- context [ew ?E0 ?n] => rewrite H end;
rewrite ?unsigned_lit_small by ta_lia.
Ltac ta_ev_in Hb :=
repeat match goal with
| AG : forall n, (n < 37)%nat -> ew ?Ev n = ew ?E0 n |- _ =>
  match type of Hb with context [ew Ev ?n] => lazymatch Ev with E0 => fail | _ => rewrite (AG n) in Hb by ta_nlia end end
end;
repeat match goal with H : bv_unsigned (ew ?E0 ?n) = _ |- _ =>
  match type of Hb with context [bv_unsigned (ew E0 n)] => rewrite H in Hb end end;
repeat match goal with H : ew ?E0 ?n = Z_to_bv 64 _ |- _ => match type of Hb with context [ew E0 n] => rewrite H in Hb end end;
rewrite ?unsigned_lit_small in Hb by ta_lia.
(* the env after a run agrees with the entry env below 37 *)
Ltac ta_ag :=
lazymatch goal with HS : st_ok _ ?Ev _ _, AG : forall n, (n < 37)%nat -> ew ?Eo n = ew ?E0 n |- _ =>
  lazymatch Eo with Ev => idtac | _ =>
    let AG2 := fresh "AG" in
    assert (AG2 : forall n, (n < 37)%nat -> ew Ev n = ew E0 n)
      by (intros nn Hnn; first
          [ rewrite <- (AG nn Hnn);
            repeat first [rewrite ew_ewset_other by ta_lia | rewrite ew_havoc_old by (try unfold TA_J; ta_lia)]; reflexivity
          | repeat first [rewrite ew_ewset_other by ta_lia | rewrite ew_havoc_old by (try unfold TA_J; ta_lia)];
            first [reflexivity | apply AG; exact Hnn] ]);
    clear AG; rename AG2 into AG end end.
(* move a value fact of an atom to the env of the current state *)
Ltac ta_carry H :=
lazymatch type of H with ew ?Eo ?n = ?v =>
lazymatch goal with HS : st_ok _ ?Ev _ _ |- _ =>
  lazymatch Eo with Ev => idtac | _ =>
    let H2 := fresh H in
    assert (H2 : ew Ev n = v)
      by (repeat first [rewrite ew_ewset_other by (try unfold TA_J; ta_lia) | rewrite ew_havoc_old by (try unfold TA_J; ta_lia)]; exact H);
    clear H; rename H2 into H end end end.
Ltac ta_awr spv :=
idtac; lazymatch goal with |- awr_ok ?E ?rs ?stk ?sp0 ?fp ?b0 ?bc ?ly ?own =>
let rs' := eval vm_compute in rs in change (awr_ok E rs' stk sp0 fp b0 bc ly own);
lazymatch goal with TW : twr_ok _ _ _ _ _ _ _ _ _ _ _ _ _ ?ipv 16 |- _ =>
repeat first
[ apply awr_ok_nil
| apply awr_ok_cons_ro; [azlit_tac|]
| eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat (spv - sp0));
  [reflexivity | ta_ev; lia | cbn [YP09.r_wlo YP09.r_whi]; lia | cbn [YP09.r_wlo YP09.r_whi]; lia |]
| eapply (cw_awr_ok_cons_twr _ E _ _ _ _ _ _ _ _ _ _ _ _ _ ipv 16 10%nat); [reflexivity | ta_ev; reflexivity | cbn; lia | cbn; lia | exact TW |] ]
end end.
Ltac ta_awr2 spv :=
idtac; lazymatch goal with |- awr_ok ?E ?rs ?stk ?sp0 ?fp ?b0 ?bc ?ly ?own =>
let rs' := eval vm_compute in rs in change (awr_ok E rs' stk sp0 fp b0 bc ly own);
lazymatch goal with TW : twr_ok _ _ _ _ _ _ _ _ _ _ _ _ _ ?ipv 16, TWQ : twr_ok _ _ _ _ _ _ _ _ _ _ _ _ _ ?qv 1,
  EQ : ew _ 100 = Z_to_bv 64 ?qv |- _ =>
repeat first
[ apply awr_ok_nil
| apply awr_ok_cons_ro; [azlit_tac|]
| eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat (spv - sp0));
  [reflexivity | ta_ev; lia | cbn [YP09.r_wlo YP09.r_whi]; lia | cbn [YP09.r_wlo YP09.r_whi]; lia |]
| eapply (cw_awr_ok_cons_twr _ E _ _ _ _ _ _ _ _ _ _ _ _ _ ipv 16 10%nat); [reflexivity | ta_ev; reflexivity | cbn; lia | cbn; lia | exact TW |]
| eapply (cw_awr_ok_cons_twr _ E _ _ _ _ _ _ _ _ _ _ _ _ _ qv 1 100%nat);
  [reflexivity | rewrite EQ; apply unsigned_lit_small; lia | cbn; lia | cbn; lia | exact TWQ |] ]
end end.
Ltac ta_kwr :=
idtac; let a := fresh "a" in let r := fresh "r" in let Hr := fresh "Hr" in let Hb := fresh "Hb" in
intros a (r & Hr & Hb); cbv beta;
lazymatch type of Hr with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hr end;
repeat (destruct Hr as [<- | Hr]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb; ta_ev_in Hb;
  lia | ]); destruct Hr.
(* keep the regions of the state at the positions idxs *)
Ltac ta_norm := lazymatch goal with HS : st_ok _ _ _ _ |- _ => norm_ss HS end.
Ltac ta_keep_regs idxs :=
ta_norm;
lazymatch goal with HS : st_ok _ ?Ex ?ssx ?msx |- _ =>
  let rs := eval vm_compute in (pick (ss_mem ssx) idxs) in
  let HS3 := fresh "HS3" in
  pose proof (st_ok_submem tfibsegs Ex ssx msx rs HS ltac:(cbn [ss_mem]; submem_tac) ltac:(vm_compute; reflexivity)) as HS3;
  clear HS; rename HS3 into HS end; ta_norm.
(* put the region R at the head of the state; rok proves region_ok, dis the disjointness from the others *)
Ltac ta_add_region R rok dis :=
lazymatch goal with HS : st_ok _ ?Ex ?ssx ?msx |- _ =>
  let HS3 := fresh "HS3" in
  pose proof (ast_ok_add_region tfibsegs Ex ssx msx R HS ltac:(vm_compute; reflexivity) ltac:(rok) ltac:(dis)) as HS3;
  clear HS; rename HS3 into HS end;
lazymatch goal with HS : st_ok _ _ ?ss3 _ |- _ => let v := eval vm_compute in ss3 in change ss3 with v in HS end.
(* a register at a stop, as the engine's symbolic value *)
Ltac ta_reg r R :=
lazymatch goal with HS : st_ok ?segs ?E ?ss (restrict ?H ?ms) |- _ =>
  let e := eval vm_compute in (sr_get (ss_regs ss) r) in
  assert (R : getr (ms_regs ms) r = sv_denot E e) by exact (st_ok_restrict_reg segs H E ss ms r HS) end.
(* the join at 0x83d0c: the stack region is at position is, the cursor at ic; V12 / V16 give a2 and a6 (the cursor's
   two words) *)
Ltac ta_join is ic V12 V16 :=
lazymatch goal with HS : st_ok _ ?Ev ?ssv (restrict ?Hh ?msv) |- SRr _ _ (mkCfg ?msv _) _ =>
  let rc := eval vm_compute in (nth ic (ss_mem ssv) ta_curJ) in
  let HRC := fresh "HRC" in
  pose proof (st_ok_region_nth Ev ssv (restrict Hh msv) ic rc HS eq_refl) as HRC;
  lazymatch rc with YP09.mkRegion (Some 10%nat) 0 16 0 16 ?cs =>
    let e0 := eval vm_compute in (sr_get (ss_regs ssv) (16%bv : bv 5)) in
    let e8 := eval vm_compute in (sr_get (ss_regs ssv) (12%bv : bv 5)) in
    let R16 := fresh "R16" in let R12 := fresh "R12" in
    assert (R16 : sv_denot Ev e0 = getr (ms_regs msv) (16%bv : bv 5)) by exact (eq_sym (st_ok_restrict_reg tfibsegs Hh Ev ssv msv (16%bv : bv 5) HS));
    assert (R12 : sv_denot Ev e8 = getr (ms_regs msv) (12%bv : bv 5)) by exact (eq_sym (st_ok_restrict_reg tfibsegs Hh Ev ssv msv (12%bv : bv 5) HS));
    rewrite V16 in R16; rewrite V12 in R12;
    pose proof (field_of_region Ev _ 10 _ cs 0 16 0 16 0 8 e0 _ HRC ltac:(ta_ev; reflexivity)
      ltac:(cbn [In]; repeat (first [left; reflexivity | right])) R16 ltac:(change (8 * Z.of_N 8) with 64; lia) ltac:(change (Z.of_N 8) with 8; lia)) as V0;
    pose proof (field_of_region Ev _ 10 _ cs 0 16 0 16 8 8 e8 _ HRC ltac:(ta_ev; reflexivity)
      ltac:(cbn [In]; repeat (first [left; reflexivity | right])) R12 ltac:(change (8 * Z.of_N 8) with 64; lia) ltac:(change (Z.of_N 8) with 8; lia)) as V8;
    cbn [ms_mem restrict N.to_nat] in V0, V8;
    destruct HRC as (_ & _ & HRW & _); cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val ms_mem restrict] in HRW;
    ta_ev_in HRW; clear R16 R12
  end;
  rewrite (st_ok_restrict_mkst tfibsegs Hh Ev ssv msv HS eq_refl);
  let HS1 := fresh "HS1" in
  pose proof (YF0x.st_ok_forget TA_J Ev ssv Hh msv ta_clob HS eq_refl ltac:(vm_compute; reflexivity)
     ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
     ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)) as HS1;
  clear HS; rename HS1 into HS
end;
ta_ag; ta_keep_regs [is];
lazymatch goal with HS : st_ok _ ?Ex ?ssx ?msx |- _ =>
  let RK := fresh "RK" in let RD := fresh "RD" in let HS3 := fresh "HS3" in
  assert (RK : region_ok tfibsegs Ex (ms_mem msx) ta_curJ);
  [| assert (RD : all_disjoint Ex ta_curJ (ss_mem ssx));
     [| pose proof (ast_ok_add_region tfibsegs Ex ssx msx ta_curJ HS eq_refl RK RD) as HS3;
        clear HS RK RD; rename HS3 into HS ] ]
end.
(* the cursor region of the join holds a6 and a2 *)
Ltac ta_join_rk V0 V8 HRW V12 V16 :=
unfold region_ok, ta_curJ;
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
ta_ev; split; [lia|]; split; [lia|];
split; [intros o Ho; exact (HRW o Ho)|];
apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]];
[ eapply (chunk_ok_val tfibsegs _ _ _ 0 8 (SOff 70 0) _);
  [ cbn [sv_denot]; change 70%nat with (TA_J + 10)%nat; rewrite (ew_havoc_new _ TA_J _ 10 (Z_to_bv 64 0)) by (cbn; lia);
    cbn [nth map ta_clob]; rewrite V16, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
  | change (8 * Z.of_N 8) with 64; lia | change (Z.of_N 8) with 8; lia | exact V0 ]
| eapply (chunk_ok_val tfibsegs _ _ _ 8 8 (SOff 66 0) _);
  [ cbn [sv_denot]; change 66%nat with (TA_J + 6)%nat; rewrite (ew_havoc_new _ TA_J _ 6 (Z_to_bv 64 0)) by (cbn; lia);
    cbn [nth map ta_clob]; rewrite V12, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
  | change (8 * Z.of_N 8) with 64; lia | change (Z.of_N 8) with 8; lia | exact V8 ] ].
Ltac ta_join_rd :=
apply all_disjoint_of_extents; cbn [ss_mem]; unfold extent_of_region, ta_curJ;
cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val zall_disjoint]; ta_ev; unfold zdisj; cbn [fst snd];
lazymatch goal with CWI : _ + 16 <= _ - (32 + 4096) \/ _ <= _ |- _ => clear - CWI; repeat split; lia end.
Ltac ta_join_end :=
ta_norm;
lazymatch goal with HS : st_ok _ ?Ex ?ssx ?msx |- _ =>
  let HS3 := fresh "HS3" in
  pose proof (st_ok_facts_incl3 tfibsegs Ex ssx msx ta_afJ [] [] HS
    ltac:(let x := fresh "x" in let Hx := fresh "Hx" in
          intros x Hx; unfold ta_afJ, cw_atoms in Hx; cbn [app In] in Hx; cbn [ss_facts f_atoms];
          repeat (destruct Hx as [<- | Hx]; [cbn [In]; repeat (first [left; reflexivity | right]) |]); destruct Hx)
    ltac:(let x := fresh "x" in intros x [])
    ltac:(let x := fresh "x" in intros x [])) as HS3;
  clear HS; rename HS3 into HS end;
lazymatch goal with HS : st_ok _ ?Ex ?ssx ?msx |- _ => change ssx with ta_ssJ in HS end;
lazymatch goal with HS : st_ok _ _ _ (restrict _ (mkst _ (Z_to_bv 64 (ss_pc ?x)) _ _)) |- _ =>
  change (ss_pc x) with 539916 in * end.

(* the 65 bytes of the text after the call: the copied bytes, the 0, the rest as they were *)
Lemma ta_garr8_text : forall segs m t (len hdr : nat) (data tj : list Z),
  (hdr + len <= length data)%nat -> (len < 65)%nat -> length tj = 65%nat ->
  (forall j, (j < len)%nat -> val_mem segs m (t + Z.of_nat j) 1 (nth (hdr + j) data 0) /\ 0 <= nth (hdr + j) data 0 < 256) ->
  val_mem segs m (t + Z.of_nat len) 1 0 ->
  (forall j, (len < j < 65)%nat -> val_mem segs m (t + Z.of_nat j) 1 (nth j tj 0) /\ 0 <= nth j tj 0 < 256) ->
  garr8 segs m t (firstn len (skipn hdr data) ++ [0] ++ skipn (1 + len) tj).
Proof.
intros segs m t len hdr data tj Hhl Hl Htj H1 H2 H3 j Hj.
assert (Lf : length (firstn len (skipn hdr data)) = len) by (rewrite firstn_length_le; [reflexivity | rewrite length_skipn; lia]).
rewrite !length_app, Lf, length_skipn in Hj. cbn [length] in Hj.
destruct (Nat.lt_ge_cases j len) as [Hjl | Hjl].
- rewrite app_nth1 by lia. rewrite nth_firstn, (proj2 (Nat.ltb_lt j len) Hjl), nth_skipn by lia.
  exact (H1 j Hjl).
- rewrite app_nth2 by lia. rewrite Lf. destruct (Nat.eq_dec j len) as [-> | Hne].
  + rewrite Nat.sub_diag. cbn [app nth]. split; [exact H2 | lia].
  + replace (j - len)%nat with (S (j - len - 1)) by lia. cbn [app nth]. rewrite nth_skipn.
    replace (1 + len + (j - len - 1))%nat with j by lia. exact (H3 j ltac:(lia)).
Qed.
(* the model after the runs keeps the input of the model at the call *)
Ltac ta_kio := first [apply same_io_refl | eapply same_io_trans; [| apply cw_same_io_wvb]; ta_kio
  | eapply same_io_trans; [| apply same_io_materialized; eassumption]; ta_kio].
(* the post of the tail (same_io from the join's model) gives the post of the call (same_io from mdc) *)
Ltac ta_post_mdc :=
let W' := fresh "W'" in let c' := fresh "c'" in let Hle := fresh "Hle" in let HQ := fresh "HQ" in
intros W' c' Hle HQ; unfold cdc_post in HQ |- *;
let qly := fresh "qly" in let qS := fresh "qS" in let qrg := fresh "qrg" in let qmem := fresh "qmem" in
let qmd := fresh "qmd" in let qc := fresh "qc" in let qJ := fresh "qJ" in let qP := fresh "qP" in
let qF := fresh "qF" in let qB := fresh "qB" in let qI := fresh "qI" in let qM := fresh "qM" in
let qK := fresh "qK" in let qR := fresh "qR" in
destruct HQ as (qly & qS & qrg & qmem & qmd & qc & qJ & qP & qF & qB & qI & qM & qK & qR);
exists qly, qS, qrg, qmem, qmd;
split; [exact qc|]; split; [exact qJ|]; split; [exact qP|]; split; [exact qF|]; split; [exact qB|];
split; [eapply same_io_trans; [| exact qI]; ta_kio|];
split; [exact qM|]; split; [exact qK | exact qR].
(* a path's join state, with s1 / a1 / a2 / a6 at the stop (V9 V11 V12 V16), handed to TAIL *)
Ltac ta_tail TAIL V9 V11 V12 V16 :=
lazymatch goal with HS : st_ok _ ?Ej _ (restrict _ (mkst ?rg _ ?mm _)) |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdv) _ =>
  eapply SRr_mono;
  [ apply (TAIL Ej rg mm mdv HS);
    [ eassumption
    | lazymatch goal with AG : forall n, (n < 37)%nat -> ew Ej n = _ |- _ => exact AG end
    | lazymatch goal with HAE : env_agree 32 _ _ |- _ => env_agree_chain HAE end
    | change 63%nat with (TA_J + 3)%nat; rewrite (ew_havoc_new _ TA_J _ 3 (Z_to_bv 64 0)) by (cbn; ta_lia); exact V9
    | change 65%nat with (TA_J + 5)%nat; rewrite (ew_havoc_new _ TA_J _ 5 (Z_to_bv 64 0)) by (cbn; ta_lia); exact V11
    | change 66%nat with (TA_J + 6)%nat; rewrite (ew_havoc_new _ TA_J _ 6 (Z_to_bv 64 0)) by (cbn; ta_lia); exact V12
    | change 70%nat with (TA_J + 10)%nat; rewrite (ew_havoc_new _ TA_J _ 10 (Z_to_bv 64 0)) by (cbn; ta_lia); exact V16
    | lazymatch goal with KE : forall a, _ -> ~ _ -> aview _ _ mm a = _ |- _ => exact KE end ]
  | ta_post_mdc ]
end.
(* a byte whose view is the view of a byte of another memory holds that byte's value *)
Lemma ta_val1_move : forall H (m m' : word -> option byte) a a' v,
  aview tfibsegs H m' a' = aview tfibsegs H m a -> val_mem tfibsegs (mrestrict H m) a 1 v ->
  val_mem tfibsegs (mrestrict H m') a' 1 v.
Proof.
intros H m m' a a' v E Hv k Hk. replace k with 0%nat by lia. cbn [Z.of_nat]. rewrite Z.add_0_r.
pose proof (Hv 0%nat ltac:(lia)) as H0. cbn [Z.of_nat] in H0. rewrite Z.add_0_r in H0.
unfold aview in E. rewrite H0 in E.
destruct (mbyte tfibsegs (mrestrict H m') a') as [b|] eqn:Eb; cbn [option_map] in E; [|discriminate E].
injection E as E. f_equal. apply bv_eq. exact E.
Qed.

(* the UBSan check after the copy (0x83d18 - 0x83d1c) compares ~text with the length *)
Lemma ta_lxor_ones : forall v, 0 <= v < 2 ^ 64 -> Z.lxor v (Z.ones 64) = Z.ones 64 - v.
Proof.
intros v Hv.
assert (Hd : Z.land v (Z.lxor v (Z.ones 64)) = 0).
{ apply Z.bits_inj_0. intros i. rewrite Z.land_spec, Z.lxor_spec.
  destruct (Z_lt_le_dec i 0) as [Hn|Hn]; [rewrite Z.testbit_neg_r by exact Hn; reflexivity|].
  destruct (Z_lt_le_dec i 64) as [Hi|Hi].
  - rewrite Z.ones_spec_low by lia. destruct (Z.testbit v i); reflexivity.
  - rewrite Z.ones_spec_high by lia. rewrite <- (Z.mod_small v (2 ^ 64)) by exact Hv.
    rewrite Z.mod_pow2_bits_high by lia. reflexivity. }
pose proof (Z.add_nocarry_lxor _ _ Hd) as Hs. rewrite <- Z.lxor_assoc, Z.lxor_nilpotent, Z.lxor_0_l in Hs. lia.
Qed.
Lemma ta_U_not : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
  U E (SAlu ALU_XOR (SOff n 0) (SLit (-1))) = 2 ^ 64 - 1 - v.
Proof.
intros E n v H Hv. rewrite U_SAlu. cbn [zalu_raw]. rewrite (U_atom E n v H Hv), U_SLit.
replace (zcanon (-1)) with (Z.ones 64) by reflexivity.
rewrite ta_lxor_ones by exact Hv. rewrite Z.ones_equiv, zcanon_id by (unfold M64; lia). lia.
Qed.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
(* a range keeps its usable marks when the walk's kept fact covers its shadow bytes *)
Lemma ta_ra_kept : forall (Zn : Z -> Prop) H (m m' : word -> option byte) q n,
  (forall a, 0 <= a < 2 ^ 64 -> ~ Zn a -> aview tfibsegs H m' a = aview tfibsegs H m a) ->
  (forall x, q <= x < q + n -> 0 <= shadow_of_addr SHADOW_OFF x < 2 ^ 64 /\ ~ Zn (shadow_of_addr SHADOW_OFF x)) ->
  range_addressable (aview tfibsegs H m) SHADOW_OFF q n -> range_addressable (aview tfibsegs H m') SHADOW_OFF q n.
Proof.
intros Zn H m m' q n KE Hz Hr x Hx. destruct (Hr x Hx) as (s & Hs & Hok). exists s. split; [|exact Hok].
destruct (Hz x Hx) as [H1 H2]. rewrite (KE _ H1 H2). exact Hs.
Qed.
(* the shadow bytes the wrappers read around a range keep their view when the walk's kept fact covers them *)
Lemma ta_hull_kept : forall (Zn : Z -> Prop) H (m m' : word -> option byte) q n q' n',
  (forall a, 0 <= a < 2 ^ 64 -> ~ Zn a -> aview tfibsegs H m' a = aview tfibsegs H m a) ->
  (forall s, shadow_addr q / 8 * 8 <= s < shadow_addr (q + n - 1) / 8 * 8 + 8 -> 0 <= s < 2 ^ 64 /\ ~ Zn s) ->
  0 <= q -> q <= q' -> 0 < n' -> q' + n' <= q + n ->
  shadow_hull_vis (aview tfibsegs H m) q n -> shadow_hull_vis (aview tfibsegs H m') q' n'.
Proof.
intros Zn H m m' q n q' n' KE Hz Hq Hq' Hn' Hle Hh s Hs.
assert (Hr : shadow_addr q / 8 * 8 <= s < shadow_addr (q + n - 1) / 8 * 8 + 8).
{ unfold shadow_addr in *.
  assert (A0 : q / 8 <= q' / 8) by (apply Z.div_le_mono; lia).
  assert (A0' : (q' + n' - 1) / 8 <= (q + n - 1) / 8) by (apply Z.div_le_mono; lia).
  assert (A1 : (SHADOW_OFF + q / 8) / 8 <= (SHADOW_OFF + q' / 8) / 8) by (apply Z.div_le_mono; lia).
  assert (A2 : (SHADOW_OFF + (q' + n' - 1) / 8) / 8 <= (SHADOW_OFF + (q + n - 1) / 8) / 8) by (apply Z.div_le_mono; lia).
  lia. }
destruct (Hz s Hr) as [H1 H2]. rewrite (KE s H1 H2). exact (Hh s Hr).
Qed.
(* an engine obligation on an input byte at p + c: its usable marks at entry (RAD), kept by the walk (KE, HSO) *)
Ltac ta_obl RAD HSO :=
idtac;
lazymatch goal with |- range_addressable (rd_of _ _) (U ?Ev CW_Bx) (U ?Ev (SOff 33 ?c)) ?nn =>
  rewrite (cw_U_Bx Ev ltac:(ta_ev; reflexivity));
  rewrite U_SOff; ta_ev; unfold zcanon, M64; rewrite Z.mod_small by lia;
  rewrite <- aview_rd_of;
  eapply ta_ra_kept; [eassumption | intros x Hx; apply HSO; lia | ];
  eapply range_addressable_sub; [exact RAD | lia | lia]
end.
Section d.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis TL : TfibLib B.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis AMEMCPY : aintrin_realizes tfibsegs B OCpy 0x51ae8.
(* the UBSan checks between the length and the join (0x83cdc bltu a6,a1; 0x83cec beqz a7) when the engine leaves
   them: the trap is not taken *)
Ltac ta_Uin H pv nv :=
  repeat match type of H with
  | context [U ?Ev (SOff 33 ?c)] => rewrite (U_atom_off Ev 33 pv c) in H by (first [ta_ev; reflexivity | ta_lia])
  | context [U ?Ev (SOff 34 ?c)] => rewrite (U_atom_off Ev 34 nv c) in H by (first [ta_ev; reflexivity | ta_lia])
  | context [U ?Ev (SLit ?z)] => rewrite (U_lit Ev z) in H by ta_lia
  end.
Ltac ta_ub_refute H pv nv :=
  first [rewrite branch_ltu_U in H | rewrite branch_geu_U in H | rewrite branch_eq_U in H | rewrite branch_ne_U in H];
  repeat (first [ match goal with Hx : U ?Ev ?e = _ |- _ => rewrite Hx in H end
                | rewrite U_SAlu in H; cbn [zalu_raw] in H ]);
  ta_Uin H pv nv;
  repeat match type of H with context [zcanon ?z] => rewrite (zcanon_id z) in H by (unfold M64; ta_lia) end;
  repeat match type of H with context [if (?a <? ?b) then _ else _] =>
    let Hl := fresh "Hl" in destruct (Z.ltb_spec a b) as [Hl|Hl] end;
  first [ discriminate H | ta_lia
        | apply Z.ltb_lt in H; ta_lia | apply Z.ltb_ge in H; ta_lia | apply Z.eqb_eq in H; ta_lia
        | apply negb_true_iff, Z.ltb_ge in H; ta_lia | apply negb_true_iff, Z.ltb_lt in H; ta_lia
        | vm_compute in H; discriminate H ].
Ltac ta_at_join := lazymatch goal with HS : st_ok _ _ ?ss _ |- _ =>
  let b := eval vm_compute in (Z.eqb (ss_pc ss) 539916) in lazymatch b with true => idtac | false => fail end end.
Ltac ta_to_join_rec spv pv nv :=
  tryif ta_at_join then idtac else
    (let Hu := fresh "Hu" in cw_branch Hu;
     [ exfalso; ta_ub_refute Hu pv nv
     | clear Hu; cw_run_to ltac:(ta_awr spv) 0x83d0c; cw_keep ta_kwr; ta_ag; ta_to_join_rec spv pv nv ]).
Ltac ta_to_join spv pv nv :=
  cw_run_to ltac:(ta_awr spv) 0x83d0c; cw_keep ta_kwr; ta_ag; ta_to_join_rec spv pv nv.
(* a byte of a heap block or a live frame of the call state is present *)
Lemma ta_tdst_present : forall lyc Sc (W : world tfibsegs) m md q n,
  tdst_ok B lyc Sc q n -> AR tfibsegs B lyc Sc W m md -> forall a, q <= a < q + n -> apresent (w_H W) m a.
Proof.
intros lyc Sc W m md q n Hd HAR a Ha. destruct (Hd a Ha) as [(b & mm & Hin & Hr) | (cid & pos & Hin & Hr)].
- destruct (al_blocks _ _ LAWS _ _ _ _ _ b mm HAR Hin) as (_ & _ & _ & _ & Hp & _). exact (proj1 (Hp a Hr)).
- destruct (al_frames _ _ LAWS _ _ _ _ _ cid pos HAR Hin) as (_ & _ & Hp & _).
  unfold frame_rng, in_zr in Hr. cbn [fst snd] in Hr. exact (proj1 (Hp a Hr)).
Qed.

Theorem text_arg_B_holds : cdcU_text_arg_specX tfibsegs B MT TA_B.
Proof.
unfold cdcU_text_arg_specX.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs ip tx p data tj
  HEN H10 Hal8 HCUR Vp Vn Hp0 Hpn HD HCRD H11 HTX HT HTL D1 D2 D3.
pose proof Hwx_tfa as Hwx. pose proof tfib_segs_low as Hsegs.
pose proof (cw_entry_stack B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs TB_text_arg HEN
  ltac:(unfold TB_text_arg, ESTACK; lia)) as (Hceil & H47 & H46 & Hal16 & Hpres).
pose proof HEN as (HJ & Hra & Hra4 & Hgp & Htp & _ & Hwlo & Hwhi & Hev & Hlive).
pose proof HJ as (HAR & Hly & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
pose proof Hstk as (Hsp016 & HSTK & Hsceil & Hslo & Hshi & HS47 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HCUR as (Hip0 & Hip63 & Hiplo & Hiphi & TWI & RAI & HVI & AMI & CWI).
pose proof HCRD as (_ & _ & HPRD & RAD & HVD & AMD & CWD).
pose proof HTX as (Htx0 & Htx63 & TDX & TWX & RAX & HVX & AMX & CWX).
assert (Ex0 : 0 <= nth 0 data 0 < 256) by exact (ta_garr8_nth _ _ _ _ 0 HD).
assert (Ex1 : 0 <= nth 1 data 0 < 256) by exact (ta_garr8_nth _ _ _ _ 1 HD).
set (xs := ta_xs p data).
set (E0 := Ereg regs (cw_extra xs)).
assert (E1 : ew E0 1 = getr regs 1) by exact (cw_ew_reg regs xs 1 1%bv eq_refl).
assert (E2 : ew E0 2 = getr regs 2) by exact (cw_ew_reg regs xs 2 2%bv eq_refl).
assert (E3 : ew E0 3 = getr regs 3) by exact (cw_ew_reg regs xs 3 3%bv eq_refl).
assert (E4 : ew E0 4 = getr regs 4) by exact (cw_ew_reg regs xs 4 4%bv eq_refl).
assert (E10 : ew E0 10 = Z_to_bv 64 ip) by exact (eq_trans (cw_ew_reg regs xs 10 10%bv eq_refl) H10).
assert (E11 : ew E0 11 = Z_to_bv 64 tx) by exact (eq_trans (cw_ew_reg regs xs 11 11%bv eq_refl) H11).
assert (E32 : ew E0 32 = Z_to_bv 64 SB) by exact (cw_ew_SB regs xs).
assert (E33 : ew E0 33 = Z_to_bv 64 p) by exact (cw_ew_x regs xs 0).
assert (E34 : ew E0 34 = Z_to_bv 64 (Z.of_nat (length data))) by exact (cw_ew_x regs xs 1).
assert (E35 : ew E0 35 = Z_to_bv 64 (nth 0 data 0)) by exact (cw_ew_x regs xs 2).
assert (E36 : ew E0 36 = Z_to_bv 64 (nth 1 data 0)) by exact (cw_ew_x regs xs 3).
assert (Usp : bv_unsigned (ew E0 2) = spZ regs) by (rewrite E2; reflexivity).
assert (AG : forall n, (n < 37)%nat -> ew E0 n = ew E0 n) by (intros; reflexivity).
assert (HAE : env_agree 32 (Ereg regs (cw_extra xs)) E0) by apply env_agree_refl.
unfold coff_win, amem_range in CWI, CWD, CWX, AMI, AMD, AMX.
unfold TB_text_arg, ESTACK in Hceil, H46, Hpres, Hwlo, CWI, CWD, CWX.
assert (HS : st_ok tfibsegs E0 ta_ss0 (restrict (w_H W) (mkst regs (Z_to_bv 64 TA_B) memc (seg_rom tfibsegs)))).
{ unfold ta_ss0. apply (cw_entry B TL LAWS TA_B 32 xs [ta_cur] ta_af lyc Sc W regs memc mdc HAR ltac:(lia) ltac:(lia) Hal16
    ltac:(intros a Ha; apply Hpres; lia)).
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil]. unfold region_ok, ta_cur.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    fold E0. rewrite E10, unsigned_lit_small by lia.
    split; [lia|]. split; [lia|].
    split; [intros o Ho; apply (apresent_writable tfibsegs); exact (proj1 (proj2 (TWI (ip + o) ltac:(lia))))|].
    constructor; [|constructor; [|constructor]].
    + apply (chunk_ok_val tfibsegs E0 _ ip 0 8 (SOff 33 0) p);
      [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | rewrite Z.add_0_r; exact Vp].
    + apply (chunk_ok_val tfibsegs E0 _ ip 8 8 (SOff 34 0) (Z.of_nat (length data)));
      [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact Vn].
  - apply pairwise_disjoint_of_extents. fold E0.
    unfold cw_regs, ta_cur, stack_region, got_region, bcell_region, extent_of_region.
    cbn [app map YP09.r_base YP09.r_lo YP09.r_hi]. cbn [base_val].
    rewrite Usp, E10, unsigned_lit_small by lia.
    unfold A_GOT_shadow, A_shadow_glob.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
  - fold E0. cbn [ta_af atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite E10, E33, E34, E35, E36, !unsigned_lit_small by lia.
    rewrite !Z.pow_0_r, !Z.mod_1_r. change (2 ^ 3) with 8. repeat split; lia. }
assert (SHOK : sh_ok tfibsegs CW_Bx ta_SH E0 (mrestrict (w_H W) memc)).
{ unfold sh_ok, ta_SH. apply Forall_cons; [|apply Forall_nil].
  exact (cw_shent_ra W memc E0 10 ip 16 RAI AMI ltac:(lia) ltac:(lia) ltac:(lia) E10 E32). }
assert (KE : forall a, 0 <= a < 2 ^ 64 ->
  ~ ((spZ regs - (32 + 4096) <= a < spZ regs) \/ (ip <= a < ip + 16)) ->
  aview tfibsegs (w_H W) memc a = aview tfibsegs (w_H W) memc a) by (intros; reflexivity).
assert (HSO : forall x, 0 <= x < 2 ^ 47 -> 0 <= shadow_of_addr SHADOW_OFF x < 2 ^ 64 /\
  ~ ((spZ regs - (32 + 4096) <= shadow_of_addr SHADOW_OFF x < spZ regs) \/ (ip <= shadow_of_addr SHADOW_OFF x < ip + 16))).
{ intros x Hx. unfold shadow_of_addr, SHADOW_OFF.
  pose proof (Z.div_mod x 8 ltac:(lia)). pose proof (Z.mod_pos_bound x 8 ltac:(lia)).
  clear - Hx Hceil C1 C3 C5 Hiplo Eslo Hsceil H H0. lia. }
assert (HSH : forall q n s, 0 <= q -> q + n <= 2 ^ 47 -> 0 < n ->
  shadow_addr q / 8 * 8 <= s < shadow_addr (q + n - 1) / 8 * 8 + 8 -> 0 <= s < 2 ^ 64 /\
  ~ ((spZ regs - (32 + 4096) <= s < spZ regs) \/ (ip <= s < ip + 16))).
{ intros q n0 s Hq Hqn Hn Hs. unfold shadow_addr, SHADOW_OFF in Hs.
  assert (A1 : 0 <= q / 8) by (apply Z.div_pos; lia).
  assert (A2 : (q + n0 - 1) / 8 <= (2 ^ 47) / 8) by (apply Z.div_le_mono; lia).
  change ((2 ^ 47) / 8) with (2 ^ 44) in A2.
  assert (A3 : 0 <= (2147450880 + q / 8) / 8) by (apply Z.div_pos; lia).
  assert (A4 : (2147450880 + (q + n0 - 1) / 8) / 8 <= (2147450880 + 2 ^ 44) / 8) by (apply Z.div_le_mono; lia).
  change ((2147450880 + 2 ^ 44) / 8) with 2199291686912 in A4.
  clear - Hs A1 A2 A3 A4 Hceil C1 Hiplo Eslo Hsceil. lia. }
assert (HDK : forall j, 0 <= j < Z.of_nat (length data) -> 0 <= p + j < 2 ^ 64 /\
  ~ ((spZ regs - (32 + 4096) <= p + j < spZ regs) \/ (ip <= p + j < ip + 16))).
{ intros j Hj. clear - Hj Hp0 Hpn CWD D3. lia. }
cw_keep_j0 HJ HJ0.
(* ---- the tail every path reaches: the join state ta_ssJ at 0x83d0c; the moves of the copy's arguments and the jal
   at 0x83d14, __asan_memcpy (text, p + header, length), the UBSan check of text + length, text[length] = 0, the
   epilogue, the `ret` ---- *)
lazymatch goal with |- SRr _ _ _ (cdc_post ?sg ?Bv ?MTv ?STKv ?sp0v ?FPv ?lyv ?Sv ?W0v ?mem0v ?md0v ?ownv ?kv ?regsv ?Tv ?Ezv ?lycv ?Scv ?Wv ?memcv _ ?Rv) =>
assert (TAIL : forall Ej regsj memj mdj,
  st_ok tfibsegs Ej ta_ssJ (restrict (w_H W) (mkst regsj (Z_to_bv 64 539916) memj (seg_rom tfibsegs))) ->
  ajournal tfibsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memj mdj k ->
  (forall n, (n < 37)%nat -> ew Ej n = ew E0 n) ->
  env_agree 32 (Ereg regs (cw_extra xs)) Ej ->
  ew Ej 63 = Z_to_bv 64 (Z.of_nat (text_lenZ data)) ->
  ew Ej 65 = Z_to_bv 64 (p + Z.of_nat (text_hdrZ data)) ->
  ew Ej 66 = Z_to_bv 64 (Z.of_nat (length data - text_usedZ data)) ->
  ew Ej 70 = Z_to_bv 64 (p + Z.of_nat (text_usedZ data)) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ ((spZ regs - (32 + 4096) <= a < spZ regs) \/ (ip <= a < ip + 16)) ->
     aview tfibsegs (w_H W) memj a = aview tfibsegs (w_H W) memc a) ->
  SRr tfibsegs W (mkCfg (mkst regsj (Z_to_bv 64 539916) memj (seg_rom tfibsegs)) mdj)
    (cdc_post sg Bv MTv STKv sp0v FPv lyv Sv W0v mem0v md0v ownv kv regsv Tv Ezv lycv Scv Wv memcv mdj Rv))
end.
{ intros Ej regsj memj mdj HSt HJt AGt HAEt E63 E65 E66 E70 KEt.
  clear HS SHOK HJ AG HAE KE. rename HSt into HS, HJt into HJ, AGt into AG, HAEt into HAE, KEt into KE.
  assert (E1j : ew Ej 1 = getr regs 1) by (rewrite (AG 1%nat) by lia; exact E1).
  assert (Hlen64 : 0 <= Z.of_nat (text_lenZ data) <= 64)
    by (rewrite ta_len_cases; unfold text_hdrZ; pose proof (Z.mod_pos_bound (text_u16Z data) 65 ltac:(lia)); ta_lia).
  assert (Hhdr2 : 0 <= Z.of_nat (text_hdrZ data) <= 2) by (unfold text_hdrZ; ta_lia).
  assert (Huse : Z.of_nat (text_usedZ data) = Z.of_nat (text_hdrZ data) + Z.of_nat (text_lenZ data))
    by (unfold text_usedZ; ta_lia).
  assert (Huse_n : Z.of_nat (text_hdrZ data) + Z.of_nat (text_lenZ data) <= Z.of_nat (length data))
    by (rewrite ta_len_cases; unfold text_hdrZ; ta_lia).
  (* mv a0, s0; mv a2, s1; jal: the run stops at the entry of __asan_memcpy (0x51ae8) *)
  assert (SHOK : sh_ok tfibsegs CW_Bx [] Ej (mrestrict (w_H W) memj)) by (unfold sh_ok; apply Forall_nil).
  cw_run ltac:(ta_awr (spZ regs)).
  cw_keep ta_kwr. ta_ag.
  ta_carry E63. ta_carry E65. ta_carry E66. ta_carry E70.
  lazymatch goal with HS : st_ok _ _ _ (restrict _ ?m) |- _ => is_var m; rename m into msc end.
  assert (Hsp : spZ (ms_regs msc) = spZ regs - 32).
  { ta_reg (2%bv : bv 5) Gr2. unfold spZ at 1. rewrite Gr2. cbn [sv_denot]. ta_ev. ta_lia. }
  lazymatch goal with HS : st_ok _ ?Ev ?ssv (restrict _ msc) |- SRr _ _ (mkCfg msc ?mdv) _ =>
    eapply (cw_intrin_call B LAWS OCpy CB_MEMCPY AMEMCPY W Ev ssv msc mdv STK sp0 FP ly S W0 mem0 md0 own lyc Sc k
      tx (p + Z.of_nat (text_hdrZ data)) (Z.of_nat (text_lenZ data)) 0x83d18 80 [ta_curJ; ta_stkJ])
  end.
  { exact HS. }
  { vm_compute. reflexivity. }
  { vm_compute. reflexivity. }
  { eassumption. }
  { ta_reg (10%bv : bv 5) Gq10. rewrite Gq10, sv_denot_SOff0. ta_ev. reflexivity. }
  { ta_reg (11%bv : bv 5) Gq11. rewrite Gq11, sv_denot_SOff0, E65. reflexivity. }
  { ta_reg (12%bv : bv 5) Gq12. rewrite Gq12, sv_denot_SOff0, E63. reflexivity. }
  { ta_lia. }
  { ta_lia. }
  { ta_lia. }
  { rewrite Hsp. unfold ESTACK. ta_lia. }
  { rewrite Hsp. ta_lia. }
  { rewrite Hsp. rewrite Zminus_mod, Hal16. reflexivity. }
  { exact Hsp016. }
  { ta_reg (3%bv : bv 5) Gq3. rewrite Gq3, sv_denot_SOff0. ta_ev. rewrite E3. exact Hgp. }
  { ta_reg (4%bv : bv 5) Gq4. rewrite Gq4, sv_denot_SOff0. ta_ev. rewrite E4. exact Htp. }
  { vm_compute. reflexivity. }
  { ta_lia. }
  { unfold YK0s.ret_ok. apply bv_eq. vm_compute. reflexivity. }
  { intros a Ha. rewrite Hsp. unfold ESTACK. split; [exact (proj1 (TWX a ltac:(lia)))|]. clear - Ha CWX Hlen64. lia. }
  { unfold amem_range. clear - AMX Hlen64 C2 C3 C4 C5. lia. }
  { eapply ta_ra_kept; [exact KE | intros x Hx; apply HSO; clear - Hx Htx0 AMX Hlen64 C3 C4 C5; lia |].
    eapply range_addressable_sub; [exact RAX | ta_lia | ta_lia]. }
  { intros Hl0. eapply (ta_hull_kept _ _ _ _ tx 65); [exact KE | intros s0 Hs0; apply (HSH tx 65); [lia | clear - AMX C3 C4 C5; lia | lia | exact Hs0] | lia | lia | lia | lia | exact (HVX ltac:(lia))]. }
  { split; [ta_lia|]. split; [ta_lia|]. split.
    { intros a Ha. rewrite Hsp. unfold ESTACK. split; [| clear - Ha CWD Huse_n Hlen64 Hhdr2; lia].
      destruct (HDK (a - p) ltac:(ta_lia)) as [HDK1 HDK2]. replace (p + (a - p)) with a in HDK2 by ta_lia.
      rewrite (KE a ltac:(ta_lia) HDK2). apply HPRD. ta_lia. }
    split; [clear - D2 Huse_n Hlen64 Hhdr2; lia|].
    split; [unfold amem_range; clear - AMD Huse_n Hlen64 Hhdr2 C2 C3 C4 C5; lia|].
    split.
    { eapply ta_ra_kept; [exact KE | intros x Hx; apply HSO; clear - Hx Hp0 AMD Huse_n Hlen64 Hhdr2 C3 C4 C5; lia |].
      eapply range_addressable_sub; [exact RAD | ta_lia | ta_lia]. }
    intros Hl0. eapply (ta_hull_kept _ _ _ _ p (Z.of_nat (length data)));
      [exact KE | intros s0 Hs0; apply (HSH p (Z.of_nat (length data))); [lia | clear - AMD C3 C4 C5; lia | lia | exact Hs0]
      | ta_lia | ta_lia | ta_lia | ta_lia | exact (HVD ltac:(ta_lia))]. }
  { vm_compute. reflexivity. }
  { vm_compute. reflexivity. }
  { vm_compute. reflexivity. }
  { vm_compute. reflexivity. }
  { cbn [ss_mem]. apply submem_refl. }
  { apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val ta_curJ ta_stkJ];
    (split; [intros a Ha; ta_ev_in Ha; rewrite Hsp; unfold ESTACK; clear - Ha D1 CWI CWX Hlen64 Hceil C1 H47 Hip0 Hip63; lia | lia]). }
  intros regs2 mem2 md2 HJ2 HP2 Ha02 Heff Hfr2 Hpres2 Hsm2 HS2.
  cbn [ms_regs ms_mem mkst] in HP2, Heff, Hfr2, Hpres2.
  clear HS. rename HS2 into HS. ta_norm. ta_ag.
  rewrite Hsp in Hfr2. unfold ESTACK in Hfr2.
  (* the text's bytes after the copy, in terms of the entry memory *)
  assert (DATA2 : forall j, 0 <= j < Z.of_nat (text_lenZ data) ->
    aview tfibsegs (w_H W) mem2 (tx + j) = aview tfibsegs (w_H W) memc (p + Z.of_nat (text_hdrZ data) + j)).
  { intros j Hj. rewrite (Heff j Hj). destruct (HDK (Z.of_nat (text_hdrZ data) + j) ltac:(ta_lia)) as [HDK1 HDK2].
    replace (p + Z.of_nat (text_hdrZ data) + j) with (p + (Z.of_nat (text_hdrZ data) + j)) by ta_lia.
    apply KE; [ta_lia | exact HDK2]. }
  assert (TJ2 : forall j, Z.of_nat (text_lenZ data) <= j < 65 ->
    aview tfibsegs (w_H W) mem2 (tx + j) = aview tfibsegs (w_H W) memc (tx + j)).
  { intros j Hj. rewrite Hfr2 by (clear - Hj CWX Htx0 Htx63 Hlen64; lia). apply KE; [lia | clear - Hj D1 CWX Htx0; lia]. }
  assert (KE2 : forall a, 0 <= a < 2 ^ 64 ->
    ~ ((spZ regs - (32 + 4096) <= a < spZ regs) \/ (ip <= a < ip + 16) \/ (tx <= a < tx + 65)) ->
    aview tfibsegs (w_H W) mem2 a = aview tfibsegs (w_H W) memc a).
  { intros a Ha Hz. rewrite Hfr2 by (clear - Ha Hz Hlen64; lia). apply KE; [exact Ha | clear - Hz; tauto]. }
  assert (HSO2 : forall x, 0 <= x < 2 ^ 47 -> 0 <= shadow_of_addr SHADOW_OFF x < 2 ^ 64 /\
    ~ ((spZ regs - (32 + 4096) <= shadow_of_addr SHADOW_OFF x < spZ regs) \/ (ip <= shadow_of_addr SHADOW_OFF x < ip + 16) \/
       (tx <= shadow_of_addr SHADOW_OFF x < tx + 65))).
  { intros x Hx. destruct (HSO x Hx) as [HS1 HS2]. split; [exact HS1|].
    intros [Hz | [Hz | Hz]]; [tauto | tauto |]. unfold shadow_of_addr, SHADOW_OFF in Hz.
    pose proof (Z.div_mod x 8 ltac:(ta_lia)). pose proof (Z.mod_pos_bound x 8 ltac:(ta_lia)).
    clear - Hx Hz AMX C2 C3 C4 C5 H H0. lia. }
  clear KE Heff Hfr2. rename KE2 into KE.
  pose proof (cj_dst_byte tfibsegs B LAWS lyc Sc W memc mdc tx 65 (tx + Z.of_nat (text_lenZ data)) HAR TDX ltac:(ta_lia)) as (HQ1 & HQ2).
  assert (TWQ : twr_ok tfibsegs B STK sp0 FP ly S lyc Sc own W memc (spZ regs) (tx + Z.of_nat (text_lenZ data)) 1)
    by (intros a Ha; apply TWX; ta_lia).
  (* atom 100 = text + length, the address the 0 is stored to; a0 = s0 + s1 becomes it by an alias *)
  lazymatch goal with HS : st_ok _ ?Ev ?ssv ?msv |- _ =>
    pose proof (YCeo.st_ok_havoc_win tfibsegs 100 Ev ssv msv [Z_to_bv 64 (tx + Z.of_nat (text_lenZ data))] HS ltac:(vm_compute; reflexivity)) as HS3;
    clear HS; rename HS3 into HS end.
  ta_ag. ta_carry E63. ta_carry E66. ta_carry E70.
  lazymatch goal with HS : st_ok _ ?Ev _ _ |- _ =>
    assert (E100 : ew Ev 100 = Z_to_bv 64 (tx + Z.of_nat (text_lenZ data)))
      by (change 100%nat with (100 + 0)%nat; rewrite (ew_havoc_new _ 100 _ 0 (Z_to_bv 64 0)) by (cbn; ta_lia); reflexivity) end.
  lazymatch goal with HS : st_ok _ ?Ev ?ssv ?msv |- _ =>
    assert (Hal : sv_denot Ev (SAlu ALU_ADD (SOff 11 0) (SOff 63 0)) = sv_denot Ev (SOff 100 0));
    [ rewrite !denot_lit_U; f_equal; rewrite U_SAlu; cbn [zalu_raw];
      rewrite (U_atom Ev 11 tx), (U_atom Ev 63 (Z.of_nat (text_lenZ data))), (U_atom Ev 100 (tx + Z.of_nat (text_lenZ data)))
        by (first [ta_lia | assumption | ta_ev; reflexivity]);
      apply zcanon_id; unfold M64; ta_lia
    | pose proof (YFl3.st_ok_add_alias Ev ssv msv _ _ HS Hal) as HS3; clear HS Hal; rename HS3 into HS ] end.
  lazymatch goal with HS : st_ok _ ?Ev ?ssv ?msv |- _ =>
    pose proof (YP03.st_ok_add_fact tfibsegs Ev ssv msv 100 (mkAF 4096 (2 ^ 47 - 1) 0) HS
      ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E100, unsigned_lit_small by ta_lia; rewrite Z.pow_0_r, Z.mod_1_r; ta_lia)) as HS3;
    clear HS; rename HS3 into HS end.
  ta_norm.
  lazymatch goal with HS : st_ok _ ?Ex ?ssx ?msx |- _ =>
    assert (RK : region_ok tfibsegs Ex (ms_mem msx) (YP09.mkRegion (Some 100%nat) 0 1 0 1 []));
    [| assert (RD : all_disjoint Ex (YP09.mkRegion (Some 100%nat) 0 1 0 1 []) (ss_mem ssx));
       [| pose proof (ast_ok_add_region tfibsegs Ex ssx msx (YP09.mkRegion (Some 100%nat) 0 1 0 1 []) HS eq_refl RK RD) as HS3;
          clear HS RK RD; rename HS3 into HS; ta_norm ] ] end.
  { unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst].
    rewrite E100, unsigned_lit_small by ta_lia. split; [ta_lia|]. split; [ta_lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable tfibsegs).
    exact (ta_tdst_present lyc Sc W mem2 md2 tx 65 TDX (proj1 HJ2) (tx + Z.of_nat (text_lenZ data) + o) ltac:(ta_lia)). }
  { apply all_disjoint_of_extents. cbn [ss_mem]. unfold extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val zall_disjoint]. rewrite E100, unsigned_lit_small by ta_lia. ta_ev.
    unfold zdisj. cbn [fst snd]. clear - D1 CWX Hlen64 Htx0; repeat split; lia. }
  clear SHOK.
  lazymatch goal with HS : st_ok _ ?Ev _ _ |- _ =>
    assert (SHOK : sh_ok tfibsegs CW_Bx [mkSHE 10 0 16; mkSHE 100 0 1] Ev (mrestrict (w_H W) mem2)) end.
  { unfold sh_ok. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    - apply (cw_shent_ra W mem2 _ 10 ip 16); [| exact AMI | ta_lia | ta_lia | ta_lia | ta_ev; reflexivity | ta_ev; reflexivity].
      eapply ta_ra_kept; [exact KE | intros x Hx; apply HSO2; clear - Hx Hip0 AMI C3 C4 C5; unfold amem_range in AMI; lia | exact RAI].
    - apply (cw_shent_ra W mem2 _ 100 (tx + Z.of_nat (text_lenZ data)) 1);
        [| unfold amem_range; clear - AMX Hlen64 C3 C4 C5; lia | lia | lia | lia | exact E100 | ta_ev; reflexivity].
      eapply ta_ra_kept; [exact KE | intros x Hx; apply HSO2; clear - Hx Htx0 AMX Hlen64 C3 C4 C5; lia |].
      eapply range_addressable_sub; [exact RAX | ta_lia | ta_lia]. }
(* the last run: the UBSan check of text + length (0x83d18 - 0x83d1c), a0 = text + length, its check, sb zero, the
     epilogue; stop at ret. KT keeps the text's bytes other than text[length] from the memory after the copy *)
  assert (KT : forall a, 0 <= a < 2 ^ 64 ->
    ~ ((spZ regs - (32 + 4096) <= a < spZ regs) \/ (ip <= a < ip + 16) \/ (a = tx + Z.of_nat (text_lenZ data))) ->
    aview tfibsegs (w_H W) mem2 a = aview tfibsegs (w_H W) mem2 a) by (intros; reflexivity).
  cw_run ltac:(ta_awr2 (spZ regs)).
 
  lazymatch goal with HFr : frame_of _ _ (mrestrict _ _) (mrestrict _ _) |- _ =>
    pose proof (cw_kept_run _ _ _ _ _ _ _ KT HFr) as KT2 end.
  lazymatch type of KT2 with ?P -> _ => assert (KW : P) by ta_kwr end.
  specialize (KT2 KW). clear KW KT. revert KT2.
  cw_keep ta_kwr. intros KT. cbv beta in KE, KT.
  ta_ag. ta_carry E63. ta_carry E66. ta_carry E70. ta_carry E100.
  cw_branch Hb9.
  { (* bltu ~text, length taken: text + length >= 2 ^ 64, impossible *)
    exfalso. rewrite branch_ltu_U in Hb9.
    rewrite (ta_U_not _ 11 tx), (U_atom _ 63 (Z.of_nat (text_lenZ data))) in Hb9 by (first [ta_ev; reflexivity | assumption | ta_lia]).
    apply Z.ltb_lt in Hb9. ta_lia. }
  clear Hb9.
  cw_run ltac:(ta_awr2 (spZ regs)).
 
  lazymatch goal with HFr : frame_of _ _ (mrestrict _ _) (mrestrict _ _) |- _ =>
    pose proof (cw_kept_run _ _ _ _ _ _ _ KT HFr) as KT2 end.
  lazymatch type of KT2 with ?P -> _ => assert (KW : P) by ta_kwr end.
  specialize (KT2 KW). clear KW KT. revert KT2.
  cw_keep ta_kwr. intros KT. cbv beta in KE, KT.
  ta_ag. ta_carry E66. ta_carry E70. ta_carry E100.
  assert (HwloT : sp0 - STK <= spZ regs - TB_text_arg) by (unfold TB_text_arg, ESTACK; ta_lia).
  cw_leaf
    ltac:(idtac; cw_kept HJ0 KE
      ltac:(idtac; let a := fresh "a" in let Ha := fresh "Ha" in let Himg := fresh "Himg" in
            intros a Ha Himg; cbv beta in Ha; destruct Ha as [Ha | Ha];
            [pose proof (tfib_segs_low a Himg) as Hl; ta_lia
            | exact (cw_tdst_not_img _ _ LAWS tfib_segs_low _ _ _ _ _ _ _ _ HAR TDX Ha Himg)])
      ltac:(idtac; let a := fresh "a" in let Hz := fresh "Hz" in let Ha := fresh "Ha" in
            intros a Hz; cbv beta in Hz |- *; destruct Hz as [Ha | [Ha | Ha]];
            [left; unfold TB_text_arg, ESTACK; ta_lia | right; left; exact Ha | right; right; exact Ha]))
    ltac:(idtac).
  (* the result: the cursor's two words, the text *)
  lazymatch goal with HS : st_ok _ ?Ef ?ssf (restrict ?Hh ?msf) |- _ =>
    let r0 := eval vm_compute in (nth 0 (ss_mem ssf) ta_curJ) in
    let r1 := eval vm_compute in (nth 1 (ss_mem ssf) ta_curJ) in
    pose proof (st_ok_region_nth Ef ssf (restrict Hh msf) 0 r0 HS eq_refl) as HRC0;
    pose proof (st_ok_region_nth Ef ssf (restrict Hh msf) 1 r1 HS eq_refl) as HRC1
  end.
  cbn [ms_mem restrict] in HRC0, HRC1.
  cbv beta. split; [|split].
  { pose proof (field_of_region _ _ 10 ip _ 0 16 0 16 0 8 (SOff 70 0) (p + Z.of_nat (text_usedZ data)) HRC1
      ltac:(ta_ev; reflexivity) ltac:(cbn [In]; repeat (first [left; reflexivity | right]))
      ltac:(rewrite sv_denot_SOff0; exact E70) ltac:(change (8 * Z.of_N 8) with 64; ta_lia)
      ltac:(change (Z.of_N 8) with 8; lia)) as Vf.
    rewrite Z.add_0_r in Vf. change (N.to_nat 8) with 8%nat in Vf. exact Vf. }
  { pose proof (field_of_region _ _ 10 ip _ 0 16 0 16 8 8 (SOff 66 0) (Z.of_nat (length data - text_usedZ data)) HRC1
      ltac:(ta_ev; reflexivity) ltac:(cbn [In]; repeat (first [left; reflexivity | right]))
      ltac:(rewrite sv_denot_SOff0; exact E66) ltac:(change (8 * Z.of_N 8) with 64; ta_lia)
      ltac:(change (Z.of_N 8) with 8; lia)) as Vf.
    change (N.to_nat 8) with 8%nat in Vf. exact Vf. }
  unfold text_takenZ.
  apply ta_garr8_text.
  { ta_lia. }
  { ta_lia. }
  { exact HTL. }
  { intros j Hj. destruct (HD (text_hdrZ data + j)%nat ltac:(ta_lia)) as [HV HR]. split; [|exact HR].
    apply (ta_val1_move (w_H W) memc _ (p + Z.of_nat (text_hdrZ data + j)) (tx + Z.of_nat j)); [|exact HV].
    rewrite (KT (tx + Z.of_nat j)) by (clear - Hj CWX D1 Htx0 Htx63 Hlen64; lia).
    rewrite (DATA2 (Z.of_nat j)) by ta_lia. f_equal. ta_lia. }
  { pose proof (field_of_region _ _ 100 (tx + Z.of_nat (text_lenZ data)) _ 0 1 0 1 0 1 (SLit 0) 0 HRC0
      ltac:(rewrite E100; apply unsigned_lit_small; ta_lia) ltac:(left; reflexivity)
      ltac:(reflexivity) ltac:(change (8 * Z.of_N 1) with 8; lia) ltac:(change (Z.of_N 1) with 1; lia)) as Vf.
    rewrite Z.add_0_r in Vf. change (N.to_nat 1) with 1%nat in Vf. exact Vf. }
  { intros j Hj. destruct (HT j ltac:(rewrite HTL; lia)) as [HV HR]. split; [|exact HR].
    apply (ta_val1_move (w_H W) memc _ (tx + Z.of_nat j) (tx + Z.of_nat j)); [|exact HV].
    rewrite (KT (tx + Z.of_nat j)) by (clear - Hj CWX D1 Htx0 Htx63 Hlen64; lia).
    apply TJ2. lia. }
}
unfold cfg_at. change (w64 TA_B) with (Z_to_bv 64 TA_B).
(* run 1: prologue, the alignment check of the cursor, the loads of n; stop at 0x83be8 beqz a7 *)
cw_run ltac:(ta_awr (spZ regs)).
cw_keep ta_kwr. ta_ag.
cw_branch Hb1.
- (* beqz a7 taken: n = 0 *)
  rewrite branch_eq_U, (U_atom _ 34 (Z.of_nat (length data))), U_lit in Hb1 by (first [lia | ta_ev; reflexivity]).
  apply Z.eqb_eq in Hb1.
  cw_run ltac:(ta_awr (spZ regs)).
  cw_keep ta_kwr. ta_ag.
  cw_branch Hb3.
  + (* bltu s1, a2 taken: 0 < n = 0, impossible *)
    exfalso. rewrite branch_ltu_U, U_lit, (U_atom _ 34 (Z.of_nat (length data))) in Hb3 by (first [lia | ta_ev; reflexivity]).
    rewrite Hb1 in Hb3. discriminate Hb3.
  + (* not taken: the length is n = 0 *)
    clear Hb3.
    ta_to_join (spZ regs) p (Z.of_nat (length data)).
   
    lazymatch goal with HS : st_ok _ _ _ (restrict _ ?m) |- _ => is_var m; rename m into msj end.
    assert (L0 : length data = 0%nat) by lia.
    assert (Hhdr : text_hdrZ data = 0%nat) by (unfold text_hdrZ; rewrite L0; reflexivity).
    assert (Hlen : text_lenZ data = 0%nat) by (unfold text_lenZ; rewrite Hhdr, L0; apply Nat.min_0_r).
    assert (Hused : text_usedZ data = 0%nat) by (unfold text_usedZ; rewrite Hhdr, Hlen; reflexivity).
    lazymatch goal with HS : st_ok _ ?Ev _ _ |- _ =>
      assert (U34 : U Ev (SOff 34 0) = Z.of_nat (length data)) by (apply U_atom; [ta_ev; reflexivity | lia]);
      assert (U33 : U Ev (SOff 33 0) = p) by (apply U_atom; [ta_ev; reflexivity | lia]) end.
    ta_reg (9%bv : bv 5) Gr9. ta_reg (11%bv : bv 5) Gr11. ta_reg (12%bv : bv 5) Gr12. ta_reg (16%bv : bv 5) Gr16.
    rewrite denot_lit_U in Gr9, Gr11, Gr12, Gr16.
    assert (V9 : getr (ms_regs msj) 9%bv = Z_to_bv 64 (Z.of_nat (text_lenZ data))) by (rewrite Gr9, U34, Hlen, Hb1; reflexivity).
    assert (V11 : getr (ms_regs msj) 11%bv = Z_to_bv 64 (p + Z.of_nat (text_hdrZ data)))
      by (rewrite Gr11, U33, Hhdr, Z.add_0_r; reflexivity).
    assert (V12 : getr (ms_regs msj) 12%bv = Z_to_bv 64 (Z.of_nat (length data - text_usedZ data)))
      by (rewrite Gr12, U_lit by lia; rewrite L0, Hused; reflexivity).
    assert (V16 : getr (ms_regs msj) 16%bv = Z_to_bv 64 (p + Z.of_nat (text_usedZ data))).
    { rewrite Gr16, U_SAlu. cbn [zalu_raw]. rewrite U33, U34, Hb1, Hused. unfold zcanon, M64. f_equal.
      rewrite Z.mod_small by lia. lia. }
    clear Gr9 Gr11 Gr12 Gr16.
    ta_join 0%nat 3%nat V12 V16.
    { ta_join_rk V0 V8 HRW V12 V16. }
    { ta_join_rd. }
    ta_join_end.
    ta_tail TAIL V9 V11 V12 V16.
- (* not taken: n <> 0 *)
  rewrite branch_eq_U, (U_atom _ 34 (Z.of_nat (length data))), U_lit in Hb1 by (first [lia | ta_ev; reflexivity]).
  assert (Hn0 : Z.of_nat (length data) <> 0) by (intros Ez; rewrite Ez in Hb1; discriminate Hb1). clear Hb1.
  ta_keep_regs [0; 3]%nat.
  lazymatch goal with HS : st_ok _ ?Ex ?ssx (restrict _ ?msx) |- _ =>
    assert (RK : region_ok tfibsegs Ex (mrestrict (w_H W) (ms_mem msx)) ta_d0);
    [| assert (RD : all_disjoint Ex ta_d0 (ss_mem ssx)); [| 
       pose proof (ast_ok_add_region tfibsegs Ex ssx (restrict (w_H W) msx) ta_d0 HS eq_refl RK RD) as HS3;
       clear HS RK RD; rename HS3 into HS; ta_norm ] ] end.
  { unfold region_ok, ta_d0. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    ta_ev. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val tfibsegs _ _ p 0 1 (SOff 35 0) (nth 0 data 0)).
    - cbn [sv_denot]. ta_ev. rewrite Z.add_0_r. reflexivity.
    - zside.
    - zside.
    - eapply cw_val_mem_kept; [| exact (proj1 (HD 0%nat ltac:(lia)))].
      intros x Hx. cbn in Hx. destruct (HDK 0 ltac:(lia)) as [HDK1 HDK2]. replace x with (p + 0) by lia.
      apply KE; [lia | exact HDK2]. }
  { apply all_disjoint_of_extents. cbn [ss_mem]. unfold extent_of_region, ta_d0.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val zall_disjoint]. ta_ev. unfold zdisj. cbn [fst snd].
    clear - Hn0 CWD D3 Hp0 Hpn. repeat split; lia. }
  (* run 2: n - 1 to in->n, the UBSan check of p + 1, p + 1 to in->p, the first byte's check; stop at 0x83c38 beqz t1 *)
  cw_run_ob ltac:(ta_awr (spZ regs)) ltac:(ta_obl RAD HSO).
  cw_keep ta_kwr. ta_ag.
  cw_branch Hb2.
  + (* beqz t1 taken: n = 1 *)
    rewrite branch_eq_U, (U_atom_off _ 34 (Z.of_nat (length data)) (-1)), U_lit in Hb2 by (first [lia | ta_ev; reflexivity]).
    assert (Hn1 : Z.of_nat (length data) = 1) by (apply Z.eqb_eq in Hb2; lia). clear Hb2.
    cw_run ltac:(ta_awr (spZ regs)).
    cw_keep ta_kwr. ta_ag.
    lazymatch goal with HS : st_ok _ ?Ev _ _ |- _ =>
      pose proof (ta_U_v1 Ev (nth 0 data 0) ltac:(ta_ev; reflexivity) Ex0) as Uv;
      pose proof (ta_U_m65 Ev _ _ Uv ltac:(lia)) as Ul;
      assert (U34m : U Ev (SOff 34 (-1)) = Z.of_nat (length data) - 1) by (apply U_atom_off; [ta_ev; reflexivity | lia | lia]) end.
    pose proof (Z.mod_pos_bound (nth 0 data 0) 65 ltac:(lia)) as Hm65.
    cw_branch Hb3.
    * (* bltu s1, a2 taken: x0 mod 65 < n - 1 = 0, impossible *)
      exfalso. rewrite branch_ltu_U, Ul, U34m, Hn1 in Hb3. apply Z.ltb_lt in Hb3. lia.
    * (* not taken: the length is n - 1 = 0 *)
      clear Hb3.
      ta_to_join (spZ regs) p (Z.of_nat (length data)).
     
      lazymatch goal with HS : st_ok _ _ _ (restrict _ ?m) |- _ => is_var m; rename m into msj end.
      assert (L1 : length data = 1%nat) by lia.
      assert (Hhdr : text_hdrZ data = 1%nat) by (unfold text_hdrZ; rewrite L1; reflexivity).
      assert (Hlen : text_lenZ data = 0%nat) by (unfold text_lenZ; rewrite Hhdr, L1; apply Nat.min_0_r).
      assert (Hused : text_usedZ data = 1%nat) by (unfold text_usedZ; rewrite Hhdr, Hlen; reflexivity).
      lazymatch goal with HS : st_ok _ ?Ev _ _ |- _ =>
        assert (U34m1 : U Ev (SOff 34 (-1)) = 0)
          by (rewrite (U_atom_off _ 34 (Z.of_nat (length data)) (-1)) by (first [lia | ta_ev; reflexivity]); lia);
        assert (U34 : U Ev (SOff 34 0) = 1) by (rewrite <- Hn1; apply U_atom; [ta_ev; reflexivity | lia]);
        assert (U33p : U Ev (SOff 33 1) = p + 1) by (apply U_atom_off; [ta_ev; reflexivity | lia | lia]);
        assert (U33 : U Ev (SOff 33 0) = p) by (apply U_atom; [ta_ev; reflexivity | lia]) end.
      ta_reg (9%bv : bv 5) Gr9. ta_reg (11%bv : bv 5) Gr11. ta_reg (12%bv : bv 5) Gr12. ta_reg (16%bv : bv 5) Gr16.
      rewrite denot_lit_U in Gr9, Gr11, Gr12, Gr16.
      assert (V9 : getr (ms_regs msj) 9%bv = Z_to_bv 64 (Z.of_nat (text_lenZ data))) by (rewrite Gr9, U34m1, Hlen; reflexivity).
      assert (V11 : getr (ms_regs msj) 11%bv = Z_to_bv 64 (p + Z.of_nat (text_hdrZ data))) by (rewrite Gr11, U33p, Hhdr; reflexivity).
      assert (V12 : getr (ms_regs msj) 12%bv = Z_to_bv 64 (Z.of_nat (length data - text_usedZ data)))
        by (rewrite Gr12, U_lit by lia; rewrite L1, Hused; reflexivity).
      assert (V16 : getr (ms_regs msj) 16%bv = Z_to_bv 64 (p + Z.of_nat (text_usedZ data))).
      { rewrite Gr16, U_SAlu. cbn [zalu_raw]. rewrite ?U33, ?U34, ?U33p, ?U34m1, Hused. unfold zcanon, M64. f_equal.
        rewrite Z.mod_small by lia. lia. }
      clear Gr9 Gr11 Gr12 Gr16.
      ta_join 1%nat 2%nat V12 V16.
      { ta_join_rk V0 V8 HRW V12 V16. }
      { ta_join_rd. }
      ta_join_end.
      ta_tail TAIL V9 V11 V12 V16.
  + (* not taken: n >= 2 *)
    rewrite branch_eq_U, (U_atom_off _ 34 (Z.of_nat (length data)) (-1)), U_lit in Hb2 by (first [lia | ta_ev; reflexivity]).
    assert (Hn1 : Z.of_nat (length data) <> 1) by (intros Ez; rewrite Ez in Hb2; discriminate Hb2). clear Hb2.
    lazymatch goal with HS : st_ok _ ?Ex ?ssx ?msx |- _ =>
      pose proof (YP03.st_ok_add_fact tfibsegs Ex ssx msx 33 (mkAF 1 (2 ^ 47 - 3) 0) HS
        ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; ta_ev; rewrite Z.pow_0_r, Z.mod_1_r; lia)) as HS3;
      clear HS; rename HS3 into HS end.
    ta_norm.
    lazymatch goal with HS : st_ok _ ?Ex ?ssx (restrict _ ?msx) |- _ =>
      assert (RK : region_ok tfibsegs Ex (mrestrict (w_H W) (ms_mem msx)) ta_d1);
      [| assert (RD : all_disjoint Ex ta_d1 (ss_mem ssx)); [|
         pose proof (ast_ok_add_region tfibsegs Ex ssx (restrict (w_H W) msx) ta_d1 HS eq_refl RK RD) as HS3;
         clear HS RK RD; rename HS3 into HS; ta_norm ] ] end.
    { unfold region_ok, ta_d1. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      ta_ev. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val tfibsegs _ _ p 1 1 (SOff 36 0) (nth 1 data 0)).
      - cbn [sv_denot]. ta_ev. rewrite Z.add_0_r. reflexivity.
      - zside.
      - zside.
      - eapply cw_val_mem_kept; [| exact (proj1 (HD 1%nat ltac:(lia)))].
        intros x Hx. cbn in Hx. destruct (HDK 1 ltac:(lia)) as [HDK1 HDK2]. replace x with (p + 1) by lia.
        apply KE; [lia | exact HDK2]. }
    { apply all_disjoint_of_extents. cbn [ss_mem]. unfold extent_of_region, ta_d1.
      cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val zall_disjoint]. ta_ev. unfold zdisj. cbn [fst snd].
      clear - Hn0 Hn1 CWD D3 Hp0 Hpn. repeat split; lia. }
    (* run 3: n - 2 to in->n, the UBSan check of p + 2, p + 2 to in->p, the second byte's check, the length; stop at
       0x83cc0 bltu s1, a2 *)
    cw_run_ob ltac:(ta_awr (spZ regs)) ltac:(ta_obl RAD HSO).
    cw_keep ta_kwr. ta_ag.
    cw_branch Hb3.
    * (* bltu s1, a2 taken: the length is v mod 65, below n - 2 *)
      lazymatch goal with HS : st_ok _ ?Ev _ _ |- _ =>
        pose proof (ta_U_v2 Ev (nth 0 data 0) (nth 1 data 0) ltac:(ta_ev; reflexivity) ltac:(ta_ev; reflexivity) Ex0 Ex1) as Uv;
        pose proof (ta_U_m65 Ev _ _ Uv ltac:(lia)) as Ul;
        assert (U34 : U Ev (SOff 34 (-2)) = Z.of_nat (length data) - 2) by (apply U_atom_off; [ta_ev; reflexivity | lia | lia]);
        assert (U33 : U Ev (SOff 33 2) = p + 2) by (apply U_atom_off; [ta_ev; reflexivity | lia | lia]) end.
      rewrite branch_ltu_U, Ul, U34 in Hb3. apply Z.ltb_lt in Hb3.
      assert (Hu16 : text_u16Z data = nth 0 data 0 + 256 * nth 1 data 0) by reflexivity.
      assert (Hhdr : Z.of_nat (text_hdrZ data) = 2) by (unfold text_hdrZ; lia).
      assert (Hlen : Z.of_nat (text_lenZ data) = (nth 0 data 0 + 256 * nth 1 data 0) mod 65)
        by (rewrite ta_len_cases, Hu16, Hhdr; lia).
      assert (Hused : Z.of_nat (text_usedZ data) = 2 + (nth 0 data 0 + 256 * nth 1 data 0) mod 65)
        by (unfold text_usedZ; rewrite Nat2Z.inj_add, Hhdr, Hlen; lia).
      pose proof (Z.mod_pos_bound (nth 0 data 0 + 256 * nth 1 data 0) 65 ltac:(lia)) as Hm65.
      ta_to_join (spZ regs) p (Z.of_nat (length data)).
     
      lazymatch goal with HS : st_ok _ _ _ (restrict _ ?m) |- _ => is_var m; rename m into msj end.
      ta_reg (9%bv : bv 5) Gr9. ta_reg (11%bv : bv 5) Gr11. ta_reg (12%bv : bv 5) Gr12. ta_reg (16%bv : bv 5) Gr16.
      rewrite denot_lit_U in Gr9, Gr11, Gr12, Gr16.
      rewrite Ul in Gr9. rewrite U33 in Gr11.
      rewrite U_SAlu in Gr12, Gr16. cbn [zalu_raw] in Gr12, Gr16.
      rewrite Ul, U34 in Gr12. rewrite Ul, U33 in Gr16.
      assert (V9 : getr (ms_regs msj) 9%bv = Z_to_bv 64 (Z.of_nat (text_lenZ data))) by (rewrite Gr9, Hlen; reflexivity).
      assert (V11 : getr (ms_regs msj) 11%bv = Z_to_bv 64 (p + Z.of_nat (text_hdrZ data))) by (rewrite Gr11, Hhdr; reflexivity).
      assert (V12 : getr (ms_regs msj) 12%bv = Z_to_bv 64 (Z.of_nat (length data - text_usedZ data))).
      { rewrite Gr12, Nat2Z.inj_sub, Hused by (apply Nat2Z.inj_le; rewrite Hused; lia).
        unfold zcanon, M64. f_equal. rewrite Z.mod_small by lia. lia. }
      assert (V16 : getr (ms_regs msj) 16%bv = Z_to_bv 64 (p + Z.of_nat (text_usedZ data))).
      { rewrite Gr16, Hused. unfold zcanon, M64. f_equal. rewrite Z.mod_small by lia. lia. }
      clear Gr9 Gr11 Gr12 Gr16.
      ta_join 2%nat 3%nat V12 V16.
      { ta_join_rk V0 V8 HRW V12 V16. }
      { ta_join_rd. }
      ta_join_end.
      ta_tail TAIL V9 V11 V12 V16.
    * (* bltu s1, a2 not taken: the length is n - 2, at most v mod 65 *)
      lazymatch goal with HS : st_ok _ ?Ev _ _ |- _ =>
        pose proof (ta_U_v2 Ev (nth 0 data 0) (nth 1 data 0) ltac:(ta_ev; reflexivity) ltac:(ta_ev; reflexivity) Ex0 Ex1) as Uv;
        pose proof (ta_U_m65 Ev _ _ Uv ltac:(lia)) as Ul;
        assert (U34 : U Ev (SOff 34 (-2)) = Z.of_nat (length data) - 2) by (apply U_atom_off; [ta_ev; reflexivity | lia | lia]) end.
      rewrite branch_ltu_U, Ul, U34 in Hb3. apply Z.ltb_ge in Hb3.
      assert (Hu16 : text_u16Z data = nth 0 data 0 + 256 * nth 1 data 0) by reflexivity.
      assert (Hhdr : Z.of_nat (text_hdrZ data) = 2) by (unfold text_hdrZ; lia).
      assert (Hlen : Z.of_nat (text_lenZ data) = Z.of_nat (length data) - 2) by (rewrite ta_len_cases, Hu16, Hhdr; lia).
      assert (Hused : Z.of_nat (text_usedZ data) = Z.of_nat (length data))
        by (unfold text_usedZ; rewrite Nat2Z.inj_add, Hhdr, Hlen; lia).
      ta_to_join (spZ regs) p (Z.of_nat (length data)).
     
      lazymatch goal with HS : st_ok _ _ _ (restrict _ ?m) |- _ => is_var m; rename m into msj end.
      lazymatch goal with HS : st_ok _ ?Ev _ _ |- _ =>
        assert (U34m2 : U Ev (SOff 34 (-2)) = Z.of_nat (length data) - 2) by (apply U_atom_off; [ta_ev; reflexivity | lia | lia]);
        assert (U34z : U Ev (SOff 34 0) = Z.of_nat (length data)) by (apply U_atom; [ta_ev; reflexivity | lia]);
        assert (U33p : U Ev (SOff 33 2) = p + 2) by (apply U_atom_off; [ta_ev; reflexivity | lia | lia]);
        assert (U33z : U Ev (SOff 33 0) = p) by (apply U_atom; [ta_ev; reflexivity | lia]) end.
      ta_reg (9%bv : bv 5) Gr9. ta_reg (11%bv : bv 5) Gr11. ta_reg (12%bv : bv 5) Gr12. ta_reg (16%bv : bv 5) Gr16.
      rewrite denot_lit_U in Gr9, Gr11, Gr12, Gr16.
      assert (V9 : getr (ms_regs msj) 9%bv = Z_to_bv 64 (Z.of_nat (text_lenZ data))) by (rewrite Gr9, U34m2, Hlen; reflexivity).
      assert (V11 : getr (ms_regs msj) 11%bv = Z_to_bv 64 (p + Z.of_nat (text_hdrZ data))) by (rewrite Gr11, U33p, Hhdr; reflexivity).
      assert (V12 : getr (ms_regs msj) 12%bv = Z_to_bv 64 (Z.of_nat (length data - text_usedZ data))).
      { rewrite Gr12, U_lit by lia. rewrite Nat2Z.inj_sub by (apply Nat2Z.inj_le; rewrite Hused; lia).
        rewrite Hused. f_equal. lia. }
      assert (V16 : getr (ms_regs msj) 16%bv = Z_to_bv 64 (p + Z.of_nat (text_usedZ data))).
      { rewrite Gr16, U_SAlu. cbn [zalu_raw]. rewrite ?U33z, ?U34z, ?U33p, ?U34m2, Hused. unfold zcanon, M64. f_equal.
        rewrite Z.mod_small by lia. lia. }
      clear Gr9 Gr11 Gr12 Gr16.
      ta_join 2%nat 3%nat V12 V16.
      { ta_join_rk V0 V8 HRW V12 V16. }
      { ta_join_rd. }
      ta_join_end.
      ta_tail TAIL V9 V11 V12 V16.
Qed.
End d.
End b.
