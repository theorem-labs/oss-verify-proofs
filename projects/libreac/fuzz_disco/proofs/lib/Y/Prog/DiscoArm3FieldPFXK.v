(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the generic part of proofs/cgif/cgif_file_fuzzer/lib/YC1i.v for libreac/fuzz_disco's program walk (ceil, alias_srlw_sll, req_size_pos', PTR, Bspan, region_kept_at1) over fuzz_disco's listing; cgif's create_byte_list_block walk is left out; module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/YC1i.v, with its module paths and module names changed; 21 of its 45 lines of code are new or changed and 45 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/DiscoArm3FieldPFA4.v, with its module paths and module names changed; 353 of its 387 lines of code are new or changed and 11 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/Y/Prog/DiscoArm3FieldPH.v; 163 of its 236 lines of code are new or changed and 314 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0s YI00 YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YCbp YE00 YE01 YO09.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0b YP0a YP0c YP0d YP07 YC80 YI0w YI0z YI12 YC4a YC1f YC8g YC1g YC44 YC45.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YC1h YC1i YC81 YCjr YCj1 YCja YXcalls.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import
DiscoYEntryInv DiscoYEntSeatStmt DiscoArm3TailK.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import DiscoArm3 DiscoArm3FieldCut DiscoArm3FieldPFXKit.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require
disco_table_c disco_table disco_json_text.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import slot_inv.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Lemma a3f_u4_range : forall (T : list byte) (k : Z), 0 <= disco_table_c.u_at T k 4 < 2 ^ 32.
Proof.
  intros T k. unfold disco_table_c.u_at.
  pose proof (disco_table.ble_range (disco_table_c.sub T k 4)) as H.
  assert (HL : (length (disco_table_c.sub T k 4) <= 4)%nat).
  { unfold disco_table_c.sub. rewrite length_firstn. lia. }
  assert (HP : 2 ^ (8 * Z.of_nat (length (disco_table_c.sub T k 4))) <= 2 ^ 32).
  { apply Z.pow_le_mono_r; lia. }
  lia.
Qed.

Lemma a3f_role_u : forall (T : list byte) (p : Z),
  0 <= disco_table_c.role_of_e T p <= 2 ->
  disco_table_c.u_at T (48 * p + 8) 4 = disco_table_c.role_of_e T p.
Proof.
  intros T p Hr. unfold disco_table_c.role_of_e, disco_table_c.s32_at in Hr |- *.
  pose proof (a3f_u4_range T (48 * p + 8)) as Hu.
  set (u := disco_table_c.u_at T (48 * p + 8) 4) in *.
  unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus in Hr |- *.
  change (2 ^ Z.of_N 32) with 4294967296 in Hr |- *.
  change (4294967296 / 2) with 2147483648 in Hr |- *.
  destruct (Z.lt_ge_cases u 2147483648) as [Hlt | Hge].
  - rewrite (Z.mod_small (u + 2147483648) 4294967296) by lia. lia.
  - rewrite <- (Z.mod_add (u + 2147483648) (-1) 4294967296) in Hr by lia.
    rewrite (Z.mod_small (u + 2147483648 + -1 * 4294967296) 4294967296) in Hr by lia. lia.
Qed.

Lemma a3f_used_split : forall p, 0 <= p < 8 ->
  length (firstn (Z.to_nat (4 * p)) (a3f_used p)) = Z.to_nat (4 * p) /\
  a3f_used p =
    firstn (Z.to_nat (4 * p)) (a3f_used p) ++ [0; 0; 0; 0] ++ skipn (Z.to_nat (4 * p + 4)) (a3f_used p) /\
  a3f_used (p + 1) =
    firstn (Z.to_nat (4 * p)) (a3f_used p) ++ [1; 0; 0; 0] ++ skipn (Z.to_nat (4 * p + 4)) (a3f_used p).
Proof.
  intros p Hp.
  assert (E : p = 0 \/ p = 1 \/ p = 2 \/ p = 3 \/ p = 4 \/ p = 5 \/ p = 6 \/ p = 7) by lia.
  destruct E as [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]];
    (split; [vm_compute; reflexivity | split; vm_compute; reflexivity]).
Qed.

Lemma a3f_used_bytes : forall p, 0 <= p <= 8 -> length (a3f_used p) = 32%nat.
Proof.
  intros p Hp.
  assert (E : p = 0 \/ p = 1 \/ p = 2 \/ p = 3 \/ p = 4 \/ p = 5 \/ p = 6 \/ p = 7 \/ p = 8) by lia.
  destruct E as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]; vm_compute; reflexivity.
Qed.

Definition a3f_xacs (p : Z) : list YP09.chunk :=
  [YP09.mkChunk 264 (CVal 8 (SOff 563 0)); YP09.mkChunk 280 (CVal 8 (SOff 564 0));
   YP09.mkChunk 408 (CVal 8 (SOff AT_F (240 + 144 * p)))].
Definition a3f_xfcs (p r : Z) : list YP09.chunk :=
  [YP09.mkChunk (1664 + 4 * p) (CVal 4 (SLit 0)); YP09.mkChunk (2168 + 48 * p) (CVal 4 (SLit r))].
Definition a3f_xfa : list (nat * afact) :=
  [(563%nat, mkAF (2 ^ 64 - 2 ^ 47) (2 ^ 64 - 1) 0); (564%nat, mkAF (2 ^ 64 - 2 ^ 47) (2 ^ 64 - 1) 0)].
Definition a3f_narrow (lo hi : Z) (l : smem) : smem :=
  match l with
  | [r0; r1; r2; r3; r4; r5] =>
      [set_window r0 0 0; set_window r1 0 0; set_window r2 lo hi; set_window r3 0 0; set_window r4 0 0;
       set_window r5 0 0]
  | _ => l
  end.

Lemma a3f_sw_sub : forall r a b, (b <= a \/ (YP09.r_wlo r <= a /\ b <= YP09.r_whi r)) ->
  subregion (set_window r a b) r.
Proof.
  intros r a b H. unfold subregion, set_window.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [exact H | intros c Hc; exact Hc].
Qed.

Lemma a3f_narrow_sub : forall lo hi shf acs fcs, 0 <= lo -> hi <= DFRAME_SIZE ->
  submem (a3f_narrow lo hi (d_kregions shf acs fcs)) (d_kregions shf acs fcs).
Proof.
  intros lo hi shf acs fcs Hlo Hhi. unfold d_kregions, a3f_narrow.
  apply submem_keep; [apply a3f_sw_sub; left; lia|].
  apply submem_keep; [apply a3f_sw_sub; left; lia|].
  apply submem_keep; [apply a3f_sw_sub; destruct (Z.le_gt_cases hi lo); [left; lia | right];
    cbn [YP09.r_wlo YP09.r_whi]; lia|].
  apply submem_keep; [apply a3f_sw_sub; left; lia|].
  apply submem_keep; [apply a3f_sw_sub; left; lia|].
  apply submem_keep; [apply a3f_sw_sub; left; lia|].
  apply submem_nil.
Qed.

Section d. Context {rc : YM05.RunCeil} {SK : YI16.sink_head} {LS : lib_shape}.
Section f.
Context {PI : PAImg lib_both3_0_listing}.
#[local] Notation SEGS := (@pa_segs _ lib_both3_0_listing PI).
#[local] Notation VAL := (@pa_val _ lib_both3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_both3_0_listing PI A_TEXT).
#[local] Notation rd W mem := (mrestrict (w_H W) mem).

Lemma a3f_rolestr : forall (W : world SEGS) (mem : word -> option byte) (r : Z),
  0 <= r <= 2 -> dimg_strs W mem ->
  d_rostr W mem (VAL (A_OBJ (a3f_roleobj r))) (disco_json_text.rolename r).
Proof.
  intros W mem r Hr HS.
  destruct HS as (_ & _ & _ & _ & _ & _ & _ & S11 & S66 & S67 & _).
  assert (E : r = 0 \/ r = 1 \/ r = 2) by lia.
  unfold a3f_roleobj, disco_json_text.rolename, disco_json_text.s_unknown, disco_json_text.s_box,
    disco_json_text.s_master.
  destruct E as [-> | [-> | ->]]; cbn [Z.eqb].
  - exact S11.
  - exact S67.
  - exact S66.
Qed.

Lemma a3f_env_reg : forall (cx : dcx) (E : env) (regs : bvmap 5 word) (ex : list word) (r : bv 5) (a : nat),
  a = (AT_X + Z.to_nat (bv_unsigned r))%nat -> ew (d_env cx E (a3f_vals regs ++ ex)) a = getr regs r.
Proof.
  intros cx E regs ex r a ->.
  pose proof (bv_unsigned_in_range _ r) as Hr. change (bv_modulus 5) with 32 in Hr.
  rewrite d_env_x by (unfold a3f_vals; rewrite length_app, length_map, length_seq; lia).
  unfold a3f_vals. rewrite app_nth1 by (rewrite length_map, length_seq; lia).
  rewrite (nth_indep _ _ ((fun r0 : nat => getr regs (Z_to_bv 5 (Z.of_nat r0))) 0%nat))
    by (rewrite length_map, length_seq; lia).
  pose proof (map_nth (fun r0 : nat => getr regs (Z_to_bv 5 (Z.of_nat r0))) (seq 0 32) 0%nat
    (Z.to_nat (bv_unsigned r))) as Hm.
  cbv beta in Hm |- *. rewrite Hm, seq_nth by lia. cbn [Nat.add]. rewrite Z2Nat.id by lia.
  rewrite Z_to_bv_bv_unsigned. reflexivity.
Qed.

Lemma a3f_regs_ok : forall (cx : dcx) (E : env) (so : Z) (regs : bvmap 5 word) (ex : list word),
  d_E cx E -> 0 <= d_A cx < 2 ^ 64 -> spZ regs = d_A cx + so ->
  getr regs 8 = w64 (d_S cx) -> getr regs 9 = w64 (d_A cx) -> getr regs 19 = w64 SHADOW_OFF ->
  getr regs 18 = w64 WS_MASK -> getr regs 20 = w64 32 ->
  regs_ok (d_env cx E (a3f_vals regs ++ ex)) (a3f_sr so) regs.
Proof.
  intros cx E so regs ex HE HA Hsp H8 H9 H19 H18 H20.
  pose proof (d_E_env cx E (a3f_vals regs ++ ex) HE) as HE'.
  destruct HE' as (HER & H32 & _ & HA60 & _ & _). unfold AT_A in HA60.
  apply regs_ok_by_cases. intros r Hr. cbv [all_regs In] in Hr.
  repeat match goal with Hx : _ \/ _ |- _ => destruct Hx as [<-|Hx] end; [ .. | contradiction ].
  all: match goal with |- _ = sv_denot ?Ex (sr_get ?sr ?r) =>
         let v := eval vm_compute in (sr_get sr r) in change (sr_get sr r) with v end.
  all: cbn [sv_denot].
  all: first
    [ rewrite getr_zero; reflexivity
    | rewrite HA60; unfold w64; rewrite (unsigned_lit_small (d_A cx)) by lia;
      first [ rewrite <- Hsp; unfold spZ; rewrite Z_to_bv_bv_unsigned; reflexivity
            | rewrite Z.add_0_r; exact H9 ]
    | rewrite (HER 2%nat 2%bv eq_refl), Z.add_0_r; exact H8
    | rewrite H32, Z.add_0_r; unfold w64; rewrite Z_to_bv_bv_unsigned; exact H19
    | exact H18
    | exact H20
    | match goal with |- getr ?rg ?x = Z_to_bv 64 (bv_unsigned (ew ?Ex ?a) + 0) =>
        rewrite (a3f_env_reg cx E regs ex x a eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity end ].
Qed.

Lemma a3f_kept_of : forall E rs (H : word -> bool) (m m' : word -> option byte) lo hi,
  frame_of E rs m m' -> (forall a, in_wrange E rs a -> lo <= a < hi) ->
  forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> aview SEGS H m' a = aview SEGS H m a.
Proof.
  intros E rs H m m' lo hi HF HW a Ha Hn. unfold aview, mbyte, mrestrict. cbv beta.
  rewrite (HF (Z_to_bv 64 a)); [reflexivity|].
  rewrite unsigned_lit_small by lia. intros Hw. exact (Hn (HW a Hw)).
Qed.

Lemma a3f_g8_kept : forall (H H' : word -> bool) (m m' : word -> option byte) a l,
  (forall k, 0 <= k < Z.of_nat (length l) -> aview SEGS H' m' (a + k) = aview SEGS H m (a + k)) ->
  garr8 SEGS (mrestrict H m) a l -> garr8 SEGS (mrestrict H' m') a l.
Proof.
  intros H H' m m' a l HK G j Hj. destruct (G j Hj) as [V Hr]. split; [|exact Hr].
  apply (val_mem_kept SEGS H H' m m' (a + Z.of_nat j) 1 (nth j l 0)); [|exact V].
  intros kk Hkk. change (Z.of_nat 1) with 1 in Hkk.
  replace (a + Z.of_nat j + kk) with (a + (Z.of_nat j + kk)) by lia. apply HK. lia.
Qed.

Lemma a3f_g8_w1 : forall (m : word -> option byte) a, val_mem SEGS m a 4 1 -> garr8 SEGS m a [1; 0; 0; 0].
Proof.
  intros m a V j Hj. cbn [length] in Hj. split.
  - intros kk Hkk. assert (Ek : kk = 0%nat) by lia. subst kk. cbn [Z.of_nat]. rewrite Z.add_0_r.
    rewrite (V j Hj). destruct j as [|[|[|[|j]]]]; [reflexivity | reflexivity | reflexivity | reflexivity | lia].
  - destruct j as [|[|[|[|j]]]]; cbn [nth]; lia.
Qed.

Lemma a3f_same_reg : forall (fq : YK11.FPState) E ss ss' ms ms' (H H' : word -> bool) (r : bv 5),
  st_ok_pi (fx := fq) SEGS VAL E ss (restrict H ms) -> st_ok (fx := fq) SEGS E ss' (restrict H' ms') ->
  sr_get (ss_regs ss') r = sr_get (ss_regs ss) r -> getr (ms_regs ms') r = getr (ms_regs ms) r.
Proof.
  intros fq E ss ss' ms ms' H H' r HS HS' Hr.
  rewrite (st_ok_restrict_reg SEGS H' E ss' ms' r HS'), (st_ok_pi_restrict_reg H E ss ms r HS), Hr. reflexivity.
Qed.

Lemma a3f_dE_hi : forall cx E k ws, d_E cx E -> (AT_FL <= k)%nat -> d_E cx (havoc E k ws).
Proof.
  intros cx E k ws (EE & E32 & HEI & E60 & EF & ESH) Hk. unfold d_E.
  rewrite !ew_havoc_old by (unfold AT_FL, AT_A, AT_F, AT_SH in *; lia).
  split; [|split; [exact E32 | split; [|split; [exact E60 | split; [exact EF | exact ESH]]]]].
  - intros nn r Hn. rewrite ew_havoc_old; [exact (EE nn r Hn)|].
    pose proof (bv_unsigned_in_range _ r) as Hr. change (bv_modulus 5) with 32 in Hr. unfold AT_FL in Hk. lia.
  - apply img_env_havoc_hi; [exact HEI | unfold A_LIM, AT_FL in *; lia].
Qed.

Lemma a3f_kept : forall (E : env) (H H2 : word -> bool) (m m2 : word -> option byte) n b lo hi wlo whi cs,
  bv_unsigned (ew E n) = b ->
  (forall a, b + lo <= a < b + hi -> aview SEGS H2 m2 a = aview SEGS H m a) ->
  (forall a, b + wlo <= a < b + whi -> apresent H2 m2 a) ->
  region_kept SEGS E (mrestrict H m) (mrestrict H2 m2) (YP09.mkRegion (Some n) lo hi wlo whi cs).
Proof.
  intros E H H2 m m2 n b lo hi wlo whi cs Hn Hav Hp.
  split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Hn; intros a Ha.
  - apply (mbyte_of_aview SEGS). apply Hav. exact Ha.
  - intros _. apply (apresent_writable SEGS). apply Hp. exact Ha.
Qed.

Lemma a3f_regs2 : forall (cx : dcx) (E : env) (R : bvmap 5 word) (ret : Z),
  img_env VAL A_LIM E -> getr R 1 = Z_to_bv 64 (BASE + ret) ->
  regs_ok (d_env cx E (map (getr R) (tl all_regs))) (SLit 0 :: SOff A_TEXT ret :: atom_regs 532 30) R.
Proof.
  intros cx E R ret HEI H1.
  assert (HEId : img_env VAL A_LIM (d_env cx E (map (getr R) (tl all_regs))))
    by (apply img_env_havoc_hi; [exact HEI | unfold AT_FL, A_LIM; lia]).
  regs_ok_cases_pre ltac:(first [ rewrite getr_zero; reflexivity
                                | rewrite H1; symmetry; exact (codeptr_val _ ret HEId) ]).
Qed.

Lemma a3f_roP_img : forall a, in_roP SEGS pa_relro_lo pa_relro_hi a -> YImgTop.IMG_LO <= a < YImgTop.IMG_TOP.
Proof.
  intros a [(s & Hs & _ & Ha) | Ha].
  - apply pa_img_range. exists s. split; [exact Hs | exact Ha].
  - apply pa_img_range. apply pa_relro_img. exact Ha.
Qed.

End f.
End d.
