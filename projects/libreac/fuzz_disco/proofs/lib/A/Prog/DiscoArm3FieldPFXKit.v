From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI04 YI09 YI08 YI00 YN3v YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YCbp YE00 YE01 YO09.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
PaTable PaSym PaShadow PaRun PaStep PaJournal DiscoSyms DiscoList DiscoAddr DiscoPa DiscoPaLib DiscoBase DiscoFrame.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import DiscoEntryInv DiscoEntryShapes DiscoArm3.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import DiscoEntSeatStmt DiscoEntSeat DiscoArm3FieldCut.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require
disco_table_c disco_table disco_json_text reac_disco_table_json_c.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import slot_inv.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).


Definition a3f_roleobj (r : Z) : nat := if r =? 2 then 12%nat else if r =? 1 then 13%nat else 11%nat.

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
Definition a3f_srx (so : Z) (r : nat) : sv :=
  match r with
  | 0%nat => SLit 0
  | 2%nat => SOff AT_A so
  | 8%nat => SOff AT_STK 0
  | 9%nat => SOff AT_A 0
  | 18%nat => SOff 32 0
  | 20%nat => SLit WS_MASK
  | 25%nat => SLit 32
  | _ => SOff (AT_X + r) 0
  end.
Definition a3f_sr (so : Z) : list sv := map (a3f_srx so) (seq 0 32).
Definition a3f_vals (regs : bvmap 5 word) : list word :=
  map (fun r => getr regs (Z_to_bv 5 (Z.of_nat r))) (seq 0 32).


Section d. Context {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg disco_listing}.
#[local] Notation SEGS := (@pa_segs _ disco_listing PI).
#[local] Notation VAL := (@pa_val _ disco_listing PI).
#[local] Notation rd W mem := (mrestrict (w_H W) mem).

Lemma a3f_rolestr : forall (W : world SEGS) (mem : word -> option byte) (r : Z),
  0 <= r <= 2 -> dimg_strs W mem ->
  d_rostr W mem (VAL (A_OBJ (a3f_roleobj r))) (disco_json_text.rolename r).
Proof.
  intros W mem r Hr HS.
  destruct HS as (_ & _ & _ & _ & _ & _ & _ & S11 & S12 & S13 & _).
  assert (E : r = 0 \/ r = 1 \/ r = 2) by lia.
  unfold a3f_roleobj, disco_json_text.rolename, disco_json_text.s_unknown, disco_json_text.s_box,
    disco_json_text.s_master.
  destruct E as [-> | [-> | ->]]; cbn [Z.eqb].
  - exact S11.
  - exact S13.
  - exact S12.
Qed.

Lemma a3f_env_reg : forall (cx : dcx) (E : env) (regs : bvmap 5 word) (r : bv 5) (a : nat),
  a = (AT_X + Z.to_nat (bv_unsigned r))%nat -> ew (d_env cx E (a3f_vals regs)) a = getr regs r.
Proof.
  intros cx E regs r a ->.
  pose proof (bv_unsigned_in_range _ r) as Hr. change (bv_modulus 5) with 32 in Hr.
  rewrite d_env_x by (unfold a3f_vals; rewrite length_map, length_seq; lia).
  unfold a3f_vals.
  set (f := fun r0 : nat => getr regs (Z_to_bv 5 (Z.of_nat r0))).
  rewrite (nth_indep _ (Z_to_bv 64 0) (f 0%nat)) by (rewrite length_map, length_seq; lia).
  rewrite map_nth, seq_nth by lia. unfold f. cbn [Nat.add]. rewrite Z2Nat.id by lia.
  rewrite Z_to_bv_bv_unsigned. reflexivity.
Qed.

Lemma a3f_regs_ok : forall (cx : dcx) (E : env) (so : Z) (regs : bvmap 5 word),
  d_E cx E -> 0 <= d_A cx < 2 ^ 64 -> spZ regs = d_A cx + so ->
  getr regs 8 = w64 (d_S cx) -> getr regs 9 = w64 (d_A cx) -> getr regs 18 = w64 SHADOW_OFF ->
  getr regs 20 = w64 WS_MASK -> getr regs 25 = w64 32 ->
  regs_ok (d_env cx E (a3f_vals regs)) (a3f_sr so) regs.
Proof.
  intros cx E so regs HE HA Hsp H8 H9 H18 H20 H25.
  pose proof (d_E_env cx E (a3f_vals regs) HE) as (HER & H32 & _ & HA60 & _ & _).
  unfold AT_A in HA60.
  assert (UA : bv_unsigned (ew (d_env cx E (a3f_vals regs)) 60) = d_A cx).
  { rewrite HA60. unfold w64. apply unsigned_lit_small. exact HA. }
  apply regs_ok_by_cases. intros r Hr. cbv [all_regs In] in Hr.
  repeat match goal with Hx : _ \/ _ |- _ => destruct Hx as [<- | Hx] end; [ .. | contradiction ].
  all: match goal with |- _ = sv_denot ?Ex (sr_get ?sr ?r) =>
         let v := eval vm_compute in (sr_get sr r) in change (sr_get sr r) with v end.
  all: cbn [sv_denot].
  all: first
    [ rewrite getr_zero; reflexivity
    | rewrite UA; first [ rewrite <- Hsp; unfold spZ; symmetry; apply Z_to_bv_bv_unsigned
                        | rewrite Z.add_0_r; exact H9 ]
    | rewrite (HER 2%nat 2%bv eq_refl), Z.add_0_r; exact H8
    | rewrite H32, Z.add_0_r; unfold w64; rewrite Z_to_bv_bv_unsigned; exact H18
    | exact H20
    | exact H25
    | match goal with |- getr ?rg ?x = Z_to_bv 64 (bv_unsigned (ew ?Ex ?a) + 0) =>
        rewrite (a3f_env_reg cx E regs x a eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity end ].
Qed.

End f.
End d.
