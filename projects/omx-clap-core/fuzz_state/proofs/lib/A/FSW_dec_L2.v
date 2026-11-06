(* preset_base64_decode (fs.asan 0x8481c), part L helper a Theorem Labs lane: the arithmetic of the loop.
   The token engine's symbolic branches as values over the env, the accumulator / stored byte of one sextet, and the scan
   model (decLA_out) step by step. Contract: (internal path) (statements verbatim). Pure Z / list lemmas, no
   Section. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YI16 YK06 YM05 YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import
AB1v AB1w FSupoison FSupoisonU FSH_YC20 FSH_Gen FSH_Base FSH_Rt FSPstat FSH_Fn_alloc FSH_Fn_writer
FSW_K FSW_ret FSW_rres FSW_writer_tbl FSW_writer_model.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require WriterSpec.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import FSW_dec_defs.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require WriterSpec WriterSpecFacts.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* the scan's verdict from a loop head (the match of dec_head's model clause, FSW_dec_defs.v dec_head) *)
Definition decLA_out (pad : Z) (six rest : list Z) : option (list Z) :=
  match WriterSpec.b64_scan pad six rest with
  | Some (six', pad') => if (pad' <=? 2) && WriterSpec.six_tail_ok six' then Some (WriterSpec.six_bytes six') else None
  | None => None
  end.

(* ---- helpers ---- *)

(* a boolean check over a range of naturals, read back at an integer of the range *)
Lemma decLA_fin : forall (P : Z -> bool) (lo n : nat), forallb (fun k => P (Z.of_nat k)) (seq lo n) = true ->
  forall c, Z.of_nat lo <= c < Z.of_nat lo + Z.of_nat n -> P c = true.
Proof.
  intros P lo n H c Hc. rewrite forallb_forall in H. specialize (H (Z.to_nat c)).
  rewrite Z2Nat.id in H by lia. apply H. apply in_seq. lia.
Qed.

Lemma decLA_swrap64_small : forall x, 0 <= x < 2 ^ 63 -> bv_swrap 64 x = x.
Proof.
  intros x Hx. apply bv_swrap_small. change (bv_half_modulus 64) with (2 ^ 63). lia.
Qed.

(* the low byte of a sign-extended 32-bit value is the low byte of the value *)
Lemma decLA_sw32_mod256 : forall y, bv_wrap 64 (bv_swrap 32 y) mod 256 = y mod 256.
Proof.
  intros y. unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2 ^ 31).
  change (bv_modulus 32) with (2 ^ 32). change (bv_modulus 64) with (2 ^ 64).
  Z.div_mod_to_equations; lia.
Qed.

(* the low byte of x >> s depends only on the low s + 8 bits of x *)
Lemma decLA_shr_low : forall x s m, 0 <= s -> s + 8 <= m ->
  Z.shiftr (x mod 2 ^ m) s mod 2 ^ 8 = Z.shiftr x s mod 2 ^ 8.
Proof.
  intros x s m Hs Hm. apply Z.bits_inj'. intros i Hi.
  destruct (Z.lt_ge_cases i 8) as [Hl | Hg].
  - rewrite !Z.mod_pow2_bits_low by lia. rewrite !Z.shiftr_spec by lia.
    rewrite Z.mod_pow2_bits_low by lia. reflexivity.
  - rewrite !Z.mod_pow2_bits_high by lia. reflexivity.
Qed.

Lemma decLA_lor_add64 : forall x y, 0 <= x < 64 -> 0 <= y -> y mod 64 = 0 -> Z.lor x y = x + y.
Proof.
  intros x y Hx Hy Hm.
  assert (L : Z.land x y = 0).
  { apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
    destruct (Z.lt_ge_cases i 6).
    - replace (Z.testbit y i) with false; [apply andb_false_r|].
      symmetry. rewrite <- (Z.mod_pow2_bits_low y 6 i) by lia. change (2 ^ 6) with 64. rewrite Hm. apply Z.bits_0.
    - replace (Z.testbit x i) with false; [reflexivity|].
      symmetry. rewrite <- (Z.mod_small x 64) by lia. change 64 with (2 ^ 6). apply Z.mod_pow2_bits_high. lia. }
  rewrite <- Z.lxor_lor by exact L. symmetry. apply Z.add_nocarry_lxor. exact L.
Qed.

Lemma decLA_last_range : forall six, Forall (fun x => 0 <= x < 64) six -> 0 <= last six 0 < 64.
Proof.
  induction six as [|a t IH]; intros H; [cbn; lia|].
  inversion H as [|? ? Ha Ht]; subst.
  destruct t as [|b t'].
  - cbn. exact Ha.
  - change (last (a :: b :: t') 0) with (last (b :: t') 0). apply IH. exact Ht.
Qed.

(* the byte one more sextet adds to six_bytes, by the sextet count k = length six *)
Definition decLA_snoc_byte (k l v : Z) : list Z :=
  if k mod 4 =? 1 then [l * 4 + v / 16]
  else if k mod 4 =? 2 then [(l mod 16) * 16 + v / 4]
  else if k mod 4 =? 3 then [(l mod 4) * 64 + v]
  else [].

Lemma decLA_six_bytes_snoc : forall six v,
  WriterSpec.six_bytes (six ++ [v]) =
  WriterSpec.six_bytes six ++ decLA_snoc_byte (Z.of_nat (length six)) (last six 0) v.
Proof.
  intros six v. induction six as [|a|a b|a b c|a b c d l IH] using WriterSpecFacts.list4_ind.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - assert (E : decLA_snoc_byte (Z.of_nat (length (a :: b :: c :: d :: l))) (last (a :: b :: c :: d :: l) 0) v
                = decLA_snoc_byte (Z.of_nat (length l)) (last l 0) v).
    { unfold decLA_snoc_byte.
      replace (Z.of_nat (length (a :: b :: c :: d :: l))) with (Z.of_nat (length l) + 1 * 4) by (cbn [length]; lia).
      rewrite Z.mod_add by lia. destruct l as [|e l]; reflexivity. }
    rewrite E. cbn [app WriterSpec.six_bytes]. rewrite IH. reflexivity.
Qed.

Lemma decLA_snoc_code : forall k l v, 0 <= k -> 0 <= l < 64 -> 0 <= v < 64 -> 2 <= 6 * k mod 8 ->
  decLA_snoc_byte k l v = [Z.shiftr (l * 64 + v) (6 * k mod 8 - 2) mod 256].
Proof.
  intros k l v Hk Hl Hv Hb. unfold decLA_snoc_byte.
  assert (H4 : k mod 4 = 1 \/ k mod 4 = 2 \/ k mod 4 = 3) by (Z.div_mod_to_equations; lia).
  destruct H4 as [H|[H|H]]; rewrite H.
  - replace (6 * k mod 8) with 6 by (Z.div_mod_to_equations; lia). cbn [Z.eqb Pos.eqb].
    change (6 - 2) with 4. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 4) with 16. f_equal.
    Z.div_mod_to_equations; lia.
  - replace (6 * k mod 8) with 4 by (Z.div_mod_to_equations; lia). cbn [Z.eqb Pos.eqb].
    change (4 - 2) with 2. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 2) with 4. f_equal.
    Z.div_mod_to_equations; lia.
  - replace (6 * k mod 8) with 2 by (Z.div_mod_to_equations; lia). cbn [Z.eqb Pos.eqb].
    change (2 - 2) with 0. rewrite Z.shiftr_0_r. f_equal.
    Z.div_mod_to_equations; lia.
Qed.

(* ---- the branches the token engine leaves symbolic (MEASURED), as values over the env ---- *)
Lemma decLA_br_ltu : forall E (na nb : nat) x y, ew E na = Z_to_bv 64 x -> ew E nb = Z_to_bv 64 y ->
  0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 ->
  branch_taken BC_LTU (sv_denot E (SOff na 0)) (sv_denot E (SOff nb 0)) = (x <? y).
Proof.
  intros E na nb x y Ha Hb Hx Hy. rewrite YI04.branch_ltu_U.
  rewrite (YI04.U_atom E na x Ha Hx), (YI04.U_atom E nb y Hb Hy). reflexivity.
Qed.

Lemma decLA_br_ne : forall E (na nb : nat) x y, ew E na = Z_to_bv 64 x -> ew E nb = Z_to_bv 64 y ->
  0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 ->
  branch_taken BC_NE (sv_denot E (SOff na 0)) (sv_denot E (SOff nb 0)) = negb (x =? y).
Proof.
  intros E na nb x y Ha Hb Hx Hy. rewrite YI04.branch_ne_U.
  rewrite (YI04.U_atom E na x Ha Hx), (YI04.U_atom E nb y Hb Hy). reflexivity.
Qed.

Lemma decLA_br_eq0 : forall E (na : nat) x, ew E na = Z_to_bv 64 x -> 0 <= x < 2 ^ 64 ->
  branch_taken BC_EQ (sv_denot E (SOff na 0)) (sv_denot E (SLit 0)) = (x =? 0).
Proof.
  intros E na x Ha Hx. rewrite YI04.branch_eq_U.
  rewrite (YI04.U_atom E na x Ha Hx), (YI04.U_lit E 0) by lia. reflexivity.
Qed.

Lemma decLA_br_ne0 : forall E (na : nat) x, ew E na = Z_to_bv 64 x -> 0 <= x < 2 ^ 64 ->
  branch_taken BC_NE (sv_denot E (SOff na 0)) (sv_denot E (SLit 0)) = negb (x =? 0).
Proof.
  intros E na x Ha Hx. rewrite YI04.branch_ne_U.
  rewrite (YI04.U_atom E na x Ha Hx), (YI04.U_lit E 0) by lia. reflexivity.
Qed.

(* the signed reading of a small literal and of a small atom *)
Lemma decLA_signed_lit : forall E z, 0 <= z < 2 ^ 63 -> bv_signed (sv_denot E (SLit z)) = z.
Proof.
  intros E z Hz. cbn [sv_denot]. rewrite YP0m.signed_lit. rewrite (YP0m.zcanon_small z) by lia.
  apply decLA_swrap64_small. exact Hz.
Qed.

Lemma decLA_signed_atom : forall E (na : nat) x, ew E na = Z_to_bv 64 x -> 0 <= x < 2 ^ 63 ->
  bv_signed (sv_denot E (SOff na 0)) = x.
Proof.
  intros E na x Ha Hx. cbn [sv_denot]. rewrite Ha, YP0m.unsigned_lit, Z.add_0_r, YP0m.signed_lit.
  rewrite (YP0m.zcanon_small x) by lia. rewrite (YP0m.zcanon_small x) by lia.
  apply decLA_swrap64_small. exact Hx.
Qed.

(* signed compares of a small literal with a small value *)
Lemma decLA_br_ge_lit : forall E (na : nat) x z, ew E na = Z_to_bv 64 x -> 0 <= x < 2 ^ 63 -> 0 <= z < 2 ^ 63 ->
  branch_taken BC_GE (sv_denot E (SLit z)) (sv_denot E (SOff na 0)) = (x <=? z).
Proof.
  intros E na x z Ha Hx Hz. cbn [branch_taken]. unfold bv_lts.
  rewrite (decLA_signed_lit E z Hz), (decLA_signed_atom E na x Ha Hx).
  rewrite Z.leb_antisym. reflexivity.
Qed.

Lemma decLA_br_lt_lit : forall E (na : nat) x z, ew E na = Z_to_bv 64 x -> 0 <= x < 2 ^ 63 -> 0 <= z < 2 ^ 63 ->
  branch_taken BC_LT (sv_denot E (SLit z)) (sv_denot E (SOff na 0)) = (z <? x).
Proof.
  intros E na x z Ha Hx Hz. cbn [branch_taken]. unfold bv_lts.
  rewrite (decLA_signed_lit E z Hz), (decLA_signed_atom E na x Ha Hx). reflexivity.
Qed.

(* `(mask >> c) & 1 != 0` with mask = 0x100002600 (bits 9, 10, 13, 32) is the whitespace test for c <= 61 *)
Lemma decLA_br_ws : forall E (nm nc : nat) c, ew E nm = Z_to_bv 64 DEC_WSMASK -> ew E nc = Z_to_bv 64 c -> 0 <= c <= 61 ->
  branch_taken BC_NE (sv_denot E (SAlu ALU_AND (SAlu ALU_SRL (SOff nm 0) (SOff nc 0)) (SLit 1))) (sv_denot E (SLit 0))
  = WriterSpec.b64_ws c.
Proof.
  intros E nm nc c Hm Hc Hr. rewrite YI04.branch_ne_U.
  rewrite (YI04.U_and_lit E _ 1) by lia. rewrite (YI04.U_lit E 0) by lia.
  rewrite YP0e.U_SAlu. cbn [zalu_raw].
  rewrite (YI04.U_atom E nm DEC_WSMASK Hm) by (unfold DEC_WSMASK; lia).
  rewrite (YI04.U_atom E nc c Hc) by lia.
  apply Bool.eqb_prop.
  apply (decLA_fin (fun n => Bool.eqb (negb (Z.land (zcanon (Z.shiftr DEC_WSMASK (Z.land n 63))) 1 =? 0))
                               (WriterSpec.b64_ws n)) 0 62); [vm_compute; reflexivity | lia].
Qed.

(* the NUL exit's `acc & ~(-1 <<w bits) != 0`, bits <= 5 *)
Lemma decLA_br_exit_and : forall E (na nb : nat) acc b, ew E na = Z_to_bv 64 acc -> 0 <= acc < 2 ^ 64 ->
  ew E nb = Z_to_bv 64 b -> 0 <= b <= 5 ->
  branch_taken BC_NE
    (sv_denot E (SAlu ALU_AND (SOff na 0)
       (SAlu ALU_XOR (SAluw ALU_SLL (SLit 18446744073709551615) (SOff nb 0)) (SLit (-1)))))
    (sv_denot E (SLit 0))
  = negb (acc mod 2 ^ b =? 0).
Proof.
  intros E na nb acc b Ha Hacc Hb Hbr. rewrite YI04.branch_ne_U. rewrite (YI04.U_lit E 0) by lia.
  assert (M : U E (SAlu ALU_XOR (SAluw ALU_SLL (SLit 18446744073709551615) (SOff nb 0)) (SLit (-1))) = 2 ^ b - 1).
  { rewrite YP0e.U_SAlu. cbn [zalu_raw]. rewrite YP0e.U_SLit.
    rewrite (YP0e.U_of_S E (SAluw _ _ _)), YP0e.S_SAluw. cbn [zalu_raw]. rewrite YP0e.U_SLit.
    rewrite (YI04.U_atom E nb b Hb) by lia.
    assert (B : b = 0 \/ b = 1 \/ b = 2 \/ b = 3 \/ b = 4 \/ b = 5) by lia.
    destruct B as [-> | [-> | [-> | [-> | [-> | ->]]]]]; vm_compute; reflexivity. }
  rewrite YP0e.U_SAlu. cbn [zalu_raw]. rewrite M, (YI04.U_atom E na acc Ha Hacc).
  assert (O : 2 ^ b - 1 = Z.ones b) by (rewrite Z.ones_equiv; lia).
  rewrite O, Z.land_ones by lia.
  assert (P : 0 < 2 ^ b) by (apply Z.pow_pos_nonneg; lia).
  assert (P5 : 2 ^ b <= 2 ^ 5) by (apply Z.pow_le_mono_r; lia). change (2 ^ 5) with 32 in P5.
  pose proof (Z.mod_pos_bound acc (2 ^ b) P).
  rewrite (YP0m.zcanon_small (acc mod 2 ^ b)) by lia. reflexivity.
Qed.

(* ---- the accumulator after memchr returned r = G_B64 + v (atom 10 = r, 19 = s3 = G_B64, 23 = s7 = acc) and the byte
   the store writes (atom 24 = s8 = bits) ---- *)
Definition decLA_acc_e : sv :=
  SAlu ALU_OR (SAlu ALU_ADD (SOff 10 0) (SMd M_MUL (SOff 19 0) (SLit (-1)))) (SAluw ALU_SLL (SOff 23 0) (SLit 6)).

Lemma decLA_acc : forall E acc v, ew E 10 = Z_to_bv 64 (G_B64 + v) -> 0 <= v < 64 -> ew E 19 = Z_to_bv 64 G_B64 ->
  ew E 23 = Z_to_bv 64 acc -> 0 <= acc < 2 ^ 64 ->
  U E decLA_acc_e mod 4096 = (acc mod 64) * 64 + v.
Proof.
  intros E acc v H10 Hv H19 H23 Hacc. unfold decLA_acc_e.
  assert (UA : U E (SAlu ALU_ADD (SOff 10 0) (SMd M_MUL (SOff 19 0) (SLit (-1)))) = v).
  { rewrite YP0e.U_SAlu. cbn [zalu_raw]. rewrite YP0e.U_SMd. cbn [zmd_raw].
    rewrite (YI04.U_atom E 10 (G_B64 + v) H10) by (unfold G_B64; lia).
    rewrite (YI04.U_atom E 19 G_B64 H19) by (unfold G_B64; lia). rewrite YP0e.U_SLit.
    replace (zcanon (G_B64 * zcanon (-1))) with (2 ^ 64 - G_B64) by (vm_compute; reflexivity).
    replace (G_B64 + v + (2 ^ 64 - G_B64)) with (v + 1 * 2 ^ 64) by ring.
    unfold zcanon, M64. rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
  assert (HS : 0 <= U E (SAluw ALU_SLL (SOff 23 0) (SLit 6)) < 2 ^ 64 /\
    U E (SAluw ALU_SLL (SOff 23 0) (SLit 6)) mod 64 = 0 /\
    U E (SAluw ALU_SLL (SOff 23 0) (SLit 6)) mod 4096 = (acc mod 64) * 64).
  { rewrite (YP0e.U_of_S E (SAluw _ _ _)), YP0e.S_SAluw. cbn [zalu_raw].
    rewrite (YI04.U_atom E 23 acc H23 Hacc), YP0e.U_SLit.
    change (Z.land (zcanon 6 mod 2 ^ 32) 31) with 6. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 6) with 64.
    unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2 ^ 31).
    change (bv_modulus 32) with (2 ^ 32). change (bv_modulus 64) with (2 ^ 64).
    split; [|split]; Z.div_mod_to_equations; lia. }
  destruct HS as (HS1 & HS2 & HS3).
  rewrite YP0e.U_SAlu. cbn [zalu_raw]. rewrite UA.
  remember (U E (SAluw ALU_SLL (SOff 23 0) (SLit 6))) as US eqn:HUS.
  rewrite decLA_lor_add64 by lia.
  assert (HS4 : US <= 2 ^ 64 - 64) by (Z.div_mod_to_equations; lia).
  rewrite (YP0m.zcanon_small (v + US)) by lia.
  Z.div_mod_to_equations; lia.
Qed.

Lemma decLA_byte : forall E e b, ew E 24 = Z_to_bv 64 b -> 2 <= b <= 6 ->
  U E (SAluw ALU_SRL e (SOff 24 (-2))) mod 256 = Z.shiftr (U E e mod 4096) (b - 2) mod 256.
Proof.
  intros E e b H24 Hb. rewrite (YP0e.U_of_S E (SAluw _ _ _)), YP0e.S_SAluw. cbn [zalu_raw].
  rewrite (YI04.U_atom_off E 24 b (-2) H24) by lia.
  rewrite (Z.mod_small (b + -2) (2 ^ 32)) by lia.
  replace (Z.land (b + -2) 31) with (b - 2).
  2:{ change 31 with (Z.ones 5). rewrite Z.land_ones by lia. rewrite Z.mod_small by lia. lia. }
  rewrite decLA_sw32_mod256. change 256 with (2 ^ 8).
  rewrite (decLA_shr_low (U E e) (b - 2) 32) by lia.
  change 4096 with (2 ^ 12). rewrite (decLA_shr_low (U E e) (b - 2) 12) by lia. reflexivity.
Qed.

(* ---- the scan model ---- *)
Lemma decLA_skipn : forall (tb : list Z) (i : nat), (i < length tb)%nat -> skipn i tb = nth i tb 0 :: skipn (S i) tb.
Proof.
  induction tb as [|x tb IH]; intros i Hi; cbn [length] in Hi; [lia|].
  destruct i as [|i]; [reflexivity|].
  cbn [skipn nth]. apply IH. lia.
Qed.

Lemma decLA_skipn_end : forall (tb : list Z), skipn (length tb) tb = [].
Proof. induction tb as [|x tb IH]; [reflexivity|]. cbn [length skipn]. exact IH. Qed.

Lemma decLA_out_nil : forall pad six,
  decLA_out pad six [] = if (pad <=? 2) && WriterSpec.six_tail_ok six then Some (WriterSpec.six_bytes six) else None.
Proof. intros pad six. reflexivity. Qed.

Lemma decLA_out_ws : forall c pad six rest, WriterSpec.b64_ws c = true -> decLA_out pad six (c :: rest) = decLA_out pad six rest.
Proof. intros c pad six rest H. unfold decLA_out. cbn [WriterSpec.b64_scan]. rewrite H. reflexivity. Qed.

Lemma decLA_out_61 : forall pad six rest, decLA_out pad six (61 :: rest) = decLA_out (pad + 1) six rest.
Proof. intros pad six rest. reflexivity. Qed.

Lemma decLA_out_bad : forall c pad six rest, WriterSpec.b64_ws c = false -> c <> 61 -> WriterSpec.b64v c = None ->
  decLA_out pad six (c :: rest) = None.
Proof.
  intros c pad six rest H1 H2 H3. unfold decLA_out. cbn [WriterSpec.b64_scan].
  rewrite H1, (proj2 (Z.eqb_neq c 61) H2), H3. reflexivity.
Qed.

Lemma decLA_out_padbad : forall c v pad six rest, WriterSpec.b64_ws c = false -> c <> 61 -> WriterSpec.b64v c = Some v ->
  pad <> 0 -> decLA_out pad six (c :: rest) = None.
Proof.
  intros c v pad six rest H1 H2 H3 H4. unfold decLA_out. cbn [WriterSpec.b64_scan].
  rewrite H1, (proj2 (Z.eqb_neq c 61) H2), H3, (proj2 (Z.eqb_neq pad 0) H4). reflexivity.
Qed.

Lemma decLA_out_val : forall c v six rest, WriterSpec.b64_ws c = false -> c <> 61 -> WriterSpec.b64v c = Some v ->
  decLA_out 0 six (c :: rest) = decLA_out 0 (six ++ [v]) rest.
Proof.
  intros c v six rest H1 H2 H3. unfold decLA_out. cbn [WriterSpec.b64_scan].
  rewrite H1, (proj2 (Z.eqb_neq c 61) H2), H3. reflexivity.
Qed.

Lemma decLA_ws_vals : forall c, WriterSpec.b64_ws c = true -> c = 9 \/ c = 10 \/ c = 13 \/ c = 32.
Proof.
  intros c H. unfold WriterSpec.b64_ws in H.
  destruct (Z.eqb_spec c 32), (Z.eqb_spec c 9), (Z.eqb_spec c 10), (Z.eqb_spec c 13); cbn in H;
    try discriminate; lia.
Qed.

Lemma decLA_ws_big : forall c, 61 < c -> WriterSpec.b64_ws c = false.
Proof.
  intros c H. unfold WriterSpec.b64_ws.
  destruct (Z.eqb_spec c 32), (Z.eqb_spec c 9), (Z.eqb_spec c 10), (Z.eqb_spec c 13); try lia; reflexivity.
Qed.

Lemma decLA_b64v_range : forall c v, WriterSpec.b64v c = Some v -> 0 <= v < 64.
Proof. exact WriterSpecFacts.b64v_range. Qed.

(* memchr (g_b64, c, 65) over the table's 64 letters and its NUL *)
Definition decLA_zchk (c : Z) : bool :=
  match zfind c WriterSpec.b64_table with
  | None => match WriterSpec.b64v c with None => true | Some _ => false end
  | Some j => match WriterSpec.b64v c with Some v => v =? Z.of_nat j | None => false end
  end.

Lemma decLA_zfind : forall c, 1 <= c <= 255 ->
  match zfind c WriterSpec.b64_table with
  | None => WriterSpec.b64v c = None
  | Some j => WriterSpec.b64v c = Some (Z.of_nat j)
  end.
Proof.
  intros c Hc.
  assert (A : decLA_zchk c = true) by (apply (decLA_fin decLA_zchk 1 255); [vm_compute; reflexivity | lia]).
  unfold decLA_zchk in A.
  destruct (zfind c WriterSpec.b64_table) as [j|]; destruct (WriterSpec.b64v c) as [v|]; try discriminate.
  - apply Z.eqb_eq in A. subst v. reflexivity.
  - reflexivity.
Qed.

(* the tail checks: acc mod 64 is the last sextet *)
Lemma decLA_tail : forall six W, W mod 64 = last six 0 ->
  WriterSpec.six_tail_ok six =
  (6 * Z.of_nat (length six) mod 8 <=? 5) && (W mod 2 ^ (6 * Z.of_nat (length six) mod 8) =? 0).
Proof.
  intros six W HW. unfold WriterSpec.six_tail_ok. cbv zeta. rewrite <- HW.
  replace ((W mod 64) mod 16) with (W mod 16) by (Z.div_mod_to_equations; lia).
  replace ((W mod 64) mod 4) with (W mod 4) by (Z.div_mod_to_equations; lia).
  remember (Z.of_nat (length six)) as k eqn:Hk.
  assert (H4 : k mod 4 = 0 \/ k mod 4 = 1 \/ k mod 4 = 2 \/ k mod 4 = 3) by (Z.div_mod_to_equations; lia).
  destruct H4 as [H|[H|[H|H]]]; rewrite H.
  - replace (6 * k mod 8) with 0 by (Z.div_mod_to_equations; lia). change (2 ^ 0) with 1. rewrite Z.mod_1_r.
    destruct (W mod 16 =? 0), (W mod 4 =? 0); reflexivity.
  - replace (6 * k mod 8) with 6 by (Z.div_mod_to_equations; lia).
    destruct (W mod 16 =? 0), (W mod 4 =? 0); reflexivity.
  - replace (6 * k mod 8) with 4 by (Z.div_mod_to_equations; lia). change (2 ^ 4) with 16.
    destruct (W mod 16 =? 0), (W mod 4 =? 0); reflexivity.
  - replace (6 * k mod 8) with 2 by (Z.div_mod_to_equations; lia). change (2 ^ 2) with 4.
    destruct (W mod 16 =? 0), (W mod 4 =? 0); reflexivity.
Qed.

(* one more sextet: no byte when bits = 0, else the byte the store writes *)
Lemma decLA_snoc0 : forall six v, 6 * Z.of_nat (length six) mod 8 = 0 ->
  WriterSpec.six_bytes (six ++ [v]) = WriterSpec.six_bytes six.
Proof.
  intros six v H. rewrite decLA_six_bytes_snoc. unfold decLA_snoc_byte.
  replace (Z.of_nat (length six) mod 4) with 0 by (Z.div_mod_to_equations; lia).
  cbn [Z.eqb]. apply app_nil_r.
Qed.

Lemma decLA_snoc : forall six v, Forall (fun x => 0 <= x < 64) six -> 0 <= v < 64 -> 2 <= 6 * Z.of_nat (length six) mod 8 ->
  WriterSpec.six_bytes (six ++ [v]) =
  WriterSpec.six_bytes six ++ [Z.shiftr (last six 0 * 64 + v) (6 * Z.of_nat (length six) mod 8 - 2) mod 256].
Proof.
  intros six v Hs Hv Hb. rewrite decLA_six_bytes_snoc.
  rewrite decLA_snoc_code; [reflexivity | lia | exact (decLA_last_range six Hs) | exact Hv | exact Hb].
Qed.

Lemma decLA_bits : forall k, 0 <= k ->
  6 * (k + 1) mod 8 = (if 6 * k mod 8 =? 0 then 6 else 6 * k mod 8 - 2).
Proof.
  intros k Hk.
  assert (H4 : k mod 4 = 0 \/ k mod 4 = 1 \/ k mod 4 = 2 \/ k mod 4 = 3) by (Z.div_mod_to_equations; lia).
  destruct H4 as [H|[H|[H|H]]].
  - replace (6 * k mod 8) with 0 by (Z.div_mod_to_equations; lia). cbn [Z.eqb].
    Z.div_mod_to_equations; lia.
  - replace (6 * k mod 8) with 6 by (Z.div_mod_to_equations; lia). cbn [Z.eqb Pos.eqb].
    Z.div_mod_to_equations; lia.
  - replace (6 * k mod 8) with 4 by (Z.div_mod_to_equations; lia). cbn [Z.eqb Pos.eqb].
    Z.div_mod_to_equations; lia.
  - replace (6 * k mod 8) with 2 by (Z.div_mod_to_equations; lia). cbn [Z.eqb Pos.eqb].
    Z.div_mod_to_equations; lia.
Qed.

Lemma decLA_bits_cases : forall k, 0 <= k ->
  6 * k mod 8 = 0 \/ 6 * k mod 8 = 2 \/ 6 * k mod 8 = 4 \/ 6 * k mod 8 = 6.
Proof.
  intros k Hk.
  assert (H4 : k mod 4 = 0 \/ k mod 4 = 1 \/ k mod 4 = 2 \/ k mod 4 = 3) by (Z.div_mod_to_equations; lia).
  destruct H4 as [H|[H|[H|H]]]; Z.div_mod_to_equations; lia.
Qed.

(* the output fits the block dec_size tb = len / 4 * 3 + 3 (FSH_Fn_writer.dec_size) with room for one more byte *)
Lemma decLA_nbytes : forall six (tb : list Z), (length six <= length tb)%nat ->
  Z.of_nat (length (WriterSpec.six_bytes six)) < dec_size tb.
Proof.
  intros six tb H. rewrite WriterSpecFacts.six_bytes_length. unfold dec_size.
  assert (L : Z.of_nat (length six) <= Z.of_nat (length tb)) by lia.
  assert (L0 : 0 <= Z.of_nat (length six)) by lia.
  Z.div_mod_to_equations; lia.
Qed.
