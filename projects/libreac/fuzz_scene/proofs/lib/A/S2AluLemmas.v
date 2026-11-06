(* Two evaluation lemmas of segment S2 of the ASan walk of fuzz_scene's entry (the 0x82d28 decision), proved for
   the S2 lane. Rule 24 is met: no function is proved here; both statements are pure arithmetic over the executor's
   terms (Z, the 64-bit words of BvBase and the symbolic values of lib/Reusable/YP0m.v), with no image, no listing
   and no sink.

   s2a_snez_xor   the `xor a,x,k; snez a,a` pair: the unsigned compare of 0 against the xor is the negation of the
                  equality test of the two 64-bit operands.
   s2a_slt_sext16 the `slli a,a,48; srai a,a,48; slti a,a,c` triple: the shift pair is the 16-bit sign extension of
                  the atom, so the signed compare against a small literal is the compare of the modelled signed
                  16-bit value v with c. *)
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YK11 YP0m YP0e YP03.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.

(* `xor` then `sltu zero, .`: 1 exactly when the two words differ. *)
Lemma s2a_snez_xor : forall x k : Z, 0 <= x < 2 ^ 64 -> 0 <= k < 2 ^ 64 ->
  bv_unsigned (alu64 ALU_SLTU (Z_to_bv 64 0) (alu64 ALU_XOR (Z_to_bv 64 x) (Z_to_bv 64 k)))
  = (if x =? k then 0 else 1).
Proof.
intros x k Hx Hk.
pose proof (Z_lxor_range x k Hx Hk) as HX.
assert (EX : alu64 ALU_XOR (Z_to_bv 64 x) (Z_to_bv 64 k) = Z_to_bv 64 (Z.lxor x k)).
{ rewrite zalu64_sound. f_equal. unfold zalu64, zcanon, M64. cbn [zalu_raw].
  rewrite (Z.mod_small x), (Z.mod_small k) by lia. apply Z.mod_small. lia. }
rewrite EX, zalu64_sound.
assert (EQ : zalu64 ALU_SLTU 0 (Z.lxor x k) = (if x =? k then 0 else 1)).
{ unfold zalu64, zcanon, M64. cbn [zalu_raw].
  rewrite (Z.mod_small 0), (Z.mod_small (Z.lxor x k)) by lia.
  destruct (Z.eqb_spec x k) as [->|Hne].
  - rewrite Z.lxor_nilpotent. vm_compute. reflexivity.
  - assert (Hnz : Z.lxor x k <> 0) by (intros Hz; apply Hne; apply Z.lxor_eq; exact Hz).
    replace (0 <? Z.lxor x k) with true by (symmetry; apply Z.ltb_lt; lia).
    vm_compute. reflexivity. }
rewrite EQ. apply unsigned_lit_small. destruct (x =? k); lia.
Qed.

(* `slli 48; srai 48` is the 16-bit sign extension, so `slti` compares the modelled v with c. *)
Lemma s2a_slt_sext16 : forall (E : env) (n : nat) (v c : Z),
  ew E n = Z_to_bv 64 (v mod 2 ^ 64) -> -32768 <= v < 32768 -> -2048 <= c < 2048 ->
  U E (SAlu ALU_SLT (SAlu ALU_SRA (SAlu ALU_SLL (SOff n 0) (SLit 48)) (SLit 48)) (SLit c))
  = (if v <? c then 1 else 0).
Proof.
intros E n v c Hn Hv Hc.
assert (Hm : 0 <= v mod 2 ^ 64 < 2 ^ 64) by (apply Z.mod_pos_bound; lia).
assert (U0 : U E (SOff n 0) = v mod 2 ^ 64).
{ rewrite U_SOff, Hn, Z.add_0_r, unsigned_lit_small by lia. apply zcanon_id. unfold M64. lia. }
(* the shift pair, on the raw Z side: the low 16 bits, sign-extended, scaled back by 2 ^ 48 *)
assert (SH : bv_swrap 64 (zcanon (Z.shiftl (v mod 2 ^ 64) 48)) = v * 2 ^ 48).
{ rewrite Z.shiftl_mul_pow2 by lia. unfold zcanon, M64.
  destruct (Z.ltb_spec v 0) as [Hneg|Hpos].
  - assert (Hvm : v mod 2 ^ 64 = v + 2 ^ 64).
    { rewrite <- (Z_mod_plus_full v 1 (2 ^ 64)).
      replace (v + 1 * 2 ^ 64) with (v + 2 ^ 64) by lia. apply Z.mod_small. lia. }
    rewrite Hvm.
    replace ((v + 2 ^ 64) * 2 ^ 48) with ((v + 65536) * 2 ^ 48 + (2 ^ 48 - 1) * 2 ^ 64) by lia.
    rewrite Z_mod_plus_full, (Z.mod_small ((v + 65536) * 2 ^ 48)) by lia.
    rewrite swrap64_of_unsigned by (unfold M64; lia).
    replace ((v + 65536) * 2 ^ 48 <? half64) with false
      by (symmetry; apply Z.ltb_ge; unfold half64; lia).
    unfold M64. lia.
  - rewrite (Z.mod_small v) by lia. rewrite (Z.mod_small (v * 2 ^ 48)) by lia.
    rewrite swrap64_of_unsigned by (unfold M64; lia).
    replace (v * 2 ^ 48 <? half64) with true by (symmetry; apply Z.ltb_lt; unfold half64; lia).
    reflexivity. }
assert (U2 : U E (SAlu ALU_SRA (SAlu ALU_SLL (SOff n 0) (SLit 48)) (SLit 48)) = v mod 2 ^ 64).
{ rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit, (zcanon_id 48) by (unfold M64; lia).
  change (Z.land 48 63) with 48.
  rewrite U_SAlu. cbn [zalu_raw]. rewrite U0, U_SLit, (zcanon_id 48) by (unfold M64; lia).
  change (Z.land 48 63) with 48.
  rewrite SH, Z.shiftr_div_pow2 by lia. rewrite Z.div_mul by lia.
  unfold zcanon, M64. reflexivity. }
assert (SV : bv_swrap 64 (v mod 2 ^ 64) = v).
{ change (v mod 2 ^ 64) with (zcanon v). rewrite zcanon_wrap, (bv_swrap_wrap 64).
  apply swrap64_id. unfold half64. lia. }
assert (SC : bv_swrap 64 (zcanon c) = c).
{ rewrite zcanon_wrap, (bv_swrap_wrap 64). apply swrap64_id. unfold half64. lia. }
rewrite U_SAlu. cbn [zalu_raw]. rewrite U2, U_SLit, SV, SC.
apply zcanon_id. unfold M64. destruct (v <? c); lia.
Qed.
