(* diginet_counter_leds_encode (diginet_codec.c:257-263; image A 0x85a7c, 146 instructions, frame 16, a leaf:
   leds_encode and sysex_encode are inlined and the payload bytes are stored into out directly), against
   lib/A/Prog/CPgEncC.v's cdc_cleds_specX over the concrete table of image A.

   a0 = the personality, a1 = bits (lw), a2 = &out. Five paths:
   - a0 = 0 (pd = None): the test at 0x85a8c is taken, nothing is written, a0 = -1.
   - bits > 127 (the unsigned compare of the sign-extended register at 0x85ab8): a0 = -11.
   - p->device (lb at p + 16) negative: a0 = -1 (the test at 0x85ae0).
   - p->counter_addr (lbu at p + 19, sign-extended by slli / srai 56) negative: a0 = -11.
   - else out gets f0 13 device 20 counter bits f7, out[24] = 7, out[25] = 0 and the word
     counter | 0x50000 = KEY 5 counter at out + 28, and a0 = 0.
   Every failing return comes before the first store into out, so the 32 bytes there stay the caller's.

   Before each load of a personality byte and each store into out the code loads the shadow byte of the
   address through the GOT slot of the shadow-offset cell and continues when it is 0 or when the address
   modulo 8 (+ 3 for the 4-byte store at out + 28) is below it. The premises range_addressable over
   [p + 16, p + 20) (pers_argA's cimg_range: usable in every state, so at the entry state too) and over
   [out, out + 32) (cenc_out's cdst_ok) are the walk's two shadow entries, so every such test is decided
   and the error path is never reached.

   The GOT slot and the shadow-offset cell are read by the first three instructions only. The personality
   and the caller's command may lie anywhere their premises allow, the two cells included, so their
   regions cannot be shown apart from the cells': the walk runs to 0x85aa0 with the cells alone, where
   the shadow offset is in a register and the cells are dead, drops them and adds the regions of the
   personality and of out, which the premises do keep apart from each other and from the save area. *)
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A Require Import AWalkFw0 ACef AF0l ACej ACeh ACem ACep.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A Require Import AWalkFw1 AWalkFw2 ACfm.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import CodecCJ CPgBase CPgEncC CPgWalk.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

Definition A_CLEDS : Z := 0x85a7c.

(* ============================== the Gallina result of each path ============================== *)
Lemma cl_lor_add : forall hi lo k, 0 <= k -> 0 <= lo < 2 ^ k -> hi mod 2 ^ k = 0 -> Z.lor hi lo = hi + lo.
Proof.
intros hi lo k Hk Hlo Hhi.
assert (HL : Z.land hi lo = 0).
{ rewrite <- (Z.mod_small lo (2 ^ k)) by lia. rewrite <- Z.land_ones by lia.
  rewrite (Z.land_comm lo), Z.land_assoc, Z.land_ones, Hhi by lia. apply Z.land_0_l. }
pose proof (Z.add_lor_land hi lo). lia.
Qed.
Lemma cl_key : forall c, 0 <= c < 128 -> Z.lor c 327680 = KEY 5 c.
Proof.
intros c Hc. unfold KEY. change 0xffff with (Z.ones 16). rewrite Z.land_ones by lia.
rewrite (Z.mod_small c) by (cbn; lia). rewrite Z.lor_comm. reflexivity.
Qed.
Lemma cl_key_range : forall c, 0 <= c < 128 -> 0 <= KEY 5 c < 2 ^ 32.
Proof.
intros c Hc. rewrite <- cl_key by lia. rewrite Z.lor_comm.
rewrite (cl_lor_add 327680 c 7); [lia | lia | cbn; lia | reflexivity].
Qed.
Lemma cl_pack : forall b c, 0 <= b < 128 -> 0 <= c < 128 -> Z.lor (b * 256) c = b * 256 + c.
Proof.
intros b c Hb Hc. rewrite (cl_lor_add (b * 256) c 8); [lia | lia | change (2 ^ 8) with 256; lia |].
apply Z.mod_mul. lia.
Qed.
Lemma cl_tb7_hi : forall x, 128 <= x < 256 -> Z.testbit x 7 = true.
Proof.
intros x H. rewrite Z.testbit_true by lia. change (2 ^ 7) with 128.
assert (E : x / 128 = 1) by (Z.div_mod_to_equations; lia). rewrite E. reflexivity.
Qed.
Lemma cl_tb7_lo : forall x, 0 <= x < 128 -> Z.testbit x 7 = false.
Proof.
intros x H. destruct (Z.testbit x 7) eqn:E; [|reflexivity]. exfalso.
rewrite Z.testbit_true in E by lia. change (2 ^ 7) with 128 in E.
assert (Hq : x / 128 = 0) by (Z.div_mod_to_equations; lia). rewrite Hq in E. discriminate.
Qed.
Lemma cl_s32_hi : forall b, 127 < b < 2 ^ 32 -> 128 <= s32 b mod 2 ^ 64 <= 2 ^ 64 - 1.
Proof.
intros b Hb. unfold s32. destruct (Z.ltb_spec b (2 ^ 31)).
- rewrite Z.mod_small by lia. lia.
- replace (b - 2 ^ 32) with ((b - 2 ^ 32 + 2 ^ 64) + (-1) * 2 ^ 64) by lia.
  rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. lia.
Qed.
Lemma cl_spec_none : forall b, counter_leds_spec None b = (E_ARG, None).
Proof. intros b. reflexivity. Qed.
Lemma cl_spec_rng : forall d b, 127 < b -> counter_leds_spec (Some d) b = (E_RANGE, None).
Proof.
intros d b Hb. cbn [counter_leds_spec]. unfold leds_spec.
rewrite (proj2 (Z.ltb_lt 0x7f b)) by lia. reflexivity.
Qed.
Lemma cl_spec_dev : forall d b, 0 <= b <= 127 -> 127 < d_dev d ->
counter_leds_spec (Some d) b = (E_ARG, None).
Proof.
intros d b Hb Hd. cbn [counter_leds_spec]. unfold leds_spec.
rewrite (proj2 (Z.ltb_ge 0x7f b)) by lia. unfold sysex_spec.
rewrite (proj2 (Z.ltb_lt 0x7f (d_dev d))) by lia. reflexivity.
Qed.
Lemma cl_spec_cnt : forall d b, 0 <= b <= 127 -> 0 <= d_dev d <= 127 -> 128 <= d_counter d < 256 ->
counter_leds_spec (Some d) b = (E_RANGE, None).
Proof.
intros d b Hb Hd Hc. cbn [counter_leds_spec]. unfold leds_spec.
rewrite (proj2 (Z.ltb_ge 0x7f b)) by lia. unfold sysex_spec.
rewrite (proj2 (Z.ltb_ge 0x7f (d_dev d))) by lia. cbn [Z.eqb].
rewrite (proj2 (Z.ltb_ge 24 (Z.of_nat (length [u8 (d_counter d); u8 b]) + 5))) by (cbn [length]; lia).
cbn [existsb orb]. unfold u8. rewrite (Z.mod_small (d_counter d) 256) by lia.
rewrite cl_tb7_hi by lia. reflexivity.
Qed.
Lemma cl_spec_ok : forall d b, 0 <= b <= 127 -> 0 <= d_dev d <= 127 -> 0 <= d_counter d <= 127 ->
counter_leds_spec (Some d) b =
(0, Some ([0xf0; 0x13; d_dev d; 0x20; d_counter d; b; 0xf7], KEY 5 (d_counter d), 0)).
Proof.
intros d b Hb Hd Hc. cbn [counter_leds_spec]. unfold leds_spec.
rewrite (proj2 (Z.ltb_ge 0x7f b)) by lia. unfold sysex_spec.
rewrite (proj2 (Z.ltb_ge 0x7f (d_dev d))) by lia. cbn [Z.eqb].
rewrite (proj2 (Z.ltb_ge 24 (Z.of_nat (length [u8 (d_counter d); u8 b]) + 5))) by (cbn [length]; lia).
cbn [existsb orb]. unfold u8.
rewrite (Z.mod_small (d_counter d) 256), (Z.mod_small b 256) by lia.
rewrite !cl_tb7_lo by lia. cbn [orb app]. unfold with_key, bit_or_0. cbn [Z.eqb orb].
reflexivity.
Qed.

(* ============================== lists of bytes ============================== *)
Lemma cl_nth_nil : forall j (dd : Z), nth j (@nil Z) dd = dd.
Proof. intros j dd. destruct j; reflexivity. Qed.
Lemma cl_nth_firstn : forall (l : list Z) n j dd, (j < n)%nat -> nth j (firstn n l) dd = nth j l dd.
Proof.
intros l. induction l as [|x l IH]; intros n j dd Hj.
- rewrite firstn_nil. rewrite !cl_nth_nil. reflexivity.
- destruct n as [|n]; [lia|]. cbn [firstn]. destruct j as [|j]; [reflexivity|]. cbn [nth]. apply IH. lia.
Qed.
Lemma cl_nth_skipn : forall (l : list Z) i j dd, nth j (skipn i l) dd = nth (i + j) l dd.
Proof.
intros l. induction l as [|x l IH]; intros i j dd.
- rewrite skipn_nil. rewrite !cl_nth_nil. reflexivity.
- destruct i as [|i]; [reflexivity|]. cbn [skipn Nat.add nth]. apply IH.
Qed.
Lemma cl_len_firstn : forall (l : list Z) n, (n <= length l)%nat -> length (firstn n l) = n.
Proof.
intros l. induction l as [|x l IH]; intros n Hn; destruct n as [|n]; cbn [length firstn] in *; try lia.
rewrite IH by lia. reflexivity.
Qed.
Lemma cl_len_skipn : forall (l : list Z) i, length (skipn i l) = (length l - i)%nat.
Proof.
intros l. induction l as [|x l IH]; intros i; destruct i as [|i]; cbn [length skipn]; try lia.
rewrite IH. reflexivity.
Qed.
Lemma cl_cmd_bytes : forall before d b, length before = 32%nat ->
0 <= b <= 127 -> 0 <= d_dev d <= 127 -> 0 <= d_counter d <= 127 ->
cmd_outZ before (snd (counter_leds_spec (Some d) b)) =
[240; 19; d_dev d; 32; d_counter d; b; 247] ++ firstn 17 (skipn 7 before) ++ [7; 0]
  ++ firstn 2 (skipn 26 before) ++ le4Z (KEY 5 (d_counter d)).
Proof.
intros before d b Hlen Hb Hd Hc. rewrite (cl_spec_ok d b Hb Hd Hc). cbn [snd].
unfold cmd_outZ. cbn [map length Z.of_nat]. unfold u8.
rewrite (Z.mod_small (d_dev d) 256), (Z.mod_small (d_counter d) 256), (Z.mod_small b 256) by lia.
change (240 mod 256) with 240. change (19 mod 256) with 19. change (32 mod 256) with 32.
change (247 mod 256) with 247. change (7 mod 256) with 7. change (0 mod 256) with 0.
replace (skipn 7 (firstn 24 before)) with (firstn 17 (skipn 7 before))
  by (rewrite firstn_skipn_comm; reflexivity).
reflexivity.
Qed.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.

(* ============================== the walk's regions and facts ============================== *)
(* the two personality bytes the call reads, at offsets 16 and 19 of the atom that holds p *)
Definition cl_pers : YP09.region :=
YP09.mkRegion (Some 10%nat) 16 20 16 16
[YP09.mkChunk 16 (CVal 1 (SOff 33 0)); YP09.mkChunk 19 (CVal 1 (SOff 34 0))].
(* the three windows of out the call writes; out[7..24) and out[26..28) are never written *)
Definition cl_out0 : YP09.region := YP09.mkRegion (Some 12%nat) 0 7 0 7 [].
Definition cl_out1 : YP09.region := YP09.mkRegion (Some 12%nat) 24 26 24 26 [].
Definition cl_out2 : YP09.region := YP09.mkRegion (Some 12%nat) 28 32 28 32 [].
Definition cl_AF (lo10 hi10 lo11 hi11 lo33 hi33 lo34 hi34 : Z) : list (nat * afact) :=
[ (10%nat, mkAF lo10 hi10 0); (11%nat, mkAF lo11 hi11 0); (12%nat, mkAF 1 (2 ^ 47 - 33) 0);
  (33%nat, mkAF lo33 hi33 0); (34%nat, mkAF lo34 hi34 0) ].
Definition cl_SHP : list shent := [mkSHE 10 16 20].
Definition cl_SHW : list shent := [mkSHE 10 16 20; mkSHE 12 0 32].

Lemma cl_ew33 : forall regs xs, ew (Ereg regs (cw_extra xs)) 33 = Z_to_bv 64 (nth 0 xs 0).
Proof. intros regs xs. exact (cw_ew_x regs xs 0). Qed.
Lemma cl_ew34 : forall regs xs, ew (Ereg regs (cw_extra xs)) 34 = Z_to_bv 64 (nth 1 xs 0).
Proof. intros regs xs. exact (cw_ew_x regs xs 1). Qed.
Lemma cl_atoms_ok : forall regs xs lo10 hi10 lo11 hi11 lo33 hi33 lo34 hi34,
lo10 <= bv_unsigned (getr regs 10) <= hi10 ->
lo11 <= bv_unsigned (getr regs 11) <= hi11 ->
1 <= bv_unsigned (getr regs 12) <= 2 ^ 47 - 33 ->
lo33 <= nth 0 xs 0 <= hi33 -> 0 <= nth 0 xs 0 < 2 ^ 64 ->
lo34 <= nth 1 xs 0 <= hi34 -> 0 <= nth 1 xs 0 < 2 ^ 64 ->
atoms_ok (Ereg regs (cw_extra xs)) (cl_AF lo10 hi10 lo11 hi11 lo33 hi33 lo34 hi34).
Proof.
intros regs xs lo10 hi10 lo11 hi11 lo33 hi33 lo34 hi34 H10 H11 H12 H33a H33b H34a H34b.
unfold cl_AF. cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite (cw_ew_reg regs xs 10 10%bv eq_refl), (cw_ew_reg regs xs 11 11%bv eq_refl),
        (cw_ew_reg regs xs 12 12%bv eq_refl), (cl_ew33 regs xs), (cl_ew34 regs xs).
rewrite !unsigned_lit_small by lia.
rewrite !Z.pow_0_r, !Z.mod_1_r.
repeat split; lia.
Qed.

(* ============================== the engine's values ============================== *)
Lemma cl_U_sra56 : forall E n c, ew E n = Z_to_bv 64 c -> 0 <= c < 128 ->
U E (SAlu ALU_SRA (SAlu ALU_SLL (SOff n 0) (SLit 56)) (SLit 56)) = c.
Proof.
intros E n c Hn Hc. rewrite !U_SAlu. cbn [zalu_raw].
rewrite (U_atom E n c Hn ltac:(lia)), !U_SLit.
change (zcanon 56) with 56. change (Z.land 56 63) with 56.
rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 56) with 72057594037927936.
rewrite (zcanon_id (c * 72057594037927936)) by (unfold M64; lia).
rewrite bv_swrap_small by (change (bv_half_modulus 64) with (2 ^ 63); lia).
rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 56) with 72057594037927936.
rewrite Z.div_mul by lia. apply zcanon_id. unfold M64. lia.
Qed.
Lemma cl_U_pack : forall E m n b c, ew E m = Z_to_bv 64 b -> ew E n = Z_to_bv 64 c ->
0 <= b < 128 -> 0 <= c < 128 ->
U E (SAlu ALU_OR (SAlu ALU_SLL (SOff m 0) (SLit 8))
      (SAlu ALU_SRA (SAlu ALU_SLL (SOff n 0) (SLit 56)) (SLit 56))) = b * 256 + c.
Proof.
intros E m n b c Hm Hn Hb Hc.
rewrite U_SAlu. cbn [zalu_raw]. rewrite (cl_U_sra56 E n c Hn Hc).
rewrite U_SAlu. cbn [zalu_raw]. rewrite (U_atom E m b Hm ltac:(lia)), U_SLit.
change (zcanon 8) with 8. change (Z.land 8 63) with 8.
rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 8) with 256.
rewrite (zcanon_id (b * 256)) by (unfold M64; lia).
rewrite cl_pack by lia. apply zcanon_id. unfold M64. lia.
Qed.
Lemma cl_U_srl8 : forall E e v, U E e = v -> 0 <= v < 2 ^ 64 ->
U E (SAlu ALU_SRL e (SLit 8)) = v / 256.
Proof.
intros E e v He Hv. rewrite U_SAlu. cbn [zalu_raw]. rewrite He, U_SLit.
change (Z.land (zcanon 8) 63) with 8. rewrite Z.shiftr_div_pow2 by lia.
change (2 ^ 8) with 256. apply zcanon_id. unfold M64.
split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia].
Qed.
Lemma cl_U_key : forall E n c, ew E n = Z_to_bv 64 c -> 0 <= c < 128 ->
U E (SAlu ALU_OR (SOff n 0) (SLit 327680)) = KEY 5 c.
Proof.
intros E n c Hn Hc. rewrite U_SAlu. cbn [zalu_raw].
rewrite (U_atom E n c Hn ltac:(lia)), U_SLit. change (zcanon 327680) with 327680.
rewrite cl_key by lia. pose proof (cl_key_range c Hc). apply zcanon_id. unfold M64. lia.
Qed.
(* `lb` of a byte x compared with 0: the sign-extended value is negative exactly when 127 < x *)
Lemma cl_br_lt0_sext8 : forall E n x, ew E n = Z_to_bv 64 x -> 0 <= x < 256 ->
branch_taken BC_LT (sv_denot E (SExt true 8 (SOff n 0))) (sv_denot E (SLit 0)) = (127 <? x).
Proof.
intros E n x Hn Hx.
rewrite (denot_lit_U E (SExt true 8 (SOff n 0))), (denot_lit_U E (SLit 0)).
cbn [branch_taken]. unfold bv_lts. rewrite !Z_to_bv_signed.
rewrite U_SExt, U_SLit, (U_atom E n x Hn ltac:(lia)). cbv iota beta.
change (2 ^ Z.of_N 8) with 256. rewrite (Z.mod_small x 256) by lia.
unfold zcanon, M64, bv_swrap, bv_wrap.
change (bv_half_modulus 8) with 128. change (bv_modulus 8) with 256.
change (bv_half_modulus 64) with (2 ^ 63). change (bv_modulus 64) with (2 ^ 64).
destruct (Z.ltb_spec 127 x).
- assert (M1 : (x + 128) mod 256 = x - 128) by (Z.div_mod_to_equations; lia). rewrite M1.
  replace (x - 128 - 128) with (x - 256) by lia.
  assert (M2 : (x - 256) mod 2 ^ 64 = x - 256 + 2 ^ 64).
  { replace (x - 256) with (x - 256 + 2 ^ 64 + (-1) * 2 ^ 64) at 1 by lia.
    rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
  rewrite M2.
  assert (M3 : (x - 256 + 2 ^ 64 + 2 ^ 63) mod 2 ^ 64 = x - 256 + 2 ^ 63).
  { replace (x - 256 + 2 ^ 64 + 2 ^ 63) with (x - 256 + 2 ^ 63 + 1 * 2 ^ 64) by lia.
    rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
  rewrite M3. change (0 mod 2 ^ 64) with 0.
  rewrite (Z.mod_small (0 + 2 ^ 63) (2 ^ 64)) by lia. apply Z.ltb_lt. lia.
- rewrite (Z.mod_small (x + 128) 256) by lia. replace (x + 128 - 128) with x by lia.
  rewrite (Z.mod_small x (2 ^ 64)) by lia.
  rewrite (Z.mod_small (x + 2 ^ 63) (2 ^ 64)) by lia.
  change (0 mod 2 ^ 64) with 0.
  rewrite (Z.mod_small (0 + 2 ^ 63) (2 ^ 64)) by lia. apply Z.ltb_ge. lia.
Qed.

(* ============================== bytes out of the final state ============================== *)
Lemma cl_vm1 : forall E m base off e,
YP09.chunk_ok tfibsegs E m base (YP09.mkChunk off (CVal 1 e)) ->
val_mem tfibsegs m (base + off) 1 (U E e mod 256).
Proof.
intros E m base off e H kk Hk. assert (kk = 0%nat) as -> by lia.
destruct (H 0 ltac:(cbn [YP09.c_len YP09.c_val cv_len]; lia)) as (bb & Hb1 & Hb2).
cbn [YP09.c_off YP09.c_val cbyte] in Hb1, Hb2. injection Hb1 as <-.
cbn [Z.of_nat]. rewrite Z.add_0_r in Hb2 |- *. rewrite Hb2. f_equal.
unfold byte_of_word, YO0f.le_byte, U.
change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0. change (8 * 0) with 0.
rewrite !Z.shiftr_0_r. change (2 ^ 8) with 256.
apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
change (2 ^ Z.of_N 8) with 256. rewrite !Z.mod_mod by lia. reflexivity.
Qed.
Lemma cl_byte_of_region : forall E m n b cs lo hi wlo whi od e,
region_ok tfibsegs E m (YP09.mkRegion (Some n) lo hi wlo whi cs) ->
bv_unsigned (ew E n) = b -> In (YP09.mkChunk od (CVal 1 e)) cs ->
val_mem tfibsegs m (b + od) 1 (U E e mod 256).
Proof.
intros E m n b cs lo hi wlo whi od e (_ & _ & _ & Hcs) Hn Hc.
pose proof (proj1 (Forall_forall _ _) Hcs _ Hc) as Hck.
cbn [YP09.r_base base_val] in Hck. rewrite Hn in Hck.
exact (cl_vm1 E m b od e Hck).
Qed.
Lemma cl_vm4 : forall m a v, val_mem tfibsegs m a 4 v -> 0 <= v < 2 ^ 32 ->
garr8 tfibsegs m a (le4Z v).
Proof.
intros m a v H Hv j Hj. unfold le4Z in *. cbn [length] in Hj.
split.
- intros kk Hk. assert (kk = 0%nat) as -> by lia. cbn [Z.of_nat]. rewrite Z.add_0_r.
  rewrite (H j Hj). f_equal. f_equal. unfold YO0f.le_byte.
  change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32). change (8 * Z.of_nat 1) with 8.
  rewrite (Z.mod_small v (2 ^ 32)) by lia.
  destruct j as [|[|[|[|j]]]]; cbn [nth]; try lia.
  all: change (8 * Z.of_nat 0) with 0; rewrite !Z.shiftr_0_r.
  + rewrite !Z.mod_mod by lia. reflexivity.
  + change (8 * Z.of_nat 1) with 8. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256.
    rewrite !Z.mod_mod by lia. reflexivity.
  + change (8 * Z.of_nat 2) with 16. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 16) with 65536.
    rewrite !Z.mod_mod by lia. reflexivity.
  + change (8 * Z.of_nat 3) with 24. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 24) with 16777216.
    rewrite !Z.mod_mod by lia. reflexivity.
- destruct j as [|[|[|[|j]]]]; cbn [nth]; try lia;
  (split; [first [lia | apply Z.div_pos; lia] | ]);
  first [apply Z.mod_pos_bound; lia | lia].
Qed.
Lemma cl_garr8_kept : forall (W : world tfibsegs) (m m2 : word -> option byte) base l,
garr8 tfibsegs (mrestrict (w_H W) m) base l ->
(forall a, base <= a < base + Z.of_nat (length l) ->
   aview tfibsegs (w_H W) m2 a = aview tfibsegs (w_H W) m a) ->
garr8 tfibsegs (mrestrict (w_H W) m2) base l.
Proof.
intros W m m2 base l H HK j Hj. split; [|exact (proj2 (H j Hj))].
apply (cw_val_mem_kept (w_H W) (w_H W) m m2 (base + Z.of_nat j) 1 (nth j l 0)).
- intros x Hx. apply HK. cbn [Z.of_nat] in Hx. lia.
- exact (proj1 (H j Hj)).
Qed.
Lemma cl_garr8_sub : forall (m : word -> option byte) base l i n,
garr8 tfibsegs m base l -> (i + n <= length l)%nat ->
garr8 tfibsegs m (base + Z.of_nat i) (firstn n (skipn i l)).
Proof.
intros m base l i n H Hin j Hj.
rewrite cl_len_firstn in Hj by (rewrite cl_len_skipn; lia).
rewrite cl_nth_firstn by lia. rewrite cl_nth_skipn.
replace (base + Z.of_nat i + Z.of_nat j) with (base + Z.of_nat (i + j)) by lia.
apply H. lia.
Qed.
Lemma cl_garr8_cmd : forall m base l1 l2 l3 l4 l5,
length l1 = 7%nat -> length l2 = 17%nat -> length l3 = 2%nat -> length l4 = 2%nat ->
garr8 tfibsegs m base l1 -> garr8 tfibsegs m (base + 7) l2 -> garr8 tfibsegs m (base + 24) l3 ->
garr8 tfibsegs m (base + 26) l4 -> garr8 tfibsegs m (base + 28) l5 ->
garr8 tfibsegs m base (l1 ++ l2 ++ l3 ++ l4 ++ l5).
Proof.
intros m base l1 l2 l3 l4 l5 N1 N2 N3 N4 G1 G2 G3 G4 G5.
apply (proj2 (garr8_app tfibsegs m base l1 _)). split; [exact G1|].
rewrite N1. change (Z.of_nat 7) with 7.
apply (proj2 (garr8_app tfibsegs m (base + 7) l2 _)). split; [exact G2|].
rewrite N2. replace (base + 7 + Z.of_nat 17) with (base + 24) by (cbn [Z.of_nat]; lia).
apply (proj2 (garr8_app tfibsegs m (base + 24) l3 _)). split; [exact G3|].
rewrite N3. replace (base + 24 + Z.of_nat 2) with (base + 26) by (cbn [Z.of_nat]; lia).
apply (proj2 (garr8_app tfibsegs m (base + 26) l4 _)). split; [exact G4|].
rewrite N4. replace (base + 26 + Z.of_nat 2) with (base + 28) by (cbn [Z.of_nat]; lia).
exact G5.
Qed.

(* ============================== the walk's tactics ============================== *)
(* an atom fact of the walk's base env, restated for the env the engine has reached *)
Ltac cl_lift idx H nm :=
lazymatch goal with HS : YP0l.st_ok _ ?Ev _ _ |- _ =>
  eassert (nm : ew Ev idx = _) by (rewrite ?ew_ewset_other by lia; exact H) end.
(* the region of the state based on atom m whose low offset is lo *)
Ltac cl_find rs m lo :=
lazymatch rs with
| cons (YP09.mkRegion (Some m) lo ?hi ?wlo ?whi ?cs) _ => constr:(YP09.mkRegion (Some m) lo hi wlo whi cs)
| cons _ ?t => cl_find t m lo
end.
Ltac cl_region HS m lo nm :=
lazymatch type of HS with
| YP0l.st_ok _ ?Ev ?ssv ?msv =>
  let l := eval vm_compute in (ss_mem ssv) in
  let r := cl_find l m lo in
  pose proof (proj1 (Forall_forall _ _)
    (proj1 (proj2 (st_ok_mem_ok tfibsegs Ev ssv msv HS))) r
    ltac:(vm_compute; repeat (first [left; reflexivity | right]))) as nm
end.
Ltac cl_find_chunk cs od :=
lazymatch cs with
| cons (YP09.mkChunk od (CVal 1 ?e)) _ => e
| cons _ ?t => cl_find_chunk t od
end.
(* the byte a one-byte chunk at offset od of the region HR leaves, as the value v *)
Ltac cl_byte HR Hb od v nm tac :=
lazymatch type of HR with
| region_ok _ ?Ev _ (YP09.mkRegion (Some ?n) ?lo ?hi ?wlo ?whi ?cs) =>
  let e := cl_find_chunk cs od in
  let H0 := fresh "Hbyte" in
  pose proof (cl_byte_of_region Ev _ n _ cs lo hi wlo whi od e HR Hb
    ltac:(cbn [In]; repeat (first [left; reflexivity | right]))) as H0;
  replace (U Ev e mod 256) with v in H0 by tac;
  rename H0 into nm
end.
(* the write windows of a state lie in the save area, or in out *)
Ltac cl_kwr_out :=
idtac; let a := fresh "a" in let r := fresh "r" in let Hr := fresh "Hr" in let Hb := fresh "Hb" in
intros a (r & Hr & Hb); cbv beta;
lazymatch type of Hr with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hr end;
repeat (destruct Hr as [<- | Hr];
[ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb;
  rewrite ?ew_ewset_other, ?ew_havoc_old in Hb by lia;
  first [ lazymatch goal with B2 : bv_unsigned (ew _ 2) = _ |- _ => rewrite B2 in Hb end; left; lia
        | lazymatch goal with B12 : bv_unsigned (ew _ 12) = _ |- _ => rewrite B12 in Hb end;
          first [right; left; lia | right; right; left; lia | right; right; right; lia]
        | lia ] | ]);
destruct Hr.
Ltac cl_awr_out :=
idtac;
lazymatch goal with |- awr_ok ?E ?rs ?stk ?sp0v ?fp ?b0 ?bc ?ly ?own =>
let rs' := eval vm_compute in rs in change (awr_ok E rs' stk sp0v fp b0 bc ly own);
lazymatch goal with B2 : bv_unsigned (ew E 2) = ?spv |- _ =>
repeat first
[ apply awr_ok_nil
| apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia |]
| eapply awr_ok_cons_stack_off with (n := 2%nat) (d := spv - sp0v);
  [ reflexivity | rewrite B2; lia | cbn [YP09.r_wlo YP09.r_whi]; lia
  | cbn [YP09.r_wlo YP09.r_whi]; lia | ]
| lazymatch goal with
  | B12 : bv_unsigned (ew E 12) = ?ov, HW : twr_ok _ _ _ _ _ _ _ _ _ _ _ _ _ ?ov 32 |- _ =>
    eapply cw_awr_ok_cons_twr with (m := 12%nat) (q := ov) (n := 32);
    [ reflexivity | exact B12 | cbn [YP09.r_wlo YP09.r_whi]; lia
    | cbn [YP09.r_wlo YP09.r_whi]; lia | exact HW | ] end ] end end.

(* after the cells are dropped: add the region of the two personality bytes, whose values the walk has kept *)
Ltac cl_add_pers E10 E33 E34 B2 KE Vdev Vcnt W memc p d :=
lazymatch goal with HS : YP0l.st_ok _ ?Ev ?ssv ?msv |- _ =>
  let Hrp := fresh "Hrp" in let Hdp := fresh "Hdp" in let HS1 := fresh "HS" in
  assert (Hrp : region_ok tfibsegs Ev (ms_mem msv) cl_pers);
  [ unfold region_ok, cl_pers;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict];
    rewrite E10, unsigned_lit_small by lia;
    split; [lia|]; split; [lia|]; split; [intros o Ho; lia|];
    apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]];
    [ apply (chunk_ok_val tfibsegs Ev _ p 16 1 (SOff 33 0) (d_dev d));
      [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |];
      apply (cw_val_mem_kept (w_H W) (w_H W) memc _); [|exact Vdev];
      intros x Hx; apply KE; [lia | cbv beta; lia]
    | apply (chunk_ok_val tfibsegs Ev _ p 19 1 (SOff 34 0) (d_counter d));
      [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |];
      apply (cw_val_mem_kept (w_H W) (w_H W) memc _);
      [ intros x Hx; apply KE; [lia | cbv beta; lia]
      | replace (p + 19) with (p + 16 + 3) by lia; exact Vcnt ] ]
  | ];
  assert (Hdp : all_disjoint Ev cl_pers (ss_mem ssv));
  [ cbn [ss_mem all_disjoint]; unfold extent_disjoint, cl_pers;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite E10, B2, unsigned_lit_small by lia;
    split; [lia | exact I]
  | ];
  pose proof (ast_ok_add_region tfibsegs Ev ssv msv cl_pers HS eq_refl Hrp Hdp) as HS1;
  cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS1; clear HS Hrp Hdp; rename HS1 into HS
end.
(* the `ret` of a failing path: nothing but the save area was written, a0 is the code, out is `before` *)
Ltac cl_fail_leaf HJ0 KE HEIMG HBB HBlen W memc out before spec :=
cw_leaf ltac:(idtac; cw_kept HJ0 KE ltac:(exact HEIMG) ltac:(intros aa Hz; cbv beta in Hz; left; lia))
        ltac:(idtac; unfold cenc_res; cbv beta; rewrite spec; cbn [fst snd cmd_outZ];
              split;
              [ match goal with R : getr ?rg ?r = _ |- getr ?rg ?r = _ => rewrite R end;
                apply bv_eq; vm_compute; reflexivity
              | apply (cl_garr8_kept W memc _ out before HBB);
                let a := fresh "a" in let Ha := fresh "Ha" in
                intros a Ha; rewrite HBlen in Ha; apply KE; [lia | cbv beta; lia] ]).

Section d.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis TL : TfibLib B.
Hypothesis LAWS : AR_laws tfibsegs B.

Theorem diginet_counter_leds_encode_A_holds : cdc_cleds_specX tfibsegs B MT 0x85a7c.
Proof using MTL TL LAWS.
unfold cdc_cleds_specX.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs pd p bits out before
  HE H10 HPERS H11 H12 HOUT HDISJ.
pose proof HE as (HJ & Hra & Hra4 & Hgp & Htp & Hal16 & Hwlo & Hwhi & Hev & Hlive).
cw_keep_j0 HJ HJ0.
unfold T_cleds in *.
pose proof Hwx_tfa as Hwx. pose proof tfib_segs_low as Hsegs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (cw_entry_stack B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs 16 HE ltac:(lia))
  as (Hceil & H47 & H46 & _ & Hpres).
pose proof (proj1 HJ0) as HAR0.
pose proof HOUT as (HDST & HBB & HBlen).
pose proof HDST as (Hout0 & Hout63 & HTD & HTWR & HORA & HOHULL & HOAM & HOCOFF).
pose proof H11 as (Hbits32 & H11r).
assert (Hout47 : out + 32 <= 2 ^ 47 - 1)
  by (clear - HOAM C3 C4 C5; unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in *; lia).
change (w64 p) with (Z_to_bv 64 p) in H10.
change (w64 out) with (Z_to_bv 64 out) in H12.
change (w64 (s32 bits)) with (Z_to_bv 64 (s32 bits)) in H11r.
unfold coff_win in HOCOFF.
(* the bytes of out are no byte of the image *)
assert (HEIMG : forall a, cenc_wr out a -> in_img tfibsegs a -> False).
{ intros a Ha Himg. cbv beta in Ha. unfold cenc_wr in Ha.
  exact (cw_tdst_not_img tfibsegs B LAWS tfib_segs_low lyc Sc W memc mdc out 32 a HAR0 HTD
           ltac:(lia) Himg). }
unfold cfg_at. change (w64 0x85a7c) with (Z_to_bv 64 0x85a7c).
destruct pd as [d|].
- (* ======================= a0 is a personality ======================= *)
  pose proof HPERS as (Hp0 & Hp63 & Hdev & Hstr & Hch & Hcnt & HG8 & HCIMG).
  pose proof HCIMG as (Hq0 & Hqn & Hq63 & HQAM & HQCOFF & HQIMG & HQUSE).
  pose proof (HQUSE lyc Sc W memc mdc HAR0) as (HQRA & HQhull).
  unfold coff_win in HQCOFF.
  assert (Hp47 : p + 20 <= 2 ^ 47 - 1)
    by (clear - HQAM C3 C4 C5; unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in *; lia).
  pose proof (HG8 0%nat ltac:(cbn [length]; lia)) as (Vdev & _).
  pose proof (HG8 3%nat ltac:(cbn [length]; lia)) as (Vcnt & _).
  cbn [nth Z.of_nat] in Vdev, Vcnt. rewrite Z.add_0_r in Vdev.
  set (xs := [d_dev d; d_counter d]).
  assert (HX33 : nth 0 xs 0 = d_dev d) by reflexivity.
  assert (HX34 : nth 1 xs 0 = d_counter d) by reflexivity.
  destruct (Z.leb_spec bits 127) as [Hb|Hb].
  + (* bits is in range *)
    assert (Hs32 : s32 bits = bits) by (unfold s32; rewrite (proj2 (Z.ltb_lt bits (2 ^ 31))) by lia; reflexivity).
    rewrite Hs32 in H11r.
    destruct (Z.leb_spec (d_dev d) 127) as [Hd|Hd].
    * destruct (Z.leb_spec (d_counter d) 127) as [Hc|Hc].
      -- (* ---------------- the command is written ---------------- *)
         assert (HAF : atoms_ok (Ereg regs (cw_extra xs)) (cl_AF 1 (2 ^ 47 - 21) 0 127 0 127 0 127)).
         { apply cl_atoms_ok; rewrite ?H10, ?H11r, ?H12, ?HX33, ?HX34, ?unsigned_lit_small by lia; lia. }
         pose proof (cw_entry_base_af B TL LAWS 0x85a7c 16 xs (cl_AF 1 (2 ^ 47 - 21) 0 127 0 127 0 127)
           STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs 16 HE ltac:(lia)
           ltac:(vm_compute; reflexivity) HAF) as HS.
         remember (Ereg regs (cw_extra xs)) as E eqn:HEE.
         assert (HAE : env_agree 32 (Ereg regs (cw_extra xs)) E) by (subst E; apply env_agree_refl).
         assert (E1 : ew E 1 = getr regs 1) by (subst E; exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
         assert (B2 : bv_unsigned (ew E 2) = spZ regs)
           by (subst E; rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); reflexivity).
         assert (E10 : ew E 10 = Z_to_bv 64 p)
           by (subst E; rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
         assert (E11 : ew E 11 = Z_to_bv 64 bits)
           by (subst E; rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11r).
         assert (E12 : ew E 12 = Z_to_bv 64 out)
           by (subst E; rewrite (ew_Ereg_nat regs _ 12 12%bv eq_refl); exact H12).
         assert (B12 : bv_unsigned (ew E 12) = out) by (rewrite E12; apply unsigned_lit_small; lia).
         assert (E32 : ew E 32 = Z_to_bv 64 SB) by (subst E; apply cw_ew_SB).
         assert (E33 : ew E 33 = Z_to_bv 64 (d_dev d)) by (subst E; rewrite cl_ew33; rewrite HX33; reflexivity).
         assert (E34 : ew E 34 = Z_to_bv 64 (d_counter d)) by (subst E; rewrite cl_ew34; rewrite HX34; reflexivity).
         clear HEE.
         assert (SHOK : sh_ok tfibsegs CW_Bx cl_SHW E (mrestrict (w_H W) memc)).
         { unfold cl_SHW. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
           - exact (cw_shent_ra_off W memc E 10 p 16 4 HQRA HQAM ltac:(lia) ltac:(lia) ltac:(lia)
                      ltac:(lia) E10 E32).
           - exact (cw_shent_cdst B STK sp0 FP ly S lyc Sc own W memc (spZ regs) 16 E 12 out 32 HDST E12 E32 ltac:(lia)). }
         assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 16 <= a < spZ regs) ->
           aview tfibsegs (w_H W) memc a = aview tfibsegs (w_H W) memc a) by (intros; reflexivity).
         (* 0x85a7c-0x85a9c: the save of ra and the shadow offset through the .got slot and its cell *)
         cw_run_to cw_awr_stk 0x85aa0. cw_keep cw_kwr_stk.
         (* the cells are dead: drop them, add the personality and the three windows of out *)
         cw_drop_gb.
         lazymatch goal with HS : YP0l.st_ok _ ?Ev ?ssv ?msv |- _ =>
           assert (Hrp : region_ok tfibsegs Ev (ms_mem msv) cl_pers);
           [ unfold region_ok, cl_pers;
             cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val
                  ms_mem restrict];
             rewrite E10, unsigned_lit_small by lia;
             split; [lia|]; split; [lia|]; split; [intros o Ho; lia|];
             apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]];
             [ apply (chunk_ok_val tfibsegs Ev _ p 16 1 (SOff 33 0) (d_dev d));
               [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |];
               apply (cw_val_mem_kept (w_H W) (w_H W) memc _); [|exact Vdev];
               intros x Hx; apply KE; [lia | cbv beta; lia]
             | apply (chunk_ok_val tfibsegs Ev _ p 19 1 (SOff 34 0) (d_counter d));
               [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |];
               apply (cw_val_mem_kept (w_H W) (w_H W) memc _);
               [ intros x Hx; apply KE; [lia | cbv beta; lia]
               | replace (p + 19) with (p + 16 + 3) by lia; exact Vcnt ] ]
           | ];
           assert (Hdp : all_disjoint Ev cl_pers (ss_mem ssv));
           [ cbn [ss_mem all_disjoint]; unfold extent_disjoint, cl_pers;
             cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite E10, B2, unsigned_lit_small by lia;
             split; [lia | exact I]
           | ];
           pose proof (ast_ok_add_region tfibsegs Ev ssv msv cl_pers HS eq_refl Hrp Hdp) as HS1;
           cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS1; clear HS Hrp Hdp; rename HS1 into HS end.
         lazymatch goal with HS : YP0l.st_ok _ ?Ev ?ssv ?msv |- _ =>
           assert (Hw0 : region_ok tfibsegs Ev (ms_mem msv) cl_out0);
           [ unfold region_ok, cl_out0;
             cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val
                  ms_mem restrict];
             rewrite E12, unsigned_lit_small by lia;
             split; [lia|]; split; [lia|]; split; [|apply Forall_nil];
             intros o Ho; apply (apresent_writable tfibsegs);
             apply (apresent_transfer tfibsegs (w_H W) (w_H W) memc _ (out + o));
             [ lia
             | intros Himg; exact (HEIMG (out + o) ltac:(unfold cenc_wr; cbv beta; lia) Himg)
             | apply KE; [lia | cbv beta; lia]
             | exact (proj1 (proj2 (HTWR (out + o) ltac:(lia)))) ]
           | ];
           assert (Hd0 : all_disjoint Ev cl_out0 (ss_mem ssv));
           [ cbn [ss_mem all_disjoint]; unfold extent_disjoint, cl_out0, cl_pers;
             cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite E10, E12, B2, !unsigned_lit_small by lia;
             unfold cpers_disj in HDISJ;
             split; [lia|]; split; [lia | exact I]
           | ];
           pose proof (ast_ok_add_region tfibsegs Ev ssv msv cl_out0 HS eq_refl Hw0 Hd0) as HS1;
           cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS1; clear HS Hw0 Hd0; rename HS1 into HS end.
         lazymatch goal with HS : YP0l.st_ok _ ?Ev ?ssv ?msv |- _ =>
           assert (Hw1 : region_ok tfibsegs Ev (ms_mem msv) cl_out1);
           [ unfold region_ok, cl_out1;
             cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val
                  ms_mem restrict];
             rewrite E12, unsigned_lit_small by lia;
             split; [lia|]; split; [lia|]; split; [|apply Forall_nil];
             intros o Ho; apply (apresent_writable tfibsegs);
             apply (apresent_transfer tfibsegs (w_H W) (w_H W) memc _ (out + o));
             [ lia
             | intros Himg; exact (HEIMG (out + o) ltac:(unfold cenc_wr; cbv beta; lia) Himg)
             | apply KE; [lia | cbv beta; lia]
             | exact (proj1 (proj2 (HTWR (out + o) ltac:(lia)))) ]
           | ];
           assert (Hd1 : all_disjoint Ev cl_out1 (ss_mem ssv));
           [ cbn [ss_mem all_disjoint]; unfold extent_disjoint, cl_out0, cl_out1, cl_pers;
             cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite E10, E12, B2, !unsigned_lit_small by lia;
             unfold cpers_disj in HDISJ;
             split; [lia|]; split; [lia|]; split; [lia | exact I]
           | ];
           pose proof (ast_ok_add_region tfibsegs Ev ssv msv cl_out1 HS eq_refl Hw1 Hd1) as HS1;
           cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS1; clear HS Hw1 Hd1; rename HS1 into HS end.
         lazymatch goal with HS : YP0l.st_ok _ ?Ev ?ssv ?msv |- _ =>
           assert (Hw2 : region_ok tfibsegs Ev (ms_mem msv) cl_out2);
           [ unfold region_ok, cl_out2;
             cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val
                  ms_mem restrict];
             rewrite E12, unsigned_lit_small by lia;
             split; [lia|]; split; [lia|]; split; [|apply Forall_nil];
             intros o Ho; apply (apresent_writable tfibsegs);
             apply (apresent_transfer tfibsegs (w_H W) (w_H W) memc _ (out + o));
             [ lia
             | intros Himg; exact (HEIMG (out + o) ltac:(unfold cenc_wr; cbv beta; lia) Himg)
             | apply KE; [lia | cbv beta; lia]
             | exact (proj1 (proj2 (HTWR (out + o) ltac:(lia)))) ]
           | ];
           assert (Hd2 : all_disjoint Ev cl_out2 (ss_mem ssv));
           [ cbn [ss_mem all_disjoint]; unfold extent_disjoint, cl_out0, cl_out1, cl_out2, cl_pers;
             cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite E10, E12, B2, !unsigned_lit_small by lia;
             unfold cpers_disj in HDISJ;
             split; [lia|]; split; [lia|]; split; [lia|]; split; [lia | exact I]
           | ];
           pose proof (ast_ok_add_region tfibsegs Ev ssv msv cl_out2 HS eq_refl Hw2 Hd2) as HS1;
           cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS1; clear HS Hw2 Hd2; rename HS1 into HS end.
         (* from here the walk writes out too: widen the kept zone *)
         lazymatch goal with KE : forall a, _ -> ~ _ -> aview _ _ ?m1 a = _ |- _ =>
           assert (KEW : forall a, 0 <= a < 2 ^ 64 ->
             ~ ((spZ regs - 16 <= a < spZ regs) \/ (out <= a < out + 7) \/
                (out + 24 <= a < out + 26) \/ (out + 28 <= a < out + 32)) ->
             aview tfibsegs (w_H W) m1 a = aview tfibsegs (w_H W) memc a)
             by (intros aa Ha Hn; apply KE; [lia | intros Hs; apply Hn; left; exact Hs]);
           clear KE; rename KEW into KE end.
         (* 0x85aa0 .. 0x85c14: the two personality bytes, the eight stores and the return *)
         cw_run cl_awr_out. cw_keep cl_kwr_out.
         (* the leaf's return address is read in the walk's base env (rreg folds the fresh atoms away) *)
         cl_lift 11%nat E11 F11. cl_lift 12%nat E12 F12.
         cl_lift 33%nat E33 F33. cl_lift 34%nat E34 F34.
         assert (BF12 : bv_unsigned (ew _ 12) = out) by (rewrite F12; apply unsigned_lit_small; lia).
         cw_leaf ltac:(idtac; cw_kept HJ0 KE ltac:(exact HEIMG)
                        ltac:(intros aa Hz; cbv beta in Hz; unfold cenc_wr; cbv beta;
                              destruct Hz as [Hz|[Hz|[Hz|Hz]]]; [left; lia | right; lia | right; lia | right; lia]))
                ltac:(idtac;
           lazymatch goal with HS : YP0l.st_ok _ ?Ev _ _ |- _ =>
             cl_region HS 12%nat 0 HR0; cl_region HS 12%nat 24 HR1; cl_region HS 12%nat 28 HR2 end;
           cl_byte HR0 BF12 0 240 Q0 ltac:(symmetry; vm_compute; reflexivity);
           cl_byte HR0 BF12 1 19 Q1 ltac:(symmetry; vm_compute; reflexivity);
           cl_byte HR0 BF12 2 (d_dev d) Q2
             ltac:(symmetry; rewrite (U_atom _ 33 (d_dev d) F33 ltac:(lia)); apply Z.mod_small; lia);
           cl_byte HR0 BF12 3 32 Q3 ltac:(symmetry; vm_compute; reflexivity);
           cl_byte HR0 BF12 4 (d_counter d) Q4
             ltac:(symmetry; rewrite (cl_U_pack _ 11 34 bits (d_counter d) F11 F34 ltac:(lia) ltac:(lia));
                   rewrite Z.add_comm, Z.mod_add by lia; apply Z.mod_small; lia);
           cl_byte HR0 BF12 5 bits Q5
             ltac:(symmetry;
                   rewrite (cl_U_srl8 _ _ (bits * 256 + d_counter d)
                             (cl_U_pack _ 11 34 bits (d_counter d) F11 F34 ltac:(lia) ltac:(lia)) ltac:(lia));
                   replace ((bits * 256 + d_counter d) / 256) with bits by (Z.div_mod_to_equations; lia);
                   apply Z.mod_small; lia);
           cl_byte HR0 BF12 6 247 Q6 ltac:(symmetry; vm_compute; reflexivity);
           cl_byte HR1 BF12 24 7 Q24 ltac:(symmetry; vm_compute; reflexivity);
           cl_byte HR1 BF12 25 0 Q25 ltac:(symmetry; vm_compute; reflexivity);
           unfold cenc_res; cbv beta;
           rewrite (cl_cmd_bytes before d bits HBlen ltac:(lia) ltac:(lia) ltac:(lia));
           rewrite (cl_spec_ok d bits ltac:(lia) ltac:(lia) ltac:(lia)); cbn [fst];
           split; [rewrite R10; apply bv_eq; vm_compute; reflexivity|];
           apply cl_garr8_cmd;
           [ reflexivity
           | rewrite cl_len_firstn by (rewrite cl_len_skipn; lia); reflexivity
           | reflexivity
           | rewrite cl_len_firstn by (rewrite cl_len_skipn; lia); reflexivity
           | intros j Hj; cbn [length] in Hj;
             destruct j as [|[|[|[|[|[|[|j]]]]]]]; cbn [nth Z.of_nat]; try lia;
             [ split; [exact Q0 | lia] | split; [exact Q1 | lia] | split; [exact Q2 | lia]
             | split; [exact Q3 | lia] | split; [exact Q4 | lia] | split; [exact Q5 | lia]
             | split; [exact Q6 | lia] ]
           | replace (out + 7) with (out + Z.of_nat 7) by (cbn [Z.of_nat]; lia);
             apply (cl_garr8_kept W memc _ (out + Z.of_nat 7) (firstn 17 (skipn 7 before)));
             [ apply cl_garr8_sub; [exact HBB | lia]
             | intros a Ha; rewrite cl_len_firstn in Ha by (rewrite cl_len_skipn; lia);
               cbn [Z.of_nat] in Ha; apply KE; [lia | cbv beta; lia] ]
           | intros j Hj; cbn [length] in Hj;
             destruct j as [|[|j]]; cbn [nth]; try lia;
             [ split; [ first [ replace (out + 24 + Z.of_nat 0) with (out + 24) by (cbn [Z.of_nat]; lia)
                              | replace (out + 24 + 0) with (out + 24) by lia | idtac ]; exact Q24 | lia]
             | split; [ first [ replace (out + 24 + Z.of_nat 1) with (out + 25) by (cbn [Z.of_nat]; lia)
                              | replace (out + 24 + 1) with (out + 25) by lia | idtac ]; exact Q25 | lia] ]
           | replace (out + 26) with (out + Z.of_nat 26) by (cbn [Z.of_nat]; lia);
             apply (cl_garr8_kept W memc _ (out + Z.of_nat 26) (firstn 2 (skipn 26 before)));
             [ apply cl_garr8_sub; [exact HBB | lia]
             | intros a Ha; rewrite cl_len_firstn in Ha by (rewrite cl_len_skipn; lia);
               cbn [Z.of_nat] in Ha; apply KE; [lia | cbv beta; lia] ]
           | lazymatch goal with HR : region_ok _ ?Ev _ (YP09.mkRegion (Some 12%nat) 28 _ _ _ ?cs) |- _ =>
               apply cl_vm4; [| apply cl_key_range; lia];
               apply (field_of_region Ev _ 12%nat out cs 28 32 28 32 28 4
                        (SAlu ALU_OR (SOff 34 0) (SLit 327680)) (KEY 5 (d_counter d)) HR BF12
                        ltac:(cbn [In]; repeat (first [left; reflexivity | right])));
               [ rewrite (denot_lit_U Ev), (cl_U_key Ev 34 (d_counter d) F34 ltac:(lia)); reflexivity
               | pose proof (cl_key_range (d_counter d) ltac:(lia)); cbn [Z.of_N]; lia
               | cbn [Z.of_N]; lia ] end ]).
      -- (* ---------------- the counter address has bit 7 set: -11 ---------------- *)
         assert (HAF : atoms_ok (Ereg regs (cw_extra xs)) (cl_AF 1 (2 ^ 47 - 21) 0 127 0 127 128 255)).
         { apply cl_atoms_ok; rewrite ?H10, ?H11r, ?H12, ?HX33, ?HX34, ?unsigned_lit_small by lia; lia. }
         pose proof (cw_entry_base_af B TL LAWS 0x85a7c 16 xs (cl_AF 1 (2 ^ 47 - 21) 0 127 0 127 128 255)
           STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs 16 HE ltac:(lia)
           ltac:(vm_compute; reflexivity) HAF) as HS.
         remember (Ereg regs (cw_extra xs)) as E eqn:HEE.
         assert (HAE : env_agree 32 (Ereg regs (cw_extra xs)) E) by (subst E; apply env_agree_refl).
         assert (E1 : ew E 1 = getr regs 1) by (subst E; exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
         assert (B2 : bv_unsigned (ew E 2) = spZ regs)
           by (subst E; rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); reflexivity).
         assert (E10 : ew E 10 = Z_to_bv 64 p)
           by (subst E; rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
         assert (E12 : ew E 12 = Z_to_bv 64 out)
           by (subst E; rewrite (ew_Ereg_nat regs _ 12 12%bv eq_refl); exact H12).
         assert (B12 : bv_unsigned (ew E 12) = out) by (rewrite E12; apply unsigned_lit_small; lia).
         assert (E32 : ew E 32 = Z_to_bv 64 SB) by (subst E; apply cw_ew_SB).
         assert (E33 : ew E 33 = Z_to_bv 64 (d_dev d)) by (subst E; rewrite cl_ew33; rewrite HX33; reflexivity).
         assert (E34 : ew E 34 = Z_to_bv 64 (d_counter d)) by (subst E; rewrite cl_ew34; rewrite HX34; reflexivity).
         clear HEE.
         assert (SHOK : sh_ok tfibsegs CW_Bx cl_SHP E (mrestrict (w_H W) memc)).
         { unfold cl_SHP. apply Forall_cons; [|apply Forall_nil].
           exact (cw_shent_ra_off W memc E 10 p 16 4 HQRA HQAM ltac:(lia) ltac:(lia) ltac:(lia)
                    ltac:(lia) E10 E32). }
         assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 16 <= a < spZ regs) ->
           aview tfibsegs (w_H W) memc a = aview tfibsegs (w_H W) memc a) by (intros; reflexivity).
         cw_run_to cw_awr_stk 0x85aa0. cw_keep cw_kwr_stk.
         cw_drop_gb. cl_add_pers E10 E33 E34 B2 KE Vdev Vcnt W memc p d.
         cw_run cw_awr_stk. cw_keep cw_kwr_stk.
         cl_fail_leaf HJ0 KE HEIMG HBB HBlen W memc out before (cl_spec_cnt d bits ltac:(lia) ltac:(lia) ltac:(lia)).
    * (* ---------------- the device byte has bit 7 set: -1 ---------------- *)
      assert (HAF : atoms_ok (Ereg regs (cw_extra xs)) (cl_AF 1 (2 ^ 47 - 21) 0 127 128 255 0 255)).
      { apply cl_atoms_ok; rewrite ?H10, ?H11r, ?H12, ?HX33, ?HX34, ?unsigned_lit_small by lia; lia. }
      pose proof (cw_entry_base_af B TL LAWS 0x85a7c 16 xs (cl_AF 1 (2 ^ 47 - 21) 0 127 128 255 0 255)
        STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs 16 HE ltac:(lia)
        ltac:(vm_compute; reflexivity) HAF) as HS.
      remember (Ereg regs (cw_extra xs)) as E eqn:HEE.
      assert (HAE : env_agree 32 (Ereg regs (cw_extra xs)) E) by (subst E; apply env_agree_refl).
      assert (E1 : ew E 1 = getr regs 1) by (subst E; exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
      assert (B2 : bv_unsigned (ew E 2) = spZ regs)
        by (subst E; rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); reflexivity).
      assert (E10 : ew E 10 = Z_to_bv 64 p)
        by (subst E; rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
      assert (E12 : ew E 12 = Z_to_bv 64 out)
        by (subst E; rewrite (ew_Ereg_nat regs _ 12 12%bv eq_refl); exact H12).
      assert (B12 : bv_unsigned (ew E 12) = out) by (rewrite E12; apply unsigned_lit_small; lia).
      assert (E32 : ew E 32 = Z_to_bv 64 SB) by (subst E; apply cw_ew_SB).
      assert (E33 : ew E 33 = Z_to_bv 64 (d_dev d)) by (subst E; rewrite cl_ew33; rewrite HX33; reflexivity).
      assert (E34 : ew E 34 = Z_to_bv 64 (d_counter d)) by (subst E; rewrite cl_ew34; rewrite HX34; reflexivity).
      clear HEE.
      assert (SHOK : sh_ok tfibsegs CW_Bx cl_SHP E (mrestrict (w_H W) memc)).
      { unfold cl_SHP. apply Forall_cons; [|apply Forall_nil].
        exact (cw_shent_ra_off W memc E 10 p 16 4 HQRA HQAM ltac:(lia) ltac:(lia) ltac:(lia)
                 ltac:(lia) E10 E32). }
      assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 16 <= a < spZ regs) ->
        aview tfibsegs (w_H W) memc a = aview tfibsegs (w_H W) memc a) by (intros; reflexivity).
      cw_run_to cw_awr_stk 0x85aa0. cw_keep cw_kwr_stk.
      cw_drop_gb. cl_add_pers E10 E33 E34 B2 KE Vdev Vcnt W memc p d.
      cw_run cw_awr_stk. cw_keep cw_kwr_stk.
      (* 0x85ae0 bltz device *)
      cl_lift 33%nat E33 F33.
      cw_branch Hb1.
      all: rewrite (cl_br_lt0_sext8 _ 33 (d_dev d) F33 ltac:(lia)) in Hb1.
      ++ (* the run to the stop made fresh atoms: restate sp for the env it reached *)
         lazymatch goal with HS : YP0l.st_ok _ ?Ev _ _ |- _ =>
           assert (B2r : bv_unsigned (ew Ev 2) = spZ regs) by (rewrite ?ew_ewset_other by lia; exact B2) end.
         cw_run cw_awr_stk. clear B2r. cw_keep cw_kwr_stk.
         cl_fail_leaf HJ0 KE HEIMG HBB HBlen W memc out before (cl_spec_dev d bits ltac:(lia) ltac:(lia)).
      ++ exfalso. apply Z.ltb_ge in Hb1. lia.
  + (* ---------------- bits is out of range: -11 ---------------- *)
    assert (HAF : atoms_ok (Ereg regs (cw_extra xs)) (cl_AF 1 (2 ^ 47 - 21) 128 (2 ^ 64 - 1) 0 255 0 255)).
    { apply cl_atoms_ok; rewrite ?H10, ?H12, ?HX33, ?HX34, ?unsigned_lit_small by lia; try lia.
      rewrite H11r, unsigned_lit; unfold zcanon, M64; apply cl_s32_hi; lia. }
    pose proof (cw_entry_base_af B TL LAWS 0x85a7c 16 xs (cl_AF 1 (2 ^ 47 - 21) 128 (2 ^ 64 - 1) 0 255 0 255)
      STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs 16 HE ltac:(lia)
      ltac:(vm_compute; reflexivity) HAF) as HS.
    remember (Ereg regs (cw_extra xs)) as E eqn:HEE.
    assert (HAE : env_agree 32 (Ereg regs (cw_extra xs)) E) by (subst E; apply env_agree_refl).
    assert (E1 : ew E 1 = getr regs 1) by (subst E; exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
    assert (B2 : bv_unsigned (ew E 2) = spZ regs)
      by (subst E; rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); reflexivity).
    assert (E10 : ew E 10 = Z_to_bv 64 p)
      by (subst E; rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
    assert (E12 : ew E 12 = Z_to_bv 64 out)
      by (subst E; rewrite (ew_Ereg_nat regs _ 12 12%bv eq_refl); exact H12).
    assert (B12 : bv_unsigned (ew E 12) = out) by (rewrite E12; apply unsigned_lit_small; lia).
    assert (E32 : ew E 32 = Z_to_bv 64 SB) by (subst E; apply cw_ew_SB).
    clear HEE.
    assert (SHOK : sh_ok tfibsegs CW_Bx cl_SHP E (mrestrict (w_H W) memc)).
    { unfold cl_SHP. apply Forall_cons; [|apply Forall_nil].
      exact (cw_shent_ra_off W memc E 10 p 16 4 HQRA HQAM ltac:(lia) ltac:(lia) ltac:(lia)
               ltac:(lia) E10 E32). }
    assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 16 <= a < spZ regs) ->
      aview tfibsegs (w_H W) memc a = aview tfibsegs (w_H W) memc a) by (intros; reflexivity).
    cw_run_to cw_awr_stk 0x85aa0. cw_keep cw_kwr_stk.
    cw_drop_gb.
    cw_run cw_awr_stk. cw_keep cw_kwr_stk.
    cl_fail_leaf HJ0 KE HEIMG HBB HBlen W memc out before (cl_spec_rng d bits ltac:(lia)).
- (* ======================= a0 is NULL: -1 ======================= *)
  cbn [pers_argA] in HPERS. subst p.
  set (xs := [0; 0]).
  assert (HX33 : nth 0 xs 0 = 0) by reflexivity.
  assert (HX34 : nth 1 xs 0 = 0) by reflexivity.
  assert (HAF : atoms_ok (Ereg regs (cw_extra xs)) (cl_AF 0 0 0 (2 ^ 64 - 1) 0 255 0 255)).
  { apply cl_atoms_ok; rewrite ?H10, ?H12, ?HX33, ?HX34, ?unsigned_lit_small by lia; try lia.
    pose proof (bv_unsigned_in_range 64 (getr regs 11)) as Hr.
    change (bv_modulus 64) with (2 ^ 64) in Hr. lia. }
  pose proof (cw_entry_base_af B TL LAWS 0x85a7c 16 xs (cl_AF 0 0 0 (2 ^ 64 - 1) 0 255 0 255)
    STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs 16 HE ltac:(lia)
    ltac:(vm_compute; reflexivity) HAF) as HS.
  remember (Ereg regs (cw_extra xs)) as E eqn:HEE.
  assert (HAE : env_agree 32 (Ereg regs (cw_extra xs)) E) by (subst E; apply env_agree_refl).
  assert (E1 : ew E 1 = getr regs 1) by (subst E; exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
  assert (B2 : bv_unsigned (ew E 2) = spZ regs)
    by (subst E; rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); reflexivity).
  assert (E10 : ew E 10 = Z_to_bv 64 0)
    by (subst E; rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
  assert (E12 : ew E 12 = Z_to_bv 64 out)
    by (subst E; rewrite (ew_Ereg_nat regs _ 12 12%bv eq_refl); exact H12).
  assert (B12 : bv_unsigned (ew E 12) = out) by (rewrite E12; apply unsigned_lit_small; lia).
  assert (E32 : ew E 32 = Z_to_bv 64 SB) by (subst E; apply cw_ew_SB).
  clear HEE.
  assert (SHOK : sh_ok tfibsegs CW_Bx (@nil shent) E (mrestrict (w_H W) memc)) by apply Forall_nil.
  assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 16 <= a < spZ regs) ->
    aview tfibsegs (w_H W) memc a = aview tfibsegs (w_H W) memc a) by (intros; reflexivity).
  (* 0x85a8c beqz a3 *)
  cw_run cw_awr_stk. cw_keep cw_kwr_stk.
  cl_lift 10%nat E10 F10.
  cw_branch Hb1.
  all: rewrite branch_eq_U, (U_atom _ 10 0 F10 ltac:(lia)), U_lit in Hb1 by lia.
  + cw_run cw_awr_stk. cw_keep cw_kwr_stk.
    cl_fail_leaf HJ0 KE HEIMG HBB HBlen W memc out before (cl_spec_none bits).
  + cbn in Hb1. discriminate.
Qed.
End d.
End b.
