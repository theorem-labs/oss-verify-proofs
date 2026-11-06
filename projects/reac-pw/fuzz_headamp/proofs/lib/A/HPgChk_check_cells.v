(* check_cells 0x84148 of fuzz_headamp.asan (unstripped sha256
   b5f352154c54a97c66fd92dfa228e8a854498f6cd313dba0107900546b043f9a; the pinned f3e0669d2819 has the same loaded
   bytes except .note.gnu.build-id), the image-A walk against lib/A/HPgCSpec.v's hd_check_cells_specX. Proves function check_cells
   (written new; the common plumbing is lib/A/HPgChkBase.v).

   THE CODE (104 words, fuzz_headamp.c:239-259). Prologue and the rc test:
     0x84148 addi sp,sp,-0x10; sd ra,8(sp); auipc a3,0x18; ld a3,0x220(a3) (the .got word 0x9c370);
     ld a3,0(a3) (the shadow-offset cell 0xa4db8: 0x7fff8000);
     0x8415c .. 0x84168 the instrumented check of x (a2) and 0x8416c lw a4,0(a2) = x->rc;
     0x84170 bne a1,a4 -> abort; 0x84174 blez a1 -> the epilogue;
     0x84178 .. 0x8418c a4 := 0, a6 := 12 rc (`slli`, `slli`, `sub`, which the engine folds to a product),
     a5 := x + 8, a7 := out + 2.
   One turn of the loop (head L 0x84190, back edge 0x84240), at index i with a4 = 12 i, a0 = out + 3 i,
   a7 = out + 3 i + 2:
     three instrumented 1-byte checks of out + 3 i + {0, 1, 2} (0x84190, 0x841cc, 0x84200; slow arms 0x84244,
     0x84260, 0x8427c) with their `lbu` at a7 - 2, a7 - 1, a7 + 0;
     three instrumented 4-byte checks of x + 4 + 12 i + {0, 4, 8} (0x841a8, 0x841e0, 0x84214; slow arms 0x84250,
     0x8426c, 0x84288) with their `lw` at t1 - 4, t1 + 0, t1 + 4 (t1 = a5 + a4 = x + 8 + 12 i);
     the three comparisons 0x841c4, 0x841f8, 0x8422c -> abort 0x842a8;
     0x84230 .. 0x84238 a4 += 12, a0 += 3, a7 += 3; 0x8423c beq a6,a4 -> the epilogue; 0x84240 j L.
   Epilogue 0x8429c ld ra,8(sp); addi sp,sp,0x10; 0x842a4 ret. Abort 0x842a8 jal the no-return helper; jal abort.
   The only store of the whole function is `sd ra,8(sp)` into the save slot [sp - 16, sp).

   WHY THE ABORT IS UNREACHABLE. 0x84170 compares rc (a1) with the sign-extended word at x, which the contract
   fixes as rc mod 2^32 with -2^31 <= rc <= 10, so the two are the same 64-bit value and the `bne` is not taken.
   Inside the loop each comparison is a `lw` of x->cell[i].f against a `lbu` of out[3 i + f]: the contract's two
   garr8 premises give both from the same cell list cs (Spec/HeadBytes.v x_cells_bytes / ha_cells_bytes) and
   cell_bytes_ok makes each field a byte, so the two values are equal and no `bne` is taken.
   WHY NO REPORT CALL IS REACHED. The shadow entry of x + 4 + 12 i covers twelve bytes, so the engine reads each
   of the three 4-byte checks' shadow bytes as zero; the shadow entry of out + 3 i covers three bytes, so each
   1-byte check goes through the token engine, which continues at the `lbu` on both arms of the `bnez` - the slow
   arm included, which is live because out's last granule is partial. Both entries come from the contract's
   range_addressable and hd_app_rng premises.
   THE LOOP IS CLOSED BY ITS COUNTER. The walk is cut at the loop head: one turn goes from the head at i to the
   head at i + 1 or to the epilogue, and YA0n.SRr_loopZ closes it on the measure rc - i, which drops at every turn
   and stays non-negative because the exit test `beq a6,a4` is 12 rc = 12 (i + 1).
   WHAT THE WALK NEEDS BESIDES THE CONTRACT. The two Section hypotheses HBgot and HBcell name this image's .got
   word and shadow-offset cell in the symbol record, as role's parse walk does (lib/A/RPgParseE.v). Everything else
   is the contract's text. *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YI16 YM05 YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Lib Require Import Mem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Import Headamp.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Spec Require Import HeadBytes.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import Img0 HPgBase HPgCSpec HPgChkBase HPgMem.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

Definition A_CHECK_CELLS : Z := 0x84148.
Definition PC_LH : Z := 0x84190.
Definition PC_RET : Z := 0x842a4.
(* the 104 words 0x84148 .. 0x842e4 (the six slow arms and the abort block included) *)
Definition cc_tbl : ctable := Eval vm_compute in (build_table rsegs A_CHECK_CELLS 104 TEmpty).
Lemma cc_tbl_eq : cc_tbl = build_table rsegs A_CHECK_CELLS 104 TEmpty.
Proof. vm_cast_no_check (eq_refl cc_tbl). Qed.
Lemma cc_tbl_ok : table_ok rsegs cc_tbl.
Proof. rewrite cc_tbl_eq. apply build_table_ok0. unfold A_CHECK_CELLS. lia. Qed.

(* ===================================== the entry states ===================================== *)
(* the prologue's: the word at x (env slot 12) holds rc mod 2^32 (env slot 33) *)
Definition cc_rsP : smem := [hc_data 12 0 4 [YP09.mkChunk 0 (CVal 4 (SOff 33 0))]].
Definition cc_fsP : list (nat * afact) := [hc_pfact 12 2; (33%nat, mkAF 0 (2 ^ 32 - 1) 0)].
Definition cc_SHP : list shent := [mkSHE 12 0 4].
(* the loop head's: the save slot with the saved ra, cell i of x (slot 33 = x + 4 + 12 i; slots 34, 35, 36 its
   three words) and cell i of out at a7 (slot 17 = out + 3 i + 2; slots 37, 38, 39 its three bytes) *)
Definition cc_stk_ra : YP09.region := YP09.mkRegion (Some 2%nat) 0 16 0 0 [YP09.mkChunk 8 (CVal 8 (SOff 1 0))].
Definition cc_xcell : YP09.region := YP09.mkRegion (Some 33%nat) 0 12 0 0
  [YP09.mkChunk 0 (CVal 4 (SOff 34 0)); YP09.mkChunk 4 (CVal 4 (SOff 35 0)); YP09.mkChunk 8 (CVal 4 (SOff 36 0))].
Definition cc_ocell : YP09.region := YP09.mkRegion (Some 17%nat) (-2) 1 0 0
  [YP09.mkChunk (-2) (CVal 1 (SOff 37 0)); YP09.mkChunk (-1) (CVal 1 (SOff 38 0)); YP09.mkChunk 0 (CVal 1 (SOff 39 0))].
(* `add t0,a2,a4` and `add t1,a5,a4` are cell i's base minus 4 and plus 4 *)
Definition cc_alias : list (sv * sv) :=
  [ (SAlu ALU_ADD (SOff 12 0) (SOff 14 0), SOff 33 (-4));
    (SAlu ALU_ADD (SOff 15 0) (SOff 14 0), SOff 33 4) ].
Definition cc_fsL : list (nat * afact) :=
  [hc_pfact 10 0; hc_pfact 17 0; hc_pfact 33 2;
   (34%nat, mkAF 0 (2 ^ 32 - 1) 0); (35%nat, mkAF 0 (2 ^ 32 - 1) 0); (36%nat, mkAF 0 (2 ^ 32 - 1) 0);
   (37%nat, mkAF 0 255 0); (38%nat, mkAF 0 255 0); (39%nat, mkAF 0 255 0);
   (14%nat, mkAF 0 108 0); (16%nat, mkAF 0 120 0)].
Definition cc_SHL : list shent := [mkSHE 33 0 12; mkSHE 10 0 3].
Definition ss_cc_L : sstate :=
  mkSS PC_LH (hc_sr [((13%bv : bv 5), hc_Bx)]) [cc_stk_ra; cc_xcell; cc_ocell] None
    (mkFacts ((2%nat, mkAF (2 ^ 46) (2 ^ 47) 4) :: (32%nat, mkAF hc_SB hc_SB 0) :: cc_fsL) [] cc_alias).

(* ===================================== arithmetic ===================================== *)
Lemma cc_u64 : forall w : word, 0 <= bv_unsigned w < 2 ^ 64.
Proof. intros w. pose proof (bv_unsigned_in_range _ w) as Hb. change (bv_modulus 64) with (2 ^ 64) in Hb. exact Hb. Qed.
Lemma cc_denot_atom : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> sv_denot E (SOff n 0) = Z_to_bv 64 v.
Proof.
intros E n v H Hv. apply bv_eq. rewrite denot_SOff, H, Z.add_0_r.
rewrite !unsigned_lit_small by exact Hv. apply zcanon_id. unfold M64. lia.
Qed.
(* the index of a register, as aregs_preserved writes it and as the states hold it *)
Lemma cc_sp_idx : forall (rg : bvmap 5 word), getr rg (Z_to_bv 5 2) = getr rg (2%bv : bv 5).
Proof. intros rg. f_equal. Qed.
(* the env slot 33 + j of the walk's extra values (HPgChkBase gives only slots 32 and 33) *)
Lemma cc_Eextra : forall regs xs j, ew (Ereg regs (hc_extra xs)) (33 + j) = Z_to_bv 64 (nth j xs 0).
Proof.
intros regs xs j. unfold hc_extra. replace (33 + j)%nat with (32 + S j)%nat by lia.
rewrite ew_Ereg_extra. exact (map_nth (Z_to_bv 64) (hc_SB :: xs) 0 (S j)).
Qed.
(* the callee-saved registers other than sp, as the walk's states keep them *)
Definition CC_CS : list (bv 5) := [3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.
Lemma cc_cs_in : forall r : Z,
r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27 -> In (Z_to_bv 5 r) CC_CS.
Proof.
intros r H. unfold CC_CS. cbn [In].
repeat (destruct H as [->|H]); try subst r;
repeat (first [ left; apply bv_eq; reflexivity | right ]).
Qed.
Lemma cc_U_wrap : forall E n v, ew E n = Z_to_bv 64 v -> U E (SOff n 0) = v mod 2 ^ 64.
Proof.
intros E n v H. rewrite U_SOff, H, Z.add_0_r, Z_to_bv_unsigned.
unfold zcanon, M64, bv_wrap, bv_modulus. cbn [Z.of_N]. apply Zmod_mod.
Qed.
Lemma cc_Sg_off : forall E n v, ew E n = Z_to_bv 64 v -> - 2 ^ 63 <= v < 2 ^ 63 -> Sg E (SOff n 0) = v.
Proof.
intros E n v H Hv. rewrite S_SOff, H, Z.add_0_r, Z_to_bv_unsigned.
unfold bv_swrap. change (bv_half_modulus 64) with (2 ^ 63). unfold bv_wrap.
change (bv_modulus 64) with (2 ^ 64).
rewrite Zplus_mod_idemp_l. rewrite (Z.mod_small (v + 2 ^ 63)) by lia. lia.
Qed.
Lemma cc_branch_ge : forall E a b, branch_taken BC_GE (sv_denot E a) (sv_denot E b) = negb (Sg E a <? Sg E b).
Proof. intros E a b. cbn [branch_taken]. unfold bv_lts, Sg. reflexivity. Qed.
Lemma cc_Sg_lit : forall E, Sg E (SLit 0) = 0.
Proof. intros E. rewrite S_SLit. reflexivity. Qed.
(* the sign-extended 32-bit load of a value the contract gives modulo 2^32 *)
Lemma cc_U_sx32 : forall E n v, ew E n = Z_to_bv 64 (v mod 2 ^ 32) -> - 2 ^ 31 <= v < 2 ^ 31 ->
U E (SExt true 32 (SOff n 0)) = v mod 2 ^ 64.
Proof.
intros E n v Hn Hv.
assert (Hm : 0 <= v mod 2 ^ 32 < 2 ^ 32) by (apply Z.mod_pos_bound; lia).
rewrite U_SExt, (U_atom E n (v mod 2 ^ 32) Hn) by lia.
change (2 ^ Z.of_N 32) with (2 ^ 32). rewrite (Z.mod_small (v mod 2 ^ 32)) by lia.
unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2 ^ 31). change (bv_modulus 32) with (2 ^ 32).
assert (Hv32 : v mod 2 ^ 32 = if v <? 0 then v + 2 ^ 32 else v).
{ destruct (Z.ltb_spec v 0).
  - replace v with ((v + 2 ^ 32) + (-1) * 2 ^ 32) at 1 by ring. rewrite Z.mod_add by lia.
    apply Z.mod_small. lia.
  - apply Z.mod_small. lia. }
rewrite Hv32. destruct (Z.ltb_spec v 0).
- replace (v + 2 ^ 32 + 2 ^ 31) with ((v + 2 ^ 31) + 1 * 2 ^ 32) by ring. rewrite Z.mod_add by lia.
  rewrite (Z.mod_small (v + 2 ^ 31)) by lia.
  replace (v + 2 ^ 31 - 2 ^ 31) with v by ring. unfold zcanon, M64. reflexivity.
- rewrite (Z.mod_small (v + 2 ^ 31)) by lia.
  replace (v + 2 ^ 31 - 2 ^ 31) with v by ring. unfold zcanon, M64. reflexivity.
Qed.
Lemma cc_U_sx32_small : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 31 ->
U E (SExt true 32 (SOff n 0)) = v.
Proof.
intros E n v Hn Hv. rewrite (cc_U_sx32 E n v); [apply Z.mod_small; lia | rewrite (Z.mod_small v (2 ^ 32)) by lia; exact Hn | lia].
Qed.
Section h. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
(* a register the state holds as an atom plus a constant, as a 64-bit word *)
Lemma cc_getr_off : forall (E : env) ss ms (H : word -> bool) (r : bv 5) (n : nat) (c v : Z),
st_ok rsegs E ss (restrict H ms) -> sr_get (ss_regs ss) r = SOff n c ->
bv_unsigned (ew E n) = v -> 0 <= v + c < 2 ^ 64 -> getr (ms_regs ms) r = w64 (v + c).
Proof.
intros E ss ms H r n c v HS Hsr Hew Hv. apply bv_eq.
rewrite (st_ok_restrict_reg rsegs H E ss ms r HS), Hsr, denot_SOff, Hew.
rewrite zcanon_id by (unfold M64; lia). symmetry. apply unsigned_lit_small. lia.
Qed.
Lemma cc_getr_lit : forall (E : env) ss ms (H : word -> bool) (r : bv 5) (v : Z),
st_ok rsegs E ss (restrict H ms) -> sr_get (ss_regs ss) r = SLit v -> 0 <= v < 2 ^ 64 ->
getr (ms_regs ms) r = w64 v.
Proof.
intros E ss ms H r v HS Hsr Hv.
rewrite (st_ok_restrict_reg rsegs H E ss ms r HS), Hsr. apply hc_lit.
Qed.
(* `slli`, `slli`, `sub` folded to a product: a6 = 12 rc *)
Lemma cc_getr_mul : forall (E : env) ss ms (H : word -> bool) (r : bv 5) (n : nat) (v : Z),
st_ok rsegs E ss (restrict H ms) -> sr_get (ss_regs ss) r = SMd M_MUL (SOff n 0) (SLit 12) ->
ew E n = Z_to_bv 64 v -> 0 <= v <= 10 -> getr (ms_regs ms) r = w64 (12 * v).
Proof.
intros E ss ms H r n v HS Hsr Hew Hv. apply bv_eq.
rewrite (st_ok_restrict_reg rsegs H E ss ms r HS), Hsr.
change (bv_unsigned (sv_denot E (SMd M_MUL (SOff n 0) (SLit 12)))) with (U E (SMd M_MUL (SOff n 0) (SLit 12))).
rewrite U_SMd. cbn [zmd_raw]. rewrite (U_atom E n v Hew) by lia.
rewrite U_SLit. rewrite (zcanon_id 12) by (unfold M64; lia).
rewrite zcanon_id by (unfold M64; lia). symmetry.
rewrite Z.mul_comm. apply unsigned_lit_small. lia.
Qed.

(* ===================================== two intervals apart ===================================== *)
Lemma cc_disj_ptw : forall p n q m, 0 < n -> 0 < m ->
(forall a, p <= a < p + n -> ~ (q <= a < q + m)) -> p + n <= q \/ q + m <= p.
Proof.
intros p n q m Hn Hm H.
destruct (Z_le_gt_dec (p + n) q) as [|H1]; [left; lia|].
destruct (Z_le_gt_dec (q + m) p) as [|H2]; [right; lia|].
exfalso. apply (H (Z.max p q)); lia.
Qed.

(* ===================================== the cell lists ===================================== *)
Definition cc_ch (c : cell) : Z := fst (fst c).
Definition cc_pa (c : cell) : Z := snd (fst c).
Definition cc_va (c : cell) : Z := snd c.
Definition cc_c0 : cell := (0, 0, 0).
Lemma cc_len_xcell : forall c, length (x_cell_bytes c) = 12%nat.
Proof. intros [[a b] d]. unfold x_cell_bytes. rewrite !length_app, !length_le4. reflexivity. Qed.
Lemma cc_len_hacell : forall c, length (ha_cell_bytes c) = 3%nat.
Proof. intros [[a b] d]. reflexivity. Qed.
Lemma cc_nth_skipn : forall (l : list byte) m k d, nth k (skipn m l) d = nth (m + k) l d.
Proof.
intros l m. revert l. induction m as [|m IH]; intros l k d; [reflexivity|].
destruct l as [|a l]; cbn [skipn nth]; [destruct k; reflexivity | apply IH].
Qed.
Lemma cc_skipn_add : forall (l : list byte) a b, skipn (a + b) l = skipn b (skipn a l).
Proof.
intros l a. revert l. induction a as [|a IH]; intros l b; [reflexivity|].
destruct l as [|y l]; cbn [skipn]; [destruct b; reflexivity | apply IH].
Qed.
Lemma cc_firstn4 : forall (u v : list byte), length u = 4%nat -> firstn 4 (u ++ v) = u.
Proof.
intros u v H. rewrite firstn_app, H, Nat.sub_diag, firstn_O, app_nil_r. apply firstn_all2. lia.
Qed.
Lemma cc_skipn_app_len : forall (u v : list byte) n, length u = n -> skipn n (u ++ v) = v.
Proof. intros u v n <-. induction u as [|a u IH]; cbn [length app skipn]; [reflexivity | exact IH]. Qed.
Lemma cc_skip_flat : forall (f : cell -> list byte) (n : nat), (forall c, length (f c) = n) ->
forall (cs : list cell) (i : nat), (i < length cs)%nat ->
skipn (n * i) (flat_map f cs) = f (nth i cs cc_c0) ++ flat_map f (skipn (S i) cs).
Proof.
intros f n Hn cs. induction cs as [|c cs IH]; intros i Hi; cbn [length] in Hi; [lia|].
destruct i as [|i]; cbn [flat_map nth skipn].
- rewrite Nat.mul_0_r. reflexivity.
- replace (n * S i)%nat with (n + n * i)%nat by lia. rewrite cc_skipn_add.
  rewrite (cc_skipn_app_len (f c) (flat_map f cs) n (Hn c)).
  apply IH. cbn [length] in Hi. lia.
Qed.
Lemma cc_nth_flat : forall (f : cell -> list byte) (n : nat), (forall c, length (f c) = n) ->
forall (cs : list cell) (i k : nat) (z : byte), (i < length cs)%nat -> (k < n)%nat ->
nth (n * i + k) (flat_map f cs) z = nth k (f (nth i cs cc_c0)) z.
Proof.
intros f n Hn cs i k z Hi Hk.
rewrite <- (cc_nth_skipn (flat_map f cs) (n * i) k z), (cc_skip_flat f n Hn cs i Hi).
rewrite app_nth1 by (rewrite Hn; exact Hk). reflexivity.
Qed.
(* the three 4-byte fields of cell i inside x_cells_bytes *)
Lemma cc_xslice : forall (cs : list cell) (i : nat), (i < length cs)%nat ->
hm_slice (x_cells_bytes cs) (12 * i) 4 = Z_to_le_bytes 4 (bv_unsigned (Z_to_bv 64 (cc_ch (nth i cs cc_c0)))) /\
hm_slice (x_cells_bytes cs) (12 * i + 4) 4 = Z_to_le_bytes 4 (bv_unsigned (Z_to_bv 64 (cc_pa (nth i cs cc_c0)))) /\
hm_slice (x_cells_bytes cs) (12 * i + 8) 4 = Z_to_le_bytes 4 (bv_unsigned (Z_to_bv 64 (cc_va (nth i cs cc_c0)))).
Proof.
intros cs i Hi. unfold hm_slice, x_cells_bytes.
rewrite (cc_skip_flat x_cell_bytes 12 cc_len_xcell cs i Hi).
set (c := nth i cs cc_c0). set (r := flat_map x_cell_bytes (skipn (S i) cs)).
assert (Hc : x_cell_bytes c = le4 (Z_to_bv 64 (cc_ch c)) ++ le4 (Z_to_bv 64 (cc_pa c)) ++ le4 (Z_to_bv 64 (cc_va c)))
  by (unfold c, cc_ch, cc_pa, cc_va; destruct (nth i cs cc_c0) as [[a b] d]; reflexivity).
split; [|split].
- rewrite Hc, <- !app_assoc. apply cc_firstn4. apply length_le4.
- rewrite (cc_skipn_add _ (12 * i) 4), (cc_skip_flat x_cell_bytes 12 cc_len_xcell cs i Hi).
  fold c. fold r. rewrite Hc, <- !app_assoc.
  rewrite (cc_skipn_app_len _ _ 4 (length_le4 _)).
  apply cc_firstn4. apply length_le4.
- rewrite (cc_skipn_add _ (12 * i) 8), (cc_skip_flat x_cell_bytes 12 cc_len_xcell cs i Hi).
  fold c. fold r. rewrite Hc, <- !app_assoc.
  rewrite (app_assoc (le4 (Z_to_bv 64 (cc_ch c))) (le4 (Z_to_bv 64 (cc_pa c)))).
  rewrite (cc_skipn_app_len _ _ 8 ltac:(rewrite length_app, !length_le4; reflexivity)).
  apply cc_firstn4. apply length_le4.
Qed.
Lemma cc_onth : forall (cs : list cell) (i : nat), (i < length cs)%nat ->
nth (3 * i + 0) (ha_cells_bytes cs) (Z_to_bv 8 0) = Z_to_bv 8 (cc_ch (nth i cs cc_c0)) /\
nth (3 * i + 1) (ha_cells_bytes cs) (Z_to_bv 8 0) = Z_to_bv 8 (cc_pa (nth i cs cc_c0)) /\
nth (3 * i + 2) (ha_cells_bytes cs) (Z_to_bv 8 0) = Z_to_bv 8 (cc_va (nth i cs cc_c0)).
Proof.
intros cs i Hi. unfold ha_cells_bytes.
split; [|split].
- rewrite (cc_nth_flat ha_cell_bytes 3 cc_len_hacell cs i 0 _ Hi ltac:(lia)).
  unfold cc_ch. destruct (nth i cs cc_c0) as [[a b] d]. reflexivity.
- rewrite (cc_nth_flat ha_cell_bytes 3 cc_len_hacell cs i 1 _ Hi ltac:(lia)).
  unfold cc_pa. destruct (nth i cs cc_c0) as [[a b] d]. reflexivity.
- rewrite (cc_nth_flat ha_cell_bytes 3 cc_len_hacell cs i 2 _ Hi ltac:(lia)).
  unfold cc_va. destruct (nth i cs cc_c0) as [[a b] d]. reflexivity.
Qed.

(* a register the state holds as a plain atom *)
Lemma cc_getr_same : forall (E : env) ss ms (H : word -> bool) (r : bv 5) (n : nat) (w : word),
st_ok rsegs E ss (restrict H ms) -> sr_get (ss_regs ss) r = SOff n 0 -> ew E n = w ->
getr (ms_regs ms) r = w.
Proof.
intros E ss ms H r n w HS Hsr Hew. apply bv_eq.
rewrite (st_ok_restrict_reg rsegs H E ss ms r HS), Hsr, denot_SOff, Hew, Z.add_0_r.
apply zcanon_id. pose proof (bv_unsigned_in_range _ w) as Hb.
change (bv_modulus 64) with (2 ^ 64) in Hb. unfold M64. lia.
Qed.
(* the 8-byte value a region's chunk holds, as the save slot keeps the caller's ra *)
Lemma cc_chunk8_val : forall (E : env) ss ms (H : word -> bool) (r : YP09.region) (b off : Z) (n : nat) (w : word),
st_ok rsegs E ss (restrict H ms) -> In r (ss_mem ss) -> YP09.r_base r = Some n ->
In (YP09.mkChunk off (CVal 8 (SOff 1 0))) (YP09.r_chunks r) ->
bv_unsigned (ew E n) = b -> ew E 1 = w ->
val_mem rsegs (mrestrict H (ms_mem ms)) (b + off) 8 (bv_unsigned w).
Proof.
intros E ss ms H r b off n w HS Hin Hb Hc Hbv Hw.
destruct (st_ok_mem_ok rsegs E ss (restrict H ms) HS) as (_ & Hrs & _).
pose proof (proj1 (Forall_forall _ _) Hrs r Hin) as HR.
unfold region_ok in HR. rewrite Hb in HR. cbn [base_val] in HR. rewrite Hbv in HR.
destruct HR as (_ & _ & _ & Hcs).
pose proof (proj1 (Forall_forall _ _) Hcs _ Hc) as Hck.
pose proof (bv_unsigned_in_range _ w) as Hwr. change (bv_modulus 64) with (2 ^ 64) in Hwr.
exact (val_of_chunk_ok rsegs E (mrestrict H (ms_mem ms)) b off 8 (SOff 1 0) (bv_unsigned w) Hck
  ltac:(apply bv_eq; rewrite denot_SOff, Hw, Z.add_0_r; rewrite unsigned_lit_small by lia;
        apply zcanon_id; unfold M64; lia)
  ltac:(change (8 * Z.of_N 8) with 64; lia) ltac:(cbn; lia)).
Qed.
End h.

(* ---- the tactics of this walk (lib/A/HPgChkBase.v's, with a stop pc) ---- *)
Ltac cc_run_to stop :=
lazymatch goal with HS : st_ok _ _ _ _, HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, SHOK : sh_ok _ _ _ _ _ |- _ =>
aj_run_to_tok cc_tbl_ok HS HJ SHOK hc_Bspan stop end; [hc_awr | ].
(* HPgChkBase's branch split, with the condition named on both sides *)
Ltac cc_branch Hname :=
hc_branch cc_tbl_ok; lazymatch goal with Hb : branch_taken _ _ _ = _ |- _ => rename Hb into Hname end.
Ltac cc_io := let rec kio := first [apply same_io_refl | assumption | eapply same_io_trans; [| apply hc_same_io_wvb]; kio] in kio.
(* a fact about the entry env, at the env a run leaves *)
Ltac cc_ew Hsrc Q :=
lazymatch type of Hsrc with ew _ ?n = ?v =>
lazymatch goal with HS : st_ok _ ?Ec _ _ |- _ =>
assert (Q : ew Ec n = v) by (repeat (rewrite ew_ewset_other by lia); exact Hsrc) end end.
Ltac cc_bu Hsrc Q :=
lazymatch type of Hsrc with bv_unsigned (ew _ ?n) = ?v =>
lazymatch goal with HS : st_ok _ ?Ec _ _ |- _ =>
assert (Q : bv_unsigned (ew Ec n) = v) by (repeat (rewrite ew_ewset_other by lia); exact Hsrc) end end.
(* a register at the stop, as the engine's symbolic value *)
Ltac cc_reg HS r Q :=
lazymatch type of HS with st_ok ?segs ?E ?ss (restrict ?H ?ms) =>
let e := eval vm_compute in (sr_get (ss_regs ss) r) in
assert (Q : getr (ms_regs ms) r = sv_denot E e) by exact (st_ok_restrict_reg segs H E ss ms r HS) end.

(* ===================================== the walk ===================================== *)
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis HBgot : as_got_shadow B = HC_GOT_SH.
Hypothesis HBcell : as_shadow_cell B = HC_SH_CELL.

(* the callee-saved registers other than sp, which the loop head holds 16 below the caller's *)
Definition cc_cs_keep (r1 r2 : bvmap 5 word) : Prop :=
forall r, acallee_saved r -> r <> 2 -> getr r2 (Z_to_bv 5 r) = getr r1 (Z_to_bv 5 r).
Lemma cc_apres_trans : forall r1 r2 r3, aregs_preserved r1 r2 -> aregs_preserved r2 r3 -> aregs_preserved r1 r3.
Proof. intros r1 r2 r3 H1 H2 r Hr. rewrite (H2 r Hr). exact (H1 r Hr). Qed.
(* a range off the callee's stack window lies wholly below or above it *)
Lemma cc_off_disj : forall (regs : bvmap 5 word) p n, 0 < n -> hd_off_stack regs T_check_STK p n ->
p + n <= spZ regs - 32 \/ spZ regs <= p.
Proof.
intros regs p n Hn H. unfold hd_off_stack, T_check_STK in H.
destruct (Z_le_gt_dec (p + n) (spZ regs - 32)) as [|H1]; [left; lia|].
destruct (Z_le_gt_dec (spZ regs) p) as [|H2]; [right; lia|].
exfalso. apply (H (Z.max p (spZ regs - 32))); lia.
Qed.

(* the cut at the loop head, at index i *)
Definition cc_inv (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world rsegs)
(mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z)) (lyc : alayout) (Sc : astate)
(W : world rsegs) (memc : word -> option byte) (mdc : Model) (k : Z) (regs : bvmap 5 word)
(o rcc x : Z) (cs : list cell) (i : Z) : world rsegs -> config -> Prop :=
fun W2 c2 => exists regs2 mem2 md2,
c2 = cfg_at rsegs PC_LH regs2 mem2 md2 /\
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W2 mem2 md2 k /\
same_io mdc md2 /\
cc_cs_keep regs regs2 /\
getr regs2 (1%bv : bv 5) = getr regs (1%bv : bv 5) /\
spZ regs2 = spZ regs - 16 /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - T_check_STK <= a < spZ regs) ->
 aview rsegs (w_H W2) mem2 a = aview rsegs (w_H W) memc a) /\
val_mem rsegs (mrestrict (w_H W2) mem2) (spZ regs2 + 8) 8 (bv_unsigned (getr regs (1%bv : bv 5))) /\
0 <= i < rcc /\
getr regs2 (10%bv : bv 5) = w64 (o + 3 * i) /\
getr regs2 (12%bv : bv 5) = w64 x /\
getr regs2 (13%bv : bv 5) = w64 SHADOW_OFF /\
getr regs2 (14%bv : bv 5) = w64 (12 * i) /\
getr regs2 (15%bv : bv 5) = w64 (x + 8) /\
getr regs2 (16%bv : bv 5) = w64 (12 * rcc) /\
getr regs2 (17%bv : bv 5) = w64 (o + 3 * i + 2) /\
hm_bytes rsegs (w_H W2) mem2 o (ha_cells_bytes cs) /\
hm_bytes rsegs (w_H W2) mem2 (x + 4) (x_cells_bytes cs) /\
range_addressable (aview rsegs (w_H W2) mem2) SHADOW_OFF o (3 * rcc) /\
range_addressable (aview rsegs (w_H W2) mem2) SHADOW_OFF (x + 4) (12 * rcc).

(* the `ret` leaf into HPgCSpec's hd_post at fx2 = fx, E = False, R = True, the blocks and frames as at the call
   (lib/A/HPgChkBase.v hc_leaf's conjuncts, as a lemma, so that the loop's exit can supply sp and the
   callee-saved registers through the cut) *)
Lemma cc_post_of : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
(W2 : world rsegs) (regs2 : bvmap 5 word) (mem2 : word -> option byte) (pc : word) (md2 : Model),
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W2 mem2 md2 k ->
same_io mdc md2 ->
aregs_preserved regs regs2 ->
getr regs2 (1%bv : bv 5) = getr regs (1%bv : bv 5) ->
pc = getr regs (1%bv : bv 5) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - T_check_STK <= a < spZ regs) ->
 aview rsegs (w_H W2) mem2 a = aview rsegs (w_H W) memc a) ->
ameter_laws MT ->
hd_post rsegs B MT STK sp0 FP ly S W0 mem0 md0 own k T_check_STK regs lyc Sc W memc mdc
  (fun f => f = fx) (fun _ => False) (fun _ _ _ => True) W2 (mkCfg (mkst regs2 pc mem2 (seg_rom rsegs)) md2).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs W2 regs2 mem2 pc md2 HJ Hio Hap Hra1 Hpc HK HMT.
red. exists fx, lyc, Sc, regs2, mem2, md2.
split; [rewrite Hpc; reflexivity|].
split; [reflexivity|].
split; [exact HJ|].
split; [exact Hap|].
split; [exact Hra1|].
split; [reflexivity|].
split; [apply Permutation_refl|].
split; [exact Hio|].
split; [apply mo_le_refl; exact HMT|].
split; [intros a Ha Hz _; exact (HK a Ha Hz) | exact I].
Qed.

Theorem hd_check_cells_A : hd_check_cells_specX rsegs B MT A_CHECK_CELLS.
Proof using MTL HBgot HBcell.
unfold hd_check_cells_specX, hd_pre.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs rcc o x cs
(HJ & Hra & Hra4 & Hgp & Htp & Hal16 & Hwlo & Hwhi & Hev) H10 H11 H12 Hrcc Vx RAx OSx (Happx & Himgx) Hx4 Hpos.
pose proof (AR_laws_ok rsegs B) as LAWS.
pose proof hc_wx as Hwx. pose proof hc_segs_low as Hsegs.
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & _).
destruct (al_const _ _ LAWS lyc Sc W memc mdc HAR) as (Kcell & _ & Kgot & _).
rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell.
unfold T_check_STK in Hwlo.
destruct (hc_app_fact x 4 Happx ltac:(lia)) as (Hx0 & Hx1 & Hx2).
destruct (hc_app_apart x 4 Himgx ltac:(lia)) as [Dgotx Dcellx].
unfold ASAN_CEIL in Hx1.
assert (Hsp : 2 ^ 46 <= spZ regs <= 2 ^ 47) by lia.
assert (Hpr : forall a, spZ regs - 16 <= a < spZ regs -> apresent (w_H W) memc a)
  by (intros a Ha; apply Hpres; lia).
assert (Dstkx : x + 4 <= spZ regs - 16 \/ spZ regs <= x)
  by (destruct (cc_off_disj regs x 4 ltac:(lia) OSx); lia).
unfold HC_PHI in Hx2.

(* the shadow byte of an application address lies far below the save slot *)
assert (SHOFF : forall p n a, in_app p n -> 0 <= n -> p <= a < p + n ->
  ~ (spZ regs - 32 <= shadow_of_addr SHADOW_OFF a < spZ regs)).
{ intros p n a Hap Hn Ha Hbad.
  destruct (hc_app_fact p n Hap Hn) as (Hp0 & Hp1 & Hp2).
  unfold ASAN_CEIL, HC_PHI in Hp1, Hp2.
  apply (hm_shadow_not_high a (spZ regs - 32)); [ unfold kHighMemEnd; lia | unfold kHighMemBeg; lia | lia ]. }

(* ----------------------------------- one turn of the loop ----------------------------------- *)
assert (LOOP : forall (i : Z) (W2 : world rsegs) (c2 : config),
  cc_inv STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs o rcc x cs i W2 c2 ->
  SRr rsegs W2 c2 (fun W3 c3 =>
    hd_post rsegs B MT STK sp0 FP ly S W0 mem0 md0 own k T_check_STK regs lyc Sc W memc mdc
      (fun f => f = fx) (fun _ => False) (fun _ _ _ => True) W3 c3 \/
    exists i', 0 <= rcc - i' < rcc - i /\
      cc_inv STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs o rcc x cs i' W3 c3)).
{ intros i W2 c2 HI. unfold cc_inv in HI.
  destruct HI as (regs2 & mem2 & md2 & Hcfg & HJ2 & Hio2 & Hcs2 & Hra2 & Hsp2 & KEinv & Hslot &
    Hi & Q10 & Q12 & Q13 & Q14 & Q15 & Q16 & Q17 & Bout & Bx4 & RAo2 & RAx42).
  clear Dgotx Dcellx Dstkx HJ.
  destruct (Hpos ltac:(lia)) as (Hlen & Hbok & Ho0 & Ho1 & Hxa & Hxb & Gout & RAo & OSo & APo & Gx4 & RAx4 & OSx4 & APx4 & Hdisj).
  destruct APo as (Happo & Himgo). destruct APx4 as (Happx4 & Himgx4).
  destruct (hc_app_fact o (3 * rcc) Happo ltac:(lia)) as (Ho4096 & Hohi & Hceil2).
  destruct (hc_app_fact (x + 4) (12 * rcc) Happx4 ltac:(lia)) as (Hx4096 & Hxhi & _).
  unfold ASAN_CEIL, HC_PHI in Hohi, Hxhi, Hceil2.
  (* the cell at index i *)
  assert (Hin : (Z.to_nat i < length cs)%nat) by lia.
  set (c := nth (Z.to_nat i) cs cc_c0).
  assert (Hcok : cell_bytes_ok c) by (unfold c; apply (proj1 (Forall_forall _ _) Hbok); apply nth_In; lia).
  assert (Hch : 0 <= cc_ch c < 256 /\ 0 <= cc_pa c < 256 /\ 0 <= cc_va c < 256).
  { unfold cc_ch, cc_pa, cc_va. destruct c as [[a1 b1] d1]. exact Hcok. }
  destruct Hch as (Hch1 & Hch2 & Hch3).
  destruct (cc_xslice cs (Z.to_nat i) Hin) as (Sl0 & Sl4 & Sl8).
  destruct (cc_onth cs (Z.to_nat i) Hin) as (On0 & On1 & On2).
  fold c in Sl0, Sl4, Sl8, On0, On1, On2.
  rewrite (unsigned_lit_small (cc_ch c)) in Sl0 by lia.
  rewrite (unsigned_lit_small (cc_pa c)) in Sl4 by lia.
  rewrite (unsigned_lit_small (cc_va c)) in Sl8 by lia.
  assert (Lx : length (x_cells_bytes cs) = (12 * Z.to_nat i + (12 * (length cs - Z.to_nat i)))%nat)
    by (rewrite length_x_cells_bytes; lia).
  assert (Lo : length (ha_cells_bytes cs) = (3 * length cs)%nat) by apply length_ha_cells_bytes.
  assert (V0 : val_mem rsegs (mrestrict (w_H W2) mem2) (x + 4 + Z.of_nat (12 * Z.to_nat i)) 4 (cc_ch c))
    by (apply (hm_bytes_field rsegs (w_H W2) mem2 (x + 4) (x_cells_bytes cs) (12 * Z.to_nat i) 4);
        [exact Bx4 | exact Sl0 | rewrite length_x_cells_bytes; lia]).
  assert (V4 : val_mem rsegs (mrestrict (w_H W2) mem2) (x + 4 + Z.of_nat (12 * Z.to_nat i + 4)) 4 (cc_pa c))
    by (apply (hm_bytes_field rsegs (w_H W2) mem2 (x + 4) (x_cells_bytes cs) (12 * Z.to_nat i + 4) 4);
        [exact Bx4 | exact Sl4 | rewrite length_x_cells_bytes; lia]).
  assert (V8 : val_mem rsegs (mrestrict (w_H W2) mem2) (x + 4 + Z.of_nat (12 * Z.to_nat i + 8)) 4 (cc_va c))
    by (apply (hm_bytes_field rsegs (w_H W2) mem2 (x + 4) (x_cells_bytes cs) (12 * Z.to_nat i + 8) 4);
        [exact Bx4 | exact Sl8 | rewrite length_x_cells_bytes; lia]).
  assert (U0 : val_mem rsegs (mrestrict (w_H W2) mem2) (o + Z.of_nat (3 * Z.to_nat i + 0)) 1 (cc_ch c))
    by (pose proof (hm_bytes_byte rsegs (w_H W2) mem2 o (ha_cells_bytes cs) (3 * Z.to_nat i + 0) Bout
          ltac:(rewrite Lo; lia)) as HB; rewrite On0, hm_unsigned_byte, (Z.mod_small (cc_ch c)) in HB by lia; exact HB).
  assert (U1 : val_mem rsegs (mrestrict (w_H W2) mem2) (o + Z.of_nat (3 * Z.to_nat i + 1)) 1 (cc_pa c))
    by (pose proof (hm_bytes_byte rsegs (w_H W2) mem2 o (ha_cells_bytes cs) (3 * Z.to_nat i + 1) Bout
          ltac:(rewrite Lo; lia)) as HB; rewrite On1, hm_unsigned_byte, (Z.mod_small (cc_pa c)) in HB by lia; exact HB).
  assert (U2 : val_mem rsegs (mrestrict (w_H W2) mem2) (o + Z.of_nat (3 * Z.to_nat i + 2)) 1 (cc_va c))
    by (pose proof (hm_bytes_byte rsegs (w_H W2) mem2 o (ha_cells_bytes cs) (3 * Z.to_nat i + 2) Bout
          ltac:(rewrite Lo; lia)) as HB; rewrite On2, hm_unsigned_byte, (Z.mod_small (cc_va c)) in HB by lia; exact HB).
  (* the entry state at the loop head *)
  set (xsL := [x + 4 + 12 * i; cc_ch c; cc_pa c; cc_va c; cc_ch c; cc_pa c; cc_va c]).
  remember (Ereg regs2 (hc_extra xsL)) as E eqn:HE.
  assert (Usp : bv_unsigned (ew E 2) = spZ regs2)
    by (subst E; rewrite (ew_Ereg_nat regs2 _ 2 2%bv eq_refl); reflexivity).
  assert (E32 : ew E 32 = Z_to_bv 64 SHADOW_OFF) by (subst E; apply hc_E32).
  assert (E1 : ew E 1 = getr regs 1)
    by (subst E; rewrite (ew_Ereg_nat regs2 _ 1 1%bv eq_refl); exact Hra2).
  assert (E10 : bv_unsigned (ew E 10) = o + 3 * i)
    by (subst E; rewrite (ew_Ereg_nat regs2 _ 10 10%bv eq_refl), Q10; apply unsigned_lit_small; lia).
  assert (E12 : bv_unsigned (ew E 12) = x)
    by (subst E; rewrite (ew_Ereg_nat regs2 _ 12 12%bv eq_refl), Q12; apply unsigned_lit_small; lia).
  assert (E14 : bv_unsigned (ew E 14) = 12 * i)
    by (subst E; rewrite (ew_Ereg_nat regs2 _ 14 14%bv eq_refl), Q14; apply unsigned_lit_small; lia).
  assert (E15 : bv_unsigned (ew E 15) = x + 8)
    by (subst E; rewrite (ew_Ereg_nat regs2 _ 15 15%bv eq_refl), Q15; apply unsigned_lit_small; lia).
  assert (E16 : bv_unsigned (ew E 16) = 12 * rcc)
    by (subst E; rewrite (ew_Ereg_nat regs2 _ 16 16%bv eq_refl), Q16; apply unsigned_lit_small; lia).
  assert (E17 : bv_unsigned (ew E 17) = o + 3 * i + 2)
    by (subst E; rewrite (ew_Ereg_nat regs2 _ 17 17%bv eq_refl), Q17; apply unsigned_lit_small; lia).
  assert (E13 : sv_denot E hc_Bx = getr regs2 13)
    by (unfold hc_Bx; apply bv_eq; rewrite denot_SOff, E32, Z.add_0_r, Q13;
        rewrite !unsigned_lit_small by (unfold SHADOW_OFF; lia); reflexivity).
  assert (E33w : ew E 33 = Z_to_bv 64 (x + 4 + 12 * i))
    by (subst E; exact (cc_Eextra regs2 xsL 0)).
  assert (E33 : bv_unsigned (ew E 33) = x + 4 + 12 * i)
    by (rewrite E33w; apply unsigned_lit_small; lia).
  assert (E34 : ew E 34 = Z_to_bv 64 (cc_ch c))
    by (subst E; exact (cc_Eextra regs2 xsL 1)).
  assert (E35 : ew E 35 = Z_to_bv 64 (cc_pa c))
    by (subst E; exact (cc_Eextra regs2 xsL 2)).
  assert (E36 : ew E 36 = Z_to_bv 64 (cc_va c))
    by (subst E; exact (cc_Eextra regs2 xsL 3)).
  assert (E37 : ew E 37 = Z_to_bv 64 (cc_ch c))
    by (subst E; exact (cc_Eextra regs2 xsL 4)).
  assert (E38 : ew E 38 = Z_to_bv 64 (cc_pa c))
    by (subst E; exact (cc_Eextra regs2 xsL 5)).
  assert (E39 : ew E 39 = Z_to_bv 64 (cc_va c))
    by (subst E; exact (cc_Eextra regs2 xsL 6)).
  assert (HS : st_ok rsegs E ss_cc_L
    (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 PC_LH) mem2 (seg_rom rsegs)))).
  { rewrite restrict_mkst_fx. unfold ss_cc_L. subst E. apply (entry_st_ok_full rsegs).
    - apply hc_regs_ok. apply Forall_cons; [|apply Forall_nil]. cbn [fst snd]. split.
      + intros Hz. apply (f_equal (@bv_unsigned 5)) in Hz. vm_compute in Hz. discriminate Hz.
      + exact E13.
    - vm_compute. reflexivity.
    - unfold cc_stk_ra, cc_xcell, cc_ocell.
      repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      + rewrite Usp. split; [lia|]. split; [lia|]. split; [intros oo Hoo; lia|].
        constructor; [|constructor].
        apply (chunk_ok_val rsegs _ _ (spZ regs2) 8 8 (SOff 1 0) (bv_unsigned (getr regs 1)));
        [ apply cc_denot_atom; [rewrite E1; symmetry; apply Z_to_bv_bv_unsigned | apply cc_u64]
        | change (8 * Z.of_N 8) with 64; apply cc_u64
        | zside | exact Hslot ].
      + rewrite E33. split; [lia|]. split; [lia|]. split; [intros oo Hoo; lia|].
        constructor; [|constructor; [|constructor; [|constructor]]].
        * apply (hc_chunk4 _ _ (x + 4 + 12 * i) 0 (SOff 34 0) (cc_ch c));
          [ apply cc_denot_atom; [exact E34 | lia] | lia |].
          replace (x + 4 + 12 * i + 0) with (x + 4 + Z.of_nat (12 * Z.to_nat i)) by lia. exact V0.
        * apply (hc_chunk4 _ _ (x + 4 + 12 * i) 4 (SOff 35 0) (cc_pa c));
          [ apply cc_denot_atom; [exact E35 | lia] | lia |].
          replace (x + 4 + 12 * i + 4) with (x + 4 + Z.of_nat (12 * Z.to_nat i + 4)) by lia. exact V4.
        * apply (hc_chunk4 _ _ (x + 4 + 12 * i) 8 (SOff 36 0) (cc_va c));
          [ apply cc_denot_atom; [exact E36 | lia] | lia |].
          replace (x + 4 + 12 * i + 8) with (x + 4 + Z.of_nat (12 * Z.to_nat i + 8)) by lia. exact V8.
      + rewrite E17. split; [lia|]. split; [lia|]. split; [intros oo Hoo; lia|].
        constructor; [|constructor; [|constructor; [|constructor]]].
        * apply (hc_chunk1 _ _ (o + 3 * i + 2) (-2) (SOff 37 0) (cc_ch c));
          [ apply cc_denot_atom; [exact E37 | lia] | lia |].
          replace (o + 3 * i + 2 + -2) with (o + Z.of_nat (3 * Z.to_nat i + 0)) by lia. exact U0.
        * apply (hc_chunk1 _ _ (o + 3 * i + 2) (-1) (SOff 38 0) (cc_pa c));
          [ apply cc_denot_atom; [exact E38 | lia] | lia |].
          replace (o + 3 * i + 2 + -1) with (o + Z.of_nat (3 * Z.to_nat i + 1)) by lia. exact U1.
        * apply (hc_chunk1 _ _ (o + 3 * i + 2) 0 (SOff 39 0) (cc_va c));
          [ apply cc_denot_atom; [exact E39 | lia] | lia |].
          replace (o + 3 * i + 2 + 0) with (o + Z.of_nat (3 * Z.to_nat i + 2)) by lia. exact U2.
    - assert (Dxo : x + 4 + 12 * i + 12 <= o + 3 * i \/ o + 3 * i + 3 <= x + 4 + 12 * i) by lia.
      assert (Dsx : x + 4 + 12 * i + 12 <= spZ regs2 \/ spZ regs2 + 16 <= x + 4 + 12 * i)
        by (destruct (cc_off_disj regs (x + 4) (12 * rcc) ltac:(lia) OSx4); lia).
      assert (Dso : o + 3 * i + 3 <= spZ regs2 \/ spZ regs2 + 16 <= o + 3 * i)
        by (destruct (cc_off_disj regs o (3 * rcc) ltac:(lia) OSo); lia).
      clear Hdisj.
      apply pairwise_disjoint_of_extents.
      unfold cc_stk_ra, cc_xcell, cc_ocell, extent_of_region.
      cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite Usp, E33, E17.
      cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
    - split; [|split; [exact I|]].
      + cbn [f_atoms atoms_ok cc_fsL hc_pfact]. unfold afact_ok. cbn [af_lo af_hi af_al2].
        rewrite Usp, E10, E17, E33, E14, E16, E32, E34, E35, E36, E37, E38, E39.
        rewrite !unsigned_lit_small by (unfold SHADOW_OFF; lia).
        change (2 ^ 4) with 16. change (2 ^ 2) with 4. rewrite Z.pow_0_r, !Z.mod_1_r.
        unfold hc_SB, SHADOW_OFF, HC_PHI in *.
        repeat split; try lia.
        all: first
          [ rewrite Hsp2; replace (spZ regs - 16) with (spZ regs + (-1) * 16) by ring;
            rewrite Z.mod_add by lia; exact Hal16
          | replace (x + 4 + 12 * i) with (x + (1 + 3 * i) * 4) by ring;
            rewrite Z.add_mod by lia; rewrite Hx4, Z.mod_mul by lia; reflexivity ].
      + cbn [f_alias alias_ok cc_alias]. split; [|split; [|exact I]].
        * apply U_inj. rewrite U_SAlu. cbn [zalu_raw]. rewrite !U_SOff, E12, E14, E33, !Z.add_0_r.
          rewrite (zcanon_id x) by (unfold M64; lia). rewrite (zcanon_id (12 * i)) by (unfold M64; lia).
          rewrite !zcanon_id by (unfold M64; lia). lia.
        * apply U_inj. rewrite U_SAlu. cbn [zalu_raw]. rewrite !U_SOff, E15, E14, E33, !Z.add_0_r.
          rewrite (zcanon_id (x + 8)) by (unfold M64; lia). rewrite (zcanon_id (12 * i)) by (unfold M64; lia).
          rewrite !zcanon_id by (unfold M64; lia). lia. }
  clear Hdisj.
  assert (SHOK : sh_ok rsegs hc_Bx cc_SHL E (mrestrict (w_H W2) mem2)).
  { unfold sh_ok, cc_SHL. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    - apply (hc_shent (w_H W2) mem2 E 33 (x + 4 + 12 * i) 0 12);
      [ replace (x + 4 + 12 * i + 0) with (x + 4 + 12 * i) by lia; replace (12 - 0) with 12 by lia;
        apply (range_addressable_sub _ _ _ _ _ _ RAx42); lia
      | replace (x + 4 + 12 * i + 0) with (x + 4 + 12 * i) by lia; replace (12 - 0) with 12 by lia;
        apply (in_app_sub (x + 4) (12 * rcc)); [exact Happx4 | lia | lia | lia]
      | exact E32 | exact E33 | lia ].
    - apply (hc_shent (w_H W2) mem2 E 10 (o + 3 * i) 0 3);
      [ replace (o + 3 * i + 0) with (o + 3 * i) by lia; replace (3 - 0) with 3 by lia;
        apply (range_addressable_sub _ _ _ _ _ _ RAo2); lia
      | replace (o + 3 * i + 0) with (o + 3 * i) by lia; replace (3 - 0) with 3 by lia;
        apply (in_app_sub o (3 * rcc)); [exact Happo | lia | lia | lia]
      | exact E32 | exact E10 | lia ]. }
  assert (HAE : env_agree 32 (Ereg regs2 (hc_extra [x + 4 + 12 * i; cc_ch c; cc_pa c; cc_va c; cc_ch c; cc_pa c; cc_va c])) E)
    by (subst E; apply env_agree_refl).
  clear HE. rename Usp into B2.
  assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - T_check_STK <= a < spZ regs) ->
    aview rsegs (w_H W2) mem2 a = aview rsegs (w_H W2) mem2 a) by (intros; reflexivity).
  rewrite Hcfg. unfold cfg_at. change (w64 PC_LH) with (Z_to_bv 64 PC_LH).
  (* the three comparisons, then the loop test *)
  cc_run_to PC_RET. hc_keep.
  cc_branch Hb1.
  { exfalso. rewrite branch_ne_U in Hb1. cc_ew E34 F34. cc_ew E37 F37.
    rewrite (cc_U_sx32_small _ 34 (cc_ch c) F34 ltac:(lia)) in Hb1.
    rewrite (U_atom _ 37 (cc_ch c) F37) in Hb1 by lia.
    rewrite Z.eqb_refl in Hb1. cbn in Hb1. discriminate. }
  cc_run_to PC_RET. hc_keep.
  cc_branch Hb2.
  { exfalso. rewrite branch_ne_U in Hb2. cc_ew E35 F35. cc_ew E38 F38.
    rewrite (cc_U_sx32_small _ 35 (cc_pa c) F35 ltac:(lia)) in Hb2.
    rewrite (U_atom _ 38 (cc_pa c) F38) in Hb2 by lia.
    rewrite Z.eqb_refl in Hb2. cbn in Hb2. discriminate. }
  cc_run_to PC_RET. hc_keep.
  cc_branch Hb3.
  { exfalso. rewrite branch_ne_U in Hb3. cc_ew E36 F36. cc_ew E39 F39.
    rewrite (cc_U_sx32_small _ 36 (cc_va c) F36 ltac:(lia)) in Hb3.
    rewrite (U_atom _ 39 (cc_va c) F39) in Hb3 by lia.
    rewrite Z.eqb_refl in Hb3. cbn in Hb3. discriminate. }
  cc_run_to PC_RET. hc_keep.
  cc_branch Hb4.
  { (* 12 rc = 12 (i + 1): the last turn, the epilogue and the `ret` *)
    rewrite branch_eq_U in Hb4. cc_bu E16 F16. cc_bu E14 F14.
    rewrite (U_atom _ 16 (12 * rcc) ltac:(apply bv_eq; rewrite F16; symmetry; apply unsigned_lit_small; lia)) in Hb4 by lia.
    rewrite (U_atom_off _ 14 (12 * i) 12 ltac:(apply bv_eq; rewrite F14; symmetry; apply unsigned_lit_small; lia)) in Hb4 by lia.
    apply Z.eqb_eq in Hb4.
    cc_run_to PC_RET. hc_keep.
    lazymatch goal with HSx : st_ok _ ?Ec ?ssx (restrict (w_H ?Wx) ?msx) |- _ =>
      cc_reg HSx (1%bv : bv 5) R1;
      assert (Rsp : getr (ms_regs msx) (Z_to_bv 5 2) = getr regs (Z_to_bv 5 2));
      [ rewrite !cc_sp_idx;
        rewrite (cc_getr_off Ec ssx msx (w_H Wx) (2%bv : bv 5) 2 16 (spZ regs2) HSx
          ltac:(vm_compute; reflexivity) ltac:(repeat (rewrite ew_ewset_other by lia); exact B2) ltac:(lia));
        rewrite Hsp2; replace (spZ regs - 16 + 16) with (spZ regs) by lia;
        unfold spZ; apply Z_to_bv_bv_unsigned
      | eapply (SRr_ret_at rsegs cc_tbl cc_tbl_ok hc_wx Wx Ec); [exact HSx | reflexivity | vm_compute; reflexivity |] ]
    end.
    intros mat'. left.
    lazymatch goal with HSx : st_ok _ ?Ec _ (restrict _ ?msx) |- _ =>
    eapply (cc_post_of STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs _ (ms_regs msx) (ms_mem msx)) end.
    - eapply ajournal_materialize; eassumption.
    - cc_io.
    - (* every callee-saved register: sp was restored, the others were never written *)
      intros r Hr. destruct (Z.eq_dec r 2) as [->|Hne]; [exact Rsp|].
      assert (Hcase : r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
        r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by (unfold acallee_saved in Hr; lia).
      lazymatch goal with HSx : st_ok _ ?Ec ?ssx (restrict _ ?msx) |- _ =>
        etransitivity;
        [ exact (regs_kept_of_st_ok rsegs Ec ssx (restrict (w_H W2) msx) regs2
            (hc_extra [x + 4 + 12 * i; cc_ch c; cc_pa c; cc_va c; cc_ch c; cc_pa c; cc_va c])
            CC_CS HSx ltac:(env_agree_chain HAE)
            ltac:(vm_compute; reflexivity) (Z_to_bv 5 r)
            ltac:(apply cc_cs_in; exact Hcase))
        | apply Hcs2; [exact Hr | exact Hne] ] end.
    - lazymatch goal with HSx : st_ok _ ?Ec _ _ |- _ =>
        rewrite R1; assert (D1 : sv_denot Ec (SOff 1 0) = getr regs 1);
        [ apply bv_eq; rewrite denot_SOff; rewrite (ltac:(repeat (rewrite ew_ewset_other by lia); exact E1) : ew Ec 1 = getr regs 1);
          rewrite Z.add_0_r; apply zcanon_id;
          pose proof (bv_unsigned_in_range _ (getr regs 1)) as Hb;
          change (bv_modulus 64) with (2 ^ 64) in Hb; unfold M64; lia
        | exact D1 ] end.
    - lazymatch goal with HSx : st_ok _ ?Ec _ _ |- _ =>
        rewrite R1; rewrite (ltac:(apply bv_eq; rewrite denot_SOff;
          rewrite (ltac:(repeat (rewrite ew_ewset_other by lia); exact E1) : ew Ec 1 = getr regs 1);
          rewrite Z.add_0_r; apply zcanon_id;
          pose proof (bv_unsigned_in_range _ (getr regs 1)) as Hb;
          change (bv_modulus 64) with (2 ^ 64) in Hb; unfold M64; lia) : sv_denot Ec (SOff 1 0) = getr regs 1);
        exact Hra end.
    - intros a Ha Hz. rewrite (KE a Ha Hz). exact (KEinv a Ha Hz).
    - exact MTL. }
  { (* 12 rc <> 12 (i + 1): the back edge, the cut at i + 1 *)
    rewrite branch_eq_U in Hb4. cc_bu E16 F16. cc_bu E14 F14.
    rewrite (U_atom _ 16 (12 * rcc) ltac:(apply bv_eq; rewrite F16; symmetry; apply unsigned_lit_small; lia)) in Hb4 by lia.
    rewrite (U_atom_off _ 14 (12 * i) 12 ltac:(apply bv_eq; rewrite F14; symmetry; apply unsigned_lit_small; lia)) in Hb4 by lia.
    apply Z.eqb_neq in Hb4.
    cc_run_to PC_LH. hc_keep.
    lazymatch goal with HSx : st_ok _ ?Ec ?ssx (restrict (w_H ?Wx) ?msx) |- _ =>
      pose proof (st_ok_restrict_mkst rsegs (w_H Wx) Ec ssx msx HSx eq_refl) as Hshape;
      rewrite Hshape; apply SRr_ret; right; exists (i + 1); split; [lia|];
      unfold cc_inv; exists (ms_regs msx), (ms_mem msx); eexists end.
    split; [reflexivity|].
    split; [first [eassumption | eapply ajournal_materialize; eassumption]|].
    split; [cc_io|].
    split.
    { intros r Hr Hne.
      assert (Hcase : r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
        r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by (unfold acallee_saved in Hr; lia).
      lazymatch goal with HSx : st_ok _ ?Ec ?ssx (restrict _ ?msx) |- _ =>
        etransitivity;
        [ exact (regs_kept_of_st_ok rsegs Ec ssx (restrict (w_H W2) msx) regs2
            (hc_extra [x + 4 + 12 * i; cc_ch c; cc_pa c; cc_va c; cc_ch c; cc_pa c; cc_va c])
            CC_CS HSx ltac:(env_agree_chain HAE)
            ltac:(vm_compute; reflexivity) (Z_to_bv 5 r)
            ltac:(apply cc_cs_in; exact Hcase))
        | apply Hcs2; [exact Hr | exact Hne] ] end. }
    split.
    { lazymatch goal with HSx : st_ok _ ?Ec ?ssx (restrict _ ?msx) |- _ =>
        rewrite (cc_getr_same Ec ssx msx (w_H W2) (1%bv : bv 5) 1 (getr regs 1) HSx
          ltac:(vm_compute; reflexivity) ltac:(repeat (rewrite ew_ewset_other by lia); exact E1)) end.
      reflexivity. }
    split.
    { unfold spZ at 1. lazymatch goal with HSx : st_ok _ ?Ec ?ssx (restrict _ ?msx) |- _ =>
        rewrite (cc_getr_off Ec ssx msx (w_H W2) (2%bv : bv 5) 2 0 (spZ regs2) HSx
          ltac:(vm_compute; reflexivity) ltac:(repeat (rewrite ew_ewset_other by lia); exact B2) ltac:(lia)) end.
      rewrite unsigned_lit_small by lia. lia. }
    split; [intros a Ha Hz; rewrite (KE a Ha Hz); exact (KEinv a Ha Hz)|].
    split.
    { lazymatch goal with HSx : st_ok _ ?Ec ?ssx (restrict _ ?msx) |- _ =>
        assert (Rsp0 : spZ (ms_regs msx) = spZ regs2);
        [ unfold spZ at 1; rewrite (cc_getr_off Ec ssx msx (w_H W2) (2%bv : bv 5) 2 0 (spZ regs2) HSx
            ltac:(vm_compute; reflexivity) ltac:(repeat (rewrite ew_ewset_other by lia); exact B2) ltac:(lia));
          rewrite unsigned_lit_small by lia; lia
        | rewrite Rsp0;
          replace (spZ regs2 + 8) with (spZ regs2 + 8) by lia;
          exact (cc_chunk8_val Ec ssx msx (w_H W2) cc_stk_ra (spZ regs2) 8 2 (getr regs 1) HSx
            ltac:(unfold cc_stk_ra; cbn [ss_mem]; left; reflexivity) eq_refl
            ltac:(unfold cc_stk_ra; cbn [YP09.r_chunks]; left; reflexivity)
            ltac:(repeat (rewrite ew_ewset_other by lia); exact B2)
            ltac:(repeat (rewrite ew_ewset_other by lia); exact E1)) ] end. }
    split; [lia|].
    (* the eight registers at the back edge *)
    lazymatch goal with HSx : st_ok _ ?Ec ?ssx (restrict _ ?msx) |- _ =>
      let G := fresh "G" in
      assert (G : True) by exact I; clear G;
      split; [ rewrite (cc_getr_off Ec ssx msx (w_H W2) (10%bv : bv 5) 10 3 (o + 3 * i) HSx
                 ltac:(vm_compute; reflexivity) ltac:(repeat (rewrite ew_ewset_other by lia); exact E10) ltac:(lia));
               f_equal; lia |];
      split; [ rewrite (cc_getr_off Ec ssx msx (w_H W2) (12%bv : bv 5) 12 0 x HSx
                 ltac:(vm_compute; reflexivity) ltac:(repeat (rewrite ew_ewset_other by lia); exact E12) ltac:(lia));
               f_equal; lia |];
      split; [ rewrite (cc_getr_off Ec ssx msx (w_H W2) (13%bv : bv 5) 32 0 SHADOW_OFF HSx
                 ltac:(vm_compute; reflexivity)
                 ltac:(repeat (rewrite ew_ewset_other by lia);
                       rewrite E32; apply unsigned_lit_small; unfold SHADOW_OFF; lia)
                 ltac:(unfold SHADOW_OFF; lia));
               f_equal; lia |];
      split; [ rewrite (cc_getr_off Ec ssx msx (w_H W2) (14%bv : bv 5) 14 12 (12 * i) HSx
                 ltac:(vm_compute; reflexivity) ltac:(repeat (rewrite ew_ewset_other by lia); exact E14) ltac:(lia));
               f_equal; lia |];
      split; [ rewrite (cc_getr_off Ec ssx msx (w_H W2) (15%bv : bv 5) 15 0 (x + 8) HSx
                 ltac:(vm_compute; reflexivity) ltac:(repeat (rewrite ew_ewset_other by lia); exact E15) ltac:(lia));
               f_equal; lia |];
      split; [ rewrite (cc_getr_off Ec ssx msx (w_H W2) (16%bv : bv 5) 16 0 (12 * rcc) HSx
                 ltac:(vm_compute; reflexivity) ltac:(repeat (rewrite ew_ewset_other by lia); exact E16) ltac:(lia));
               f_equal; lia |];
      split; [ rewrite (cc_getr_off Ec ssx msx (w_H W2) (17%bv : bv 5) 17 3 (o + 3 * i + 2) HSx
                 ltac:(vm_compute; reflexivity) ltac:(repeat (rewrite ew_ewset_other by lia); exact E17) ltac:(lia));
               f_equal; lia |]
    end.
    (* the memory facts: the turn wrote nothing *)
    split; [apply (hm_bytes_kept rsegs (w_H W2) mem2); [exact Bout|]|].
    { intros xx Hxx. rewrite length_ha_cells_bytes in Hxx.
      apply KE; [lia|]. intros Hc2. exact (OSo xx ltac:(lia) Hc2). }
    split; [apply (hm_bytes_kept rsegs (w_H W2) mem2); [exact Bx4|]|].
    { intros xx Hxx. rewrite length_x_cells_bytes in Hxx.
      apply KE; [lia|]. intros Hc2. exact (OSx4 xx ltac:(lia) Hc2). }
    split.
    { apply (hm_ra_kept rsegs (w_H W2) mem2); [exact RAo2|].
      intros xx Hxx. apply KE.
      - pose proof (hm_shadow_band xx ltac:(unfold kHighMemEnd; lia)) as Hb.
        unfold kLowMemEnd, kHighMemBeg in Hb. lia.
      - unfold T_check_STK. exact (SHOFF o (3 * rcc) xx Happo ltac:(lia) Hxx). }
    { apply (hm_ra_kept rsegs (w_H W2) mem2); [exact RAx42|].
      intros xx Hxx. apply KE.
      - pose proof (hm_shadow_band xx ltac:(unfold kHighMemEnd; lia)) as Hb.
        unfold kLowMemEnd, kHighMemBeg in Hb. lia.
      - unfold T_check_STK. exact (SHOFF (x + 4) (12 * rcc) xx Happx4 ltac:(lia) Hxx). } }
}

(* ------------------------- the prologue, the rc test and the loop set-up ------------------------- *)
remember (Ereg regs (hc_extra [rcc mod 2 ^ 32])) as E eqn:HE.
assert (Usp : bv_unsigned (ew E 2) = spZ regs)
  by (subst E; rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); reflexivity).
assert (E12 : bv_unsigned (ew E 12) = x)
  by (subst E; rewrite (ew_Ereg_nat regs _ 12 12%bv eq_refl), H12; apply unsigned_lit_small; lia).
assert (E11 : ew E 11 = Z_to_bv 64 rcc)
  by (subst E; rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
assert (E33 : ew E 33 = Z_to_bv 64 (rcc mod 2 ^ 32))
  by (subst E; exact (cc_Eextra regs [rcc mod 2 ^ 32] 0)).
assert (E32 : ew E 32 = Z_to_bv 64 SHADOW_OFF) by (subst E; apply hc_E32).
assert (E1 : ew E 1 = getr regs 1) by (subst E; exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (Hm32 : 0 <= rcc mod 2 ^ 32 < 2 ^ 32) by (apply Z.mod_pos_bound; lia).
assert (E10p : 0 < rcc -> bv_unsigned (ew E 10) = o).
{ intros Hp. destruct (Hpos Hp) as (_ & _ & Hoa & Hob & _).
  subst E. rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl), H10. apply unsigned_lit_small. lia. }
assert (D33 : sv_denot E (SOff 33 0) = Z_to_bv 64 (rcc mod 2 ^ 32)).
{ apply cc_denot_atom; [exact E33 | lia]. }
assert (HS : st_ok rsegs E (ss_hc A_CHECK_CELLS [] cc_rsP cc_fsP)
  (restrict (w_H W) (mkst regs (Z_to_bv 64 A_CHECK_CELLS) memc (seg_rom rsegs)))).
{ subst E. apply (hc_entry A_CHECK_CELLS [] [rcc mod 2 ^ 32] cc_rsP cc_fsP W regs memc
    ltac:(unfold A_CHECK_CELLS; lia) (Forall_nil _) Hpr Hsp Kgot Kcell).
  - vm_compute. reflexivity.
  - unfold cc_rsP. apply Forall_cons; [|apply Forall_nil].
    apply (hc_data_ok _ _ 12 x 0 4 _ E12); [lia | lia |].
    apply Forall_cons; [|apply Forall_nil].
    apply (hc_chunk4 _ _ x 0 (SOff 33 0) (rcc mod 2 ^ 32) D33 ltac:(lia)).
    rewrite Z.add_0_r. exact Vx.
  - unfold hc_base_regions, cc_rsP, hc_stack_region, hc_got_region, hc_cell_region, hc_data, extent_of_region.
    cbn [app map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite Usp, E12.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    unfold HC_GOT_SH, HC_SH_CELL in *. repeat split; lia.
  - cbn [atoms_ok cc_fsP hc_pfact]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite Usp, E12, E32, E33, !unsigned_lit_small by (unfold SHADOW_OFF; lia).
    change (2 ^ 4) with 16. change (2 ^ 2) with 4. rewrite Z.pow_0_r, !Z.mod_1_r.
    unfold hc_SB, SHADOW_OFF, HC_PHI in *. repeat split; lia. }
assert (SHOK : sh_ok rsegs hc_Bx cc_SHP E (mrestrict (w_H W) memc)).
{ unfold sh_ok, cc_SHP. apply Forall_cons; [|apply Forall_nil].
  apply (hc_shent (w_H W) memc E 12 x 0 4);
  [ replace (x + 0) with x by lia; replace (4 - 0) with 4 by lia; exact RAx
  | replace (x + 0) with x by lia; replace (4 - 0) with 4 by lia; exact Happx
  | exact E32 | exact E12 | lia ]. }
assert (HAE : env_agree 32 (Ereg regs (hc_extra [rcc mod 2 ^ 32])) E) by (subst E; apply env_agree_refl).
assert (HAE34 : env_agree 34 E E) by (apply env_agree_refl).
clear HE. rename Usp into B2.
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 16 <= a < spZ regs) ->
  aview rsegs (w_H W) memc a = aview rsegs (w_H W) memc a) by (intros; reflexivity).
unfold cfg_at. change (w64 A_CHECK_CELLS) with (Z_to_bv 64 A_CHECK_CELLS).
(* the whole walk: the prologue's two tests, then either the epilogue or the loop *)
eapply (SRr_bind rsegs W _ (fun W2 c2 =>
  hd_post rsegs B MT STK sp0 FP ly S W0 mem0 md0 own k T_check_STK regs lyc Sc W memc mdc
    (fun f => f = fx) (fun _ => False) (fun _ _ _ => True) W2 c2 \/
  cc_inv STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs o rcc x cs 0 W2 c2)).
{ (* 0x84148 .. 0x8416c, stop at the `bne a1,a4` 0x84170 *)
  cc_run_to PC_LH. hc_keep.
  cc_branch Hbne.
  { exfalso. rewrite branch_ne_U in Hbne. cc_ew E11 F11. cc_ew E33 F33.
    rewrite (cc_U_wrap _ 11 rcc F11) in Hbne.
    rewrite (cc_U_sx32 _ 33 rcc F33 ltac:(lia)) in Hbne.
    rewrite Z.eqb_refl in Hbne. cbn in Hbne. discriminate. }
  (* 0x84174 blez a1 *)
  cc_run_to PC_LH. hc_keep.
  cc_branch Hble.
  { (* rc <= 0: nothing to check, the epilogue and the `ret` *)
    rewrite cc_branch_ge, cc_Sg_lit in Hble. cc_ew E11 G11.
    rewrite (cc_Sg_off _ 11 rcc G11 ltac:(lia)) in Hble.
    cc_run_to PC_RET. hc_keep.
    lazymatch goal with HSx : st_ok _ ?Ec ?ssx (restrict (w_H ?Wx) ?msx) |- _ =>
      cc_reg HSx (1%bv : bv 5) R1;
      eapply (SRr_ret_at rsegs cc_tbl cc_tbl_ok hc_wx Wx Ec); [exact HSx | reflexivity | vm_compute; reflexivity |]
    end.
    intros mat'. left.
    lazymatch goal with HSx : st_ok _ ?Ec _ (restrict _ ?msx) |- _ =>
    eapply (cc_post_of STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs _ (ms_regs msx) (ms_mem msx)) end.
    - first [eassumption | eapply ajournal_materialize; eassumption].
    - cc_io.
    - lazymatch goal with HSx : st_ok _ _ _ _ |- _ =>
        eapply aregs_preserved_of_st_ok; [exact HSx | env_agree_chain HAE | vm_compute; reflexivity] end.
    - lazymatch goal with HSx : st_ok _ ?Ec _ _ |- _ =>
        rewrite R1; apply bv_eq; rewrite denot_SOff;
        rewrite (ltac:(repeat (rewrite ew_ewset_other by lia); exact E1) : ew Ec 1 = getr regs 1);
        rewrite Z.add_0_r; apply zcanon_id;
        pose proof (bv_unsigned_in_range _ (getr regs 1)) as Hb;
        change (bv_modulus 64) with (2 ^ 64) in Hb; unfold M64; lia end.
    - lazymatch goal with HSx : st_ok _ ?Ec _ _ |- _ =>
        rewrite R1;
        rewrite (ltac:(apply bv_eq; rewrite denot_SOff;
          rewrite (ltac:(repeat (rewrite ew_ewset_other by lia); exact E1) : ew Ec 1 = getr regs 1);
          rewrite Z.add_0_r; apply zcanon_id;
          pose proof (bv_unsigned_in_range _ (getr regs 1)) as Hb;
          change (bv_modulus 64) with (2 ^ 64) in Hb; unfold M64; lia) : sv_denot Ec (SOff 1 0) = getr regs 1);
        exact Hra end.
    - intros a Ha Hz. apply (KE a Ha). intros Hc. apply Hz. unfold T_check_STK. lia.
    - exact MTL. }
  { (* 0 < rc: the loop set-up, then the cut at index 0 *)
    rewrite cc_branch_ge, cc_Sg_lit in Hble. cc_ew E11 G11.
    rewrite (cc_Sg_off _ 11 rcc G11 ltac:(lia)) in Hble.
    assert (Hrpos : 0 < rcc) by (destruct (Z.ltb_spec 0 rcc); [lia | cbn in Hble; discriminate]).
    destruct (Hpos Hrpos) as (Hlen & Hbok & Ho0 & Ho1 & Hxa & Hxb & Gout & RAo & OSo & APo & Gx4 & RAx4 & OSx4 & APx4 & Hdisj).
    destruct APo as (Happo & Himgo). destruct APx4 as (Happx4 & Himgx4).
    destruct (hc_app_fact o (3 * rcc) Happo ltac:(lia)) as (Ho4096 & Hohi & _).
    destruct (hc_app_fact (x + 4) (12 * rcc) Happx4 ltac:(lia)) as (Hx4096 & Hxhi & _).
    unfold ASAN_CEIL, HC_PHI in Hohi, Hxhi.
    cc_run_to PC_LH. hc_keep.
    lazymatch goal with HSx : st_ok _ ?Ec ?ssx (restrict (w_H ?Wx) ?msx) |- _ =>
      pose proof (st_ok_restrict_mkst rsegs (w_H Wx) Ec ssx msx HSx eq_refl) as Hshape;
      rewrite Hshape; apply SRr_ret; right;
      unfold cc_inv; exists (ms_regs msx), (ms_mem msx); eexists end.
    split; [reflexivity|].
    split; [first [eassumption | eapply ajournal_materialize; eassumption]|].
    split; [cc_io|].
    split.
    { intros r Hr Hne.
      assert (Hcase : r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
        r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by (unfold acallee_saved in Hr; lia).
      lazymatch goal with HSx : st_ok _ ?Ec ?ssx (restrict _ ?msx) |- _ =>
        exact (regs_kept_of_st_ok rsegs Ec ssx (restrict (w_H W) msx) regs (hc_extra [rcc mod 2 ^ 32])
          CC_CS HSx ltac:(env_agree_chain HAE)
          ltac:(vm_compute; reflexivity) (Z_to_bv 5 r)
          ltac:(apply cc_cs_in; exact Hcase)) end. }
    split.
    { lazymatch goal with HSx : st_ok _ ?Ec ?ssx (restrict _ ?msx) |- _ =>
        rewrite (cc_getr_same Ec ssx msx (w_H W) (1%bv : bv 5) 1 (getr regs 1) HSx
          ltac:(vm_compute; reflexivity) ltac:(repeat (rewrite ew_ewset_other by lia); exact E1)) end.
      reflexivity. }
    split.
    { unfold spZ at 1. lazymatch goal with HSx : st_ok _ ?Ec ?ssx (restrict _ ?msx) |- _ =>
        rewrite (cc_getr_off Ec ssx msx (w_H W) (2%bv : bv 5) 2 (-16) (spZ regs) HSx
          ltac:(vm_compute; reflexivity) ltac:(repeat (rewrite ew_ewset_other by lia); exact B2) ltac:(lia)) end.
      rewrite unsigned_lit_small by lia. lia. }
    split; [intros a Ha Hz; apply (KE a Ha); intros Hc; apply Hz; unfold T_check_STK; lia|].
    split.
    { lazymatch goal with HSx : st_ok _ ?Ec ?ssx (restrict _ ?msx) |- _ =>
        assert (Rsp0 : spZ (ms_regs msx) = spZ regs - 16);
        [ unfold spZ at 1; rewrite (cc_getr_off Ec ssx msx (w_H W) (2%bv : bv 5) 2 (-16) (spZ regs) HSx
            ltac:(vm_compute; reflexivity) ltac:(repeat (rewrite ew_ewset_other by lia); exact B2) ltac:(lia));
          rewrite unsigned_lit_small by lia; lia
        | rewrite Rsp0;
          replace (spZ regs - 16 + 8) with (spZ regs + -8) by lia;
          exact (cc_chunk8_val Ec ssx msx (w_H W)
            (YP09.mkRegion (Some 2%nat) (-16) 0 (-16) 0 [YP09.mkChunk (-8) (CVal 8 (SOff 1 0))])
            (spZ regs) (-8) 2 (getr regs 1) HSx
            ltac:(cbn [ss_mem]; left; reflexivity) eq_refl
            ltac:(cbn [YP09.r_chunks]; left; reflexivity)
            ltac:(repeat (rewrite ew_ewset_other by lia); exact B2)
            ltac:(repeat (rewrite ew_ewset_other by lia); exact E1)) ] end. }
    split; [lia|].
    lazymatch goal with HSx : st_ok _ ?Ec ?ssx (restrict _ ?msx) |- _ =>
      split; [ rewrite (cc_getr_off Ec ssx msx (w_H W) (10%bv : bv 5) 10 0 o HSx
                 ltac:(vm_compute; reflexivity)
                 ltac:(repeat (rewrite ew_ewset_other by lia); exact (E10p Hrpos))
                 ltac:(lia));
               f_equal; lia |];
      split; [ rewrite (cc_getr_off Ec ssx msx (w_H W) (12%bv : bv 5) 12 0 x HSx
                 ltac:(vm_compute; reflexivity) ltac:(repeat (rewrite ew_ewset_other by lia); exact E12) ltac:(lia));
               f_equal; lia |];
      split; [ rewrite (cc_getr_off Ec ssx msx (w_H W) (13%bv : bv 5) 32 0 SHADOW_OFF HSx
                 ltac:(vm_compute; reflexivity)
                 ltac:(repeat (rewrite ew_ewset_other by lia);
                       rewrite E32; apply unsigned_lit_small; unfold SHADOW_OFF; lia)
                 ltac:(unfold SHADOW_OFF; lia));
               f_equal; lia |];
      split; [ rewrite (cc_getr_lit Ec ssx msx (w_H W) (14%bv : bv 5) 0 HSx
                 ltac:(vm_compute; reflexivity) ltac:(lia));
               f_equal; lia |];
      split; [ rewrite (cc_getr_off Ec ssx msx (w_H W) (15%bv : bv 5) 12 8 x HSx
                 ltac:(vm_compute; reflexivity) ltac:(repeat (rewrite ew_ewset_other by lia); exact E12) ltac:(lia));
               reflexivity |];
      split; [ rewrite (cc_getr_mul Ec ssx msx (w_H W) (16%bv : bv 5) 11 rcc HSx
                 ltac:(vm_compute; reflexivity) ltac:(repeat (rewrite ew_ewset_other by lia); exact E11) ltac:(lia));
               reflexivity |];
      split; [ rewrite (cc_getr_off Ec ssx msx (w_H W) (17%bv : bv 5) 10 2 o HSx
                 ltac:(vm_compute; reflexivity)
                 ltac:(repeat (rewrite ew_ewset_other by lia); exact (E10p Hrpos))
                 ltac:(lia));
               f_equal; lia |]
    end.
    split; [apply (hm_bytes_kept rsegs (w_H W) memc); [apply (proj2 (hm_bytes_zbytes rsegs (w_H W) memc o (ha_cells_bytes cs))); exact Gout|]|].
    { intros xx Hxx. rewrite length_ha_cells_bytes in Hxx.
      apply KE; [lia|]. intros Hc2. apply (OSo xx ltac:(lia)). unfold T_check_STK. lia. }
    split; [apply (hm_bytes_kept rsegs (w_H W) memc); [apply (proj2 (hm_bytes_zbytes rsegs (w_H W) memc (x + 4) (x_cells_bytes cs))); exact Gx4|]|].
    { intros xx Hxx. rewrite length_x_cells_bytes in Hxx.
      apply KE; [lia|]. intros Hc2. apply (OSx4 xx ltac:(lia)). unfold T_check_STK. lia. }
    split.
    { apply (hm_ra_kept rsegs (w_H W) memc); [exact RAo|].
      intros xx Hxx. apply KE.
      - pose proof (hm_shadow_band xx ltac:(unfold kHighMemEnd; lia)) as Hb.
        unfold kLowMemEnd, kHighMemBeg in Hb. lia.
      - intros Hc2. apply (SHOFF o (3 * rcc) xx Happo ltac:(lia) Hxx). lia. }
    { apply (hm_ra_kept rsegs (w_H W) memc); [exact RAx4|].
      intros xx Hxx. apply KE.
      - pose proof (hm_shadow_band xx ltac:(unfold kHighMemEnd; lia)) as Hb.
        unfold kLowMemEnd, kHighMemBeg in Hb. lia.
      - intros Hc2. apply (SHOFF (x + 4) (12 * rcc) xx Happx4 ltac:(lia) Hxx). lia. } } }
(* the loop's closure on the measure rc - i *)
intros W2 c2 Hle [HQ | HI]; [apply SRr_ret; exact HQ|].
exact (SRr_loopZ rsegs Z (fun i => rcc - i)
  (cc_inv STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs o rcc x cs)
  (hd_post rsegs B MT STK sp0 FP ly S W0 mem0 md0 own k T_check_STK regs lyc Sc W memc mdc
    (fun f => f = fx) (fun _ => False) (fun _ _ _ => True)) LOOP 0 W2 c2 HI).
Qed.
End c.

Print Assumptions hd_check_cells_A.
