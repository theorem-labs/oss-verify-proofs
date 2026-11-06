(* check_cells 0x841c0 of fuzz_headamp.asan-ubsan (image B; unstripped sha256
   1674e30a0698f381704e66d2398d7906c881f4ba8fc619cb41b89fb97ad112ff; the pinned 53edda9bdeeb has the same loaded
   bytes except .note.gnu.build-id), the image-B walk against lib/A/HPgCSpec.v's hd_check_cells_specX on lib/AU/Img0U.v rsegs. Proves
   function check_cells (written new as the twin of lib/A/HPgChk_check_cells.v, whose cell-list and arithmetic
   lemmas, which name no image, this file reuses; the plumbing is lib/A/HPgChkBase.v and lib/AU/HPgChkBaseU.v).

   THE CODE (121 words, 0x841c0 .. 0x843a4; fuzz_headamp.c:239-259). Image A's shape at new addresses, with the
   .got word 0x9c7f0, a 32-byte frame (ra at 0x18(sp), s0 at 0x10(sp), s1 at 8(sp): s0 and s1 are written inside
   the loop, so the walk carries the saved words through the cut and the epilogue restores them) and four UBSan
   traps to the `unimp` 0x8435c. Prologue 0x841c0 .. 0x84228: the save, x's alignment trap 0x841d0
   `andi a3,a2,3; bnez a3`, the .got / cell load, the instrumented check and `lw` of x->rc, `bne a1,a4` ->
   abort 0x84360, `blez a1` -> the epilogue, then the loop set-up (a4 = 3 i, a5 = 12 i, a6 = ~out, a7 = out + 1,
   t0 = x + 8, t1 = ~(x + 4), t2 = 12 rc, t3 = 120).
   One turn (head L 0x8422c, back edge 0x842ec): the three UBSan traps 0x8422c `bltu a6,a4`, 0x84240
   `beq a5,t3` and 0x84244 `bltu t1,a5`; three instrumented 1-byte checks of out + 3 i + {0,1,2} (0x84230,
   0x84270, 0x842a4; slow arms 0x842f0, 0x8430c, 0x84328) with their `lbu` at a7 - 1, a7 + 0, a7 + 1; three
   instrumented 4-byte checks of x + 4 + 12 i + {0,4,8} (0x8424c, 0x84284, 0x842b8; slow arms 0x842fc, 0x84318,
   0x84334) with their `lw` at t5 - 4, t5 + 0, t5 + 4 (t5 = t0 + a5); the three comparisons 0x8426c, 0x842a0,
   0x842d4 -> abort; the increments and the loop test 0x842e8 `beq t2,a5`. Epilogue 0x84348 .. 0x84358.

   WHY NO TRAP AND NO ABORT IS REACHED. The alignment trap: the atom of x carries x mod 4 = 0 (the contract's
   premise), so the `andi` is 0. The three loop traps are decided by the atoms' ranges, which the cut carries:
   a6 = 2^64 - 1 - out and t1 = 2^64 - 1 - (x + 4) are at least 2^63 - 1 (the contract bounds out + 3 rc and
   x + 4 + 12 rc by 2^63), while a4 = 3 i <= 27 and a5 = 12 i <= 108, so neither `bltu` is taken; and t3 is 120
   while a5 <= 108, because i < rc and the contract gives rc <= 10 (the array has ten cells: this is the premise
   image B needs and image A does not). Each comparison is a `lw` of x->cell[i].f against a `lbu` of
   out[3 i + f], and the contract's two garr8 premises give both from one cell list with cell_bytes_ok, so the
   values are equal and no `bne` is taken. The shadow entry of x + 4 + 12 i covers twelve bytes, so the engine
   reads the three 4-byte checks' shadow bytes as zero; the shadow entry of out + 3 i covers three bytes, so each
   1-byte check goes through the token engine, whose slow arm continues at the `lbu`.
   THE LOOP IS CLOSED BY ITS COUNTER: YA0n.SRr_loopZ on the measure rc - i, the exit test `beq t2,a5` being
   12 rc = 12 (i + 1).
   BESIDES THE CONTRACT the walk takes the two Section hypotheses HBgot and HBcell of lib/AU/HPgChkBaseU.v, this
   image's .got word 0x9c7f0 and shadow-offset cell 0xa5238. *)
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
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require Import Img0U HPgChkBaseU.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgBase HPgCSpec HPgChkBase HPgMem HPgChk_check_cells.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

Definition B_CHECK_CELLS : Z := 0x841c0.
Definition PCU_LH : Z := 0x8422c.
Definition PCU_RET : Z := 0x84358.
(* the 121 words 0x841c0 .. 0x843a4 (the six slow arms, the trap and the abort block included) *)
Definition ccu_tbl : ctable := Eval vm_compute in (build_table rsegs B_CHECK_CELLS 121 TEmpty).
Lemma ccu_tbl_eq : ccu_tbl = build_table rsegs B_CHECK_CELLS 121 TEmpty.
Proof. vm_cast_no_check (eq_refl ccu_tbl). Qed.
Lemma ccu_tbl_ok : table_ok rsegs ccu_tbl.
Proof. rewrite ccu_tbl_eq. apply build_table_ok0. unfold B_CHECK_CELLS. lia. Qed.

(* ===================================== the entry states ===================================== *)
(* the prologue's: the lower half of the 32-byte frame (HPgChkBase's save slot is its upper half) and the word
   at x (env slot 12), which holds rc mod 2^32 (env slot 33) *)
Definition ccu_stk_lo : YP09.region := YP09.mkRegion (Some 2%nat) (-32) (-16) (-32) (-16) [].
Definition ccu_rsP : smem := [ccu_stk_lo; hc_data 12 0 4 [YP09.mkChunk 0 (CVal 4 (SOff 33 0))]].
Definition ccu_fsP : list (nat * afact) := [hc_pfact 12 2; (33%nat, mkAF 0 (2 ^ 32 - 1) 0)].
Definition ccu_SHP : list shent := [mkSHE 12 0 4].
(* the loop head's: the whole save slot with the three saved words (slots 40, 41 the caller's s0, s1), cell i of
   x (slot 33 = x + 4 + 12 i; slots 34, 35, 36 its three words) and cell i of out at a7 (slot 17 = out + 1 + 3 i;
   slots 37, 38, 39 its three bytes) *)
Definition ccu_stk : YP09.region := YP09.mkRegion (Some 2%nat) 0 32 0 0
  [YP09.mkChunk 8 (CVal 8 (SOff 41 0)); YP09.mkChunk 16 (CVal 8 (SOff 40 0)); YP09.mkChunk 24 (CVal 8 (SOff 1 0))].
Definition ccu_xcell : YP09.region := YP09.mkRegion (Some 33%nat) 0 12 0 0
  [YP09.mkChunk 0 (CVal 4 (SOff 34 0)); YP09.mkChunk 4 (CVal 4 (SOff 35 0)); YP09.mkChunk 8 (CVal 4 (SOff 36 0))].
Definition ccu_ocell : YP09.region := YP09.mkRegion (Some 17%nat) (-1) 2 0 0
  [YP09.mkChunk (-1) (CVal 1 (SOff 37 0)); YP09.mkChunk 0 (CVal 1 (SOff 38 0)); YP09.mkChunk 1 (CVal 1 (SOff 39 0))].
(* `add t4,a2,a5` and `add t5,t0,a5` are cell i's base minus 4 and plus 4 *)
Definition ccu_alias : list (sv * sv) :=
  [ (SAlu ALU_ADD (SOff 12 0) (SOff 15 0), SOff 33 (-4));
    (SAlu ALU_ADD (SOff 5 0) (SOff 15 0), SOff 33 4) ].
Definition ccu_fsL : list (nat * afact) :=
  [hc_pfact 10 0; hc_pfact 17 0; hc_pfact 33 2;
   (34%nat, mkAF 0 (2 ^ 32 - 1) 0); (35%nat, mkAF 0 (2 ^ 32 - 1) 0); (36%nat, mkAF 0 (2 ^ 32 - 1) 0);
   (37%nat, mkAF 0 255 0); (38%nat, mkAF 0 255 0); (39%nat, mkAF 0 255 0);
   (14%nat, mkAF 0 27 0); (15%nat, mkAF 0 108 0); (7%nat, mkAF 0 120 0); (28%nat, mkAF 120 120 0);
   (16%nat, mkAF (2 ^ 63 - 1) (2 ^ 64 - 1 - 4096) 0); (6%nat, mkAF (2 ^ 63 - 1) (2 ^ 64 - 1 - 4096) 0)].
Definition ccu_SHL : list shent := [mkSHE 33 0 12; mkSHE 10 0 3].
Definition ss_ccu_L : sstate :=
  mkSS PCU_LH (hc_sr [((13%bv : bv 5), hc_Bx)]) [ccu_stk; ccu_xcell; ccu_ocell] None
    (mkFacts ((2%nat, mkAF (2 ^ 46) (2 ^ 47) 4) :: (32%nat, mkAF hc_SB hc_SB 0) :: ccu_fsL) [] ccu_alias).

(* ===================================== arithmetic ===================================== *)
(* `not rd,rs` is `xori rd,rs,-1` (lib/CJ/Lib/Bytes.v's lnot_mod64 is the same identity at the kit's literal) *)
Lemma ccu_lxor_mask : forall v, 0 <= v < 2 ^ 64 -> Z.lxor v (2 ^ 64 - 1) = 2 ^ 64 - 1 - v.
Proof.
intros v Hv. change (2 ^ 64 - 1) with (Z.ones 64) at 1.
assert (Hb : Z.lxor v (Z.ones 64) = Z.land (Z.lnot v) (Z.ones 64)).
{ apply Z.bits_inj'. intros i Hi. rewrite Z.lxor_spec, Z.land_spec, Z.lnot_spec by lia.
  destruct (Z.lt_ge_cases i 64).
  - rewrite Z.ones_spec_low by lia. rewrite xorb_true_r, andb_true_r. reflexivity.
  - rewrite Z.ones_spec_high by lia. rewrite xorb_false_r, andb_false_r.
    apply Z.bits_above_log2; [lia|].
    destruct (Z.eq_dec v 0) as [->|Hz]; [cbn; lia|].
    apply Z.lt_le_trans with 64; [apply Z.log2_lt_pow2; lia | lia]. }
rewrite Hb, Z.land_ones by lia.
assert (HL : Z.lnot v = (2 ^ 64 - 1 - v) + (-1) * 2 ^ 64) by (unfold Z.lnot; lia).
rewrite HL, Z.mod_add by lia. apply Z.mod_small. lia.
Qed.
Lemma ccu_U_not : forall E n c v, bv_unsigned (ew E n) = v -> 0 <= v + c < 2 ^ 64 ->
U E (SAlu ALU_XOR (SOff n c) (SLit (-1))) = 2 ^ 64 - 1 - (v + c).
Proof.
intros E n c v Hew Hv. rewrite U_SAlu. cbn [zalu_raw].
rewrite U_SOff, Hew, (zcanon_id (v + c)) by (unfold M64; lia).
rewrite U_SLit. change (zcanon (-1)) with (2 ^ 64 - 1).
rewrite ccu_lxor_mask by lia. apply zcanon_id. unfold M64. lia.
Qed.
(* the callee-saved registers other than sp, s0 and s1, which this frame saves and restores *)
Definition CCU_CS : list (bv 5) := [3; 4; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.
Lemma ccu_cs_in : forall r : Z,
r = 3 \/ r = 4 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27 -> In (Z_to_bv 5 r) CCU_CS.
Proof.
intros r H. unfold CCU_CS. cbn [In].
repeat (destruct H as [->|H]); try subst r;
repeat (first [ left; apply bv_eq; reflexivity | right ]).
Qed.
Lemma ccu_idx8 : forall (rg : bvmap 5 word), getr rg (Z_to_bv 5 8) = getr rg (8%bv : bv 5).
Proof. intros rg. f_equal. Qed.
Lemma ccu_idx9 : forall (rg : bvmap 5 word), getr rg (Z_to_bv 5 9) = getr rg (9%bv : bv 5).
Proof. intros rg. f_equal. Qed.

Section h. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
(* a register the state holds as an atom plus a constant, as a 64-bit word *)
Lemma ccu_getr_off : forall (E : env) ss ms (H : word -> bool) (r : bv 5) (n : nat) (c v : Z),
st_ok rsegs E ss (restrict H ms) -> sr_get (ss_regs ss) r = SOff n c ->
bv_unsigned (ew E n) = v -> 0 <= v + c < 2 ^ 64 -> getr (ms_regs ms) r = w64 (v + c).
Proof.
intros E ss ms H r n c v HS Hsr Hew Hv. apply bv_eq.
rewrite (st_ok_restrict_reg rsegs H E ss ms r HS), Hsr, denot_SOff, Hew.
rewrite zcanon_id by (unfold M64; lia). symmetry. apply unsigned_lit_small. lia.
Qed.
Lemma ccu_getr_lit : forall (E : env) ss ms (H : word -> bool) (r : bv 5) (v : Z),
st_ok rsegs E ss (restrict H ms) -> sr_get (ss_regs ss) r = SLit v -> 0 <= v < 2 ^ 64 ->
getr (ms_regs ms) r = w64 v.
Proof.
intros E ss ms H r v HS Hsr Hv.
rewrite (st_ok_restrict_reg rsegs H E ss ms r HS), Hsr. apply hc_lit.
Qed.
(* a register the state holds as a plain atom *)
Lemma ccu_getr_same : forall (E : env) ss ms (H : word -> bool) (r : bv 5) (n : nat) (w : word),
st_ok rsegs E ss (restrict H ms) -> sr_get (ss_regs ss) r = SOff n 0 -> ew E n = w ->
getr (ms_regs ms) r = w.
Proof.
intros E ss ms H r n w HS Hsr Hew. apply bv_eq.
rewrite (st_ok_restrict_reg rsegs H E ss ms r HS), Hsr, denot_SOff, Hew, Z.add_0_r.
apply zcanon_id. pose proof (cc_u64 w) as Hb. unfold M64. lia.
Qed.
(* `slli`, `slli`, `sub` folded to a product: t2 = 12 rc *)
Lemma ccu_getr_mul : forall (E : env) ss ms (H : word -> bool) (r : bv 5) (n : nat) (v : Z),
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
(* `not rd,rs`: a6 = ~out and t1 = ~(x + 4) *)
Lemma ccu_getr_not : forall (E : env) ss ms (H : word -> bool) (r : bv 5) (n : nat) (c v : Z),
st_ok rsegs E ss (restrict H ms) -> sr_get (ss_regs ss) r = SAlu ALU_XOR (SOff n c) (SLit (-1)) ->
bv_unsigned (ew E n) = v -> 0 <= v + c < 2 ^ 64 ->
getr (ms_regs ms) r = w64 (2 ^ 64 - 1 - (v + c)).
Proof.
intros E ss ms H r n c v HS Hsr Hew Hv. apply bv_eq.
rewrite (st_ok_restrict_reg rsegs H E ss ms r HS), Hsr.
change (bv_unsigned (sv_denot E (SAlu ALU_XOR (SOff n c) (SLit (-1)))))
  with (U E (SAlu ALU_XOR (SOff n c) (SLit (-1)))).
rewrite (ccu_U_not E n c v Hew Hv). symmetry. apply unsigned_lit_small. lia.
Qed.
(* the 8-byte value a region's chunk holds, as the save slot keeps the caller's ra, s0 and s1 *)
Lemma ccu_chunk8_val : forall (E : env) ss ms (H : word -> bool) (r : YP09.region) (b off : Z) (n m : nat) (w : word),
st_ok rsegs E ss (restrict H ms) -> In r (ss_mem ss) -> YP09.r_base r = Some n ->
In (YP09.mkChunk off (CVal 8 (SOff m 0))) (YP09.r_chunks r) ->
bv_unsigned (ew E n) = b -> ew E m = w ->
val_mem rsegs (mrestrict H (ms_mem ms)) (b + off) 8 (bv_unsigned w).
Proof.
intros E ss ms H r b off n m w HS Hin Hb Hc Hbv Hw.
destruct (st_ok_mem_ok rsegs E ss (restrict H ms) HS) as (_ & Hrs & _).
pose proof (proj1 (Forall_forall _ _) Hrs r Hin) as HR.
unfold region_ok in HR. rewrite Hb in HR. cbn [base_val] in HR. rewrite Hbv in HR.
destruct HR as (_ & _ & _ & Hcs).
pose proof (proj1 (Forall_forall _ _) Hcs _ Hc) as Hck.
pose proof (cc_u64 w) as Hwr.
exact (val_of_chunk_ok rsegs E (mrestrict H (ms_mem ms)) b off 8 (SOff m 0) (bv_unsigned w) Hck
  ltac:(apply cc_denot_atom; [rewrite Hw; symmetry; apply Z_to_bv_bv_unsigned | exact Hwr])
  ltac:(change (8 * Z.of_N 8) with 64; lia) ltac:(cbn; lia)).
Qed.
End h.

(* ---- the tactics of this walk (lib/A/HPgChkBase.v's, with a stop pc and the env after a run) ---- *)
Ltac ccu_run_to stop :=
lazymatch goal with HS : st_ok _ _ _ _, HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, SHOK : sh_ok _ _ _ _ _ |- _ =>
aj_run_to_tok ccu_tbl_ok HS HJ SHOK hc_Bspan stop end; [hc_awr | ].
Ltac ccu_branch Hname :=
hc_branch ccu_tbl_ok; lazymatch goal with Hb : branch_taken _ _ _ = _ |- _ => rename Hb into Hname end.
Ltac ccu_io := let rec kio := first [apply same_io_refl | assumption | eapply same_io_trans; [| apply hc_same_io_wvb]; kio] in kio.
Ltac ccu_ew Hsrc Q :=
lazymatch type of Hsrc with ew _ ?n = ?v =>
lazymatch goal with HS : st_ok _ ?Ec _ _ |- _ =>
assert (Q : ew Ec n = v) by (repeat (rewrite ew_ewset_other by lia); exact Hsrc) end end.
Ltac ccu_bu Hsrc Q :=
lazymatch type of Hsrc with bv_unsigned (ew _ ?n) = ?v =>
lazymatch goal with HS : st_ok _ ?Ec _ _ |- _ =>
assert (Q : bv_unsigned (ew Ec n) = v) by (repeat (rewrite ew_ewset_other by lia); exact Hsrc) end end.
Ltac ccu_reg HS r Q :=
lazymatch type of HS with st_ok ?segs ?E ?ss (restrict ?H ?ms) =>
let e := eval vm_compute in (sr_get (ss_regs ss) r) in
assert (Q : getr (ms_regs ms) r = sv_denot E e) by exact (st_ok_restrict_reg segs H E ss ms r HS) end.

(* ===================================== the walk ===================================== *)
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis HBgot : as_got_shadow B = HCU_GOT_SH.
Hypothesis HBcell : as_shadow_cell B = HCU_SH_CELL.

(* the callee-saved registers other than sp, s0 and s1 *)
Definition ccu_cs_keep (r1 r2 : bvmap 5 word) : Prop :=
forall r, acallee_saved r -> r <> 2 -> r <> 8 -> r <> 9 -> getr r2 (Z_to_bv 5 r) = getr r1 (Z_to_bv 5 r).

(* the cut at the loop head, at index i *)
Definition ccu_inv (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world rsegs)
(mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z)) (lyc : alayout) (Sc : astate)
(W : world rsegs) (memc : word -> option byte) (mdc : Model) (k : Z) (regs : bvmap 5 word)
(o rcc x : Z) (cs : list cell) (i : Z) : world rsegs -> config -> Prop :=
fun W2 c2 => exists regs2 mem2 md2,
c2 = cfg_at rsegs PCU_LH regs2 mem2 md2 /\
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W2 mem2 md2 k /\
same_io mdc md2 /\
ccu_cs_keep regs regs2 /\
getr regs2 (1%bv : bv 5) = getr regs (1%bv : bv 5) /\
spZ regs2 = spZ regs - 32 /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - T_check_STK <= a < spZ regs) ->
 aview rsegs (w_H W2) mem2 a = aview rsegs (w_H W) memc a) /\
val_mem rsegs (mrestrict (w_H W2) mem2) (spZ regs2 + 8) 8 (bv_unsigned (getr regs (9%bv : bv 5))) /\
val_mem rsegs (mrestrict (w_H W2) mem2) (spZ regs2 + 16) 8 (bv_unsigned (getr regs (8%bv : bv 5))) /\
val_mem rsegs (mrestrict (w_H W2) mem2) (spZ regs2 + 24) 8 (bv_unsigned (getr regs (1%bv : bv 5))) /\
0 <= i < rcc /\
getr regs2 (5%bv : bv 5) = w64 (x + 8) /\
getr regs2 (6%bv : bv 5) = w64 (2 ^ 64 - 1 - (x + 4)) /\
getr regs2 (7%bv : bv 5) = w64 (12 * rcc) /\
getr regs2 (10%bv : bv 5) = w64 (o + 3 * i) /\
getr regs2 (12%bv : bv 5) = w64 x /\
getr regs2 (13%bv : bv 5) = w64 SHADOW_OFF /\
getr regs2 (14%bv : bv 5) = w64 (3 * i) /\
getr regs2 (15%bv : bv 5) = w64 (12 * i) /\
getr regs2 (16%bv : bv 5) = w64 (2 ^ 64 - 1 - o) /\
getr regs2 (17%bv : bv 5) = w64 (o + 1 + 3 * i) /\
getr regs2 (28%bv : bv 5) = w64 120 /\
hm_bytes rsegs (w_H W2) mem2 o (ha_cells_bytes cs) /\
hm_bytes rsegs (w_H W2) mem2 (x + 4) (x_cells_bytes cs) /\
range_addressable (aview rsegs (w_H W2) mem2) SHADOW_OFF o (3 * rcc) /\
range_addressable (aview rsegs (w_H W2) mem2) SHADOW_OFF (x + 4) (12 * rcc).

(* the `ret` leaf into hd_post (lib/A/HPgChkBase.v hc_leaf's conjuncts, as a lemma, so that the loop's exit can
   supply sp, s0, s1 and the other callee-saved registers through the cut) *)
Lemma ccu_post_of : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
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

Theorem hd_check_cells_B : hd_check_cells_specX rsegs B MT B_CHECK_CELLS.
Proof using MTL HBgot HBcell.
unfold hd_check_cells_specX, hd_pre.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs rcc o x cs
(HJ & Hra & Hra4 & Hgp & Htp & Hal16 & Hwlo & Hwhi & Hev) H10 H11 H12 Hrcc Vx RAx OSx (Happx & Himgx) Hx4 Hpos.
hcu_prelude.
destruct (hc_app_fact x 4 Happx ltac:(lia)) as (Hx0 & Hx1 & Hx2).
destruct (hcu_app_apart x 4 Himgx ltac:(lia)) as [Dgotx Dcellx].
unfold ASAN_CEIL in Hx1. unfold HC_PHI in Hx2.
assert (Dstkx : x + 4 <= spZ regs - 32 \/ spZ regs <= x)
  by (destruct (cc_off_disj regs x 4 ltac:(lia) OSx); lia).
(* the shadow byte of an application address lies far below the save slot *)
assert (SHOFF : forall p n a, in_app p n -> 0 <= n -> p <= a < p + n ->
  ~ (spZ regs - 32 <= shadow_of_addr SHADOW_OFF a < spZ regs)).
{ intros p n a Hap Hn Ha Hbad.
  destruct (hc_app_fact p n Hap Hn) as (Hp0 & Hp1 & Hp2).
  unfold ASAN_CEIL, HC_PHI in Hp1, Hp2.
  apply (hm_shadow_not_high a (spZ regs - 32)); [ unfold kHighMemEnd; lia | unfold kHighMemBeg; lia | lia ]. }

(* ----------------------------------- one turn of the loop ----------------------------------- *)
assert (LOOP : forall (i : Z) (W2 : world rsegs) (c2 : config),
  ccu_inv STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs o rcc x cs i W2 c2 ->
  SRr rsegs W2 c2 (fun W3 c3 =>
    hd_post rsegs B MT STK sp0 FP ly S W0 mem0 md0 own k T_check_STK regs lyc Sc W memc mdc
      (fun f => f = fx) (fun _ => False) (fun _ _ _ => True) W3 c3 \/
    exists i', 0 <= rcc - i' < rcc - i /\
      ccu_inv STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs o rcc x cs i' W3 c3)).
{ intros i W2 c2 HI. unfold ccu_inv in HI.
  destruct HI as (regs2 & mem2 & md2 & Hcfg & HJ2 & Hio2 & Hcs2 & Hra2 & Hsp2 & KEinv & Hs1 & Hs0 & Hsra &
    Hi & Q5 & Q6 & Q7 & Q10 & Q12 & Q13 & Q14 & Q15 & Q16 & Q17 & Q28 & Bout & Bx4 & RAo2 & RAx42).
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
  set (xsL := [x + 4 + 12 * i; cc_ch c; cc_pa c; cc_va c; cc_ch c; cc_pa c; cc_va c;
               bv_unsigned (getr regs (8%bv : bv 5)); bv_unsigned (getr regs (9%bv : bv 5))]).
  remember (Ereg regs2 (hc_extra xsL)) as E eqn:HE.
  assert (Usp : bv_unsigned (ew E 2) = spZ regs2)
    by (subst E; rewrite (ew_Ereg_nat regs2 _ 2 2%bv eq_refl); reflexivity).
  assert (E32 : ew E 32 = Z_to_bv 64 SHADOW_OFF) by (subst E; apply hc_E32).
  assert (E1 : ew E 1 = getr regs 1)
    by (subst E; rewrite (ew_Ereg_nat regs2 _ 1 1%bv eq_refl); exact Hra2).
  assert (E5 : bv_unsigned (ew E 5) = x + 8)
    by (subst E; rewrite (ew_Ereg_nat regs2 _ 5 5%bv eq_refl), Q5; apply unsigned_lit_small; lia).
  assert (E6 : bv_unsigned (ew E 6) = 2 ^ 64 - 1 - (x + 4))
    by (subst E; rewrite (ew_Ereg_nat regs2 _ 6 6%bv eq_refl), Q6; apply unsigned_lit_small; lia).
  assert (E7 : bv_unsigned (ew E 7) = 12 * rcc)
    by (subst E; rewrite (ew_Ereg_nat regs2 _ 7 7%bv eq_refl), Q7; apply unsigned_lit_small; lia).
  assert (E10 : bv_unsigned (ew E 10) = o + 3 * i)
    by (subst E; rewrite (ew_Ereg_nat regs2 _ 10 10%bv eq_refl), Q10; apply unsigned_lit_small; lia).
  assert (E12 : bv_unsigned (ew E 12) = x)
    by (subst E; rewrite (ew_Ereg_nat regs2 _ 12 12%bv eq_refl), Q12; apply unsigned_lit_small; lia).
  assert (E14 : bv_unsigned (ew E 14) = 3 * i)
    by (subst E; rewrite (ew_Ereg_nat regs2 _ 14 14%bv eq_refl), Q14; apply unsigned_lit_small; lia).
  assert (E15 : bv_unsigned (ew E 15) = 12 * i)
    by (subst E; rewrite (ew_Ereg_nat regs2 _ 15 15%bv eq_refl), Q15; apply unsigned_lit_small; lia).
  assert (E16 : bv_unsigned (ew E 16) = 2 ^ 64 - 1 - o)
    by (subst E; rewrite (ew_Ereg_nat regs2 _ 16 16%bv eq_refl), Q16; apply unsigned_lit_small; lia).
  assert (E17 : bv_unsigned (ew E 17) = o + 1 + 3 * i)
    by (subst E; rewrite (ew_Ereg_nat regs2 _ 17 17%bv eq_refl), Q17; apply unsigned_lit_small; lia).
  assert (E28 : bv_unsigned (ew E 28) = 120)
    by (subst E; rewrite (ew_Ereg_nat regs2 _ 28 28%bv eq_refl), Q28; apply unsigned_lit_small; lia).
  assert (E13 : sv_denot E hc_Bx = getr regs2 13)
    by (unfold hc_Bx; apply bv_eq; rewrite denot_SOff, E32, Z.add_0_r, Q13;
        rewrite !unsigned_lit_small by (unfold SHADOW_OFF; lia); reflexivity).
  assert (E33w : ew E 33 = Z_to_bv 64 (x + 4 + 12 * i)) by (subst E; exact (cc_Eextra regs2 xsL 0)).
  assert (E33 : bv_unsigned (ew E 33) = x + 4 + 12 * i)
    by (rewrite E33w; apply unsigned_lit_small; lia).
  assert (E34 : ew E 34 = Z_to_bv 64 (cc_ch c)) by (subst E; exact (cc_Eextra regs2 xsL 1)).
  assert (E35 : ew E 35 = Z_to_bv 64 (cc_pa c)) by (subst E; exact (cc_Eextra regs2 xsL 2)).
  assert (E36 : ew E 36 = Z_to_bv 64 (cc_va c)) by (subst E; exact (cc_Eextra regs2 xsL 3)).
  assert (E37 : ew E 37 = Z_to_bv 64 (cc_ch c)) by (subst E; exact (cc_Eextra regs2 xsL 4)).
  assert (E38 : ew E 38 = Z_to_bv 64 (cc_pa c)) by (subst E; exact (cc_Eextra regs2 xsL 5)).
  assert (E39 : ew E 39 = Z_to_bv 64 (cc_va c)) by (subst E; exact (cc_Eextra regs2 xsL 6)).
  assert (E40 : ew E 40 = Z_to_bv 64 (bv_unsigned (getr regs (8%bv : bv 5))))
    by (subst E; exact (cc_Eextra regs2 xsL 7)).
  assert (E41 : ew E 41 = Z_to_bv 64 (bv_unsigned (getr regs (9%bv : bv 5))))
    by (subst E; exact (cc_Eextra regs2 xsL 8)).
  assert (HS : st_ok rsegs E ss_ccu_L
    (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 PCU_LH) mem2 (seg_rom rsegs)))).
  { rewrite restrict_mkst_fx. unfold ss_ccu_L. subst E. apply (entry_st_ok_full rsegs).
    - apply hc_regs_ok. apply Forall_cons; [|apply Forall_nil]. cbn [fst snd]. split.
      + apply hc_nz. vm_compute. discriminate.
      + exact E13.
    - vm_compute. reflexivity.
    - unfold ccu_stk, ccu_xcell, ccu_ocell.
      repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      + rewrite Usp. split; [lia|]. split; [lia|]. split; [intros oo Hoo; lia|].
        constructor; [|constructor; [|constructor; [|constructor]]].
        * apply (chunk_ok_val rsegs _ _ (spZ regs2) 8 8 (SOff 41 0) (bv_unsigned (getr regs (9%bv : bv 5))));
          [ apply cc_denot_atom; [exact E41 | apply cc_u64] | change (8 * Z.of_N 8) with 64; apply cc_u64
          | zside | exact Hs1 ].
        * apply (chunk_ok_val rsegs _ _ (spZ regs2) 16 8 (SOff 40 0) (bv_unsigned (getr regs (8%bv : bv 5))));
          [ apply cc_denot_atom; [exact E40 | apply cc_u64] | change (8 * Z.of_N 8) with 64; apply cc_u64
          | zside | exact Hs0 ].
        * apply (chunk_ok_val rsegs _ _ (spZ regs2) 24 8 (SOff 1 0) (bv_unsigned (getr regs (1%bv : bv 5))));
          [ apply cc_denot_atom; [rewrite E1; symmetry; apply Z_to_bv_bv_unsigned | apply cc_u64]
          | change (8 * Z.of_N 8) with 64; apply cc_u64 | zside | exact Hsra ].
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
        * apply (hc_chunk1 _ _ (o + 1 + 3 * i) (-1) (SOff 37 0) (cc_ch c));
          [ apply cc_denot_atom; [exact E37 | lia] | lia |].
          replace (o + 1 + 3 * i + -1) with (o + Z.of_nat (3 * Z.to_nat i + 0)) by lia. exact U0.
        * apply (hc_chunk1 _ _ (o + 1 + 3 * i) 0 (SOff 38 0) (cc_pa c));
          [ apply cc_denot_atom; [exact E38 | lia] | lia |].
          replace (o + 1 + 3 * i + 0) with (o + Z.of_nat (3 * Z.to_nat i + 1)) by lia. exact U1.
        * apply (hc_chunk1 _ _ (o + 1 + 3 * i) 1 (SOff 39 0) (cc_va c));
          [ apply cc_denot_atom; [exact E39 | lia] | lia |].
          replace (o + 1 + 3 * i + 1) with (o + Z.of_nat (3 * Z.to_nat i + 2)) by lia. exact U2.
    - assert (Dxo : x + 4 + 12 * i + 12 <= o + 3 * i \/ o + 1 + 3 * i + 2 <= x + 4 + 12 * i) by lia.
      assert (Dsx : x + 4 + 12 * i + 12 <= spZ regs2 \/ spZ regs2 + 32 <= x + 4 + 12 * i)
        by (destruct (cc_off_disj regs (x + 4) (12 * rcc) ltac:(lia) OSx4); lia).
      assert (Dso : o + 1 + 3 * i + 2 <= spZ regs2 \/ spZ regs2 + 32 <= o + 1 + 3 * i - 1)
        by (destruct (cc_off_disj regs o (3 * rcc) ltac:(lia) OSo); lia).
      clear Hdisj.
      apply pairwise_disjoint_of_extents.
      unfold ccu_stk, ccu_xcell, ccu_ocell, extent_of_region.
      cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite Usp, E33, E17.
      cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
    - split; [|split; [exact I|]].
      + cbn [f_atoms atoms_ok ccu_fsL hc_pfact]. unfold afact_ok. cbn [af_lo af_hi af_al2].
        rewrite Usp, E10, E17, E33, E14, E15, E7, E28, E16, E6, E32, E34, E35, E36, E37, E38, E39.
        rewrite !unsigned_lit_small by (unfold SHADOW_OFF; lia).
        change (2 ^ 4) with 16. change (2 ^ 2) with 4. rewrite Z.pow_0_r, !Z.mod_1_r.
        unfold hc_SB, SHADOW_OFF, HC_PHI in *.
        repeat split; try lia.
        all: first
          [ rewrite Hsp2; replace (spZ regs - 32) with (spZ regs + (-2) * 16) by ring;
            rewrite Z.mod_add by lia; exact Hal16
          | replace (x + 4 + 12 * i) with (x + (1 + 3 * i) * 4) by ring;
            rewrite Z.add_mod by lia; rewrite Hx4, Z.mod_mul by lia; reflexivity ].
      + cbn [f_alias alias_ok ccu_alias]. split; [|split; [|exact I]].
        * apply U_inj. rewrite U_SAlu. cbn [zalu_raw]. rewrite !U_SOff, E12, E15, E33, !Z.add_0_r.
          rewrite (zcanon_id x) by (unfold M64; lia). rewrite (zcanon_id (12 * i)) by (unfold M64; lia).
          rewrite !zcanon_id by (unfold M64; lia). lia.
        * apply U_inj. rewrite U_SAlu. cbn [zalu_raw]. rewrite !U_SOff, E5, E15, E33, !Z.add_0_r.
          rewrite (zcanon_id (x + 8)) by (unfold M64; lia). rewrite (zcanon_id (12 * i)) by (unfold M64; lia).
          rewrite !zcanon_id by (unfold M64; lia). lia. }
  clear Hdisj.
  assert (SHOK : sh_ok rsegs hc_Bx ccu_SHL E (mrestrict (w_H W2) mem2)).
  { unfold sh_ok, ccu_SHL. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
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
  assert (HAE : env_agree 32 (Ereg regs2 (hc_extra xsL)) E) by (subst E; apply env_agree_refl).
  clear HE. rename Usp into B2.
  rewrite Hcfg. unfold cfg_at. change (w64 PCU_LH) with (Z_to_bv 64 PCU_LH).
  assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - T_check_STK <= a < spZ regs) ->
    aview rsegs (w_H W2) mem2 a = aview rsegs (w_H W2) mem2 a) by (intros; reflexivity).
  (* the three UBSan traps are decided; stop at the three comparisons, then the loop test *)
  ccu_run_to PCU_RET. hc_keep.
  ccu_branch Hb1.
  { exfalso. rewrite branch_ne_U in Hb1. ccu_ew E34 F34. ccu_ew E37 F37.
    rewrite (cc_U_sx32_small _ 34 (cc_ch c) F34 ltac:(lia)) in Hb1.
    rewrite (U_atom _ 37 (cc_ch c) F37) in Hb1 by lia.
    rewrite Z.eqb_refl in Hb1. cbn in Hb1. discriminate. }
  ccu_run_to PCU_RET. hc_keep.
  ccu_branch Hb2.
  { exfalso. rewrite branch_ne_U in Hb2. ccu_ew E35 F35. ccu_ew E38 F38.
    rewrite (cc_U_sx32_small _ 35 (cc_pa c) F35 ltac:(lia)) in Hb2.
    rewrite (U_atom _ 38 (cc_pa c) F38) in Hb2 by lia.
    rewrite Z.eqb_refl in Hb2. cbn in Hb2. discriminate. }
  ccu_run_to PCU_RET. hc_keep.
  ccu_branch Hb3.
  { exfalso. rewrite branch_ne_U in Hb3. ccu_ew E36 F36. ccu_ew E39 F39.
    rewrite (cc_U_sx32_small _ 36 (cc_va c) F36 ltac:(lia)) in Hb3.
    rewrite (U_atom _ 39 (cc_va c) F39) in Hb3 by lia.
    rewrite Z.eqb_refl in Hb3. cbn in Hb3. discriminate. }
  ccu_run_to PCU_RET. hc_keep.
  ccu_branch Hb4.
  { (* 12 rc = 12 (i + 1): the last turn, the epilogue and the `ret` *)
    rewrite branch_eq_U in Hb4. ccu_bu E7 F7. ccu_bu E15 F15.
    rewrite (U_atom _ 7 (12 * rcc) ltac:(apply bv_eq; rewrite F7; symmetry; apply unsigned_lit_small; lia)) in Hb4 by lia.
    rewrite (U_atom_off _ 15 (12 * i) 12 ltac:(apply bv_eq; rewrite F15; symmetry; apply unsigned_lit_small; lia)) in Hb4 by lia.
    apply Z.eqb_eq in Hb4.
    ccu_run_to PCU_RET. hc_keep.
    lazymatch goal with HSx : st_ok _ ?Ec ?ssx (restrict (w_H ?Wx) ?msx) |- _ =>
      ccu_reg HSx (1%bv : bv 5) R1;
      assert (Rsp : getr (ms_regs msx) (Z_to_bv 5 2) = getr regs (Z_to_bv 5 2));
      [ rewrite !cc_sp_idx;
        rewrite (ccu_getr_off Ec ssx msx (w_H Wx) (2%bv : bv 5) 2 32 (spZ regs2) HSx
          ltac:(vm_compute; reflexivity) ltac:(repeat (rewrite ew_ewset_other by lia); exact B2) ltac:(lia));
        rewrite Hsp2; replace (spZ regs - 32 + 32) with (spZ regs) by lia;
        unfold spZ; apply Z_to_bv_bv_unsigned
      | ] end.
    lazymatch goal with HSx : st_ok _ ?Ec ?ssx (restrict (w_H ?Wx) ?msx) |- _ =>
      assert (Rs0 : getr (ms_regs msx) (Z_to_bv 5 8) = getr regs (Z_to_bv 5 8));
      [ rewrite !ccu_idx8;
        rewrite (ccu_getr_same Ec ssx msx (w_H Wx) (8%bv : bv 5) 40 (getr regs (8%bv : bv 5)) HSx
          ltac:(vm_compute; reflexivity)
          ltac:(repeat (rewrite ew_ewset_other by lia); rewrite E40; apply Z_to_bv_bv_unsigned));
        reflexivity
      | ] end.
    lazymatch goal with HSx : st_ok _ ?Ec ?ssx (restrict (w_H ?Wx) ?msx) |- _ =>
      assert (Rs1 : getr (ms_regs msx) (Z_to_bv 5 9) = getr regs (Z_to_bv 5 9));
      [ rewrite !ccu_idx9;
        rewrite (ccu_getr_same Ec ssx msx (w_H Wx) (9%bv : bv 5) 41 (getr regs (9%bv : bv 5)) HSx
          ltac:(vm_compute; reflexivity)
          ltac:(repeat (rewrite ew_ewset_other by lia); rewrite E41; apply Z_to_bv_bv_unsigned));
        reflexivity
      | eapply (SRr_ret_at rsegs ccu_tbl ccu_tbl_ok hcu_wx Wx Ec); [exact HSx | reflexivity | vm_compute; reflexivity |] ] end.
    intros mat'. left.
    lazymatch goal with HSx : st_ok _ ?Ec _ (restrict _ ?msx) |- _ =>
    eapply (ccu_post_of STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs _ (ms_regs msx) (ms_mem msx)) end.
    - eapply ajournal_materialize; eassumption.
    - ccu_io.
    - (* every callee-saved register: sp, s0 and s1 restored, the others never written *)
      intros r Hr.
      destruct (Z.eq_dec r 2) as [->|Hne2]; [exact Rsp|].
      destruct (Z.eq_dec r 8) as [->|Hne8]; [exact Rs0|].
      destruct (Z.eq_dec r 9) as [->|Hne9]; [exact Rs1|].
      assert (Hcase : r = 3 \/ r = 4 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
        r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by (unfold acallee_saved in Hr; lia).
      lazymatch goal with HSx : st_ok _ ?Ec ?ssx (restrict _ ?msx) |- _ =>
        etransitivity;
        [ exact (regs_kept_of_st_ok rsegs Ec ssx (restrict (w_H W2) msx) regs2 (hc_extra xsL)
            CCU_CS HSx ltac:(env_agree_chain HAE)
            ltac:(vm_compute; reflexivity) (Z_to_bv 5 r)
            ltac:(apply ccu_cs_in; exact Hcase))
        | apply Hcs2; [exact Hr | exact Hne2 | exact Hne8 | exact Hne9] ] end.
    - lazymatch goal with HSx : st_ok _ ?Ec _ _ |- _ =>
        rewrite R1; apply bv_eq; rewrite denot_SOff;
        rewrite (ltac:(repeat (rewrite ew_ewset_other by lia); exact E1) : ew Ec 1 = getr regs 1);
        rewrite Z.add_0_r; apply zcanon_id;
        pose proof (cc_u64 (getr regs 1)) as Hb; unfold M64; lia end.
    - lazymatch goal with HSx : st_ok _ ?Ec _ _ |- _ =>
        rewrite R1;
        rewrite (ltac:(apply bv_eq; rewrite denot_SOff;
          rewrite (ltac:(repeat (rewrite ew_ewset_other by lia); exact E1) : ew Ec 1 = getr regs 1);
          rewrite Z.add_0_r; apply zcanon_id;
          pose proof (cc_u64 (getr regs 1)) as Hb; unfold M64; lia) : sv_denot Ec (SOff 1 0) = getr regs 1);
        exact Hra end.
    - intros a Ha Hz. rewrite (KE a Ha Hz). exact (KEinv a Ha Hz).
    - exact MTL. }
  { (* 12 rc <> 12 (i + 1): the back edge, the cut at i + 1 *)
    rewrite branch_eq_U in Hb4. ccu_bu E7 F7. ccu_bu E15 F15.
    rewrite (U_atom _ 7 (12 * rcc) ltac:(apply bv_eq; rewrite F7; symmetry; apply unsigned_lit_small; lia)) in Hb4 by lia.
    rewrite (U_atom_off _ 15 (12 * i) 12 ltac:(apply bv_eq; rewrite F15; symmetry; apply unsigned_lit_small; lia)) in Hb4 by lia.
    apply Z.eqb_neq in Hb4.
    ccu_run_to PCU_LH. hc_keep.
    lazymatch goal with HSx : st_ok _ ?Ec ?ssx (restrict (w_H ?Wx) ?msx) |- _ =>
      pose proof (st_ok_restrict_mkst rsegs (w_H Wx) Ec ssx msx HSx eq_refl) as Hshape;
      rewrite Hshape; apply SRr_ret; right; exists (i + 1); split; [lia|];
      unfold ccu_inv; exists (ms_regs msx), (ms_mem msx); eexists end.
    split; [reflexivity|].
    split; [first [eassumption | eapply ajournal_materialize; eassumption]|].
    split; [ccu_io|].
    split.
    { intros r Hr Hne2 Hne8 Hne9.
      assert (Hcase : r = 3 \/ r = 4 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
        r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by (unfold acallee_saved in Hr; lia).
      lazymatch goal with HSx : st_ok _ ?Ec ?ssx (restrict _ ?msx) |- _ =>
        etransitivity;
        [ exact (regs_kept_of_st_ok rsegs Ec ssx (restrict (w_H W2) msx) regs2 (hc_extra xsL)
            CCU_CS HSx ltac:(env_agree_chain HAE)
            ltac:(vm_compute; reflexivity) (Z_to_bv 5 r)
            ltac:(apply ccu_cs_in; exact Hcase))
        | apply Hcs2; [exact Hr | exact Hne2 | exact Hne8 | exact Hne9] ] end. }
    split.
    { lazymatch goal with HSx : st_ok _ ?Ec ?ssx (restrict _ ?msx) |- _ =>
        rewrite (ccu_getr_same Ec ssx msx (w_H W2) (1%bv : bv 5) 1 (getr regs 1) HSx
          ltac:(vm_compute; reflexivity) ltac:(repeat (rewrite ew_ewset_other by lia); exact E1)) end.
      reflexivity. }
    split.
    { unfold spZ at 1. lazymatch goal with HSx : st_ok _ ?Ec ?ssx (restrict _ ?msx) |- _ =>
        rewrite (ccu_getr_off Ec ssx msx (w_H W2) (2%bv : bv 5) 2 0 (spZ regs2) HSx
          ltac:(vm_compute; reflexivity) ltac:(repeat (rewrite ew_ewset_other by lia); exact B2) ltac:(lia)) end.
      rewrite unsigned_lit_small by lia. lia. }
    split; [intros a Ha Hz; rewrite (KE a Ha Hz); exact (KEinv a Ha Hz)|].
    (* the save slot: unchanged, and the three words still in its chunks *)
    assert (Rsp0 : spZ (ms_regs (ltac:(lazymatch goal with HSx : st_ok _ _ _ (restrict _ ?msx) |- _ => exact msx end))) = spZ regs2).
    { unfold spZ at 1. lazymatch goal with HSx : st_ok _ ?Ec ?ssx (restrict _ ?msx) |- _ =>
        rewrite (ccu_getr_off Ec ssx msx (w_H W2) (2%bv : bv 5) 2 0 (spZ regs2) HSx
          ltac:(vm_compute; reflexivity) ltac:(repeat (rewrite ew_ewset_other by lia); exact B2) ltac:(lia)) end.
      rewrite unsigned_lit_small by lia. lia. }
    split.
    { rewrite Rsp0. lazymatch goal with HSx : st_ok _ ?Ec ?ssx (restrict _ ?msx) |- _ =>
        exact (ccu_chunk8_val Ec ssx msx (w_H W2) ccu_stk (spZ regs2) 8 2 41 (getr regs (9%bv : bv 5)) HSx
          ltac:(unfold ccu_stk; cbn [ss_mem]; left; reflexivity) eq_refl
          ltac:(unfold ccu_stk; cbn [YP09.r_chunks]; left; reflexivity)
          ltac:(repeat (rewrite ew_ewset_other by lia); exact B2)
          ltac:(repeat (rewrite ew_ewset_other by lia); rewrite E41; apply Z_to_bv_bv_unsigned)) end. }
    split.
    { rewrite Rsp0. lazymatch goal with HSx : st_ok _ ?Ec ?ssx (restrict _ ?msx) |- _ =>
        exact (ccu_chunk8_val Ec ssx msx (w_H W2) ccu_stk (spZ regs2) 16 2 40 (getr regs (8%bv : bv 5)) HSx
          ltac:(unfold ccu_stk; cbn [ss_mem]; left; reflexivity) eq_refl
          ltac:(unfold ccu_stk; cbn [YP09.r_chunks]; right; left; reflexivity)
          ltac:(repeat (rewrite ew_ewset_other by lia); exact B2)
          ltac:(repeat (rewrite ew_ewset_other by lia); rewrite E40; apply Z_to_bv_bv_unsigned)) end. }
    split.
    { rewrite Rsp0. lazymatch goal with HSx : st_ok _ ?Ec ?ssx (restrict _ ?msx) |- _ =>
        exact (ccu_chunk8_val Ec ssx msx (w_H W2) ccu_stk (spZ regs2) 24 2 1 (getr regs (1%bv : bv 5)) HSx
          ltac:(unfold ccu_stk; cbn [ss_mem]; left; reflexivity) eq_refl
          ltac:(unfold ccu_stk; cbn [YP09.r_chunks]; right; right; left; reflexivity)
          ltac:(repeat (rewrite ew_ewset_other by lia); exact B2)
          ltac:(repeat (rewrite ew_ewset_other by lia); exact E1)) end. }
    split; [lia|].
    (* the twelve registers at the back edge *)
    lazymatch goal with HSx : st_ok _ ?Ec ?ssx (restrict _ ?msx) |- _ =>
      split; [ rewrite (ccu_getr_off Ec ssx msx (w_H W2) (5%bv : bv 5) 5 0 (x + 8) HSx
                 ltac:(vm_compute; reflexivity) ltac:(repeat (rewrite ew_ewset_other by lia); exact E5) ltac:(lia));
               f_equal; lia |];
      split; [ rewrite (ccu_getr_off Ec ssx msx (w_H W2) (6%bv : bv 5) 6 0 (2 ^ 64 - 1 - (x + 4)) HSx
                 ltac:(vm_compute; reflexivity) ltac:(repeat (rewrite ew_ewset_other by lia); exact E6) ltac:(lia));
               f_equal; lia |];
      split; [ rewrite (ccu_getr_off Ec ssx msx (w_H W2) (7%bv : bv 5) 7 0 (12 * rcc) HSx
                 ltac:(vm_compute; reflexivity) ltac:(repeat (rewrite ew_ewset_other by lia); exact E7) ltac:(lia));
               f_equal; lia |];
      split; [ rewrite (ccu_getr_off Ec ssx msx (w_H W2) (10%bv : bv 5) 10 3 (o + 3 * i) HSx
                 ltac:(vm_compute; reflexivity) ltac:(repeat (rewrite ew_ewset_other by lia); exact E10) ltac:(lia));
               f_equal; lia |];
      split; [ rewrite (ccu_getr_off Ec ssx msx (w_H W2) (12%bv : bv 5) 12 0 x HSx
                 ltac:(vm_compute; reflexivity) ltac:(repeat (rewrite ew_ewset_other by lia); exact E12) ltac:(lia));
               f_equal; lia |];
      split; [ rewrite (ccu_getr_off Ec ssx msx (w_H W2) (13%bv : bv 5) 32 0 SHADOW_OFF HSx
                 ltac:(vm_compute; reflexivity)
                 ltac:(repeat (rewrite ew_ewset_other by lia);
                       rewrite E32; apply unsigned_lit_small; unfold SHADOW_OFF; lia)
                 ltac:(unfold SHADOW_OFF; lia));
               f_equal; lia |];
      split; [ rewrite (ccu_getr_off Ec ssx msx (w_H W2) (14%bv : bv 5) 14 3 (3 * i) HSx
                 ltac:(vm_compute; reflexivity) ltac:(repeat (rewrite ew_ewset_other by lia); exact E14) ltac:(lia));
               f_equal; lia |];
      split; [ rewrite (ccu_getr_off Ec ssx msx (w_H W2) (15%bv : bv 5) 15 12 (12 * i) HSx
                 ltac:(vm_compute; reflexivity) ltac:(repeat (rewrite ew_ewset_other by lia); exact E15) ltac:(lia));
               f_equal; lia |];
      split; [ rewrite (ccu_getr_off Ec ssx msx (w_H W2) (16%bv : bv 5) 16 0 (2 ^ 64 - 1 - o) HSx
                 ltac:(vm_compute; reflexivity) ltac:(repeat (rewrite ew_ewset_other by lia); exact E16) ltac:(lia));
               f_equal; lia |];
      split; [ rewrite (ccu_getr_off Ec ssx msx (w_H W2) (17%bv : bv 5) 17 3 (o + 1 + 3 * i) HSx
                 ltac:(vm_compute; reflexivity) ltac:(repeat (rewrite ew_ewset_other by lia); exact E17) ltac:(lia));
               f_equal; lia |];
      split; [ rewrite (ccu_getr_off Ec ssx msx (w_H W2) (28%bv : bv 5) 28 0 120 HSx
                 ltac:(vm_compute; reflexivity) ltac:(repeat (rewrite ew_ewset_other by lia); exact E28) ltac:(lia));
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
assert (E8 : ew E 8 = getr regs 8) by (subst E; exact (ew_Ereg_nat regs _ 8 8%bv eq_refl)).
assert (E9 : ew E 9 = getr regs 9) by (subst E; exact (ew_Ereg_nat regs _ 9 9%bv eq_refl)).
assert (Hm32 : 0 <= rcc mod 2 ^ 32 < 2 ^ 32) by (apply Z.mod_pos_bound; lia).
assert (E10p : 0 < rcc -> bv_unsigned (ew E 10) = o).
{ intros Hp. destruct (Hpos Hp) as (_ & _ & Hoa & Hob & _).
  subst E. rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl), H10. apply unsigned_lit_small. lia. }
assert (D33 : sv_denot E (SOff 33 0) = Z_to_bv 64 (rcc mod 2 ^ 32))
  by (apply cc_denot_atom; [exact E33 | lia]).
assert (HS : st_ok rsegs E (ss_hcu B_CHECK_CELLS [] ccu_rsP ccu_fsP)
  (restrict (w_H W) (mkst regs (Z_to_bv 64 B_CHECK_CELLS) memc (seg_rom rsegs)))).
{ subst E. apply (hcu_entry B_CHECK_CELLS [] [rcc mod 2 ^ 32] ccu_rsP ccu_fsP W regs memc
    ltac:(unfold B_CHECK_CELLS; lia) (Forall_nil _) Hpr Hsp Kgot Kcell).
  - vm_compute. reflexivity.
  - unfold ccu_rsP. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    + unfold ccu_stk_lo, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
      intros oo Hoo. apply (apresent_writable rsegs). apply Hpres. lia.
    + apply (hc_data_ok _ _ 12 x 0 4 _ E12); [lia | lia |].
      apply Forall_cons; [|apply Forall_nil].
      apply (hc_chunk4 _ _ x 0 (SOff 33 0) (rcc mod 2 ^ 32) D33 ltac:(lia)).
      rewrite Z.add_0_r. exact Vx.
  - unfold hcu_base_regions, ccu_rsP, ccu_stk_lo, hc_stack_region, hcu_got_region, hcu_cell_region, hc_data,
      extent_of_region.
    cbn [app map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite Usp, E12.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    unfold HCU_GOT_SH, HCU_SH_CELL in *. repeat split; lia.
  - cbn [atoms_ok ccu_fsP hc_pfact]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite Usp, E12, E32, E33, !unsigned_lit_small by (unfold SHADOW_OFF; lia).
    change (2 ^ 4) with 16. change (2 ^ 2) with 4. rewrite Z.pow_0_r, !Z.mod_1_r.
    unfold hc_SB, SHADOW_OFF, HC_PHI in *. repeat split; lia. }
assert (SHOK : sh_ok rsegs hc_Bx ccu_SHP E (mrestrict (w_H W) memc)).
{ unfold sh_ok, ccu_SHP. apply Forall_cons; [|apply Forall_nil].
  apply (hc_shent (w_H W) memc E 12 x 0 4);
  [ replace (x + 0) with x by lia; replace (4 - 0) with 4 by lia; exact RAx
  | replace (x + 0) with x by lia; replace (4 - 0) with 4 by lia; exact Happx
  | exact E32 | exact E12 | lia ]. }
assert (HAE : env_agree 32 (Ereg regs (hc_extra [rcc mod 2 ^ 32])) E) by (subst E; apply env_agree_refl).
clear HE. rename Usp into B2.
(* the walk writes the whole 32-byte frame [sp - 32, sp), which is the callee's stack window [sp - T_check_STK, sp) *)
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 32 <= a < spZ regs) ->
  aview rsegs (w_H W) memc a = aview rsegs (w_H W) memc a) by (intros; reflexivity).
unfold cfg_at. change (w64 B_CHECK_CELLS) with (Z_to_bv 64 B_CHECK_CELLS).
(* the whole walk: the prologue's two tests, then either the epilogue or the loop *)
eapply (SRr_bind rsegs W _ (fun W2 c2 =>
  hd_post rsegs B MT STK sp0 FP ly S W0 mem0 md0 own k T_check_STK regs lyc Sc W memc mdc
    (fun f => f = fx) (fun _ => False) (fun _ _ _ => True) W2 c2 \/
  ccu_inv STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs o rcc x cs 0 W2 c2)).
{ (* 0x841c0 .. 0x841f4 (x's alignment trap decided), stop at the `bne a1,a4` 0x841f8 *)
  ccu_run_to PCU_LH. hc_keep.
  ccu_branch Hbne.
  { exfalso. rewrite branch_ne_U in Hbne. ccu_ew E11 F11. ccu_ew E33 F33.
    rewrite (cc_U_wrap _ 11 rcc F11) in Hbne.
    rewrite (cc_U_sx32 _ 33 rcc F33 ltac:(lia)) in Hbne.
    rewrite Z.eqb_refl in Hbne. cbn in Hbne. discriminate. }
  (* 0x841fc blez a1 *)
  ccu_run_to PCU_LH. hc_keep.
  ccu_branch Hble.
  { (* rc <= 0: nothing to check, the epilogue and the `ret` *)
    rewrite cc_branch_ge, cc_Sg_lit in Hble. ccu_ew E11 G11.
    rewrite (cc_Sg_off _ 11 rcc G11 ltac:(lia)) in Hble.
    ccu_run_to PCU_RET. hc_keep.
    lazymatch goal with HSx : st_ok _ ?Ec ?ssx (restrict (w_H ?Wx) ?msx) |- _ =>
      ccu_reg HSx (1%bv : bv 5) R1;
      eapply (SRr_ret_at rsegs ccu_tbl ccu_tbl_ok hcu_wx Wx Ec); [exact HSx | reflexivity | vm_compute; reflexivity |]
    end.
    intros mat'. left.
    lazymatch goal with HSx : st_ok _ ?Ec _ (restrict _ ?msx) |- _ =>
    eapply (ccu_post_of STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs _ (ms_regs msx) (ms_mem msx)) end.
    - first [eassumption | eapply ajournal_materialize; eassumption].
    - ccu_io.
    - lazymatch goal with HSx : st_ok _ _ _ _ |- _ =>
        eapply aregs_preserved_of_st_ok; [exact HSx | env_agree_chain HAE | vm_compute; reflexivity] end.
    - lazymatch goal with HSx : st_ok _ ?Ec _ _ |- _ =>
        rewrite R1; apply bv_eq; rewrite denot_SOff;
        rewrite (ltac:(repeat (rewrite ew_ewset_other by lia); exact E1) : ew Ec 1 = getr regs 1);
        rewrite Z.add_0_r; apply zcanon_id;
        pose proof (cc_u64 (getr regs 1)) as Hb; unfold M64; lia end.
    - lazymatch goal with HSx : st_ok _ ?Ec _ _ |- _ =>
        rewrite R1;
        rewrite (ltac:(apply bv_eq; rewrite denot_SOff;
          rewrite (ltac:(repeat (rewrite ew_ewset_other by lia); exact E1) : ew Ec 1 = getr regs 1);
          rewrite Z.add_0_r; apply zcanon_id;
          pose proof (cc_u64 (getr regs 1)) as Hb; unfold M64; lia) : sv_denot Ec (SOff 1 0) = getr regs 1);
        exact Hra end.
    - intros a Ha Hz. apply (KE a Ha). intros Hc. apply Hz. unfold T_check_STK. lia.
    - exact MTL. }
  { (* 0 < rc: the loop set-up, then the cut at index 0 *)
    rewrite cc_branch_ge, cc_Sg_lit in Hble. ccu_ew E11 G11.
    rewrite (cc_Sg_off _ 11 rcc G11 ltac:(lia)) in Hble.
    assert (Hrpos : 0 < rcc) by (destruct (Z.ltb_spec 0 rcc); [lia | cbn in Hble; discriminate]).
    destruct (Hpos Hrpos) as (Hlen & Hbok & Ho0 & Ho1 & Hxa & Hxb & Gout & RAo & OSo & APo & Gx4 & RAx4 & OSx4 & APx4 & Hdisj).
    destruct APo as (Happo & Himgo). destruct APx4 as (Happx4 & Himgx4).
    destruct (hc_app_fact o (3 * rcc) Happo ltac:(lia)) as (Ho4096 & Hohi & _).
    destruct (hc_app_fact (x + 4) (12 * rcc) Happx4 ltac:(lia)) as (Hx4096 & Hxhi & _).
    unfold ASAN_CEIL, HC_PHI in Hohi, Hxhi.
    ccu_run_to PCU_LH. hc_keep.
    lazymatch goal with HSx : st_ok _ ?Ec ?ssx (restrict (w_H ?Wx) ?msx) |- _ =>
      pose proof (st_ok_restrict_mkst rsegs (w_H Wx) Ec ssx msx HSx eq_refl) as Hshape;
      rewrite Hshape; apply SRr_ret; right;
      unfold ccu_inv; exists (ms_regs msx), (ms_mem msx); eexists end.
    split; [reflexivity|].
    split; [first [eassumption | eapply ajournal_materialize; eassumption]|].
    split; [ccu_io|].
    split.
    { intros r Hr Hne2 Hne8 Hne9.
      assert (Hcase : r = 3 \/ r = 4 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
        r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by (unfold acallee_saved in Hr; lia).
      lazymatch goal with HSx : st_ok _ ?Ec ?ssx (restrict _ ?msx) |- _ =>
        exact (regs_kept_of_st_ok rsegs Ec ssx (restrict (w_H W) msx) regs (hc_extra [rcc mod 2 ^ 32])
          CCU_CS HSx ltac:(env_agree_chain HAE)
          ltac:(vm_compute; reflexivity) (Z_to_bv 5 r)
          ltac:(apply ccu_cs_in; exact Hcase)) end. }
    split.
    { lazymatch goal with HSx : st_ok _ ?Ec ?ssx (restrict _ ?msx) |- _ =>
        rewrite (ccu_getr_same Ec ssx msx (w_H W) (1%bv : bv 5) 1 (getr regs 1) HSx
          ltac:(vm_compute; reflexivity) ltac:(repeat (rewrite ew_ewset_other by lia); exact E1)) end.
      reflexivity. }
    split.
    { unfold spZ at 1. lazymatch goal with HSx : st_ok _ ?Ec ?ssx (restrict _ ?msx) |- _ =>
        rewrite (ccu_getr_off Ec ssx msx (w_H W) (2%bv : bv 5) 2 (-32) (spZ regs) HSx
          ltac:(vm_compute; reflexivity) ltac:(repeat (rewrite ew_ewset_other by lia); exact B2) ltac:(lia)) end.
      rewrite unsigned_lit_small by lia. lia. }
    split; [intros a Ha Hz; apply (KE a Ha); intros Hc; apply Hz; unfold T_check_STK; lia|].
    assert (Rsp0 : spZ (ms_regs (ltac:(lazymatch goal with HSx : st_ok _ _ _ (restrict _ ?msx) |- _ => exact msx end))) = spZ regs - 32).
    { unfold spZ at 1. lazymatch goal with HSx : st_ok _ ?Ec ?ssx (restrict _ ?msx) |- _ =>
        rewrite (ccu_getr_off Ec ssx msx (w_H W) (2%bv : bv 5) 2 (-32) (spZ regs) HSx
          ltac:(vm_compute; reflexivity) ltac:(repeat (rewrite ew_ewset_other by lia); exact B2) ltac:(lia)) end.
      rewrite unsigned_lit_small by lia. lia. }
    split.
    { rewrite Rsp0. replace (spZ regs - 32 + 8) with (spZ regs + -24) by lia.
      lazymatch goal with HSx : st_ok _ ?Ec ?ssx (restrict _ ?msx) |- _ =>
        exact (ccu_chunk8_val Ec ssx msx (w_H W)
          (YP09.mkRegion (Some 2%nat) (-32) (-16) (-32) (-16) [YP09.mkChunk (-24) (CVal 8 (SOff 9 0))])
          (spZ regs) (-24) 2 9 (getr regs (9%bv : bv 5)) HSx
          ltac:(cbn [ss_mem]; right; right; right; left; reflexivity) eq_refl
          ltac:(cbn [YP09.r_chunks]; left; reflexivity)
          ltac:(repeat (rewrite ew_ewset_other by lia); exact B2)
          ltac:(repeat (rewrite ew_ewset_other by lia); exact E9)) end. }
    split.
    { rewrite Rsp0. replace (spZ regs - 32 + 16) with (spZ regs + -16) by lia.
      lazymatch goal with HSx : st_ok _ ?Ec ?ssx (restrict _ ?msx) |- _ =>
        exact (ccu_chunk8_val Ec ssx msx (w_H W)
          (YP09.mkRegion (Some 2%nat) (-16) 0 (-16) 0
             [YP09.mkChunk (-16) (CVal 8 (SOff 8 0)); YP09.mkChunk (-8) (CVal 8 (SOff 1 0))])
          (spZ regs) (-16) 2 8 (getr regs (8%bv : bv 5)) HSx
          ltac:(cbn [ss_mem]; left; reflexivity) eq_refl
          ltac:(cbn [YP09.r_chunks]; left; reflexivity)
          ltac:(repeat (rewrite ew_ewset_other by lia); exact B2)
          ltac:(repeat (rewrite ew_ewset_other by lia); exact E8)) end. }
    split.
    { rewrite Rsp0. replace (spZ regs - 32 + 24) with (spZ regs + -8) by lia.
      lazymatch goal with HSx : st_ok _ ?Ec ?ssx (restrict _ ?msx) |- _ =>
        exact (ccu_chunk8_val Ec ssx msx (w_H W)
          (YP09.mkRegion (Some 2%nat) (-16) 0 (-16) 0
             [YP09.mkChunk (-16) (CVal 8 (SOff 8 0)); YP09.mkChunk (-8) (CVal 8 (SOff 1 0))])
          (spZ regs) (-8) 2 1 (getr regs (1%bv : bv 5)) HSx
          ltac:(cbn [ss_mem]; left; reflexivity) eq_refl
          ltac:(cbn [YP09.r_chunks]; right; left; reflexivity)
          ltac:(repeat (rewrite ew_ewset_other by lia); exact B2)
          ltac:(repeat (rewrite ew_ewset_other by lia); exact E1)) end. }
    split; [lia|].
    lazymatch goal with HSx : st_ok _ ?Ec ?ssx (restrict _ ?msx) |- _ =>
      split; [ rewrite (ccu_getr_off Ec ssx msx (w_H W) (5%bv : bv 5) 12 8 x HSx
                 ltac:(vm_compute; reflexivity) ltac:(repeat (rewrite ew_ewset_other by lia); exact E12) ltac:(lia));
               reflexivity |];
      split; [ rewrite (ccu_getr_not Ec ssx msx (w_H W) (6%bv : bv 5) 12 4 x HSx
                 ltac:(vm_compute; reflexivity) ltac:(repeat (rewrite ew_ewset_other by lia); exact E12) ltac:(lia));
               reflexivity |];
      split; [ rewrite (ccu_getr_mul Ec ssx msx (w_H W) (7%bv : bv 5) 11 rcc HSx
                 ltac:(vm_compute; reflexivity) ltac:(repeat (rewrite ew_ewset_other by lia); exact E11) ltac:(lia));
               reflexivity |];
      split; [ rewrite (ccu_getr_off Ec ssx msx (w_H W) (10%bv : bv 5) 10 0 o HSx
                 ltac:(vm_compute; reflexivity) ltac:(repeat (rewrite ew_ewset_other by lia); exact (E10p Hrpos))
                 ltac:(lia));
               f_equal; lia |];
      split; [ rewrite (ccu_getr_off Ec ssx msx (w_H W) (12%bv : bv 5) 12 0 x HSx
                 ltac:(vm_compute; reflexivity) ltac:(repeat (rewrite ew_ewset_other by lia); exact E12) ltac:(lia));
               f_equal; lia |];
      split; [ rewrite (ccu_getr_off Ec ssx msx (w_H W) (13%bv : bv 5) 32 0 SHADOW_OFF HSx
                 ltac:(vm_compute; reflexivity)
                 ltac:(repeat (rewrite ew_ewset_other by lia);
                       rewrite E32; apply unsigned_lit_small; unfold SHADOW_OFF; lia)
                 ltac:(unfold SHADOW_OFF; lia));
               f_equal; lia |];
      split; [ rewrite (ccu_getr_lit Ec ssx msx (w_H W) (14%bv : bv 5) 0 HSx
                 ltac:(vm_compute; reflexivity) ltac:(lia));
               f_equal; lia |];
      split; [ rewrite (ccu_getr_lit Ec ssx msx (w_H W) (15%bv : bv 5) 0 HSx
                 ltac:(vm_compute; reflexivity) ltac:(lia));
               f_equal; lia |];
      split; [ rewrite (ccu_getr_not Ec ssx msx (w_H W) (16%bv : bv 5) 10 0 o HSx
                 ltac:(vm_compute; reflexivity) ltac:(repeat (rewrite ew_ewset_other by lia); exact (E10p Hrpos))
                 ltac:(lia));
               f_equal; lia |];
      split; [ rewrite (ccu_getr_off Ec ssx msx (w_H W) (17%bv : bv 5) 10 1 o HSx
                 ltac:(vm_compute; reflexivity) ltac:(repeat (rewrite ew_ewset_other by lia); exact (E10p Hrpos))
                 ltac:(lia));
               f_equal; lia |];
      split; [ rewrite (ccu_getr_lit Ec ssx msx (w_H W) (28%bv : bv 5) 120 HSx
                 ltac:(vm_compute; reflexivity) ltac:(lia));
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
  (ccu_inv STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs o rcc x cs)
  (hd_post rsegs B MT STK sp0 FP ly S W0 mem0 md0 own k T_check_STK regs lyc Sc W memc mdc
    (fun f => f = fx) (fun _ => False) (fun _ _ _ => True)) LOOP 0 W2 c2 HI).
Qed.
End c.

Print Assumptions hd_check_cells_B.
