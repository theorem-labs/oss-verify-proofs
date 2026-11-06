(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: ported from proofs/cgif/cgif_file_fuzzer/lib/A/AChd.v (entry state, region and fact proofs, the run/branch loop and its leaf) with the caller-journal leaf of lib/A/ACeu.v rfc_A_ok, aview_frame_off of lib/A/AD28.v (as kept_step) and frm_off_img of lib/A/ACeh.v (as frame_not_img) at c8557374ad2e to libreac/fuzz_knock: lib_asan3_0_listing -> knock_asan_listing, AF_asan3_cmpPixel -> AF_asan_reac_knock_step, tcmp_spec / tcmp_post -> tknock_step_specX / kn_post_step of lib/A/APgCSpec.v, cmp_entry / cmp_regions / cmp_facts / ss_cmp / cmp_SH / cmp_extra / EC / CBx / CBspan / pb_cmpPixel -> step_entry / step_regions / step_facts / ss_step / step_SH / step_extra / EK / KBx / KBspan / pb_knock_stepX; constants: TCMP_STK 16 + ESTACK -> T_step_STK 16, shadow-base atom 42 -> 39, GOT shadow slot / shadow-base cell A_OBJ 0 / A_OBJ 12 -> A_OBJ 1 / A_OBJ 7 (lib/Reusable/YC1f.v got_regionP / bcell_regionP / PALib), image bounds only through lib/Reusable/YImgTop.v (knock's 0x10000 .. 0x5f3000); the struct kp lies in a caller frame (cid, pos) of any class, written through awr_byte's in_frames case by In (cid, pos) own. *)
(* Modified by Theorem Labs, 2026-10: made from proofs/reac-pw/fuzz_qdisc/lib/A/QPgCheck.v at 236fd9c95ca (itself made from proofs/libreac/fuzz_knock/lib/A/APgStep.v at origin/ossv/recipes 6ebe35ba632: the save-slot region, its write obligation awr_stk / kwr_stk, the run / keep / leaf chain) with the kit-only plumbing of lib/A/RPgCfgChanges.v at 964efd2f474 (the image's own code table, cfg_wx / cfg_segs_low, kept_run, the leaf into lib/A/RPgCSpec.v's rl_post) for reac-pw/fuzz_role's image A (fuzz_role.asan): it walks check_absent 0x82bb4, check_role 0x82bdc and check_malformed 0x82c04 against rl_check_absent_specX / rl_check_role_specX / rl_check_malformed_specX on the concrete image lib/A/Img0.v rsegs; the entry state carries the registers the contract fixes (a0, a1, and a2 = a1 for check_role) as literals or as the atom they equal, so the engine decides every abort branch itself; qdisc's divisor-constant region, its arithmetic lemmas and its branch splits are dropped. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgCheck.v at 77f59d02b01 for reac-pw/fuzz_headamp image A: it walks check_cells_valid 0x83f7c against lib/A/HPgCSpec.v hd_check_cells_valid_specX on lib/A/Img0.v rsegs. Kept from the donor: regs_ok_override / ck_sr / ck_regs_ok (as cv_), ck_kept_run (cv_kept_run), the save-slot entry region and awr_stk / kwr_stk, the `ret` leaf into the contract's post. New: the shadow-offset GOT word and cell regions read at entry, the token run over the three instrumented loads of a cell, and the loop: YA0n.SRr_loopZ over a loop-head invariant at 0x83fa0, one fresh entry state per cell. *)
(* check_cells_valid 0x83f7c of fuzz_headamp.asan (pinned sha256 f3e0669d2819724922df0556b11c2dcd22d1e16fe7e0fe1535ce784b34436c47;
   addresses read on the unstripped twin b5f352154c54a97c66fd92dfa228e8a854498f6cd313dba0107900546b043f9a), 56 words:
     0x83f7c addi sp,sp,-0x10; sd ra,8(sp); 0x83f84 blez a1,0x8403c;
     0x83f88 auipc a2; ld a2,0x3e8(a2) (the GOT word 0x9c370, which holds the shadow-offset cell 0xa4db8);
       ld a3,0(a2) (the shadow offset); a4 := a0 + 2; a5 := 0x2f; a6 := 2;
     loop 0x83fa0: the shadow check of a0 + 1 (lb 0x83fac, bnez -> 0x84014: andi t0,a2,7; bge t0,a7 -> report; j back),
       of a0 (lb 0x83fbc, bnez -> 0x84020), lbu a2 = out[a0 + 1] (param), lbu a7 = out[a0] (channel);
       0x83fcc bltu 0x2f,a7 -> 0x84048 (abort); 0x83fd0 bltu 2,a2 -> 0x84048; 0x83fd4 beq a2,2: a7 := 0x37, else a7 := 1;
       the shadow check of a0 + 2 (lb 0x83ff0, bnez -> 0x8402c: andi t1,a2,7; blt t1,t0 -> back, else report);
       lbu a2 = out[a0 + 2] (value); 0x83ffc bltu a7,a2 -> 0x84048;
       a1 -= 1; a0 += 3; a4 += 3; 0x8400c beqz a1,0x8403c; 0x84010 j 0x83fa0;
     0x8403c ld ra,8(sp); addi sp,sp,0x10; 0x84044 ret; 0x84048 jal __asan_handle_no_return; jal abort.
   WHY THE ABORT PATH IS UNREACHABLE: for rc <= 0 the entry state carries the condition (bge zero,a1), so the engine
   takes `blez` to the epilogue. For rc > 0 each cell (ch, p, v) of the premise's list is valid (Pod/Headamp.v
   cell_valid: ch < 48, p <= 2, v <= (p = 2 ? 0x37 : 1)); the cell's entry state holds p as a literal (one state per
   p in {0, 1, 2}) and ch, v as atoms with the facts [0, 47] and [0, 0x37 or 1], so every `bltu` to 0x84048 is decided
   not taken from the facts. WHY NO REPORT IS REACHED: each of the three `lb` of a shadow byte is a token load
   (YCbn.tok_load); its `bnez` and the `andi` / `bge` (or `blt`) block after it are the engine's slow_block, which
   continues at the checked load and leaves the obligation range_addressable (x, 1) for x = a0, a0 + 1, a0 + 2
   (YCbn.ob_holds); the premise range_addressable (out, 3 rc) gives them. The checked bytes lie below 2^47 and outside
   the image (HPgCSpec.hd_app_rng), so the engine's shadow span holds them. THE LOOP: the invariant at the loop head
   0x83fa0 after i cells (cv_inv): a0 = out + 3 i, a1 = rc - i, a3 = the shadow offset, a4 = a0 + 2, a5 = 0x2f, a6 = 2,
   sp = entry sp - 16, ra and every callee-saved register but sp as at entry, ra in the save slot, every byte
   outside the save slot as at entry, the caller's journal; the measure rc - i falls by one per cell; on the last
   cell (rc - i = 1, a1 the literal 1) the run goes on to `ret`. *)
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
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YG0q YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YO0b YO0c.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Headamp.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Spec Require Import HeadBytes.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import Img0 HPgBase HPgCSpec.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- the image: the function, its loop head, its latch, its `ret`, the two cells it reads at entry ---- *)
Definition A_CHECK_CELLS_VALID : Z := 0x83f7c.
Definition CV_LOOP : Z := 0x83fa0.
Definition CV_LATCH : Z := 0x84010.
Definition CV_RET : Z := 0x84044.
(* the GOT word of __asan_shadow_memory_dynamic_address and the cell itself (.symtab of the unstripped twin) *)
Definition A_GOT_SHADOW : Z := 0x9c370.
Definition A_SHADOW_CELL : Z := 0xa4db8.
(* the 56 words 0x83f7c .. 0x84058 *)
Definition cv_tbl : ctable := build_table rsegs A_CHECK_CELLS_VALID 56 TEmpty.
Lemma cv_tbl_ok : table_ok rsegs cv_tbl.
Proof. apply build_table_ok0. unfold A_CHECK_CELLS_VALID. lia. Qed.
Lemma cv_wx : wx_segs_nowrap rsegs.
Proof. apply wx_segs_nowrap_of_b. vm_compute. reflexivity. Qed.
Lemma cv_segs_low : forall a, in_img rsegs a -> 0 <= a < kLowMemEnd.
Proof.
intros a (sg & Hin & Hr).
assert (HB : forallb (fun s : Segment => Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? kLowMemEnd) rsegs = true)
by (vm_compute; reflexivity).
pose proof (proj1 (forallb_forall _ _) HB sg Hin) as H. apply Z.leb_le in H. lia.
Qed.
Lemma cv_ret_word : clookup cv_tbl CV_RET = Some RET_WORD_r.
Proof. vm_compute. reflexivity. Qed.
Lemma same_io_wvb_cv : forall md l X, same_io md (with_vm_backing l X md).
Proof. intros md l X. destruct md as [fd [maps lazy mat] io fs proc lim tm]. repeat split; reflexivity. Qed.

(* ---- the token engine's context: env slot 32 is the shadow offset ---- *)
Definition cv_Bx : sv := SOff 32 0.
Definition cv_Bspan : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).

(* ---- the entry state at 0x83f7c ---- *)
Definition cv_got_region : YP09.region :=
  YP09.mkRegion None A_GOT_SHADOW (A_GOT_SHADOW + 8) 0 0 [YP09.mkChunk A_GOT_SHADOW (CVal 8 (SLit A_SHADOW_CELL))].
Definition cv_cell_region : YP09.region :=
  YP09.mkRegion None A_SHADOW_CELL (A_SHADOW_CELL + 8) 0 0 [YP09.mkChunk A_SHADOW_CELL (CVal 8 (SOff 32 0))].
Definition cv_regions0 : smem := [YP09.mkRegion (Some 2%nat) (-16) 0 (-16) 0 []; cv_got_region; cv_cell_region].
Definition cv_extra0 : list word := [Z_to_bv 64 SHADOW_OFF].
(* rc > 0: a1's atom in [1, 2^31 - 1]; rc <= 0: the condition of `blez a1` (bge zero, a1) *)
Definition cv_facts0 (pos : bool) : facts :=
  if pos then mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (11%nat, mkAF 1 (2 ^ 31 - 1) 0);
                       (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0)] [] []
  else mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0)]
               [mkAC BC_GE (SLit 0) (SOff 11 0)] [].
Definition cv_ss0 (pos : bool) : sstate := mkSS A_CHECK_CELLS_VALID sr_atoms cv_regions0 None (cv_facts0 pos).

(* ---- the entry state of one cell at the loop head 0x83fa0 ---- *)
(* env slots 32 .. 34: the shadow offset, the cell's channel and value bytes *)
Definition cv_extra (ch v : Z) : list word := [Z_to_bv 64 SHADOW_OFF; Z_to_bv 64 ch; Z_to_bv 64 v].
(* the registers: sr_atoms with the overrides (register, value) [donor ck_sr] *)
Definition cv_sr_of (ov : list (bv 5 * sv)) : list sv := fold_left (fun sr p => sr_set sr (fst p) (snd p)) ov sr_atoms.
Definition cv_ov (last : bool) : list (bv 5 * sv) :=
  [((13%bv : bv 5), SOff 32 0); ((14%bv : bv 5), SOff 10 2); ((15%bv : bv 5), SLit 47); ((16%bv : bv 5), SLit 2)]
  ++ (if last then [((11%bv : bv 5), SLit 1)] else []).
(* the save slot (sp = atom 2 is the entry sp - 16; ra at sp + 8) and the cell's three bytes at a0 = atom 10 *)
Definition cv_stk : YP09.region := YP09.mkRegion (Some 2%nat) 0 16 0 0 [YP09.mkChunk 8 (CVal 8 (SOff 1 0))].
Definition cv_cells (p : Z) : YP09.region :=
  YP09.mkRegion (Some 10%nat) 0 3 0 0
    [YP09.mkChunk 0 (CVal 1 (SOff 33 0)); YP09.mkChunk 1 (CVal 1 (SLit p)); YP09.mkChunk 2 (CVal 1 (SOff 34 0))].
(* closed numerals only (a free variable in a fact makes the engine's decisions stick) *)
Definition cv_facts (lim : Z) (last : bool) : facts :=
  mkFacts ([(2%nat, mkAF (2 ^ 46 - 16) (2 ^ 47 - 16) 4); (10%nat, mkAF 4096 0x7fffff800000 0);
            (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (33%nat, mkAF 0 47 0); (34%nat, mkAF 0 lim 0)]
           ++ (if last then [] else [(11%nat, mkAF 2 (2 ^ 31 - 1) 0)])) [] [].
Definition cv_ss (p lim : Z) (last : bool) : sstate :=
  mkSS CV_LOOP (cv_sr_of (cv_ov last)) [cv_stk; cv_cells p] None (cv_facts lim last).

(* ---- the callee-saved registers other than sp ---- *)
Definition CS_NOSP : list (bv 5) := [3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.
Lemma cs_nosp_in : forall r, acallee_saved r -> r <> 2 -> In (Z_to_bv 5 r) CS_NOSP.
Proof.
intros r Hr H2. unfold acallee_saved in Hr.
assert (Hc : r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/
  r = 25 \/ r = 26 \/ r = 27) by lia.
cbv [CS_NOSP In].
destruct Hc as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]]]];
repeat (first [left; apply bv_eq; reflexivity | right]).
Qed.

(* ---- generic facts ---- *)
Lemma cv_ub : forall z, bv_unsigned (Z_to_bv 8 z) = z mod 256.
Proof. intros z. rewrite Z_to_bv_unsigned. reflexivity. Qed.
(* the three bytes of cell i of ha_cells_bytes *)
Lemma cv_cell_bytes : forall (cs : list Headamp.cell) (i : nat) ch p v,
  nth_error cs i = Some (ch, p, v) ->
  nth (3 * i) (hd_zbytes (ha_cells_bytes cs)) 0 = ch mod 256 /\
  nth (3 * i + 1) (hd_zbytes (ha_cells_bytes cs)) 0 = p mod 256 /\
  nth (3 * i + 2) (hd_zbytes (ha_cells_bytes cs)) 0 = v mod 256.
Proof.
induction cs as [|[[ch0 p0] v0] cs IH]; intros i ch p v H.
- destruct i; discriminate H.
- destruct i as [|i].
  + cbn in H. injection H as E1 E2 E3. subst ch0 p0 v0.
    unfold hd_zbytes, ha_cells_bytes. cbn [flat_map ha_cell_bytes app map Nat.mul Nat.add nth].
    rewrite !cv_ub. repeat split; reflexivity.
  + cbn [nth_error] in H. destruct (IH i ch p v H) as (H0 & H1 & H2).
    unfold hd_zbytes, ha_cells_bytes in *. cbn [flat_map ha_cell_bytes app map].
    replace (3 * S i)%nat with (S (S (S (3 * i)))) by lia.
    replace (S (S (S (3 * i))) + 1)%nat with (S (S (S (3 * i + 1)))) by lia.
    replace (S (S (S (3 * i))) + 2)%nat with (S (S (S (3 * i + 2)))) by lia.
    cbn [nth]. repeat split; assumption.
Qed.
Lemma cv_denot_off : forall E n v c, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> 0 <= v + c < 2 ^ 64 ->
  sv_denot E (SOff n c) = Z_to_bv 64 (v + c).
Proof.
intros E n v c Hn Hv Hc. apply bv_eq. rewrite denot_SOff, Hn, !unsigned_lit_small by lia.
apply zcanon_id. unfold M64. lia.
Qed.
Lemma cv_bv_of : forall (w : word), w = Z_to_bv 64 (bv_unsigned w).
Proof. intros w. symmetry. apply Z_to_bv_bv_unsigned. Qed.
Lemma cv_u64 : forall (w : word), 0 <= bv_unsigned w < 2 ^ 64.
Proof. intros w. pose proof (bv_unsigned_in_range _ w) as Hb. change (bv_modulus 64) with (2 ^ 64) in Hb. exact Hb. Qed.

(* an override of a register by a value it already has keeps regs_ok [donor regs_ok_override / ck_regs_ok] *)
Lemma cv_regs_ok_override : forall E sr regs (r : bv 5) e,
regs_ok E sr regs -> r <> 0%bv -> sv_denot E e = getr regs r -> regs_ok E (sr_set sr r e) regs.
Proof.
intros E sr regs r e Hr Hr0 Hv r'.
unfold sr_set. destruct (bv_eqb r 0) eqn:Hb0.
{ exfalso. apply Hr0. unfold bv_eqb in Hb0. apply Z.eqb_eq in Hb0. apply bv_eq. exact Hb0. }
specialize (Hr r'). unfold sr_get in *.
destruct (bv_eqb r' 0) eqn:Hr'0; [exact Hr|].
rewrite nth_sr_upd.
destruct (Nat.eqb (ridx r') (ridx r)) eqn:Hi; [|exact Hr].
apply Nat.eqb_eq in Hi. apply ridx_inj in Hi. subst r'. symmetry. exact Hv.
Qed.
Lemma cv_regs_ok : forall regs extra (ov : list (bv 5 * sv)),
Forall (fun p => fst p <> 0%bv /\ sv_denot (Ereg regs extra) (snd p) = getr regs (fst p)) ov ->
regs_ok (Ereg regs extra) (cv_sr_of ov) regs.
Proof.
intros regs extra ov Hov. unfold cv_sr_of.
assert (G : forall sr, regs_ok (Ereg regs extra) sr regs ->
regs_ok (Ereg regs extra) (fold_left (fun sr p => sr_set sr (fst p) (snd p)) ov sr) regs).
{ induction Hov as [|[r e] ov [Hr0 Hv] Hov IH]; intros sr Hsr; cbn [fold_left]; [exact Hsr|].
apply IH. apply cv_regs_ok_override; assumption. }
apply G. apply regs_ok_Ereg.
Qed.
Section mem. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
(* segment-generic: the image B walks (lib/AU/HPgChkU_*.v) use them at their own segments *)
Context {segs : list Segment}.
Lemma cv_mbyte_aview : forall H (m m' : word -> option byte) a,
  aview segs H m' a = aview segs H m a -> mbyte segs (mrestrict H m') a = mbyte segs (mrestrict H m) a.
Proof.
intros H m m' a E. unfold aview in E.
destruct (mbyte segs (mrestrict H m') a) as [b1|] eqn:E1, (mbyte segs (mrestrict H m) a) as [b2|] eqn:E2;
cbn [option_map] in E; try discriminate E; [|reflexivity].
injection E as E. f_equal. apply bv_eq. exact E.
Qed.
Lemma cv_val_kept : forall H (m m' : word -> option byte) a n v,
  val_mem segs (mrestrict H m) a n v ->
  (forall j, (j < n)%nat -> aview segs H m' (a + Z.of_nat j) = aview segs H m (a + Z.of_nat j)) ->
  val_mem segs (mrestrict H m') a n v.
Proof. intros H m m' a n v Hv HK j Hj. rewrite (cv_mbyte_aview H m m' _ (HK j Hj)). exact (Hv j Hj). Qed.
Lemma cv_ra_kept : forall H (m m' : word -> option byte) a n,
  range_addressable (aview segs H m) SHADOW_OFF a n ->
  (forall x, a <= x < a + n -> aview segs H m' (shadow_of_addr SHADOW_OFF x) = aview segs H m (shadow_of_addr SHADOW_OFF x)) ->
  range_addressable (aview segs H m') SHADOW_OFF a n.
Proof. intros H m m' a n Hr HK x Hx. destruct (Hr x Hx) as (s & Hs & Hok). exists s. rewrite HK by exact Hx. split; assumption. Qed.
(* a run keeps every byte outside the zone its write windows lie in [donor ck_kept_run] *)
Lemma cv_kept_run : forall (Zn : Z -> Prop) E rs (H : word -> bool) (m0 m1 m2 : word -> option byte),
(forall a, 0 <= a < 2 ^ 64 -> ~ Zn a -> aview segs H m1 a = aview segs H m0 a) ->
frame_of E rs (mrestrict H m1) (mrestrict H m2) ->
(forall a, in_wrange E rs a -> Zn a) ->
forall a, 0 <= a < 2 ^ 64 -> ~ Zn a -> aview segs H m2 a = aview segs H m0 a.
Proof.
intros Zn E rs H m0 m1 m2 HK HF HW a Ha Hz. rewrite <- (HK a Ha Hz). unfold aview, mbyte.
rewrite (HF (Z_to_bv 64 a)); [reflexivity|]. rewrite unsigned_lit_small by exact Ha. intros X. exact (Hz (HW a X)).
Qed.
Lemma cv_region_at : forall E ss ms i r,
  st_ok segs E ss ms -> nth_error (ss_mem ss) i = Some r -> region_ok segs E (ms_mem ms) r.
Proof.
intros E ss ms i r HS Hi. pose proof (st_ok_mem_ok segs E ss ms HS) as (_ & HF & _).
exact (proj1 (Forall_forall _ _) HF r (nth_error_In _ _ Hi)).
Qed.
(* a register the state holds as its own atom keeps its value across a run *)
Lemma cv_reg_kept : forall H E ss ms regs0 extra k (r : bv 5),
  st_ok segs E ss (restrict H ms) -> env_agree k (Ereg regs0 extra) E -> (Z.to_nat (bv_unsigned r) < k)%nat ->
  sr_get (ss_regs ss) r = SOff (Z.to_nat (bv_unsigned r)) 0 -> getr (ms_regs ms) r = getr regs0 r.
Proof.
intros H E ss ms regs0 extra k r HS [HA _] Hk Hsr.
rewrite (st_ok_restrict_reg segs H E ss ms r HS), Hsr. cbn [sv_denot]. rewrite Z.add_0_r.
rewrite HA by exact Hk. rewrite ew_Ereg_reg, Z_to_bv_bv_unsigned. reflexivity.
Qed.
Lemma cv_cs_kept : forall H E ss ms regs0 extra k,
  st_ok segs E ss (restrict H ms) -> env_agree k (Ereg regs0 extra) E -> (32 <= k)%nat ->
  forallb (fun r : bv 5 => sv_eqb (sr_get (ss_regs ss) r) (SOff (Z.to_nat (bv_unsigned r)) 0)) CS_NOSP = true ->
  forall r, acallee_saved r -> r <> 2 -> getr (ms_regs ms) (Z_to_bv 5 r) = getr regs0 (Z_to_bv 5 r).
Proof.
intros H E ss ms regs0 extra k HS HA Hk Hcs r Hr Hr2.
pose proof (proj1 (forallb_forall _ _) Hcs _ (cs_nosp_in r Hr Hr2)) as Hq. cbn beta in Hq. apply sv_eqb_eq in Hq.
eapply cv_reg_kept; [exact HS | exact HA | | exact Hq].
pose proof (u5_range (Z_to_bv 5 r)). lia.
Qed.
End mem.

(* write windows of the states: none in a cell's state, the save slot [sp - 16, sp) at entry [donor kwr_stk] *)
Ltac cv_nowr :=
idtac; let a := fresh "a" in let r := fresh "r" in let Hr := fresh "Hr" in let Hb := fresh "Hb" in
intros a (r & Hr & Hb);
lazymatch type of Hr with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hr end;
repeat (destruct Hr as [<- | Hr]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb; lia | ]);
destruct Hr.
Ltac cv_kwr B2 :=
idtac; let a := fresh "a" in let r := fresh "r" in let Hr := fresh "Hr" in let Hb := fresh "Hb" in
intros a (r & Hr & Hb); cbv beta;
lazymatch type of Hr with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hr end;
repeat (destruct Hr as [<- | Hr]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb;
first [ rewrite B2 in Hb; lia | lia ] | ]);
destruct Hr.
(* the entry run's write obligation: the save slot lies in the caller's stack allowance [donor awr_stk] *)
Ltac cv_awr B2 :=
idtac; lazymatch goal with |- awr_ok ?E ?rs ?stk ?sp0 ?fp ?b0 ?bc ?ly ?own =>
let rs' := eval vm_compute in rs in change (awr_ok E rs' stk sp0 fp b0 bc ly own);
lazymatch type of B2 with bv_unsigned (ew E 2) = ?spv =>
repeat first
[ apply awr_ok_nil
| apply awr_ok_cons_ro; [azlit_tac|]
| eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat (spv - sp0));
[reflexivity | rewrite B2; lia | cbn [YP09.r_wlo YP09.r_whi]; lia | cbn [YP09.r_wlo YP09.r_whi]; lia |] ]
end end.
Ltac cv_agree HAE :=
first [ exact HAE
| eapply env_agree_trans; [ | eapply env_agree_le; [ | apply env_agree_ewset ]; cbv; lia ]; cv_agree HAE ].

Section e. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
(* the entry state at 0x83f7c *)
Lemma cv_entry0 : forall (pos : bool) (W : world rsegs) regs memc rcc,
  (forall a, spZ regs - 16 <= a < spZ regs -> apresent (w_H W) memc a) ->
  2 ^ 46 <= spZ regs <= 2 ^ 47 -> spZ regs mod 16 = 0 ->
  val_mem rsegs (mrestrict (w_H W) memc) A_GOT_SHADOW 8 A_SHADOW_CELL ->
  val_mem rsegs (mrestrict (w_H W) memc) A_SHADOW_CELL 8 SHADOW_OFF ->
  getr regs 11 = w64 rcc -> - 2 ^ 31 <= rcc < 2 ^ 31 ->
  (if pos then 0 < rcc else rcc <= 0) ->
  st_ok rsegs (Ereg regs cv_extra0) (cv_ss0 pos)
    (restrict (w_H W) (mkst regs (Z_to_bv 64 A_CHECK_CELLS_VALID) memc (seg_rom rsegs))).
Proof.
intros pos W regs memc rcc Hpres Hsp Hal Vgot Vcell H11 Hrc Hpos.
rewrite restrict_mkst_fx. unfold cv_ss0.
assert (E2 : bv_unsigned (ew (Ereg regs cv_extra0) 2) = spZ regs) by (rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); reflexivity).
assert (E11 : ew (Ereg regs cv_extra0) 11 = Z_to_bv 64 rcc) by (rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
assert (E32 : ew (Ereg regs cv_extra0) 32 = Z_to_bv 64 SHADOW_OFF) by (exact (ew_Ereg_extra regs _ 0)).
assert (HSB : 0 <= SHADOW_OFF < 2 ^ 64) by (unfold SHADOW_OFF; lia).
apply entry_st_ok_full.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- unfold cv_regions0. apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
  + apply (region_ok_stack rsegs (Ereg regs cv_extra0) _ 2 (spZ regs) (-16) E2); [lia | lia |].
    intros a Ha. apply (apresent_writable rsegs). apply Hpres. lia.
  + unfold region_ok, cv_got_region. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    unfold A_GOT_SHADOW. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val rsegs (Ereg regs cv_extra0) _ 0 A_GOT_SHADOW 8 (SLit A_SHADOW_CELL) A_SHADOW_CELL);
      [reflexivity | unfold A_SHADOW_CELL; cbn; lia | lia | exact Vgot].
  + unfold region_ok, cv_cell_region. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    unfold A_SHADOW_CELL. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val rsegs (Ereg regs cv_extra0) _ 0 A_SHADOW_CELL 8 (SOff 32 0) SHADOW_OFF);
      [rewrite (cv_denot_off (Ereg regs cv_extra0) 32 SHADOW_OFF 0 E32 HSB) by lia; rewrite Z.add_0_r; reflexivity
      | unfold SHADOW_OFF; cbn; lia | lia | exact Vcell].
- unfold cv_regions0, cv_got_region, cv_cell_region. cbn [pairwise_disjoint all_disjoint].
  unfold extent_disjoint. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite E2.
  unfold A_GOT_SHADOW, A_SHADOW_CELL. repeat split; lia.
- destruct pos; unfold cv_facts0; split; cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
  + unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E2, E11, E32, !unsigned_lit_small by (unfold SHADOW_OFF in *; lia).
    change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r. repeat split; lia.
  + split; exact I.
  + unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E2, E32, !unsigned_lit_small by (unfold SHADOW_OFF in *; lia).
    change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r. repeat split; lia.
  + split; [|exact I]. split; [|exact I]. unfold acond_ok. cbn [ac_c ac_a ac_b].
    rewrite YO0c.branch_ge. cbn [sv_denot]. rewrite E11, Z.add_0_r, Z_to_bv_bv_unsigned.
    rewrite !YO0c.lit64_unsigned. unfold YO0b.s64.
    destruct (Z.eq_dec rcc 0) as [->|Hn].
    * reflexivity.
    * replace (rcc mod 2 ^ 64) with (rcc + 2 ^ 64) by (apply Z.mod_unique with (-1); lia).
      change (0 mod 2 ^ 64) with 0.
      destruct (Z.ltb_spec (rcc + 2 ^ 64) (2 ^ 63)); [lia|]. destruct (Z.ltb_spec 0 (2 ^ 63)); [|lia].
      apply negb_true_iff. apply Z.ltb_ge. lia.
Qed.
End e.

Section w. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Let LAWS : AR_laws rsegs B := AR_laws_ok rsegs B.
(* image A's symbol record holds the shadow-offset GOT word and cell (both read by check_cells_valid at entry) *)
Hypothesis HBgot : as_got_shadow B = A_GOT_SHADOW.
Hypothesis HBcell : as_shadow_cell B = A_SHADOW_CELL.

Section loop.
Variables (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world rsegs)
  (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z)) (lyc : alayout) (Sc : astate)
  (W : world rsegs) (memc : word -> option byte) (mdc : Model) (k : Z) (regs : bvmap 5 word)
  (rcc o : Z) (cs : list Headamp.cell).
Hypothesis Hrc : 0 < rcc < 2 ^ 31.
Hypothesis Hlen : Z.of_nat (length cs) = rcc.
Hypothesis Hval : Forall Headamp.cell_valid cs.
Hypothesis Hg : garr8 rsegs (mrestrict (w_H W) memc) o (hd_zbytes (ha_cells_bytes cs)).
Hypothesis Hra : range_addressable (aview rsegs (w_H W) memc) SHADOW_OFF o (3 * rcc).
Hypothesis Hoff : hd_off_stack regs T_check_STK o (3 * rcc).
Hypothesis Happ : hd_app_rng rsegs o (3 * rcc).
Hypothesis Hsp : 2 ^ 46 <= spZ regs <= 2 ^ 47.
Hypothesis Hal16 : spZ regs mod 16 = 0.
Hypothesis Hrar : YK0s.ret_ok (getr regs 1).
Hypothesis H10 : getr regs 10 = w64 o.
Hypothesis H11 : getr regs 11 = w64 rcc.
Hypothesis HJ0 : ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k.
Hypothesis Hwlo : sp0 - STK <= spZ regs - 32.
Hypothesis Hwhi : spZ regs <= sp0.
Hypothesis Hpres16 : forall a, spZ regs - 16 <= a < spZ regs -> apresent (w_H W) memc a.
Hypothesis Vgot : val_mem rsegs (mrestrict (w_H W) memc) A_GOT_SHADOW 8 A_SHADOW_CELL.
Hypothesis Vcell : val_mem rsegs (mrestrict (w_H W) memc) A_SHADOW_CELL 8 SHADOW_OFF.

Definition cv_post : world rsegs -> config -> Prop :=
  hd_post rsegs B MT STK sp0 FP ly S W0 mem0 md0 own k T_check_STK regs lyc Sc W memc mdc
    (fun f => f = fx) (fun _ => False) (fun _ _ _ => True).

(* the loop head after i cells *)
Definition cv_inv (i : Z) (regs_i : bvmap 5 word) (mem_i : word -> option byte) (md_i : Model) : Prop :=
  0 <= i < rcc /\
  ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem_i md_i k /\
  same_io mdc md_i /\
  getr regs_i 10 = w64 (o + 3 * i) /\ getr regs_i 11 = w64 (rcc - i) /\
  getr regs_i 13 = w64 SHADOW_OFF /\ getr regs_i 14 = w64 (o + 3 * i + 2) /\
  getr regs_i 15 = w64 47 /\ getr regs_i 16 = w64 2 /\
  getr regs_i 2 = w64 (spZ regs - 16) /\ getr regs_i 1 = getr regs 1 /\
  (forall r, acallee_saved r -> r <> 2 -> getr regs_i (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) /\
  val_mem rsegs (mrestrict (w_H W) mem_i) (spZ regs - 8) 8 (raZ regs) /\
  (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 16 <= a < spZ regs) -> aview rsegs (w_H W) mem_i a = aview rsegs (w_H W) memc a).
Definition cv_P (i : Z) (W' : world rsegs) (c : config) : Prop :=
  W' = W /\ exists regs_i mem_i md_i,
  c = mkCfg (mkst regs_i (Z_to_bv 64 CV_LOOP) mem_i (seg_rom rsegs)) md_i /\ cv_inv i regs_i mem_i md_i.

(* ---- the checked range, as the premises give it ---- *)
Lemma cv_rng : 4096 <= o /\ o + 3 * rcc <= 0x7fffff800000.
Proof.
destruct Happ as ([H0 Hr] & _). pose proof ASAN_CEIL_range as [CR _].
unfold kLowShadowBeg, kHighMemBeg in Hr. lia.
Qed.
Lemma cv_off : forall x, o <= x < o + 3 * rcc -> ~ (spZ regs - 32 <= x < spZ regs).
Proof. intros x Hx. exact (Hoff x Hx). Qed.
(* the bytes and the shadow of the cells at a memory that is the entry memory outside the save slot *)
Lemma cv_g_at : forall mem_i,
  (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 16 <= a < spZ regs) -> aview rsegs (w_H W) mem_i a = aview rsegs (w_H W) memc a) ->
  garr8 rsegs (mrestrict (w_H W) mem_i) o (hd_zbytes (ha_cells_bytes cs)).
Proof.
intros mem_i KE j Hj. destruct (Hg j Hj) as [Hv Hb]. split; [|exact Hb].
unfold hd_zbytes in Hj. rewrite length_map, length_ha_cells_bytes in Hj.
pose proof cv_rng as Hr.
apply (cv_val_kept _ memc mem_i _ 1 _ Hv). intros jj Hjj. assert (jj = 0%nat) by lia. subst jj.
apply KE; [lia|]. pose proof (cv_off (o + Z.of_nat j) ltac:(lia)). lia.
Qed.
Lemma cv_ra_at : forall mem_i,
  (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 16 <= a < spZ regs) -> aview rsegs (w_H W) mem_i a = aview rsegs (w_H W) memc a) ->
  range_addressable (aview rsegs (w_H W) mem_i) SHADOW_OFF o (3 * rcc).
Proof.
intros mem_i KE. apply (cv_ra_kept _ memc mem_i _ _ Hra). intros x Hx.
pose proof cv_rng as Hr. unfold shadow_of_addr.
assert (Hq : 0 <= x / 8 < 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
apply KE; unfold SHADOW_OFF; lia.
Qed.

(* ---- the obligations of a cell's run: range_addressable (a0 + c, 1) ---- *)
Lemma cv_obl : forall i ch v regs_i mem_i md_i c,
  cv_inv i regs_i mem_i md_i -> 0 <= c < 3 ->
  range_addressable (rd_of rsegs (mrestrict (w_H W) mem_i)) (U (Ereg regs_i (cv_extra ch v)) cv_Bx)
    (U (Ereg regs_i (cv_extra ch v)) (SOff 10 c)) 1.
Proof.
intros i ch v regs_i mem_i md_i c HI Hc.
destruct HI as (Hi & _ & _ & R10 & _ & _ & _ & _ & _ & _ & _ & _ & _ & KE).
pose proof cv_rng as Hr.
assert (E10 : ew (Ereg regs_i (cv_extra ch v)) 10 = Z_to_bv 64 (o + 3 * i)) by (rewrite (ew_Ereg_nat regs_i _ 10 10%bv eq_refl); exact R10).
rewrite (U_atom_off _ 10 (o + 3 * i) c E10) by lia.
eapply obl_of_range; [exact (cv_ra_at mem_i KE) | | lia | lia].
unfold cv_Bx. apply (U_atom _ 32 SHADOW_OFF); [exact (ew_Ereg_extra regs_i _ 0) | unfold SHADOW_OFF; lia].
Qed.

(* ---- a cell's entry state ---- *)
Lemma cv_it_entry : forall i ch p v lim (last : bool) regs_i mem_i md_i,
  cv_inv i regs_i mem_i md_i ->
  nth_error cs (Z.to_nat i) = Some (ch, p, v) ->
  0 <= ch <= 47 -> 0 <= p <= 2 -> 0 <= v <= lim -> lim < 256 ->
  (if last then rcc - i = 1 else 2 <= rcc - i) ->
  st_ok rsegs (Ereg regs_i (cv_extra ch v)) (cv_ss p lim last)
    (restrict (w_H W) (mkst regs_i (Z_to_bv 64 CV_LOOP) mem_i (seg_rom rsegs))).
Proof.
intros i ch p v lim last regs_i mem_i md_i HI Hnth Hch Hp Hv Hlim Hl.
destruct HI as (Hi & _ & _ & R10 & R11 & R13 & R14 & R15 & R16 & R2 & R1 & _ & Hslot & KE).
pose proof cv_rng as Hr.
rewrite restrict_mkst_fx. unfold cv_ss.
assert (E1 : ew (Ereg regs_i (cv_extra ch v)) 1 = getr regs 1) by (rewrite (ew_Ereg_nat regs_i _ 1 1%bv eq_refl); exact R1).
assert (E2 : ew (Ereg regs_i (cv_extra ch v)) 2 = Z_to_bv 64 (spZ regs - 16)) by (rewrite (ew_Ereg_nat regs_i _ 2 2%bv eq_refl); exact R2).
assert (E10 : ew (Ereg regs_i (cv_extra ch v)) 10 = Z_to_bv 64 (o + 3 * i)) by (rewrite (ew_Ereg_nat regs_i _ 10 10%bv eq_refl); exact R10).
assert (E11 : ew (Ereg regs_i (cv_extra ch v)) 11 = Z_to_bv 64 (rcc - i)) by (rewrite (ew_Ereg_nat regs_i _ 11 11%bv eq_refl); exact R11).
assert (E32 : ew (Ereg regs_i (cv_extra ch v)) 32 = Z_to_bv 64 SHADOW_OFF) by (exact (ew_Ereg_extra regs_i _ 0)).
assert (E33 : ew (Ereg regs_i (cv_extra ch v)) 33 = Z_to_bv 64 ch) by (exact (ew_Ereg_extra regs_i _ 1)).
assert (E34 : ew (Ereg regs_i (cv_extra ch v)) 34 = Z_to_bv 64 v) by (exact (ew_Ereg_extra regs_i _ 2)).
assert (HSB : 0 <= SHADOW_OFF < 2 ^ 64) by (unfold SHADOW_OFF; lia).
(* the cell's bytes at mem_i *)
pose proof (cv_g_at mem_i KE) as Hgi.
assert (Hi3 : (3 * Z.to_nat i + 2 < length (hd_zbytes (ha_cells_bytes cs)))%nat).
{ unfold hd_zbytes. rewrite length_map, length_ha_cells_bytes. lia. }
destruct (cv_cell_bytes cs (Z.to_nat i) ch p v Hnth) as (B0 & B1 & B2).
destruct (Hgi (3 * Z.to_nat i)%nat ltac:(lia)) as [V0 _].
destruct (Hgi (3 * Z.to_nat i + 1)%nat ltac:(lia)) as [V1 _].
destruct (Hgi (3 * Z.to_nat i + 2)%nat ltac:(lia)) as [V2 _].
rewrite B0, Z.mod_small in V0 by lia. rewrite B1, Z.mod_small in V1 by lia. rewrite B2, Z.mod_small in V2 by lia.
assert (Hti : Z.of_nat (Z.to_nat i) = i) by lia.
apply entry_st_ok_full.
- apply cv_regs_ok. unfold cv_ov.
  destruct last; cbn [app]; repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; split;
    try (let Hz := fresh "Hz" in intros Hz; apply (f_equal (@bv_unsigned 5)) in Hz; vm_compute in Hz; discriminate Hz).
  all: first
    [ rewrite (cv_denot_off _ 32 SHADOW_OFF 0 E32 HSB) by lia; rewrite Z.add_0_r; symmetry; exact R13
    | rewrite (cv_denot_off _ 10 (o + 3 * i) 2 E10) by lia; symmetry; exact R14
    | cbn [sv_denot]; symmetry; first [exact R15 | exact R16 | rewrite R11; unfold w64; f_equal; lia] ].
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
  + unfold region_ok, cv_stk. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite E2, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros o' Ho'; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val rsegs (Ereg regs_i (cv_extra ch v)) _ (spZ regs - 16) 8 8 (SOff 1 0) (raZ regs)).
    * rewrite (cv_denot_off (Ereg regs_i (cv_extra ch v)) 1 (raZ regs) 0) by (first [rewrite E1; apply cv_bv_of | apply cv_u64 | pose proof (cv_u64 (getr regs 1)); unfold raZ; lia]).
      rewrite Z.add_0_r. reflexivity.
    * pose proof (cv_u64 (getr regs 1)). unfold raZ. cbn. lia.
    * lia.
    * replace (spZ regs - 16 + 8) with (spZ regs - 8) by lia. exact Hslot.
  + unfold region_ok, cv_cells. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite E10, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros o' Ho'; lia|].
    apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
    * apply (chunk_ok_val rsegs (Ereg regs_i (cv_extra ch v)) _ (o + 3 * i) 0 1 (SOff 33 0) ch).
      { rewrite (cv_denot_off (Ereg regs_i (cv_extra ch v)) 33 ch 0 E33) by lia. rewrite Z.add_0_r. reflexivity. }
      { cbn. lia. } { lia. }
      { replace (o + 3 * i + 0) with (o + Z.of_nat (3 * Z.to_nat i)) by lia. exact V0. }
    * apply (chunk_ok_val rsegs (Ereg regs_i (cv_extra ch v)) _ (o + 3 * i) 1 1 (SLit p) p); [reflexivity | cbn; lia | lia |].
      replace (o + 3 * i + 1) with (o + Z.of_nat (3 * Z.to_nat i + 1)) by lia. exact V1.
    * apply (chunk_ok_val rsegs (Ereg regs_i (cv_extra ch v)) _ (o + 3 * i) 2 1 (SOff 34 0) v).
      { rewrite (cv_denot_off (Ereg regs_i (cv_extra ch v)) 34 v 0 E34) by lia. rewrite Z.add_0_r. reflexivity. }
      { cbn. lia. } { lia. }
      { replace (o + 3 * i + 2) with (o + Z.of_nat (3 * Z.to_nat i + 2)) by lia. exact V2. }
- cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint, cv_stk, cv_cells.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite E2, E10, !unsigned_lit_small by lia.
  pose proof (cv_off (o + 3 * i) ltac:(lia)) as X0.
  split; [split; [lia | exact I] | split; exact I].
- unfold cv_facts. split; [|split; exact I].
  destruct last; cbn [app f_atoms atoms_ok]; unfold afact_ok; cbn [af_lo af_hi af_al2];
  rewrite ?E2, ?E10, ?E11, ?E32, ?E33, ?E34, !unsigned_lit_small by (unfold SHADOW_OFF; lia);
  change (2 ^ 4) with 16; rewrite !Z.pow_0_r, !Z.mod_1_r;
  repeat split; try lia; rewrite Zminus_mod, Hal16; reflexivity.
Qed.

(* ---- the loop head after the next cell ---- *)
Lemma cv_next : forall i regs_i mem_i md_i ch v E' ss' ms' md',
  cv_inv i regs_i mem_i md_i -> 2 <= rcc - i ->
  st_ok rsegs E' ss' (restrict (w_H W) ms') ->
  env_agree 35 (Ereg regs_i (cv_extra ch v)) E' ->
  ss_pc ss' = CV_LOOP -> ss_resv ss' = None ->
  sr_get (ss_regs ss') 10 = SOff 10 3 -> sr_get (ss_regs ss') 11 = SOff 11 (-1) ->
  sr_get (ss_regs ss') 13 = SOff 32 0 -> sr_get (ss_regs ss') 14 = SOff 10 5 ->
  sr_get (ss_regs ss') 15 = SLit 47 -> sr_get (ss_regs ss') 16 = SLit 2 ->
  sr_get (ss_regs ss') 2 = SOff 2 0 -> sr_get (ss_regs ss') 1 = SOff 1 0 ->
  forallb (fun r : bv 5 => sv_eqb (sr_get (ss_regs ss') r) (SOff (Z.to_nat (bv_unsigned r)) 0)) CS_NOSP = true ->
  ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W (ms_mem ms') md' k ->
  same_io md_i md' ->
  (forall a, 0 <= a < 2 ^ 64 -> aview rsegs (w_H W) (ms_mem ms') a = aview rsegs (w_H W) mem_i a) ->
  ms' = mkst (ms_regs ms') (Z_to_bv 64 CV_LOOP) (ms_mem ms') (seg_rom rsegs) /\
  cv_inv (i + 1) (ms_regs ms') (ms_mem ms') md'.
Proof.
intros i regs_i mem_i md_i ch v E' ss' ms' md' HI Hnl HS HA Hpc Hrv S10 S11 S13 S14 S15 S16 S2 S1 Scs HJ' Hio' K'.
destruct HI as (Hi & _ & Hio & R10 & R11 & R13 & R14 & R15 & R16 & R2 & R1 & Rcs & Hslot & KE).
pose proof cv_rng as Hr.
split; [rewrite <- Hpc; exact (st_ok_restrict_mkst rsegs _ _ _ _ HS Hrv)|].
assert (HA0 := HA). destruct HA as [HA _].
assert (A : forall n (r : bv 5), (n < 35)%nat -> Z.of_nat n = bv_unsigned r -> ew E' n = getr regs_i r).
{ intros n r Hn Hr'. rewrite HA by exact Hn. exact (ew_Ereg_nat regs_i _ n r Hr'). }
assert (RG : forall r e, sr_get (ss_regs ss') r = e -> getr (ms_regs ms') r = sv_denot E' e).
{ intros r e He. rewrite (st_ok_restrict_reg rsegs _ _ _ _ r HS), He. reflexivity. }
split; [lia|]. split; [exact HJ'|]. split; [exact (same_io_trans _ _ _ Hio Hio')|].
split; [rewrite (RG _ _ S10), (cv_denot_off E' 10 (o + 3 * i) 3 (eq_trans (A 10%nat 10%bv ltac:(lia) eq_refl) R10)) by lia; unfold w64; f_equal; lia|].
split; [rewrite (RG _ _ S11), (cv_denot_off E' 11 (rcc - i) (-1) (eq_trans (A 11%nat 11%bv ltac:(lia) eq_refl) R11)) by lia; unfold w64; f_equal; lia|].
split; [rewrite (RG _ _ S13); cbn [sv_denot]; rewrite HA by lia; rewrite (ew_Ereg_extra regs_i _ 0), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity|].
split; [rewrite (RG _ _ S14), (cv_denot_off E' 10 (o + 3 * i) 5 (eq_trans (A 10%nat 10%bv ltac:(lia) eq_refl) R10)) by lia; unfold w64; f_equal; lia|].
split; [rewrite (RG _ _ S15); reflexivity|].
split; [rewrite (RG _ _ S16); reflexivity|].
split; [rewrite (RG _ _ S2); cbn [sv_denot]; rewrite (A 2%nat 2%bv ltac:(lia) eq_refl), R2, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity|].
split; [rewrite (RG _ _ S1); cbn [sv_denot]; rewrite (A 1%nat 1%bv ltac:(lia) eq_refl), R1, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity|].
split; [intros r Hcs Hr2; rewrite (cv_cs_kept _ _ _ _ _ _ 35 HS HA0 ltac:(lia) Scs r Hcs Hr2); exact (Rcs r Hcs Hr2)|].
split.
- apply (cv_val_kept _ mem_i (ms_mem ms') _ 8 _ Hslot). intros j Hj. apply K'. lia.
- intros a Ha Hn. rewrite (K' a Ha). exact (KE a Ha Hn).
Qed.

(* ---- the `ret` of the last cell: the contract's post ---- *)
Lemma cv_leaf : forall i regs_i mem_i md_i ch v E' ss' ms' md',
  cv_inv i regs_i mem_i md_i ->
  st_ok rsegs E' ss' (restrict (w_H W) ms') ->
  env_agree 35 (Ereg regs_i (cv_extra ch v)) E' ->
  ss_pc ss' = CV_RET -> ss_resv ss' = None ->
  sr_get (ss_regs ss') 2 = SOff 2 16 -> sr_get (ss_regs ss') 1 = SOff 1 0 ->
  forallb (fun r : bv 5 => sv_eqb (sr_get (ss_regs ss') r) (SOff (Z.to_nat (bv_unsigned r)) 0)) CS_NOSP = true ->
  ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W (ms_mem ms') md' k ->
  same_io md_i md' ->
  (forall a, 0 <= a < 2 ^ 64 -> aview rsegs (w_H W) (ms_mem ms') a = aview rsegs (w_H W) mem_i a) ->
  SRr rsegs W (mkCfg ms' md') cv_post.
Proof.
intros i regs_i mem_i md_i ch v E' ss' ms' md' HI HS HA Hpc Hrv S2 S1 Scs HJ' Hio' K'.
destruct HI as (Hi & _ & Hio & _ & _ & _ & _ & _ & _ & R2 & R1 & Rcs & _ & KE).
pose proof cv_wx as Hwx. pose proof cv_segs_low as Hsegs.
assert (HA35 := HA). destruct HA as [HA _].
assert (RG : forall r e, sr_get (ss_regs ss') r = e -> getr (ms_regs ms') r = sv_denot E' e).
{ intros r e He. rewrite (st_ok_restrict_reg rsegs _ _ _ _ r HS), He. reflexivity. }
assert (G1 : getr (ms_regs ms') 1 = getr regs 1).
{ rewrite (RG _ _ S1). cbn [sv_denot]. rewrite HA by lia. rewrite (ew_Ereg_nat regs_i _ 1 1%bv eq_refl), R1, Z.add_0_r.
  apply Z_to_bv_bv_unsigned. }
assert (G2 : getr (ms_regs ms') 2 = getr regs 2).
{ rewrite (RG _ _ S2). rewrite (cv_denot_off E' 2 (spZ regs - 16) 16) by (first [rewrite HA by lia; rewrite (ew_Ereg_nat regs_i _ 2 2%bv eq_refl); exact R2 | lia]).
  replace (spZ regs - 16 + 16) with (spZ regs) by lia. unfold spZ. apply Z_to_bv_bv_unsigned. }
eapply (SRr_ret_at rsegs cv_tbl cv_tbl_ok cv_wx W E' ss' ms' md' cv_post HS Hrv); [rewrite Hpc; exact cv_ret_word|].
intros mat'. unfold cv_post, hd_post.
exists fx, lyc, Sc, (ms_regs ms'), (ms_mem ms'), (with_vm_backing (m_vm_lazy md') mat' md').
split; [rewrite G1, Hrar; reflexivity|].
split; [reflexivity|].
split; [exact (ajournal_materialize rsegs B LAWS Hsegs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mat' HJ')|].
split.
{ intros r Hr. destruct (Z.eq_dec r 2) as [->|Hr2]; [exact G2|].
  rewrite (cv_cs_kept _ _ _ _ _ _ 35 HS HA35 ltac:(lia) Scs r Hr Hr2). exact (Rcs r Hr Hr2). }
split; [exact G1|].
split; [reflexivity|].
split; [apply Permutation_refl|].
split; [exact (same_io_trans _ _ _ (same_io_trans _ _ _ Hio Hio') (same_io_wvb_cv _ _ _))|].
split; [apply mo_le_refl; exact MTL|].
split; [|exact I].
intros a Ha Hn _. rewrite (K' a Ha). apply KE; [exact Ha|]. unfold T_check_STK in Hn. lia.
Qed.

(* ---- the loop head after the entry run ---- *)
Lemma cv_inv0 : forall E' ss' ms' md',
  st_ok rsegs E' ss' (restrict (w_H W) ms') -> env_agree 33 (Ereg regs cv_extra0) E' ->
  ss_pc ss' = CV_LOOP -> ss_resv ss' = None ->
  sr_get (ss_regs ss') 10 = SOff 10 0 -> sr_get (ss_regs ss') 11 = SOff 11 0 ->
  sr_get (ss_regs ss') 13 = SOff 32 0 -> sr_get (ss_regs ss') 14 = SOff 10 2 ->
  sr_get (ss_regs ss') 15 = SLit 47 -> sr_get (ss_regs ss') 16 = SLit 2 ->
  sr_get (ss_regs ss') 2 = SOff 2 (-16) -> sr_get (ss_regs ss') 1 = SOff 1 0 ->
  forallb (fun r : bv 5 => sv_eqb (sr_get (ss_regs ss') r) (SOff (Z.to_nat (bv_unsigned r)) 0)) CS_NOSP = true ->
  nth_error (ss_mem ss') 0 = Some (YP09.mkRegion (Some 2%nat) (-16) 0 (-16) 0 [YP09.mkChunk (-8) (CVal 8 (SOff 1 0))]) ->
  ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W (ms_mem ms') md' k ->
  same_io mdc md' ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 16 <= a < spZ regs) -> aview rsegs (w_H W) (ms_mem ms') a = aview rsegs (w_H W) memc a) ->
  ms' = mkst (ms_regs ms') (Z_to_bv 64 CV_LOOP) (ms_mem ms') (seg_rom rsegs) /\
  cv_inv 0 (ms_regs ms') (ms_mem ms') md'.
Proof.
intros E' ss' ms' md' HS HA Hpc Hrv S10 S11 S13 S14 S15 S16 S2 S1 Scs Hm0 HJ' Hio' K'.
pose proof cv_rng as Hr.
split; [rewrite <- Hpc; exact (st_ok_restrict_mkst rsegs _ _ _ _ HS Hrv)|].
assert (HA0 := HA). destruct HA as [HA _].
assert (A : forall n (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r -> ew E' n = getr regs r).
{ intros n r Hn Hr'. rewrite HA by lia. exact (ew_Ereg_nat regs _ n r Hr'). }
assert (RG : forall r e, sr_get (ss_regs ss') r = e -> getr (ms_regs ms') r = sv_denot E' e).
{ intros r e He. rewrite (st_ok_restrict_reg rsegs _ _ _ _ r HS), He. reflexivity. }
assert (A1 : ew E' 1 = Z_to_bv 64 (raZ regs)) by (rewrite (A 1%nat 1%bv ltac:(lia) eq_refl); apply cv_bv_of).
assert (A2 : ew E' 2 = Z_to_bv 64 (spZ regs)) by (rewrite (A 2%nat 2%bv ltac:(lia) eq_refl); apply cv_bv_of).
pose proof (cv_u64 (getr regs 1)) as Hra64.
split; [lia|]. split; [exact HJ'|]. split; [exact Hio'|].
split; [rewrite (RG _ _ S10), (cv_denot_off E' 10 o 0 (eq_trans (A 10%nat 10%bv ltac:(lia) eq_refl) H10)) by lia; unfold w64; f_equal; lia|].
split; [rewrite (RG _ _ S11), (cv_denot_off E' 11 rcc 0 (eq_trans (A 11%nat 11%bv ltac:(lia) eq_refl) H11)) by lia; unfold w64; f_equal; lia|].
split; [rewrite (RG _ _ S13); cbn [sv_denot]; rewrite HA by lia; rewrite (ew_Ereg_extra regs _ 0), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity|].
split; [rewrite (RG _ _ S14), (cv_denot_off E' 10 o 2 (eq_trans (A 10%nat 10%bv ltac:(lia) eq_refl) H10)) by lia; unfold w64; f_equal; lia|].
split; [rewrite (RG _ _ S15); reflexivity|].
split; [rewrite (RG _ _ S16); reflexivity|].
split; [rewrite (RG _ _ S2), (cv_denot_off E' 2 (spZ regs) (-16) A2) by lia; reflexivity|].
split; [rewrite (RG _ _ S1), (cv_denot_off E' 1 (raZ regs) 0 A1) by (unfold raZ; lia); rewrite Z.add_0_r; unfold raZ; apply Z_to_bv_bv_unsigned|].
split; [intros r Hcs Hr2; exact (cv_cs_kept _ _ _ _ _ _ 33 HS HA0 ltac:(lia) Scs r Hcs Hr2)|].
split; [|exact K'].
pose proof (cv_region_at E' ss' (restrict (w_H W) ms') 0 _ HS Hm0) as (_ & _ & _ & Hcs).
cbn [YP09.r_base YP09.r_chunks base_val] in Hcs. rewrite A2, unsigned_lit_small in Hcs by lia.
apply Forall_inv in Hcs.
pose proof (val_of_chunk_ok rsegs E' _ (spZ regs) (-8) 8 (SOff 1 0) (raZ regs) Hcs) as Hv.
replace (spZ regs + -8) with (spZ regs - 8) in Hv by lia.
apply Hv.
- rewrite (cv_denot_off E' 1 (raZ regs) 0 A1) by (unfold raZ; lia). rewrite Z.add_0_r. reflexivity.
- unfold raZ. cbn. lia.
- lia.
Qed.

(* ---- one cell: the next loop head, or the `ret` after the last cell ---- *)
Ltac cv_last_case i regs_i mem_i md_i ch v HI0 Hnth HJ P LIM :=
  let HS := fresh "HS" in let SHOK := fresh "SHOK" in let HAE := fresh "HAE" in
  pose proof (cv_it_entry i ch P v LIM true regs_i mem_i md_i HI0 Hnth ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(cbv iota; lia)) as HS;
  assert (SHOK : sh_ok rsegs cv_Bx [] (Ereg regs_i (cv_extra ch v)) (mrestrict (w_H W) mem_i)) by constructor;
  assert (HAE : env_agree 35 (Ereg regs_i (cv_extra ch v)) (Ereg regs_i (cv_extra ch v))) by apply env_agree_refl;
  aj_run_tok cv_tbl_ok HS HJ SHOK cv_Bspan;
  try solve [cbn [ms_mem mkst]; eapply cv_obl; [exact HI0 | lia]];
  try solve [awr_ok_tac];
  lazymatch goal with HFr : frame_of _ _ (mrestrict _ mem_i) (mrestrict _ (ms_mem ?msx)) |- _ =>
    let K1 := fresh "K1" in
    pose proof (cv_kept_run (segs := rsegs) (fun _ => False) _ _ _ mem_i mem_i (ms_mem msx) (fun a _ _ => eq_refl) HFr ltac:(cv_nowr)) as K1;
    eapply SRr_mono;
    [ eapply (cv_leaf i regs_i mem_i md_i ch v _ _ msx _ HI0 HS);
      [ cv_agree HAE | reflexivity | reflexivity | reflexivity | reflexivity | vm_compute; reflexivity
      | exact HJ | apply same_io_wvb_cv | intros a Ha; exact (K1 a Ha (fun x => x)) ]
    | intros W'' c'' _ HQ; left; exact HQ ]
  end.
Ltac cv_mid_case i regs_i mem_i md_i ch v HI0 Hnth HJ Hl P LIM :=
  let HS := fresh "HS" in let SHOK := fresh "SHOK" in let HAE := fresh "HAE" in
  pose proof (cv_it_entry i ch P v LIM false regs_i mem_i md_i HI0 Hnth ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(cbv iota; lia)) as HS;
  assert (SHOK : sh_ok rsegs cv_Bx [] (Ereg regs_i (cv_extra ch v)) (mrestrict (w_H W) mem_i)) by constructor;
  assert (HAE : env_agree 35 (Ereg regs_i (cv_extra ch v)) (Ereg regs_i (cv_extra ch v))) by apply env_agree_refl;
  aj_run_to_tok cv_tbl_ok HS HJ SHOK cv_Bspan CV_LATCH;
  try solve [cbn [ms_mem mkst]; eapply cv_obl; [exact HI0 | lia]];
  try solve [awr_ok_tac];
  lazymatch goal with HFr : frame_of _ _ (mrestrict _ mem_i) (mrestrict _ (ms_mem ?msx)) |- _ =>
    let K1 := fresh "K1" in
    pose proof (cv_kept_run (segs := rsegs) (fun _ => False) _ _ _ mem_i mem_i (ms_mem msx) (fun a _ _ => eq_refl) HFr ltac:(cv_nowr)) as K1;
    clear HFr;
    repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end;
    aj_run_to_tok cv_tbl_ok HS HJ SHOK cv_Bspan CV_LOOP;
    try solve [awr_ok_tac];
    lazymatch goal with HFr2 : frame_of _ _ (mrestrict _ (ms_mem msx)) (mrestrict _ (ms_mem ?msy)) |- _ =>
      let K2 := fresh "K2" in
      pose proof (cv_kept_run (segs := rsegs) (fun _ => False) _ _ _ (ms_mem msx) (ms_mem msx) (ms_mem msy) (fun a _ _ => eq_refl) HFr2 ltac:(cv_nowr)) as K2;
      lazymatch goal with |- SRr _ _ (mkCfg _ ?mdy) _ =>
        let Hn := fresh "Hn" in
        assert (Hn : msy = mkst (ms_regs msy) (Z_to_bv 64 CV_LOOP) (ms_mem msy) (seg_rom rsegs) /\
                     cv_inv (i + 1) (ms_regs msy) (ms_mem msy) mdy);
        [ eapply (cv_next i regs_i mem_i md_i ch v _ _ msy mdy HI0 Hl HS);
          [ cv_agree HAE | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
          | reflexivity | reflexivity | reflexivity | reflexivity | vm_compute; reflexivity
          | exact HJ | first [apply same_io_wvb_cv | eapply same_io_trans; apply same_io_wvb_cv]
          | intros a Ha; rewrite (K2 a Ha (fun x => x)); exact (K1 a Ha (fun x => x)) ]
        | apply SRr_ret; right; exists (i + 1); split; [lia|]; split; [reflexivity|];
          exists (ms_regs msy), (ms_mem msy), mdy; split; [f_equal; exact (proj1 Hn) | exact (proj2 Hn)] ]
      end
    end
  end.

Lemma cv_step : forall i W' c, cv_P i W' c ->
  SRr rsegs W' c (fun W'' c'' => cv_post W'' c'' \/ exists i', 0 <= rcc - i' < rcc - i /\ cv_P i' W'' c'').
Proof.
intros i W' c (-> & regs_i & mem_i & md_i & -> & HI0).
pose proof HI0 as (Hi & HJ & _).
pose proof cv_wx as Hwx. pose proof cv_segs_low as Hsegs.
assert (Hlt : (Z.to_nat i < length cs)%nat) by lia.
destruct (nth_error cs (Z.to_nat i)) as [[[ch p] v]|] eqn:Hnth; [|apply nth_error_None in Hnth; lia].
pose proof (proj1 (Forall_forall _ _) Hval _ (nth_error_In _ _ Hnth)) as Hcv.
unfold Headamp.cell_valid, Headamp.HA_CHANNELS, Headamp.HA_SENS, Headamp.HA_SENS_MAX in Hcv.
destruct Hcv as (Hch & Hp & Hv).
assert (Hp3 : p = 0 \/ p = 1 \/ p = 2) by lia.
destruct (Z.eq_dec (rcc - i) 1) as [Hl|Hl]; destruct Hp3 as [-> | [-> | ->]]; cbn in Hv.
- cv_last_case i regs_i mem_i md_i ch v HI0 Hnth HJ 0 1.
- cv_last_case i regs_i mem_i md_i ch v HI0 Hnth HJ 1 1.
- cv_last_case i regs_i mem_i md_i ch v HI0 Hnth HJ 2 55.
- assert (Hl2 : 2 <= rcc - i) by lia. cv_mid_case i regs_i mem_i md_i ch v HI0 Hnth HJ Hl2 0 1.
- assert (Hl2 : 2 <= rcc - i) by lia. cv_mid_case i regs_i mem_i md_i ch v HI0 Hnth HJ Hl2 1 1.
- assert (Hl2 : 2 <= rcc - i) by lia. cv_mid_case i regs_i mem_i md_i ch v HI0 Hnth HJ Hl2 2 55.
Qed.

Lemma cv_loop : forall i regs_i mem_i md_i, cv_inv i regs_i mem_i md_i ->
  SRr rsegs W (mkCfg (mkst regs_i (Z_to_bv 64 CV_LOOP) mem_i (seg_rom rsegs)) md_i) cv_post.
Proof.
intros i regs_i mem_i md_i HI.
apply (SRr_loopZ rsegs Z (fun i => rcc - i) cv_P cv_post cv_step i W).
split; [reflexivity|]. exists regs_i, mem_i, md_i. split; [reflexivity | exact HI].
Qed.

(* ---- rc > 0: the entry run to the loop head, then the loop ---- *)
Lemma cv_pos : SRr rsegs W (cfg_at rsegs A_CHECK_CELLS_VALID regs memc mdc) cv_post.
Proof.
pose proof cv_wx as Hwx. pose proof cv_segs_low as Hsegs.
assert (B2 : bv_unsigned (ew (Ereg regs cv_extra0) 2) = spZ regs) by (rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); reflexivity).
assert (SHOK : sh_ok rsegs cv_Bx [] (Ereg regs cv_extra0) (mrestrict (w_H W) memc)) by constructor.
pose proof (cv_entry0 true W regs memc rcc Hpres16 Hsp Hal16 Vgot Vcell H11 ltac:(lia) ltac:(cbn; lia)) as HS.
pose proof HJ0 as HJ.
unfold cfg_at. change (w64 A_CHECK_CELLS_VALID) with (Z_to_bv 64 A_CHECK_CELLS_VALID).
aj_run_to_tok cv_tbl_ok HS HJ SHOK cv_Bspan CV_LOOP; [cv_awr B2 | ].
lazymatch goal with HFr : frame_of _ _ (mrestrict _ memc) (mrestrict _ (ms_mem ?msx)) |- _ =>
  pose proof (cv_kept_run (segs := rsegs) (fun a => spZ regs - 16 <= a < spZ regs) _ _ _ memc memc (ms_mem msx) (fun a _ _ => eq_refl) HFr ltac:(cv_kwr B2)) as K1;
  lazymatch goal with |- SRr _ _ (mkCfg _ ?mdx) _ =>
    destruct (cv_inv0 _ _ msx mdx HS (env_agree_refl _ _) eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
      eq_refl eq_refl ltac:(vm_compute; reflexivity) eq_refl HJ (same_io_wvb_cv _ _ _) K1) as [Hshape HI];
    rewrite Hshape; exact (cv_loop 0 _ _ _ HI)
  end
end.
Qed.
End loop.

Theorem hd_check_cells_valid_A : hd_check_cells_valid_specX rsegs B MT A_CHECK_CELLS_VALID.
Proof using MTL HBgot HBcell.
unfold hd_check_cells_valid_specX, hd_pre.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs rcc o cs
  (HJ & Hrar & Hra4 & Hgp & Htp & Hal16 & Hwlo & Hwhi & Hev) H10 H11 Hrc Hpre.
pose proof cv_wx as Hwx. pose proof cv_segs_low as Hsegs.
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & _).
unfold T_check_STK in Hwlo.
assert (Hsp : 2 ^ 46 <= spZ regs <= 2 ^ 47) by lia.
destruct (al_const _ _ LAWS _ _ _ _ _ HAR) as (Kcell & _ & Kgot & _).
rewrite HBcell in Kcell. rewrite HBgot, HBcell in Kgot.
pose proof (val_mem_of_rdword rsegs _ _ _ _ Kgot) as Vgot.
pose proof (val_mem_of_rdword rsegs _ _ _ _ Kcell) as Vcell.
assert (Hpres16 : forall a, spZ regs - 16 <= a < spZ regs -> apresent (w_H W) memc a) by (intros a Ha; apply Hpres; lia).
destruct (Z_lt_le_dec 0 rcc) as [Hpos | Hnpos].
- destruct (Hpre Hpos) as (Hlen & Hval & Ho0 & Ho63 & Hg & Hra & Hoff & Happ).
  assert (Hrc' : 0 < rcc < 2 ^ 31) by lia.
  eapply cv_pos with (rcc := rcc) (o := o) (cs := cs); eassumption.
- assert (B2 : bv_unsigned (ew (Ereg regs cv_extra0) 2) = spZ regs) by (rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); reflexivity).
  assert (SHOK : sh_ok rsegs cv_Bx [] (Ereg regs cv_extra0) (mrestrict (w_H W) memc)) by constructor.
  pose proof (cv_entry0 false W regs memc rcc Hpres16 Hsp Hal16 Vgot Vcell H11 Hrc ltac:(cbn; lia)) as HS.
  unfold cfg_at. change (w64 A_CHECK_CELLS_VALID) with (Z_to_bv 64 A_CHECK_CELLS_VALID).
  aj_run_tok cv_tbl_ok HS HJ SHOK cv_Bspan; [cv_awr B2 | ].
  lazymatch goal with HFr : frame_of _ _ (mrestrict _ memc) (mrestrict _ (ms_mem ?msx)) |- _ =>
    pose proof (cv_kept_run (segs := rsegs) (fun a => spZ regs - 16 <= a < spZ regs) _ _ _ memc memc (ms_mem msx) (fun a _ _ => eq_refl) HFr ltac:(cv_kwr B2)) as K1;
    eapply (SRr_ret_at rsegs cv_tbl cv_tbl_ok cv_wx W _ _ msx _ _ HS eq_refl); [vm_compute; reflexivity|];
    let mat' := fresh "mat" in intros mat';
    lazymatch goal with |- _ _ (mkCfg _ (with_vm_backing _ _ ?mdx)) =>
      red; exists fx, lyc, Sc, (ms_regs msx), (ms_mem msx), (with_vm_backing (m_vm_lazy mdx) mat' mdx);
      let S1 := fresh "S1" in
      lazymatch type of HS with st_ok _ _ ?ssx _ =>
        assert (S1 : sr_get (ss_regs ssx) 1%bv = SOff 1 0) by (vm_compute; reflexivity) end;
      assert (G1 : getr (ms_regs msx) 1 = getr regs 1)
        by (rewrite (st_ok_restrict_reg rsegs _ _ _ _ 1%bv HS), S1; cbn [sv_denot];
            rewrite (ew_Ereg_nat regs _ 1 1%bv eq_refl), Z.add_0_r; apply Z_to_bv_bv_unsigned);
      split; [rewrite G1, Hrar; reflexivity|];
      split; [reflexivity|];
      split; [exact (ajournal_materialize rsegs B LAWS Hsegs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mat' HJ)|];
      split; [eapply aregs_preserved_of_st_ok; [exact HS | apply env_agree_refl | vm_compute; reflexivity]|];
      split; [exact G1|];
      split; [reflexivity|];
      split; [apply Permutation_refl|];
      split; [first [apply same_io_wvb_cv | eapply same_io_trans; apply same_io_wvb_cv]|];
      split; [apply mo_le_refl; exact MTL|];
      split; [|exact I];
      intros a Ha Hn _; apply K1; [exact Ha | clear - Hn; unfold T_check_STK in Hn; lia]
    end
  end.
Qed.
End w.

Print Assumptions hd_check_cells_valid_A.
