(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the ASan+UBSan walk of sup_instance_info (plugin-hostd/fuzz_command,
   fuzz_command.asan-ubsan, 0x8bb70, 122 instructions), after lib/A/Prog/answer_code.v (a working branch
   2ba4488ce71: a side-stack frame taken by __asan_stack_malloc_N, its header and shadow, the snprintf call and the
   release by the flag store) and lib/A/Prog/sup_instance_info.v (a working branch 0de7ca03d26: the
   recorder's chain through record, arg_s, rec_shape_of and answer and the post), re-derived on B's code, against
   a Theorem Labs lane's statement (a working branch f490061c104). The snprintf step through the shared contract and the change of FP
   state after it follow a working branch 07b554c4785 (lib/B/Prog/answer_code.v:943-1070), the release
   by the flag store answer_code.v's end, the post's block algebra a working branch b5e1a22725a
   (descriptors_panel_get_aux.v dpgb_post_of), the calls after record a working branch c79a9f2daf7. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/B/Prog/sup_instance_info.v, with its module paths and module names changed; 378 of its 447 lines of code are new or changed and 1753 lines of the source are left out. *)
(* Segment 1 of the walk of cross_check on reac-pw/fuzz_segconf's ASan+UBSan IMAGE B (fuzz_segconf.asan-ubsan,
   pin c3796c0b38f3; cross_check 0x897cc): cross_check_d.v's cc_S1P, from the entry 0x897cc through the prologue,
   the two entry UBSan trap tests, the shadow base's GOT load, the inline check of c->n and the preheader, to the
   loop head CC_LOOP 0x89874 at pass 0 (n > 0) or to the epilogue CC_EPI 0x899fc (n <= 0). Proves no function: it
   is a segment lemma of cross_check's image-B walk, chained by cross_check_a.v / cross_check.v.
   ADAPTED from the image-A G3 walk owner's image-A lib/A/Prog/cross_check_s1.v (commit c5ef7330de64), itself in
   the form of plugin-hostd/fuzz_command's lib/A/Prog/chain_words_s1.v and numberE.v (origin/ossv/recipes
   501c0d516c69): an entry seed of this file's own (cc1_entry), one token run to the branch on n (0x89840), the
   split, and a token run to each cut, whose facts are read back from the symbolic state. The structure is image
   A's; every number, the register map at the loop head, the three spill slots and the two trap sites are image
   B's (cross_check.fuzz_segconf.asan-ubsan.s lines 2-45 and 158-162).

   Instructions walked: 0x897cc-0x89870 (42), and the slow-path stub of check 1 0x89a3c-0x89a44 (3) by the token
   executor's slow-block rule; the check's error call 0x89a48-0x89a4c (2) is unreachable: the executor takes the
   check's pass edge on the obligation below.

   The two UBSan trap branches of this segment (both to the `unimp` at 0x89a38) are DECIDED NOT TAKEN by the
   symbolic executor from the facts of the seed's atom 10 (= a0 = c), which come from cc_pre:
     0x89804 `beqz a0`              c = 0          -- atom 10 lies in [4096, 2^47 - 2^23] (PaLibF.HPTR 4): the
                                                      lower bound is the blocks law (al_blocks: a live block
                                                      starts at or above 4096) over cc_pre's cp_heap, the upper
                                                      bound c + 16616 <= alloc_ceiling <= 2^47 - 2^23 (YP0m
                                                      decide_eq on the atom range against 0)
     0x89810 `bnez a0`              (c & 7) <> 0   -- atom 10's alignment 2^4 is cc_pre's cp_c16 (c mod 16 = 0),
                                                      so `andi a0,a0,7` at 0x8980c is the literal 0 (YP0m
                                                      s_and_ptr) and the branch compares 0 with 0
   Inline check 1 (0x89834 `lb a0,0(s3)` of the shadow byte of s1 = c + RC_N, 0x89838 `bnez a0` to the stub) is
   the token run's one obligation (SOff 10 11392, 4): the 4 bytes of c->n are addressable at the entry memory,
   which obl_of_range (YCbq.v) gives from cc_pre's cp_addr (sa_addr of the 16616-byte block). The `blez a0` at
   0x89840 (`bge zero,a0`) is not decidable from n's range [0, 32] and is split with psrr_branch_tok.

   The token runs read no shadow region and write only the 128-byte frame (13 saves and 3 spills), so every byte
   outside [sp0 - 128, sp0) is the entry's at both cuts: the record, the literals and the read-only window are the
   entry's; the stack-protector cells (cc_un's un_ssp) come from the segment hypothesis over AR at the cut.
   At the loop head the seed leaves exactly INV_LOOP's image-B register map: s0 = c, s1 = c + RC_N, s2 = the shadow
   base, s3 = SHADOW_OFF + (c + RC_N) / 8, s9 = 356 * 0, s10 = 0, s11 = ~c (`not s11,s0` = `xori s11,s0,-1`,
   cc1_lxor_ones), and the spills [sp + 0] = ((c + RC_N) & 7) + 3 = 3, [sp + 8] = F_xbox, [sp + 16] = F_xmodel.

   POSITIONAL NAMES (g3b-common.md), checked against image B's own tables by address: the listing object A_OBJ 0 =
   0xa3210 (the shadow base's GOT word, SegList.v's `PLdHi ... (A_OBJ 0)` at 0x89818), A_OBJ 12 = 0xac7b8 (the
   shadow-base cell it holds), A_OBJ 73 = 0x21ca0 = F_xbox (`PAddHi ... (A_OBJ 73)` at 0x8985c) and A_OBJ 74 =
   0x21c00 = F_xmodel (`PAddHi ... (A_OBJ 74)` at 0x8986c) -- lib/B/Prog/SegAddr.v seg_objs indices 0, 12, 73, 74.
   Image A has the two formats the other way round (A_OBJ 73 = F_xmodel); the hypotheses below are image B's, as
   cross_check_s3.v's. The register numbers of the image-A file (s2 = F_xmodel, s3 = the shadow base, s11 = the
   shadow byte address, two spills) are not used.

   The hypothesis list is cross_check_s3.v's cc_s3 list, unchanged; this segment uses PALib (the shadow base's GOT
   word and cell), the stack-protector hypothesis (un_ssp at the cut) and the two literal equations (the spills);
   the others are there so that cross_check.v chains the three segments over one list. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI04 YI09 YG0v YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01 YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d YCbq YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegSyms SegList SegPa SegPaLib PaLibF PaLibG PaLibH PaSB PaDenot.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegGlob SegObj SegPgBase SegABase PaFx.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import refuse_c cross_check_c cross_check_f cross_check_d.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* atoms of the entry state: 0-31 the registers, 32 the shadow base SB, 33 the value of c->n *)
(* the regions of the entry state: the 128-byte frame below sp (13 saves, 3 spills), the shadow base's GOT word
   (listing object 0, 0xa3210) and cell (object 12, 0xac7b8), the 4 bytes of c->n at c + RC_N (read-only, atom 33) *)
Definition cc1_stk_r : YP09.region := stack_region 128.
Definition cc1_n_r : YP09.region :=
  YP09.mkRegion (Some 10%nat) 0x2c80 0x2c84 0x2c80 0x2c80 [YP09.mkChunk 0x2c80 (CVal 4 (SOff 33 0))].
Definition cc1_regions0 : smem := [cc1_stk_r; got_regionP; bcell_regionP 32%nat; cc1_n_r].
(* sp: 16-aligned in [2^46, 2^47]; c: 16-aligned, a live heap block below alloc_ceiling; n: at most 32 entries *)
Definition cc1_atoms0 : list (nat * afact) :=
  [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (10%nat, HPTR 4); (32%nat, mkAF SB SB 0); (33%nat, mkAF 0 32 0)].
Definition ss_cc1 : sstate := mkSS AF_cross_check sr_atoms cc1_regions0 None (mkFacts cc1_atoms0 [] []).
Definition cc1_extra (nv : Z) : list word := map (Z_to_bv 64) [SB; nv].

(* `blez a0` at 0x89840 as the executor states it: bge zero, a0 *)
Lemma cc1_lt0_atom : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 63 ->
  branch_taken BC_LT (sv_denot E (SLit 0)) (sv_denot E (SOff n 0)) = (0 <? v).
Proof.
intros E n v Hn Hv. cbn [branch_taken]. rewrite bv_lts_signed.
change (bv_signed (sv_denot E (SOff n 0))) with (Sg E (SOff n 0)).
change (bv_signed (sv_denot E (SLit 0))) with (Sg E (SLit 0)).
rewrite S_SOff, S_SLit, Hn, Z.add_0_r, unsigned_lit_small by lia.
rewrite !swrap64_id by (unfold half64; lia). reflexivity.
Qed.
(* `not s11,s0` (0x8984c, `xori s11,s0,-1`): the complement of a 64-bit value *)
Lemma cc1_lxor_ones : forall x, 0 <= x < 2 ^ 64 -> Z.lxor x 18446744073709551615 = 18446744073709551615 - x.
Proof.
intros x Hx. change 18446744073709551615 with (Z.ones 64).
pose proof (Z.add_lnot_diag x).
assert (E : Z.lxor x (Z.ones 64) = (Z.lnot x) mod 2 ^ 64).
{ rewrite <- Z.land_ones by lia. apply Z.bits_inj'. intros i Hi.
  rewrite Z.lxor_spec, Z.land_spec, Z.lnot_spec by lia.
  destruct (Z.lt_ge_cases i 64).
  - rewrite Z.ones_spec_low by lia. rewrite xorb_true_r, andb_true_r. reflexivity.
  - rewrite Z.ones_spec_high by lia. rewrite xorb_false_r, andb_false_r.
    destruct (Z.eq_dec x 0) as [->|]; [apply Z.bits_0|].
    apply Z.bits_above_log2; [lia|]. apply Z.lt_le_trans with 64; [apply Z.log2_lt_pow2; lia | lia]. }
rewrite E. unfold Z.ones. rewrite Z.shiftl_1_l. change (Z.pred (2 ^ 64)) with (2 ^ 64 - 1).
replace (Z.lnot x) with (- x - 1) by lia.
rewrite <- (Z.mod_add _ 1) by lia. rewrite Z.mod_small by lia. lia.
Qed.
(* the 13 saved slots, as membership goals over a computed chunk list *)
Ltac cc1_saved_in :=
  let j := fresh "j" in let r := fresh "r" in let Hj := fresh "Hj" in
  intros j r Hj;
  do 13 (destruct j as [|j]; [cbn in Hj; injection Hj as <-; cbn; repeat (first [left; reflexivity | right]) |]);
  destruct j; cbn in Hj; discriminate.
(* every write of a run of this segment is in the frame region (atom 2, [-128, 0)); Usp: the region's base is sp *)
Ltac cc1_awr Usp :=
  lazymatch goal with |- awr_ok ?sg ?bb ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok sg bb Ex rs' stk spx fp b0 bc fr lyx own) end;
  eapply awr_ok_cons_stack with (n := 2%nat); [reflexivity | exact Usp | cbn [YP09.r_wlo]; lia | cbn [YP09.r_whi]; lia |];
  repeat (apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|]); apply awr_ok_nil.
(* the write windows of a run's regions lie in [sp - 128, sp) (the read-only ones are empty) *)
Ltac cc1_win Usp :=
  let b0 := fresh "b0" in let wlo := fresh "wlo" in let whi := fresh "whi" in let x := fresh "x" in
  let Hin := fresh "Hin" in let Hx := fresh "Hx" in let Hq := fresh "Hq" in
  intros b0 wlo whi x Hin Hx;
  lazymatch type of Hin with In _ (windows ?rs) => let w := eval vm_compute in (windows rs) in
    change (In (b0, wlo, whi) w) in Hin end;
  cbn [In] in Hin;
  repeat (destruct Hin as [Hq | Hin];
    [injection Hq as <- <- <-; cbn [base_val] in Hx; rewrite ?Usp in Hx; cbv beta; lia |]);
  destruct Hin.
(* the stack region of a symbolic state, as a term *)
Ltac cc1_r0 HS := lazymatch type of HS with st_ok_pi _ _ _ ?s _ => eval vm_compute in (nth 0 (ss_mem s) cc1_stk_r) end.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
(* reading the symbolic state back at a cut *)
Lemma cc1_reg : forall (H : word -> bool) E ss ms (r : bv 5) e v,
  st_ok_pi SEGS VAL E ss (restrict H ms) -> sr_get (ss_regs ss) r = e -> U E e = v -> getr (ms_regs ms) r = w64 v.
Proof.
intros H E ss ms r e v HS Hr Hv. rewrite (st_ok_pi_restrict_reg H E ss ms r HS), Hr, <- Hv.
unfold U, w64. symmetry. apply Z_to_bv_bv_unsigned.
Qed.
Lemma cc1_reg_atom : forall (H : word -> bool) E ss ms (r : bv 5) n,
  st_ok_pi SEGS VAL E ss (restrict H ms) -> sr_get (ss_regs ss) r = SOff n 0 -> getr (ms_regs ms) r = ew E n.
Proof.
intros H E ss ms r n HS Hr. rewrite (st_ok_pi_restrict_reg H E ss ms r HS), Hr.
cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
Qed.
Lemma cc1_rd_chunk8 : forall E H mem base off a e v cs,
  Forall (YP09.chunk_ok SEGS E (mrestrict H mem) base) cs -> In (YP09.mkChunk off (CVal 8 e)) cs ->
  a = base + off -> U E e = v -> rdword (aview SEGS H mem) a = Some v.
Proof.
intros E H mem base off a e v cs Hc Hin -> Hv. rewrite Forall_forall in Hc. specialize (Hc _ Hin).
pose proof (U_range E e) as Hr. unfold M64 in Hr.
apply rdword_of_val_mem; [|lia].
apply (val_of_chunk_ok SEGS E _ base off 8 e v Hc);
  [rewrite <- Hv; unfold U; symmetry; apply Z_to_bv_bv_unsigned | cbn; lia | cbn; lia].
Qed.
(* the saved registers, from the chunks the prologue's stores left in the frame region (chain_words_s1.v
   cw_saved_ok) *)
Lemma cc1_saved_ok : forall E H mem sp0 (regs : bvmap 5 word) cs,
  Forall (YP09.chunk_ok SEGS E (mrestrict H mem) sp0) cs ->
  (forall j r, nth_error cc_saved j = Some r ->
     In (YP09.mkChunk (-8 - 8 * Z.of_nat j) (CVal 8 (SOff (Z.to_nat r) 0))) cs) ->
  (forall r, In r cc_saved -> ew E (Z.to_nat r) = getr regs (Z_to_bv 5 r)) ->
  forall j r, nth_error cc_saved j = Some r ->
  rdword (aview SEGS H mem) (sp0 - 8 - 8 * Z.of_nat j) = Some (bv_unsigned (getr regs (Z_to_bv 5 r))).
Proof.
intros E H mem sp0 regs cs Hc Hin Hv j r Hj.
apply (cc1_rd_chunk8 E H mem sp0 (-8 - 8 * Z.of_nat j) _ (SOff (Z.to_nat r) 0) _ cs Hc (Hin j r Hj)); [lia|].
rewrite U_SOff, (Hv r (nth_error_In _ _ Hj)), Z.add_0_r. apply zcanon_id.
pose proof (bv_unsigned_in_range 64 (getr regs (Z_to_bv 5 r))) as Rg. change (bv_modulus 64) with (2 ^ 64) in Rg.
unfold M64. exact Rg.
Qed.
(* what the entry's facts need of the bytes: the record, the literals, the read-only window *)
Lemma cc1_keep_rconf : forall (rd rd' : reader) c rcs,
  (forall a, c <= a < c + seg_spec.SEG_C_SIZE -> rd' a = rd a) -> sa_rconf rd c rcs -> sa_rconf rd' c rcs.
Proof.
intros rd rd' c rcs HK (bs & Hb & He). exists bs. split; [|exact He].
intros i Hi. destruct He as (Hl & _). rewrite HK by lia. exact (Hb i Hi).
Qed.
Lemma cc1_keep_lit : forall B (rd : reader) H mem' a s,
  (forall x, in_img SEGS x -> aview SEGS H mem' x = rd x) ->
  sa_lit SEGS B rd a s -> sa_lit SEGS B (aview SEGS H mem') a s.
Proof.
intros B rd H mem' a s HK (Ha & ((Hz & Hn0) & Ht) & Hp & Hr & Hi).
split; [exact Ha|]. split; [|split; [exact Hp | split; [exact Hr | exact Hi]]].
split; [split; [|exact Hn0] | exact (sa_tail_of_romtail SEGS H mem' _ Hr)].
intros i Hi'. rewrite HK; [exact (Hz i Hi')|].
assert (Hl : (i < length s + 1)%nat) by (rewrite length_app in Hi'; cbn [length] in Hi'; lia).
destruct (Hi (a + Z.of_nat i)) as [Himg _]; [lia | exact Himg].
Qed.
Lemma cc1_keep_rod : forall B (rd rd' : reader),
  (forall a, in_roP SEGS SEG_RLO SEG_RHI a -> rd' a = rd a) ->
  arodata_okP SEGS SEG_RLO SEG_RHI B rd -> arodata_okP SEGS SEG_RLO SEG_RHI B rd'.
Proof. intros B rd rd' HK H a Ha H1 H2. rewrite (HK a Ha). exact (H a Ha H1 H2). Qed.
Lemma cc1_inro_low : forall a, in_roP SEGS SEG_RLO SEG_RHI a -> 0 <= a < kLowMemEnd.
Proof.
intros a [(sg & Hin & _ & Hr) | Hr].
- assert (Himg : in_img SEGS a) by (exists sg; split; [exact Hin | exact Hr]). exact (pa_segs_low a Himg).
- unfold SEG_RLO, SEG_RHI, kLowMemEnd in *. lia.
Qed.
(* the entry seed: the symbolic state at cross_check's entry (0x897cc), in the form of numberE.v's n_entry, with
   cross_check's 128-byte frame, c->n and no side-stack frame or use-after-return flag *)
Lemma cc1_entry : forall (B : asyms), AR_laws SEGS B -> PALib B -> forall STK W ly S regs mem md ch c nv,
  afn_pre SEGS B STK ly S W regs mem md ch -> 128 <= STK ->
  getr regs 10 = w64 c -> 4096 <= c <= 140737479966720 -> c mod 16 = 0 ->
  c + seg_spec.SEG_C_SIZE <= alloc_ceiling -> (c + seg_spec.SEG_C_SIZE <= 0x10000 \/ 0x602000 <= c) ->
  0 <= nv <= 32 -> rd32 (aview SEGS (w_H W) mem) (c + 0x2c80) nv ->
  st_ok_pi SEGS VAL (Eimg (Ereg regs (cc1_extra nv))) ss_cc1
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_cross_check)) mem (seg_rom SEGS))).
Proof.
intros B LAWS TL STK W ly S regs mem md ch c nv HPRE HSTK H10 Hc Hc16 Hcce Hcimg Hnv Hn32.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
destruct (al_const _ _ LAWS ly S W mem md HAR) as (Kcell & Kuar & Kgot & Kguar).
rewrite (pal_got_shadow B TL), (pal_cell B TL) in Kgot. rewrite (pal_cell B TL) in Kcell.
pose proof (pal_got_cell B TL) as Hgc.
set (sp0 := spZ regs) in *.
rewrite restrict_mkst_fx.
set (E := Eimg (Ereg regs (cc1_extra nv))). pose proof pa_B_ok as HBASE.
assert (E2 : ew E 2 = getr regs 2)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 c)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (EX : forall j, (j < 2)%nat -> ew E (32 + j) = nth j (cc1_extra nv) (Z_to_bv 64 0))
  by (intros j Hj; subst E; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
pose proof (EX 0%nat ltac:(lia)) as E32. pose proof (EX 1%nat ltac:(lia)) as E33.
cbn [Nat.add nth cc1_extra map] in E32, E33. clear EX.
assert (E241 : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0)))
  by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E253 : ew E (A_OBJ 12) = Z_to_bv 64 (VAL (A_OBJ 12)))
  by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
pose proof (pa_obj_img 0 ltac:(lia)) as Hob0. pose proof (pa_obj_img 12 ltac:(lia)) as Hob12.
unfold kImgEnd in Hob0, Hob12.
assert (Usp : bv_unsigned (ew E 2) = sp0) by (rewrite E2; reflexivity).
assert (VB : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v).
{ intros n v Hn Hv. cbn [base_val]. rewrite Hn. apply unsigned_lit_small. exact Hv. }
unfold ss_cc1. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold cc1_regions0, cc1_stk_r, stack_region, cc1_n_r, got_regionP, bcell_regionP.
  repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  + cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
  + rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E241) by (pose proof (pa_val_range (A_OBJ 0)); lia).
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 12) 0) (VAL (A_OBJ 12)));
      [cbn [sv_denot]; rewrite E253, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | pose proof (pa_val_range (A_OBJ 12)); zside | zside |].
    rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kgot).
  + rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) E253) by (pose proof (pa_val_range (A_OBJ 12)); lia).
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 12)) 0 8 (SOff 32 0) SB);
      [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB; zside | zside |].
    rewrite Z.add_0_r. rewrite SB_SHADOW_OFF. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kcell).
  + rewrite (VB 10%nat c E10) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ c 0x2c80 4 (SOff 33 0) nv);
      [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
    exact (val_mem_of_rd32 SEGS (w_H W) mem _ _ Hn32).
- apply pairwise_disjoint_of_extents.
  unfold cc1_regions0, cc1_stk_r, stack_region, cc1_n_r, got_regionP, bcell_regionP, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
  rewrite (VB 10%nat c E10) by lia.
  rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E241) by (pose proof (pa_val_range (A_OBJ 0)); lia).
  rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) E253) by (pose proof (pa_val_range (A_OBJ 12)); lia).
  cbn [base_val]. rewrite Usp.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  unfold seg_spec.SEG_C_SIZE in *.
  revert Hslo Hceil HSTK Hcce Hcimg Hob0 Hob12 Hgc C1 Hc. clear. intros.
  repeat match goal with |- _ /\ _ => split end; first [exact I | lia].
- split; [|split; exact I].
  cbn [f_atoms atoms_ok cc1_atoms0]. unfold afact_ok, HPTR. cbn [af_lo af_hi af_al2].
  rewrite Usp, E10, E32, E33, !unsigned_lit_small by (unfold SB; lia).
  change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
  revert Hslo Hshi H47 Hceil C1 HSTK Hstk0 Hal16 Hc Hc16 Hnv. clear. unfold SB. intros.
  repeat match goal with |- _ /\ _ => split end; first [exact I | lia].
Qed.
(* the segment S1: the entry to the epilogue (n <= 0) or to pass 0 of the loop (n > 0) *)
Theorem cc_s1 : forall (B : asyms) (lit : list Z -> Z) (gotw guard STK_REF : Z),
  PALib B -> PALibF B -> seg_val_objs -> seg_sig_prog ->
  (forall a, SEG_RLO <= a < SEG_RHI -> in_img SEGS a) ->
  (forall ly S (W : world SEGS) mem md,
     AR SEGS B ly S W mem md -> sa_ssp (aview SEGS (w_H W) mem) gotw guard) ->
  lit F_xmodel = VAL (A_OBJ 74) -> lit F_xbox = VAL (A_OBJ 73) -> 0 <= STK_REF ->
  (forall fx0 : YK11.FPState,
     @refuse_contract fx0 rc SK SEGS B (BASE + AF_refuse) STK_REF SEG_RLO SEG_RHI lit gotw guard) ->
  cc_S1P B lit gotw guard STK_REF.
Proof.
intros B lit gotw guard STK_REF TL TLF VOBJ SIGP RRO SSP L74 L73 HSR REF.
unfold cc_S1P. intros v HPRE HEPI HLOOP.
destruct v as [ly S W regs mem md ch c rcs].
destruct HPRE as [cp_afn cp_rod cp_a0 cp_c64 cp_c0 cp_c16 cp_rconf cp_heap cp_addr cp_ref64 cp_ssp cp_lits
  cp_room cp_nev].
unfold from_EPI, from_LOOP, cc_from in HEPI, HLOOP.
cbn [x_ly x_S x_W x_regs x_mem x_md x_ch x_c x_rcs] in *.
pose proof (YG0q.AR_laws_ok SEGS B) as LAWS.
pose proof (paj_run B LAWS) as RUN. pose proof (paj_run_to B LAWS) as RUNTO.
pose proof (paj_branch (PI := PI)) as BR.
pose proof cp_afn as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HSTK : 128 <= cc_STK STK_REF) by (unfold cc_STK; lia).
assert (Hlow : alloc_ceiling + 128 <= spZ regs) by lia.
(* the block of c: a live heap block, off the image, below alloc_ceiling *)
pose proof cp_heap as (b & m & Hbin & Hb1 & Hb2).
destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR Hbin) as (Hb16 & Hb4096 & Hbce & Hbapp & _ & _ & Hm).
pose proof (req_size_pos m ltac:(lia)) as [_ Hrm].
assert (Hboff : off_img b (req_size m)) by (eapply blk_off_imgP; eassumption).
unfold off_img in Hboff.
assert (Hcimg : c + seg_spec.SEG_C_SIZE <= 0x10000 \/ 0x602000 <= c) by (unfold seg_spec.SEG_C_SIZE in *; lia).
assert (Hcb : 4096 <= c <= 140737479966720) by (unfold seg_spec.SEG_C_SIZE in *; lia).
assert (Hcce : c + seg_spec.SEG_C_SIZE <= alloc_ceiling) by lia.
(* c->n *)
destruct (sa_rconf_n _ _ _ cp_rconf) as (Hnv & Hlen32 & _).
remember (Z.of_nat (length (rc_seg rcs))) as nv eqn:Hnvd.
assert (Hnv32 : 0 <= nv <= 32) by lia.
change seg_spec.RC_N with 0x2c80 in Hnv.
(* the entry state *)
pose proof (cc1_entry B LAWS TL (cc_STK STK_REF) W ly S regs mem md ch c nv cp_afn HSTK cp_a0 Hcb cp_c16 Hcce
  Hcimg Hnv32 Hnv) as HS.
pose proof (ajournal_init SEGS B (cc_STK STK_REF) (cross_check_W c) ly S W regs mem md ch cp_afn) as HJ.
remember (Eimg (Ereg regs (cc1_extra nv))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (rewrite HE; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r)
  by (intros n r Hn; rewrite HE; apply ew_Eimg_Ereg_nat; exact Hn).
assert (E10 : ew E 10 = Z_to_bv 64 c) by (rewrite (EE 10%nat 10%bv eq_refl); exact cp_a0).
assert (EX : forall j, (j < 2)%nat -> ew E (32 + j) = nth j (cc1_extra nv) (Z_to_bv 64 0))
  by (intros j Hj; rewrite HE, Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
pose proof (EX 0%nat ltac:(lia)) as E32. pose proof (EX 1%nat ltac:(lia)) as E33.
cbn [Nat.add nth cc1_extra map] in E32, E33. clear EX.
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite (EE 2%nat 2%bv eq_refl); reflexivity).
assert (UB : U E (SOff 32 0) = SHADOW_OFF)
  by (rewrite <- SB_SHADOW_OFF; apply U_atom; [exact E32 | unfold SB; lia]).
assert (UC : U E (SOff 10 11392) = c + 11392)
  by (rewrite U_SOff, E10, unsigned_lit_small by lia; apply zcanon_id; unfold M64; lia).
pose proof cp_addr as (_ & _ & _ & HRA & _).
assert (SHOK : sh_ok SEGS (SOff 32 0) [] E (mrestrict (w_H W) mem)) by constructor.
unfold cfg_at. change (w64 (BASE + AF_cross_check)) with (Z_to_bv 64 (BASE + AF_cross_check)).
(* 0x897cc-0x89840: the prologue, the two entry UBSan trap tests 0x89804 / 0x89810 (decided not taken from atom
   10's range and alignment), the shadow base's GOT load, s1 = c + RC_N, s3 = its shadow byte address, the inline
   check of c->n (its slow stub 0x89a3c-0x89a44 by the executor's slow-block rule), the load of n; it stops at the
   branch blez a0 (0x89840) *)
paj_run_tok RUN HS HJ SHOK Bspan.
{ rewrite UC.
  apply (obl_of_range SEGS (w_H W) mem E (SOff 32 0) (c + 11392) 4 c seg_spec.SEG_C_SIZE HRA UB);
    unfold seg_spec.SEG_C_SIZE; lia. }
{ cc1_awr Usp. }
rename HF into HF1, HFr into HFr1, HG into HG1.
lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?mx) => rename mx into ms1 end.
lazymatch goal with |- SRr _ _ (mkCfg _ ?mm) _ => set (md1 := mm) in *; clearbody md1 end.
lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ => set (E1 := Ex) in * end.
assert (E1E : forall n, (n < 1024)%nat -> ew E1 n = ew E n)
  by (intros n Hn; unfold E1; rewrite !ew_ewset_other by lia; reflexivity).
clearbody E1.
assert (Usp1 : bv_unsigned (ew E1 2) = spZ regs) by (rewrite E1E by lia; exact Usp).
assert (E1_10 : ew E1 10 = Z_to_bv 64 c) by (rewrite E1E by lia; exact E10).
assert (E1_33 : ew E1 33 = Z_to_bv 64 nv) by (rewrite E1E by lia; exact E33).
assert (UB1 : U E1 (SOff 32 0) = SHADOW_OFF)
  by (rewrite <- SB_SHADOW_OFF; apply U_atom; [rewrite E1E by lia; exact E32 | unfold SB; lia]).
assert (UC1 : U E1 (SOff 10 11392) = c + 11392)
  by (rewrite U_SOff, E1_10, unsigned_lit_small by lia; apply zcanon_id; unfold M64; lia).
(* the run wrote only the frame *)
assert (K1 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 128 <= a < spZ regs) -> rdW W (ms_mem ms1) a = rdW W mem a).
{ intros a Ha Hn.
  apply (kept_of_frame E _ (w_H W) mem (ms_mem ms1) (fun x => spZ regs - 128 <= x < spZ regs) HFr1);
    [| exact Ha | exact Hn].
  cc1_win Usp. }
(* what both cuts have: the frame part, the entry facts, the record *)
assert (CUT : forall ssK msK mdK rK,
  st_ok_pi SEGS VAL E1 ssK (restrict (w_H W) msK) ->
  nth_error (ss_mem ssK) 0 = Some rK -> YP09.r_base rK = Some 2%nat ->
  (forall j r, nth_error cc_saved j = Some r ->
     In (YP09.mkChunk (-8 - 8 * Z.of_nat j) (CVal 8 (SOff (Z.to_nat r) 0))) (YP09.r_chunks rK)) ->
  sr_get (ss_regs ssK) 2%bv = SOff 2 (-128) -> sr_get (ss_regs ssK) 3%bv = SOff 3 0 ->
  sr_get (ss_regs ssK) 4%bv = SOff 4 0 ->
  ajournal SEGS B (cc_STK STK_REF) (spZ regs) (cross_check_W c) ly S W mem md [] ly S W (ms_mem msK) mdK 0 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 128 <= a < spZ regs) -> rdW W (ms_mem msK) a = rdW W (ms_mem ms1) a) ->
  cc_fi B lit gotw guard STK_REF (mkCCX ly S W regs mem md ch c rcs) ly S W (ms_regs msK) (ms_mem msK) mdK /\
  cc_un B lit gotw guard STK_REF (mkCCX ly S W regs mem md ch c rcs) ly S W (ms_mem msK) /\
  sa_rconf (rdW W (ms_mem msK)) c rcs).
{ intros ssK msK mdK rK HSK HrK HbK HchK H2 H3 H4 HJK HKK.
  pose proof (st_ok_pi_region_nth E1 ssK _ 0%nat rK HSK HrK) as (_ & _ & _ & CST).
  rewrite HbK in CST. cbn [base_val] in CST. rewrite Usp1 in CST.
  assert (KEEP : forall a, 0 <= a < alloc_ceiling -> rdW W (ms_mem msK) a = rdW W mem a).
  { intros a Ha. rewrite HKK by lia. apply K1; lia. }
  split; [|split].
  - constructor.
    + exact HJK.
    + change (cc_sp0 _) with (spZ regs).
      apply (cc1_reg (w_H W) E1 ssK msK 2%bv (SOff 2 (-128))); [exact HSK | exact H2 |].
      rewrite U_SOff, Usp1, zcanon_id by (unfold M64; lia). lia.
    + rewrite (cc1_reg_atom (w_H W) E1 ssK msK 3%bv 3%nat HSK H3), E1E, (EE 3%nat 3%bv eq_refl) by lia. exact Hgp.
    + rewrite (cc1_reg_atom (w_H W) E1 ssK msK 4%bv 4%nat HSK H4), E1E, (EE 4%nat 4%bv eq_refl) by lia. exact Htp.
    + cbn [cc_sp0 x_regs]. apply (cc1_saved_ok E1 (w_H W) (ms_mem msK) (spZ regs) regs _ CST HchK).
      intros r Hr. cbn in Hr.
      repeat (destruct Hr as [<- | Hr]; [rewrite E1E by (cbn; lia); apply EE; reflexivity |]). destruct Hr.
    + apply sa_noalloc_refl.
  - constructor.
    + apply (cc1_keep_rod B (rdW W mem)); [|exact cp_rod].
      intros a Ha. pose proof (cc1_inro_low a Ha). apply KEEP. lia.
    + intros x Hx. apply (cc1_keep_lit B (rdW W mem)); [|exact (cp_lits x Hx)].
      intros y Hy. pose proof (pa_segs_low y Hy). apply KEEP. lia.
    + exact (SSP ly S W (ms_mem msK) mdK (proj1 HJK)).
    + exact cp_heap.
  - apply (cc1_keep_rconf (rdW W mem)); [|exact cp_rconf].
    intros a Ha. apply KEEP. unfold seg_spec.SEG_C_SIZE in *. lia. }
assert (LT : branch_taken BC_LT (sv_denot E1 (SLit 0)) (sv_denot E1 (SOff 33 0)) = (0 <? nv))
  by (apply cc1_lt0_atom; [exact E1_33 | lia]).
psrr_branch_tok RUN BR HS SHOK Bspan.
- (* n <= 0 (blez taken): the epilogue CC_EPI 0x899fc; the fold over no entry leaves rcs *)
  change BC_GE with (neg_bc BC_LT) in Hc. rewrite branch_taken_neg, LT in Hc.
  apply negb_true_iff in Hc. apply Z.ltb_ge in Hc.
  assert (Hl0 : length (rc_seg rcs) = 0%nat) by lia.
  paj_run_to_tok RUNTO HS HJ SHOK Bspan CC_EPI.
  { cc1_awr Usp1. }
  rename HF into HF2, HFr into HFr2, HG into HG2.
  lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?mx) => rename mx into ms2 end.
  lazymatch goal with |- SRr _ _ (mkCfg _ ?mm) _ => set (md2 := mm) in *; clearbody md2 end.
  assert (K2 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 128 <= a < spZ regs) ->
    rdW W (ms_mem ms2) a = rdW W (ms_mem ms1) a).
  { intros a Ha Hn.
    apply (kept_of_frame E1 _ (w_H W) (ms_mem ms1) (ms_mem ms2) (fun x => spZ regs - 128 <= x < spZ regs) HFr2);
      [| exact Ha | exact Hn].
    cc1_win Usp1. }
  lazymatch type of HS with st_ok_pi _ _ _ ?ssK _ =>
    let r0 := cc1_r0 HS in
    destruct (CUT ssK ms2 md2 r0 HS ltac:(vm_compute; reflexivity) eq_refl ltac:(cc1_saved_in)
      ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) HJ K2)
      as (CFI & CUN & CRC) end.
  pmkst HS.
  change (SRr SEGS W (cfg_at SEGS (BASE + CC_EPI) (ms_regs ms2) (ms_mem ms2) md2)
    (cc_post B lit gotw guard STK_REF (mkCCX ly S W regs mem md ch c rcs))).
  apply (HEPI ly S W (ms_regs ms2) (ms_mem ms2) md2).
  unfold INV_EPI. split; [exact CFI|].
  cbn [x_c x_rcs]. unfold SegModel.cross_check. rewrite Hl0. exact CRC.
- (* n > 0 (blez not taken): the preheader 0x89844-0x89870, to the loop head CC_LOOP 0x89874 at i = 0 *)
  change BC_GE with (neg_bc BC_LT) in Hc. rewrite branch_taken_neg, LT in Hc.
  apply negb_false_iff in Hc. apply Z.ltb_lt in Hc.
  paj_run_to_tok RUNTO HS HJ SHOK Bspan CC_LOOP.
  { cc1_awr Usp1. }
  rename HF into HF2, HFr into HFr2, HG into HG2.
  lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?mx) => rename mx into ms2 end.
  lazymatch goal with |- SRr _ _ (mkCfg _ ?mm) _ => set (md2 := mm) in *; clearbody md2 end.
  assert (K2 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 128 <= a < spZ regs) ->
    rdW W (ms_mem ms2) a = rdW W (ms_mem ms1) a).
  { intros a Ha Hn.
    apply (kept_of_frame E1 _ (w_H W) (ms_mem ms1) (ms_mem ms2) (fun x => spZ regs - 128 <= x < spZ regs) HFr2);
      [| exact Ha | exact Hn].
    cc1_win Usp1. }
  lazymatch type of HS with st_ok_pi _ _ _ ?ssK _ =>
    let r0 := cc1_r0 HS in
    destruct (CUT ssK ms2 md2 r0 HS ltac:(vm_compute; reflexivity) eq_refl ltac:(cc1_saved_in)
      ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) HJ K2)
      as (CFI & CUN & CRC);
    pose proof (st_ok_pi_region_nth E1 ssK _ 0%nat r0 HS ltac:(vm_compute; reflexivity)) as (_ & _ & _ & CST) end.
  cbn [YP09.r_base base_val] in CST. rewrite Usp1 in CST.
  assert (HEIc : img_env VAL A_LIM E1) by assumption.
  (* the loop registers (image B): s0 = c, s1 = &c->n, s2 = the shadow base, s3 = the shadow byte address of
     &c->n, s9 = s10 = 0, s11 = ~c *)
  assert (R8 : getr (ms_regs ms2) 8 = w64 c).
  { erewrite (cc1_reg_atom (w_H W) E1 _ ms2 8%bv 10%nat); [exact E1_10 | exact HS | vm_compute; reflexivity]. }
  assert (R9 : getr (ms_regs ms2) 9 = w64 (c + seg_spec.RC_N)).
  { eapply (cc1_reg (w_H W) E1 _ ms2 9%bv (SOff 10 11392)); [exact HS | vm_compute; reflexivity | exact UC1]. }
  assert (R18 : getr (ms_regs ms2) 18 = w64 SHADOW_OFF).
  { eapply (cc1_reg (w_H W) E1 _ ms2 18%bv (SOff 32 0)); [exact HS | vm_compute; reflexivity | exact UB1]. }
  assert (R19 : getr (ms_regs ms2) 19 = w64 (SHADOW_OFF + (c + seg_spec.RC_N) / 8)).
  { eapply (cc1_reg (w_H W) E1 _ ms2 19%bv (SAlu ALU_ADD (SAlu ALU_SRL (SOff 10 11392) (SLit 3)) (SOff 32 0)));
      [exact HS | vm_compute; reflexivity |].
    rewrite U_SAlu, U_SAlu, U_SLit, UC1, UB1. cbn [zalu_raw].
    change (Z.land (zcanon 3) 63) with 3.
    rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. unfold seg_spec.RC_N.
    assert (D : 0 <= (c + 11392) / 8 < 2 ^ 61) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
    unfold zcanon, M64. rewrite (Z.mod_small ((c + 11392) / 8)) by lia.
    rewrite Z.mod_small by (unfold SHADOW_OFF; lia). lia. }
  assert (R25 : getr (ms_regs ms2) 25 = w64 (356 * 0)).
  { eapply (cc1_reg (w_H W) E1 _ ms2 25%bv (SLit 0)); [exact HS | vm_compute; reflexivity |].
    rewrite U_SLit. reflexivity. }
  assert (R26 : getr (ms_regs ms2) 26 = w64 0).
  { eapply (cc1_reg (w_H W) E1 _ ms2 26%bv (SLit 0)); [exact HS | vm_compute; reflexivity |].
    rewrite U_SLit. reflexivity. }
  assert (R27 : getr (ms_regs ms2) 27 = w64 (2 ^ 64 - 1 - c)).
  { eapply (cc1_reg (w_H W) E1 _ ms2 27%bv (SAlu ALU_XOR (SOff 10 0) (SLit (-1))));
      [exact HS | vm_compute; reflexivity |].
    rewrite U_SAlu, U_SLit, (U_atom E1 10 c E1_10) by lia. cbn [zalu_raw].
    replace (zcanon (-1)) with 18446744073709551615 by (vm_compute; reflexivity).
    rewrite cc1_lxor_ones by lia. rewrite zcanon_id by (unfold M64; lia). lia. }
  (* the three spills: [sp + 0] = ((c + RC_N) & 7) + 3 = 3, [sp + 8] = F_xbox, [sp + 16] = F_xmodel *)
  assert (SP0 : rdword (rdW W (ms_mem ms2)) (spZ regs - 128) = Some 3).
  { apply (cc1_rd_chunk8 E1 (w_H W) (ms_mem ms2) (spZ regs) (-128) _ (SLit 3) 3 _ CST);
      [repeat (first [left; reflexivity | right]) | lia | rewrite U_SLit; reflexivity]. }
  assert (SP8 : rdword (rdW W (ms_mem ms2)) (spZ regs - 120) = Some (lit F_xbox)).
  { apply (cc1_rd_chunk8 E1 (w_H W) (ms_mem ms2) (spZ regs) (-120) _ (SOff 314 0) _ _ CST);
      [repeat (first [left; reflexivity | right]) | lia |].
    rewrite L73. apply (U_img_atom E1 HEIc). unfold A_OBJ, A_TEXT, A_LIM. lia. }
  assert (SP16 : rdword (rdW W (ms_mem ms2)) (spZ regs - 112) = Some (lit F_xmodel)).
  { apply (cc1_rd_chunk8 E1 (w_H W) (ms_mem ms2) (spZ regs) (-112) _ (SOff 315 0) _ _ CST);
      [repeat (first [left; reflexivity | right]) | lia |].
    rewrite L74. apply (U_img_atom E1 HEIc). unfold A_OBJ, A_TEXT, A_LIM. lia. }
  pmkst HS.
  change (SRr SEGS W (cfg_at SEGS (BASE + CC_LOOP) (ms_regs ms2) (ms_mem ms2) md2)
    (cc_post B lit gotw guard STK_REF (mkCCX ly S W regs mem md ch c rcs))).
  apply (HLOOP ly S W (ms_regs ms2) (ms_mem ms2) md2).
  unfold INV_LOOP.
  refine (conj CFI (conj CUN (conj _ (conj CRC (conj R8 (conj R9 (conj R18 (conj R19 (conj R25 (conj R26
    (conj R27 (conj SP0 (conj SP8 SP16))))))))))))).
  change (0 <= 0 < Z.of_nat (length (rc_seg rcs))). rewrite <- Hnvd. lia.
Qed.
End f.
End d.
