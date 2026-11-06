(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the ASan walk of sup_reply_code (plugin-hostd/fuzz_command, 0x89d6c, 20 instructions), in the form of proofs/cgif/cgif_file_fuzzer/lib/A/AChd.v (pb_cmpPixel, a leaf that ends in a tail jump to a runtime entry) and A/ACh2.v (the step through a call and back). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/sup_reply_code.v, with its module paths and module names changed; 498 of its 558 lines of code are new or changed and 228 lines of the source are left out. *)
(* The image-B port of lib/A/Prog/reac_segconf_role_file.v (commit 6c85b2c21267): the ASan+UBSan
   walk of reac_segconf_role_file on image B of reac-pw/fuzz_segconf (fuzz_segconf.asan-ubsan, 0x89cbc = BASE +
   AF_reac_segconf_role_file, 41 instructions, real frame 16 bytes, no side-stack frame), over image B's listing
   layer (lib/B/Prog) and image B's kit and contract copies (lib/B).

   reac_segconf_role_file_walk proves reac_segconf_role_file_contract (lib/B/Prog/reac_segconf_role_file_c.v) at
   image B's numbers, image B's instance file's (lib/B/Prog/SegInstB.v): A = BASE + AF_reac_segconf_role_file, STK =
   SegInstB.STK_reac_segconf_role_file (16 + find's SegInstB.STK_reac_segconf_find), RLO / RHI = SegInstB.RLO_A /
   RHI_A. Its Section hypotheses: find's contract at A_find = BASE + AF_reac_segconf_find,
   SegInstB.STK_reac_segconf_find, SegInstB.RLO_A, SegInstB.RHI_A (FIND), and the record facts PALib B (the GOT word
   of the shadow-base cell 0xa3210 and the cell 0xac7b8, image B's listing objects 0 and 12) and seg_sig_prog (the
   call target of find against the listing's base).

   Image B's code is image A's (A's 38 instructions in order, other pc-relative offsets and call targets) plus
   UBSan's alignment test of find's result: 0x89cdc `andi a1,a0,3`; 0x89ce0 `bnez a1` to the `unimp` at 0x89d3c.
   The run decides that branch not taken from the fact on atom 44 (a0 after the call) the walk adds after
   `beqz a0`: s = c + 356 i is 4-aligned (af_al2 = 2: query_pre's c mod 16 = 0, 356 = 4 * 89; F44 below), so
   `andi a1,a0,3` is the literal 0 (YP0m s_and_ptr). Nothing else reaches 0x89d3c: it follows the `ret` at
   0x89d38, and no other branch targets it.

   The run: the prologue stores ra and s0 in the frame and loads the shadow base through the GOT word (s0 = SB);
   find is called with c and name unchanged; on its result s = find_ptr c rcs nm the code returns 0 when s = 0,
   else tests s's alignment, checks and loads s->role_set (s + 0x14) and, when it is set, checks and loads
   s->role_file[0] (s + 0xa0) and returns s + 0xa0 when that byte is not 0, else 0. The two instrumented checks
   (0x89ce8-0x89cf4 for the load4 at 0x89cf8, 0x89d04-0x89d10 for the load1 at 0x89d14; error paths
   errpath_load4 0x89d50, errpath_load1 0x89d5c) pass by the shadow entry of the found entry [s, s + 356): the
   entry lies in the reader's heap block (query_pre's sa_heap), whose shadow the allocator law keeps addressable
   after the call (range_addressable_of_block, the block live by sa_noalloc's permutation). The bytes the two
   loads read are the block's: unchanged by the frame stores (they lie above the ceiling) and by find (its sa_kept
   clause), read through query_pre's sa_rconf. The post's sa_kept clause is the same three steps over the whole
   window (rf_kept_final). *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI00 YI04.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YO0c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal SegSyms SegList SegPa SegPaLib PaCall PaDenot PaSB.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegObj SegGlob SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec seg_query_facts.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import reac_segconf_find_c reac_segconf_role_file_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require SegInstB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* image B's pure numbers of this walk, image B's instance file's (lib/B/Prog/SegInstB.v), under the names the
   proofs below use:
   - STK_reac_segconf_find_B := SegInstB.STK_reac_segconf_find: find's frame at image B (0x89a84 `addi sp,sp,-64`,
     released at 0x89b5c) and the strcmp wrapper's 2 * ESTACK window (jal 0x89b18; RtString.astrcmp_realizes);
   - STK_reac_segconf_role_file_B := SegInstB.STK_reac_segconf_role_file: this function's frame (0x89cbc
     `addi sp,sp,-16`) and find's window, called at that sp (jal 0x89cd4);
   - RLO_B / RHI_B := SegInstB.RLO_A / RHI_A: image B's read-only window, lib/B/Prog/SegGlob.v SEG_RLO / SEG_RHI
     (0xa1c60 / 0xa3f08). *)
#[local] Notation STK_reac_segconf_find_B := SegInstB.STK_reac_segconf_find (only parsing).
#[local] Notation STK_reac_segconf_role_file_B := SegInstB.STK_reac_segconf_role_file (only parsing).
#[local] Notation RLO_B := SegInstB.RLO_A (only parsing).
#[local] Notation RHI_B := SegInstB.RHI_A (only parsing).
Lemma STK_B_values : STK_reac_segconf_find_B = 8256 /\ STK_reac_segconf_role_file_B = 8272.
Proof. split; reflexivity. Qed.

(* the shadow base, the token run's base expression (atom 32) and its band *)
Definition RF_SB : Z := 0x7fff8000.
Definition RFx : sv := SOff 32 0.
Definition RFspan : Z * Z := (RF_SB, RF_SB + 2 ^ 44 - 1).
(* atoms of the entry state: 0-31 the registers, 32 the shadow base, 33 the first role_file byte of the entry find
   returns (0 when it returns 0); the listing's objects 0 (the GOT word of the shadow-base cell) and 12 (the cell) *)
Definition rf_regions : smem := [stack_region 16; got_regionP; bcell_regionP 32].
Definition rf_facts : facts := mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (32%nat, mkAF RF_SB RF_SB 0)] [] [].
Definition ss_rf : sstate := mkSS AF_reac_segconf_role_file sr_atoms rf_regions None rf_facts.
Definition rf_b0 (rcs : rconf) (nm : list Z) : Z :=
match r_find rcs nm with Some i => hd0 (rs_role_file (r_seg rcs i)) | None => 0 end.
Definition rf_extra (b0 : Z) : list word := map (Z_to_bv 64) [RF_SB; b0].

(* list and byte facts of the reader's block *)
Lemma rf_nth_firstn : forall {A} (l : list A) n j d, (j < n)%nat -> (n <= length l)%nat ->
  nth j (firstn n l) d = nth j l d.
Proof.
intros A l n j d Hj Hn. rewrite <- (firstn_skipn n l) at 2. rewrite app_nth1; [reflexivity|].
rewrite length_firstn. lia.
Qed.
Lemma rf_nth_skipn : forall {A} (l : list A) k j d, (k <= length l)%nat -> nth j (skipn k l) d = nth (k + j) l d.
Proof.
intros A l k j d Hk. rewrite <- (firstn_skipn k l) at 2. rewrite app_nth2 by (rewrite length_firstn; lia).
rewrite length_firstn, Nat.min_l by lia. f_equal. lia.
Qed.
Lemma rf_fld_nth : forall (l : list byte) off n j, (j < n)%nat -> (off + n <= length l)%nat ->
  nth j (seg_spec.fld off n l) ZB0 = nth (off + j) l ZB0.
Proof.
intros l off n j Hj Hl. unfold seg_spec.fld. rewrite rf_nth_firstn by (try rewrite length_skipn; lia).
apply rf_nth_skipn. lia.
Qed.
(* byte j of entry i of the reader's block *)
Lemma rf_seg_byte : forall (rd : reader) c bs rcs i j, sa_bytes rd c bs -> seg_spec.rconf_enc rcs bs ->
  (i < length (rc_seg rcs))%nat -> (j < 356)%nat ->
  rd (c + 356 * Z.of_nat i + Z.of_nat j) = Some (bv_unsigned (nth j (seg_spec.fld (356 * i) 356 bs) ZB0)).
Proof.
intros rd c bs rcs i j HB HE Hi Hj. destruct HE as (HL & HLS & _). unfold seg_spec.SEG_C_SIZE in HL.
replace (c + 356 * Z.of_nat i + Z.of_nat j) with (c + Z.of_nat (356 * i + j)) by lia.
rewrite (HB (356 * i + j)%nat) by lia. rewrite rf_fld_nth by lia. reflexivity.
Qed.
(* the role_set word of entry i (`lw` at s + 0x14), 0 or 1 *)
Lemma rf_role_set_val : forall (rd : reader) c bs rcs i, sa_bytes rd c bs -> seg_spec.rconf_enc rcs bs ->
  (i < length (rc_seg rcs))%nat ->
  sa_val rd (c + 356 * Z.of_nat i + 20) 4 (seg_spec.b2z (rs_role_set (r_seg rcs i))).
Proof.
intros rd c bs rcs i HB HE Hi k Hk.
pose proof HE as (HL & HLS & HSEG & _). unfold seg_spec.SEG_C_SIZE in HL.
destruct (HSEG i Hi) as (HLf & _ & _ & HF & _).
unfold seg_spec.flag_enc, seg_spec.fldz in HF.
change (Z.to_nat seg_spec.RS_ROLE_SET) with 20%nat in HF. change (Z.to_nat 4) with 4%nat in HF.
replace (c + 356 * Z.of_nat i + 20 + Z.of_nat k) with (c + 356 * Z.of_nat i + Z.of_nat (20 + k)) by lia.
rewrite (rf_seg_byte rd c bs rcs i (20 + k) HB HE Hi) by lia.
rewrite <- (rf_fld_nth (seg_spec.fld (356 * i) 356 bs) 20 4 k) by (rewrite ?HLf; lia).
rewrite HF. unfold r_seg, seg_spec.b2z. f_equal.
destruct (rs_role_set (nth i (rc_seg rcs) rseg_d)); do 4 (destruct k as [|k]; [vm_compute; reflexivity|]); lia.
Qed.
(* the first role_file byte of entry i (`lbu` at s + 0xa0) *)
Lemma rf_role_file_byte : forall (rd : reader) c bs rcs i, sa_bytes rd c bs -> seg_spec.rconf_enc rcs bs ->
  (i < length (rc_seg rcs))%nat ->
  rd (c + 356 * Z.of_nat i + 160) = Some (hd0 (rs_role_file (r_seg rcs i))) /\
  0 <= hd0 (rs_role_file (r_seg rcs i)) < 256.
Proof.
intros rd c bs rcs i HB HE Hi.
pose proof HE as (HL & HLS & HSEG & _). unfold seg_spec.SEG_C_SIZE in HL.
destruct (HSEG i Hi) as (HLf & _ & _ & _ & _ & _ & _ & _ & _ & HRF & _).
destruct HRF as (HL96 & _ & _ & HZ).
unfold seg_spec.fldz in HL96, HZ.
change (Z.to_nat seg_spec.RS_ROLE_FILE) with 160%nat in HL96, HZ. change (Z.to_nat 96) with 96%nat in HL96, HZ.
assert (Hb : bv_unsigned (nth 0 (seg_spec.fld 160 96 (seg_spec.fld (356 * i) 356 bs)) ZB0) =
  hd0 (rs_role_file (nth i (rc_seg rcs) rseg_d))).
{ remember (seg_spec.fld 160 96 (seg_spec.fld (356 * i) 356 bs)) as g eqn:Eg.
  destruct g as [|x g']; [cbn in HL96; lia|].
  unfold seg_spec.zs in HZ. cbn [map firstn] in HZ. apply (f_equal (hd 0)) in HZ. cbn [hd] in HZ.
  cbn [nth]. rewrite HZ. destruct (rs_role_file (nth i (rc_seg rcs) rseg_d)); reflexivity. }
pose proof (bv_unsigned_in_range 8 (nth 0 (seg_spec.fld 160 96 (seg_spec.fld (356 * i) 356 bs)) ZB0)) as Rb.
change (bv_modulus 8) with 256 in Rb.
replace (c + 356 * Z.of_nat i + 160) with (c + 356 * Z.of_nat i + Z.of_nat 160) by reflexivity.
rewrite (rf_seg_byte rd c bs rcs i 160 HB HE Hi) by lia.
replace (nth 160 (seg_spec.fld (356 * i) 356 bs) ZB0) with (nth 0 (seg_spec.fld 160 96 (seg_spec.fld (356 * i) 356 bs)) ZB0)
  by (rewrite rf_fld_nth by (rewrite ?HLf; lia); reflexivity).
unfold r_seg. rewrite Hb. split; [reflexivity|]. rewrite <- Hb. lia.
Qed.
(* reads that are the same outside a window [lo, hi) *)
Definition rf_kept (rd rd' : reader) (lo hi : Z) : Prop :=
forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> rd' a = rd a.
Lemma rf_bytes_kept : forall rd rd' lo hi p bs, rf_kept rd rd' lo hi -> sa_bytes rd p bs ->
  0 <= p -> p + Z.of_nat (length bs) <= lo -> lo < 2 ^ 64 -> sa_bytes rd' p bs.
Proof. intros rd rd' lo hi p bs HK H Hp Hl Hlo i Hi. rewrite (HK (p + Z.of_nat i)) by lia. exact (H i Hi). Qed.
Lemma rf_str_kept : forall rd rd' lo hi p s, rf_kept rd rd' lo hi -> sa_str rd p s -> 0 <= p ->
  (p + Z.of_nat (length s)) - (p + Z.of_nat (length s)) mod 8 + 8 <= lo -> lo < 2 ^ 64 -> sa_str rd' p s.
Proof.
intros rd rd' lo hi p s HK [[HZ HN] HT] Hp Hl Hlo.
pose proof (Z.mod_pos_bound (p + Z.of_nat (length s)) 8 ltac:(lia)) as M.
split; [split; [|exact HN]|].
- intros i Hi. rewrite length_app in Hi. cbn [length] in Hi. rewrite (HK (p + Z.of_nat i)) by lia.
  apply HZ. rewrite length_app. cbn [length]. lia.
- intros x Hx. rewrite (HK x) by lia. exact (HT x Hx).
Qed.
Lemma rf_addr_kept : forall rd rd' lo hi q n, rf_kept rd rd' lo hi -> kHighShadowEnd <= lo ->
  sa_addr rd q n -> q + n <= 2 ^ 47 -> sa_addr rd' q n.
Proof.
intros rd rd' lo hi q n HK Hlo (H0 & H1 & H2 & H3 & H4) H47.
split; [exact H0|]. split; [exact H1|]. split; [exact H2|].
split; [exact (range_addressable_kept_win rd rd' lo hi q n HK Hlo H0 H47 H3)|].
intros Hn. exact (shadow_hull_vis_kept_win rd rd' lo hi q n HK Hlo H0 H47 Hn (H4 Hn)).
Qed.
(* the 8-byte word that holds a byte below a 4096-aligned bound ends at or below it *)
Lemma rf_tail_below : forall e cl, 0 <= e < cl -> cl mod 4096 = 0 -> e - e mod 8 + 8 <= cl.
Proof.
intros e cl He Hc. pose proof (Z.div_mod e 8 ltac:(lia)). pose proof (Z.mod_pos_bound e 8 ltac:(lia)).
pose proof (Z.div_mod cl 4096 ltac:(lia)). rewrite Hc in H1. lia.
Qed.
(* the entry region the two loads read, on atom 44 (a0 after the call: s = c + 356 i): the role_set word at
   s + 0x14 (a literal, 0 or 1) and the role_file byte at s + 0xa0 (atom 33) *)
Definition rf_ent (rs : Z) : YP09.region :=
YP09.mkRegion (Some 44%nat) 20 161 0 0 [YP09.mkChunk 20 (CVal 4 (SLit rs)); YP09.mkChunk 160 (CVal 1 (SOff 33 0))].
Definition rf_SH : list shent := [mkSHE 44 0 356].
(* the entry region lies below the frame region on atom 2 *)
Lemma rf_ent_disj : forall E rs cs, bv_unsigned (ew E 44) + 161 <= bv_unsigned (ew E 2) - 16 ->
  all_disjoint E (rf_ent rs) [YP09.mkRegion (Some 2%nat) (-16) 0 (-16) 0 cs].
Proof.
intros E rs cs H. unfold all_disjoint, extent_disjoint, rf_ent. cbn [base_val YP09.r_base YP09.r_lo YP09.r_hi].
split; [left; lia | exact I].
Qed.
(* `lbu a1; seqz a1,a1; addi a1,a1,-1; and a0,a1,a0` (0x89d14 .. 0x89d20) on the byte b and the address x *)
Lemma rf_mask : forall b x, 0 <= b < 256 -> 0 <= x < 2 ^ 64 ->
  zcanon (Z.land (zcanon (zcanon (if b <? zcanon 1 then 1 else 0) + zcanon (-1))) x) = if b =? 0 then 0 else x.
Proof.
intros b x Hb Hx. change (zcanon 1) with 1.
destruct (Z.eqb_spec b 0) as [-> | Hne].
- replace (zcanon (zcanon (if 0 <? 1 then 1 else 0) + zcanon (-1))) with 0 by (vm_compute; reflexivity).
  rewrite Z.land_0_l. reflexivity.
- replace (b <? 1) with false by (symmetry; apply Z.ltb_ge; lia).
  replace (zcanon (zcanon 0 + zcanon (-1))) with (Z.ones 64) by (vm_compute; reflexivity).
  rewrite Z.land_comm, Z.land_ones by lia. unfold zcanon, M64. rewrite !Z.mod_small by lia. reflexivity.
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation SIG s := (@pa_sigma _ seg_listing PI s).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Definition rf_E (regs : bvmap 5 word) (b0 : Z) : env := Eimg (Ereg regs (rf_extra b0)).
Section e.
Variable B : asyms.
Hypothesis TL : PALib B.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.

Lemma rf_ew_img : forall E n, img_env VAL A_LIM E -> (A_TEXT <= n < A_LIM)%nat -> ew E n = Z_to_bv 64 (VAL n).
Proof using.
intros E n HE Hn. apply bv_eq. rewrite (HE n Hn). rewrite unsigned_lit_small; [reflexivity|].
exact (pa_val_range n).
Qed.

Lemma rf_entry : forall (W : world SEGS) (regs : bvmap 5 word) mem ly S md b0,
AR SEGS B ly S W mem md ->
astk_ok STK_reac_segconf_role_file_B ly (spZ regs) ->
(forall a, spZ regs - STK_reac_segconf_role_file_B <= a < spZ regs -> apresent (w_H W) mem a) ->
st_ok_pi SEGS VAL (rf_E regs b0) ss_rf
  (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_reac_segconf_role_file)) mem (seg_rom SEGS))).
Proof using TL.
intros W regs mem ly S md b0 HAR Hstk Hpres.
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (al_const _ _ LAWS ly S W mem md HAR) as (Kcell & _ & Kgot & _).
rewrite (pal_got_shadow B TL), (pal_cell B TL) in Kgot. rewrite (pal_cell B TL) in Kcell.
pose proof (pal_got_cell B TL) as GC.
pose proof (pa_obj_img 0 ltac:(lia)) as V0. pose proof (pa_obj_img 12 ltac:(lia)) as V12.
set (E := rf_E regs b0).
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold rf_E; apply Eimg_env).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs (rf_extra b0)) n)
  by (intros n Hn; subst E; unfold rf_E; apply Eimg_low; exact Hn).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E32 : ew E 32 = Z_to_bv 64 RF_SB) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (EO0 : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0)))
  by (apply rf_ew_img; [exact HEI | unfold A_OBJ, A_TEXT, A_LIM; lia]).
assert (EO12 : ew E (A_OBJ 12) = Z_to_bv 64 (VAL (A_OBJ 12)))
  by (apply rf_ew_img; [exact HEI | unfold A_OBJ, A_TEXT, A_LIM; lia]).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (VB : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v).
{ intros n v Hn Hv. cbn [base_val]. rewrite Hn. apply unsigned_lit_small. exact Hv. }
unfold kImgEnd in V0, V12.
unfold STK_reac_segconf_role_file_B, STK_reac_segconf_find_B, ESTACK in Hstk0, Hslo, Hbot, Hpres.
unfold ss_rf. rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
- subst E. unfold rf_E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold rf_regions, stack_region, got_regionP, bcell_regionP.
  repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  + cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
  + rewrite (VB (A_OBJ 0) _ EO0) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 12) 0) (VAL (A_OBJ 12)));
      [cbn [sv_denot]; rewrite EO12, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
    rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS _ _ _ _ Kgot).
  + rewrite (VB (A_OBJ 12) _ EO12) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 12)) 0 8 (SOff 32 0) RF_SB);
      [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold RF_SB; zside | zside |].
    rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS _ _ _ _ Kcell).
- apply pairwise_disjoint_of_extents. unfold rf_regions, stack_region, got_regionP, bcell_regionP, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
  rewrite (VB (A_OBJ 0) _ EO0), (VB (A_OBJ 12) _ EO12) by lia.
  cbn [base_val]. rewrite Usp.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  revert Hslo Hshi H47 Hceil C1 Hstk0 V0 V12 GC. clear. intros. repeat split; lia.
- split; [|split; [exact I | exact I]].
  cbn [rf_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite Usp, E32, unsigned_lit_small by (unfold RF_SB; lia).
  unfold RF_SB. change (2 ^ 4) with 16. rewrite Z.pow_0_r, Z.mod_1_r.
  revert Hslo Hshi H47 Hceil Hal16 C1 Hstk0. clear. intros.
  repeat match goal with |- _ /\ _ => split end; first [exact I | lia | reflexivity].
Qed.

(* every place a query object lies (sa_loc) is below the allocation ceiling *)
Lemma rf_loc_below : forall ly S W mem md q n, AR SEGS B ly S W mem md -> 0 < n ->
  sa_loc SEGS B ly S q n -> 4096 <= q /\ q + n <= alloc_ceiling.
Proof using.
intros ly S W mem md q n HAR Hn [(b & m & Hin & H1 & H2) | [(cid & pos & Hin & Hc & H1 & H2) | HI]].
- destruct (al_blocks _ _ LAWS ly S W mem md b m HAR Hin) as (_ & Hb & Hbc & _ & _ & _ & Hm).
  pose proof (req_size_pos m ltac:(lia)) as [_ Hr]. lia.
- destruct (al_sep _ _ LAWS ly S W mem md HAR) as [_ HF]. rewrite Forall_forall in HF.
  specialize (HF (cid, pos) Hin). cbn [fst snd] in HF. lia.
- pose proof (HI q ltac:(lia)) as (Hq & _). pose proof (HI (q + n - 1) ltac:(lia)) as (Hq' & _).
  apply pa_img_range in Hq. apply pa_img_range in Hq'. pose proof asan_consts as (C1 & _).
  unfold kImgEnd in *. lia.
Qed.
(* the read-only window and the image segments lie below the frame (image B's image end 0x602000) *)
Lemma rf_aro_kept : forall rd rd' lo hi, rf_kept rd rd' lo hi -> 0x602000 <= lo -> lo < 2 ^ 64 ->
  arodata_okP SEGS RLO_B RHI_B B rd -> arodata_okP SEGS RLO_B RHI_B B rd'.
Proof using.
intros rd rd' lo hi HK H1 H2 HR a Hro Ho He.
assert (Ha : 0 <= a < 0x602000).
{ destruct Hro as [(sg & Hs & _ & Hr) | Hr].
  - assert (Hi : in_img SEGS a) by (exists sg; split; [exact Hs | exact Hr]).
    pose proof (pa_img_range a Hi) as R. unfold kImgEnd in R. lia.
  - unfold RLO_B, RHI_B, SEG_RLO, SEG_RHI in Hr. lia. }
rewrite (HK a) by lia. exact (HR a Hro Ho He).
Qed.
(* a value read through the world's view is the same value of the restricted memory *)
Lemma rf_val_of_sa : forall H (mem : word -> option byte) a n v,
  sa_val (aview SEGS H mem) a n v -> val_mem SEGS (mrestrict H mem) a n v.
Proof using.
intros H mem a n v Hv k Hk. specialize (Hv k Hk). unfold aview in Hv.
destruct (mbyte SEGS (mrestrict H mem) (a + Z.of_nat k)) as [b|] eqn:Eb; cbn in Hv; [|discriminate Hv].
injection Hv as Hb. rewrite <- (Z_to_bv_bv_unsigned 8 b). rewrite Hb. reflexivity.
Qed.
(* the post's keep clause: the frame stores before the call, find's keep clause over its window (inside this
   one), and the loads after it *)
Lemma rf_kept_final : forall (W W3 : world SEGS) mem memc mem3 mem' (regs regsc : bvmap 5 word),
  rf_kept (rdW W mem) (rdW W memc) (spZ regs - 16) (spZ regs) ->
  sa_kept SEGS W memc W3 mem3 regsc STK_reac_segconf_find_B (fun _ => False) ->
  spZ regsc = spZ regs + -16 ->
  rf_kept (rdW W3 mem3) (rdW W3 mem') (spZ regs - 16) (spZ regs) ->
  sa_kept SEGS W mem W3 mem' regs STK_reac_segconf_role_file_B (fun _ => False).
Proof using.
intros W W3 mem memc mem3 mem' regs regsc K1 K2 Hsp K3 a Ha Hn _.
unfold STK_reac_segconf_role_file_B, STK_reac_segconf_find_B, ESTACK in Hn.
rewrite (K3 a Ha) by lia.
rewrite (K2 a Ha) by (first [exact (fun x => x) | rewrite Hsp; unfold STK_reac_segconf_find_B, ESTACK; lia]).
apply K1; [exact Ha | lia].
Qed.
Lemma rf_le_byte1 : forall z, 0 <= z < 256 -> le_byte z 1 0 = z.
Proof using.
intros z Hz. unfold le_byte. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0.
rewrite Z.shiftr_0_r. change (2 ^ 8) with 256. rewrite !Z.mod_small by lia. reflexivity.
Qed.

Section w.
(* find's contract at image B's entry, stack and read-only window, at every FP state *)
Hypothesis FIND : forall fx0 : YK11.FPState,
  reac_segconf_find_contract (fx := fx0) SEGS B (BASE + AF_reac_segconf_find) SegInstB.STK_reac_segconf_find
    SegInstB.RLO_A SegInstB.RHI_A.
Hypothesis SIGP : seg_sig_prog.
Let RUN := paj_run B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_seg) (PI := PI).

Theorem reac_segconf_role_file_walk :
  reac_segconf_role_file_contract SEGS B (BASE + AF_reac_segconf_role_file) SegInstB.STK_reac_segconf_role_file
    SegInstB.RLO_A SegInstB.RHI_A.
Proof using FIND SIGP TL.
unfold reac_segconf_role_file_contract.
intros ly S W regs mem md ch c name rcs nm HPRE HROD H10 Rc H11 Rn HQ HEV.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof alloc_ceiling_value as [_ HAC].
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
assert (WS : STK_reac_segconf_role_file_B = 16 + STK_reac_segconf_find_B) by reflexivity.
assert (WS1 : STK_reac_segconf_find_B = 8256) by reflexivity.
(* the query's objects: the reader's block [c, c + 16616) in a live heap block, the name below the ceiling *)
pose proof HQ as (Hc0 & Hc16 & HRC & HHP & HAD & Hn0 & HSTR & HLOC & HADN & HNL).
pose proof HHP as (cb & cm & Hcb & Hcb1 & Hcb2). unfold seg_spec.SEG_C_SIZE in Hcb2.
destruct (al_blocks _ _ LAWS ly S W mem md cb cm HAR Hcb) as (Hb16 & Hb4096 & Hbceil & Hbapp & _ & _ & Hbm).
pose proof (req_size_pos cm ltac:(lia)) as [_ Hreq].
destruct (rf_loc_below ly S W mem md name (Z.of_nat (length nm) + 1) HAR ltac:(lia) HLOC) as [HnL HnH].
pose proof HRC as (bs & HBS & HENC).
pose proof (seg_query_facts.sq_rconf_len rcs bs HENC) as [HLbs HLS].
(* the entry state *)
set (b0 := rf_b0 rcs nm).
pose proof (rf_entry W regs mem ly S md b0 HAR Hstk Hpres) as HS.
assert (SHOK : sh_ok SEGS RFx [] (rf_E regs b0) (mrestrict (w_H W) mem)) by constructor.
pose proof (ajournal_init SEGS B STK_reac_segconf_role_file_B [] ly S W regs mem md ch HPRE) as HJ.
assert (HEI : img_env VAL A_LIM (rf_E regs b0)) by (unfold rf_E; apply Eimg_env).
remember (rf_E regs b0) as E eqn:HE.
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs (rf_extra b0)) n)
  by (intros n Hn; rewrite HE; unfold rf_E; apply Eimg_low; exact Hn).
assert (EEo : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs rr).
{ intros n rr Hn. pose proof (bv_unsigned_in_range 5 rr) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  rewrite EL by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn. }
assert (E1 : ew E 1 = getr regs 1) by (apply EEo; reflexivity).
assert (E2 : ew E 2 = getr regs 2) by (apply EEo; reflexivity).
assert (E3 : ew E 3 = getr regs 3) by (apply EEo; reflexivity).
assert (E4 : ew E 4 = getr regs 4) by (apply EEo; reflexivity).
assert (E10 : ew E 10 = getr regs 10) by (apply EEo; reflexivity).
assert (E11 : ew E 11 = getr regs 11) by (apply EEo; reflexivity).
assert (E32 : ew E 32 = Z_to_bv 64 RF_SB) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 b0) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (HAE : env_agree 32 (Ereg regs (rf_extra b0)) E).
{ split; [intros n Hn; rewrite EL by (unfold A_TEXT; lia); reflexivity | rewrite HE; reflexivity]. }
clear EL EEo.
unfold cfg_at, w64.
(* 0x89cbc .. 0x89cd4: the frame (ra, s0 stored), the shadow base through the GOT word 0xa3210, then jal find *)
paj_run_tok RUN HS HJ SHOK RFspan.
{ awr_ok_tac. exact Usp. }
lazymatch goal with Hfr : frame_of E _ (mrestrict _ _) (mrestrict _ _) |- _ =>
assert (KEEP : rf_kept (rdW W mem) (rdW W (ms_mem ms)) (spZ regs - 16) (spZ regs))
by (intros a Ha Hn; apply (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun a => spZ regs - 16 <= a < spZ regs) Hfr);
  [ intros bq wlo whi a' Hin Hrr; vm_compute in Hin;
    repeat (destruct Hin as [Hq0 | Hin]; [injection Hq0 as <- <- <-; cbn [base_val] in Hrr; rewrite ?Usp in Hrr; lia|]);
    destruct Hin
  | exact Ha | exact Hn ]) end.
clear HF HFr HG.
pmkst HS.
prreg HS (1%bv : bv 5) P1. prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
prreg HS (8%bv : bv 5) P8. prreg HS (10%bv : bv 5) P10. prreg HS (11%bv : bv 5) P11.
assert (HspT : spZ (ms_regs ms) = spZ regs + -16).
{ unfold spZ at 1. rewrite P2, Usp. rewrite unsigned_lit_small by lia. reflexivity. }
assert (P3' : getr (ms_regs ms) 3 = w64 (as_gp B)) by (rewrite P3, E3; exact Hgp).
assert (P4' : getr (ms_regs ms) 4 = w64 (as_tp B)) by (rewrite P4, E4; exact Htp).
assert (P10' : getr (ms_regs ms) 10 = w64 c) by (rewrite P10, E10; exact H10).
assert (P11' : getr (ms_regs ms) 11 = w64 name) by (rewrite P11, E11; exact H11).
assert (HraT : YK0s.ret_ok (getr (ms_regs ms) 1)) by (rewrite P1; apply ret_ok_codeptr_v; [lia | reflexivity]).
assert (Hra4T : 4096 <= bv_unsigned (getr (ms_regs ms) 1)) by (rewrite P1, unsigned_lit_small by lia; lia).
assert (HS0 : s0Z (ms_regs ms) = RF_SB) by (unfold s0Z; rewrite P8, E32; apply unsigned_lit_small; unfold RF_SB; lia).
(* find's premises at the call: the query's objects and the read-only window lie below the frame stores *)
assert (HLO : alloc_ceiling <= spZ regs - 16 - STK_reac_segconf_find_B) by lia.
assert (HQc : query_pre SEGS B ly S (rdW W (ms_mem ms)) c name rcs nm).
{ refine (conj Hc0 (conj Hc16 (conj _ (conj HHP (conj _ (conj Hn0 (conj _ (conj HLOC (conj _ HNL))))))))).
  - exists bs. split; [|exact HENC].
    apply (rf_bytes_kept _ _ (spZ regs - 16) (spZ regs) c bs KEEP HBS); lia.
  - apply (rf_addr_kept _ _ (spZ regs - 16) (spZ regs) c _ KEEP); [lia | exact HAD | unfold seg_spec.SEG_C_SIZE; lia].
  - apply (rf_str_kept _ _ (spZ regs - 16) (spZ regs) name nm KEEP HSTR); [lia | | lia].
    assert (TB : (name + Z.of_nat (length nm)) - (name + Z.of_nat (length nm)) mod 8 + 8 <= alloc_ceiling)
      by (apply rf_tail_below; [split; lia | exact HAC]).
    lia.
  - apply (rf_addr_kept _ _ (spZ regs - 16) (spZ regs) name _ KEEP); [lia | exact HADN | lia]. }
assert (HRODc : arodata_okP SEGS RLO_B RHI_B B (rdW W (ms_mem ms)))
  by (apply (rf_aro_kept _ _ (spZ regs - 16) (spZ regs) KEEP); [lia | lia | exact HROD]).
rewrite (SIGP SS_reac_segconf_find ltac:(unfold seg_prog_syms; cbn [In]; repeat (first [left; reflexivity | right]))).
replace (seg_af SS_reac_segconf_find) with AF_reac_segconf_find by (vm_compute; reflexivity).
(* 0x89cd4: find(c, name) at sp0 - 16, s0 = SB below the ceiling, so no frame chain *)
eapply SRr_bind.
{ eapply (cl_callS B LAWS W (ms_regs ms) (ms_mem ms) _ STK_reac_segconf_role_file_B (spZ regs) [] ly S W mem md [] ly S
    _ 0 STK_reac_segconf_find_B [] EV_reac_segconf_find (-16) (getr (ms_regs ms) 1) []
    (fun ly2 S2 W2 regs2 mem2 md2 => getr regs2 10 = w64 (seg_spec.find_ptr c rcs nm) /\
       sa_kept SEGS W (ms_mem ms) W2 mem2 (ms_regs ms) STK_reac_segconf_find_B (fun _ => False) /\ sa_noalloc B ly S ly2 S2)
    HJ HspT); [reflexivity | lia | lia | lia | exact P3' | exact P4' | reflexivity | exact HraT | exact Hra4T
    | rewrite HS0; apply achain_low; unfold RF_SB; lia | | ].
  - intros HPRE1. eapply SRr_mono.
    + apply (FIND fx ly S W (ms_regs ms) (ms_mem ms) _ [] c name rcs nm HPRE1 HRODc P10' Rc P11' Rn HQc HEV).
    + cbv beta. unfold apost_base. intros W3 c3 _ (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ3 & HP3 & HQ3).
      exists ly3, S3, regs3, mem3, md3. split; [reflexivity|]. split; [exact HJ3|]. split; [exact HP3 | exact HQ3].
  - intros a Ha. exfalso. exact (inFP_nil a Ha). }
cbv beta. intros W3 c3 Hwle3 (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ3 & HJc3 & HP3 & HA0 & HKF & HNA).
pose proof HNA as (HPerm3 & Hly3 & (f3 & HS3e)). subst ly3.
(* back at 0x89cd8: the stack region (the saved ra and s0) is kept, a0 is atom 44 *)
jafter_call_keep_pi HS 40%nat regs3 (mrestrict (w_H W3) mem3) HP3 [0]%nat HS3.
match type of HS3 with ?t -> _ => assert (HRK : t); [|specialize (HS3 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. apply Forall_cons; [|apply Forall_nil].
  eapply (region_kept_stack_sub SEGS B); [exact HJc3 | exact HJ3 | exact Usp | lia | lia | lia | lia | lia |].
  intros a _ Ha. exact (inFP_nil a Ha). }
clear HS. rewrite <- restrict_mkst_fx in HS3. rename HS3 into HS.
assert (A44 : ew (havoc E 40 (map (getr regs3) CLOB)) 44 = getr regs3 10) by reflexivity.
remember (havoc E 40 (map (getr regs3) CLOB)) as Ec eqn:HEc.
assert (HEIc : img_env VAL A_LIM Ec) by (rewrite HEc; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLD3 : forall n, (n < 40)%nat -> ew Ec n = ew E n) by (intros n Hn; rewrite HEc; apply YN3v.ew_havoc_old; exact Hn).
assert (HAE3 : env_agree 32 (Ereg regs (rf_extra b0)) Ec).
{ destruct HAE as [HA1 HA2]. split; [intros n Hn; rewrite OLD3 by lia; exact (HA1 n Hn) | rewrite HEc; exact HA2]. }
clear HEc.
assert (Usp3 : bv_unsigned (ew Ec 2) = spZ regs) by (rewrite OLD3 by lia; exact Usp).
assert (SHOK3 : sh_ok SEGS RFx [] Ec (mrestrict (w_H W3) mem3)) by constructor.
rewrite P1.
unfold seg_spec.find_ptr in HA0. unfold seg_spec.role_file_ptr.
destruct (r_find rcs nm) as [i|] eqn:RF.
- (* find found entry i: a0 = s = c + 356 i, not 0 *)
  assert (Hi : (i < length (rc_seg rcs))%nat) by exact (seg_query_facts.sq_find_lt rcs nm i RF).
  assert (HA0' : getr regs3 10 = Z_to_bv 64 (c + 356 * Z.of_nat i)) by (rewrite HA0; reflexivity).
  assert (U44 : U Ec (SOff 44 0) = c + 356 * Z.of_nat i) by (apply U_atom; [rewrite A44, HA0'; reflexivity | split; lia]).
  psrr_branch_tok RUN BR HS SHOK3 RFspan.
  + exfalso. rewrite branch_eq_U, U44, U_SLit in Hc. change (zcanon 0) with 0 in Hc. apply Z.eqb_eq in Hc. lia.
  + clear Hc.
    pose proof (proj1 HJ3) as HAR3.
    assert (Hcb3 : In (cb, cm) (ablocks B ly S3)) by (apply (Permutation_in _ (Permutation_sym HPerm3)); exact Hcb).
    (* the reader's block reads after the call as at the entry *)
    assert (POST : forall a, cb <= a < cb + cm -> rdW W3 mem3 a = rdW W mem a).
    { intros a Ha. rewrite (HKF a) by (first [exact (fun x => x) | rewrite HspT; lia | split; lia]).
      apply KEEP; [split; lia | lia]. }
    pose proof (rf_role_set_val (rdW W mem) c bs rcs i HBS HENC Hi) as VRS.
    destruct (rf_role_file_byte (rdW W mem) c bs rcs i HBS HENC Hi) as [VB0 RB0].
    assert (Hb0 : b0 = hd0 (rs_role_file (r_seg rcs i)))
      by (change b0 with (rf_b0 rcs nm); unfold rf_b0; rewrite RF; reflexivity).
    rewrite <- Hb0 in VB0, RB0.
    assert (V33 : ew Ec 33 = Z_to_bv 64 b0) by (rewrite OLD3 by lia; exact E33).
    (* the entry's region on atom 44 *)
    assert (RENT : forall rs, (rs = 0 \/ rs = 1) -> sa_val (rdW W mem) (c + 356 * Z.of_nat i + 20) 4 rs ->
      region_ok SEGS Ec (mrestrict (w_H W3) mem3) (rf_ent rs)).
    { intros rs Hrs Vrs. unfold rf_ent, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite A44, HA0', unsigned_lit_small by (split; lia).
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor; [|constructor]].
      - apply (chunk_ok_val SEGS Ec _ (c + 356 * Z.of_nat i) 20 4 (SLit rs) rs);
          [reflexivity | destruct Hrs as [-> | ->]; zside | zside |].
        apply rf_val_of_sa. intros k Hk. rewrite POST by (cbn in Hk; lia). exact (Vrs k Hk).
      - apply (chunk_ok_val SEGS Ec _ (c + 356 * Z.of_nat i) 160 1 (SOff 33 0) b0);
          [cbn [sv_denot]; rewrite V33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
        apply rf_val_of_sa. intros k Hk. destruct k as [|k]; [|exfalso; cbn in Hk; lia].
        rewrite POST by lia. rewrite Z.add_0_r, VB0. f_equal. symmetry. apply rf_le_byte1. lia. }
    (* s = c + 356 i at or above 4096 and 4-aligned: query_pre's c mod 16 = 0 and 356 = 4 * 89. The UBSan trap
       branch 0x89ce0 `bnez a1` (a1 = s & 3, 0x89cdc) to the `unimp` 0x89d3c is refuted by this fact: the runs
       below compute `andi a1,a0,3` as the literal 0 from af_al2 = 2 (YP0m s_and_ptr) and take the fall-through. *)
    assert (F44 : afact_ok Ec 44 (mkAF 4096 (2 ^ 47 - 4096) 2)).
    { unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite A44, HA0', unsigned_lit_small by (split; lia).
      split; [split; lia|]. split; [|split; lia].
      replace (c + 356 * Z.of_nat i) with ((4 * (c / 16) + 89 * Z.of_nat i) * 4)
        by (pose proof (Z.div_mod c 16 ltac:(lia)); lia).
      apply Z_mod_mult. }
    assert (F33 : afact_ok Ec 33 (mkAF 0 255 0)).
    { unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite V33, unsigned_lit_small by (split; lia).
      split; [split; lia|]. split; [rewrite Z.pow_0_r, Z.mod_1_r; reflexivity | split; lia]. }
    (* the shadow entry of the found entry [s, s + 356), inside the live block *)
    assert (SHOK4 : sh_ok SEGS RFx rf_SH Ec (mrestrict (w_H W3) mem3)).
    { unfold sh_ok, rf_SH. constructor; [|constructor].
      apply (shent_ok_of_range SEGS (w_H W3) mem3 Ec RFx 44 (c + 356 * Z.of_nat i) 356 (c + 356 * Z.of_nat i) 0 356).
      - apply (range_addressable_of_block SEGS B LAWS ly S3 W3 mem3 md3 cb cm); [exact HAR3 | exact Hcb3 | lia | lia].
      - unfold U, RFx. cbn [sv_denot]. rewrite OLD3, E32 by lia. rewrite Z.add_0_r, Z_to_bv_bv_unsigned.
        rewrite unsigned_lit_small by (unfold RF_SB; split; lia). reflexivity.
      - exact U44.
      - lia.
      - lia.
      - intros x Hx. destruct Hbapp as [_ [HL | [HH1 HH2]]];
          unfold kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *; lia. }
    lazymatch type of HS with st_ok_pi ?a ?b ?c ?ssx ?d => let v := eval vm_compute in ssx in change ssx with v in HS end.
    destruct (rs_role_set (r_seg rcs i)) eqn:RSET; cbn [seg_spec.b2z] in VRS.
    * (* role_set = 1: the role_file byte decides *)
      lazymatch type of HS with st_ok_pi _ _ _ ?ssx _ =>
        assert (DENT : all_disjoint Ec (rf_ent 1) (ss_mem ssx)) end.
      { cbn [ss_mem]. apply rf_ent_disj. rewrite A44, HA0', Usp3, unsigned_lit_small by (split; lia). lia. }
      lazymatch type of HS with st_ok_pi _ _ _ ?ssx _ =>
        pose proof (st_ok_pi_add_region Ec ssx _ (rf_ent 1) HS eq_refl (RENT 1 (or_intror eq_refl) VRS) DENT) as HS4 end.
      pose proof (st_ok_pi_add_fact Ec _ _ 44 (mkAF 4096 (2 ^ 47 - 4096) 2) HS4 F44) as HS5.
      pose proof (st_ok_pi_add_fact Ec _ _ 33 (mkAF 0 255 0) HS5 F33) as HS6.
      clear HS HS4 HS5. rename HS6 into HS.
      lazymatch type of HS with st_ok_pi ?a ?b ?c ?ssx ?d => let v := eval vm_compute in ssx in change ssx with v in HS end.
      (* 0x89cdc .. 0x89d38: the UBSan alignment test of s (0x89cdc `andi a1,a0,3` is 0 by F44's af_al2 = 2, so
         0x89ce0 `bnez a1` to the `unimp` 0x89d3c is not taken), both checks pass (shadow entry), the two loads,
         the mask, the epilogue *)
      paj_run_tok RUN HS HJ3 SHOK4 RFspan.
      { awr_ok_tac. exact Usp3. }
      lazymatch goal with Hfr : frame_of _ _ (mrestrict (w_H W3) mem3) (mrestrict _ ?m1) |- _ =>
      assert (K3 : rf_kept (rdW W3 mem3) (rdW W3 m1) (spZ regs - 16) (spZ regs))
      by (intros a Ha Hn; apply (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun a => spZ regs - 16 <= a < spZ regs) Hfr);
        [ intros bq wlo whi a' Hin Hrr; vm_compute in Hin;
          repeat (destruct Hin as [Hq0 | Hin]; [injection Hq0 as <- <- <-; cbn [base_val] in Hrr; rewrite ?Usp3 in Hrr; lia|]);
          destruct Hin
        | exact Ha | exact Hn ]) end.
      clear HF HFr HG.
      prreg HS (1%bv : bv 5) F1.
      lazymatch type of HS with st_ok_pi _ _ _ ?ssx (restrict _ ?msE) =>
        pose proof (st_ok_pi_restrict_reg (w_H W3) Ec ssx msE 10%bv HS) as Q10;
        let e := eval vm_compute in (sr_get (ss_regs ssx) 10%bv) in change (sr_get (ss_regs ssx) 10%bv) with e in Q10 end.
      cbn [ms_regs restrict mkst] in Q10.
      eapply (RET W3 _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
      intros mat'. unfold apost_base.
      lazymatch goal with |- exists _ _ _ _ _, mkCfg (mkst ?r _ ?m _) ?d = _ /\ _ => exists ly, S3, r, m, d end.
      split; [rewrite F1, OLD3, E1 by lia; unfold YK0s.ret_ok in Hra; rewrite Hra; reflexivity|].
      split; [apply (ajournal_materialize SEGS B LAWS Hsegs); exact HJ3|].
      split; [eapply (aregs_preserved_of_st_ok SEGS _ _ _ _ regs (rf_extra b0) HS); [exact HAE3 | vm_compute; reflexivity]|].
      split; [|split; [exact (rf_kept_final W W3 mem (ms_mem ms) mem3 _ regs (ms_regs ms) KEEP HKF HspT K3) | exact HNA]].
      rewrite Q10, denot_lit_U, !U_SAlu, !U_SLit, (U_atom Ec 33 b0 V33) by (split; lia).
      rewrite U_SOff, A44, HA0', unsigned_lit_small by (split; lia).
      rewrite (zcanon_small (c + 356 * Z.of_nat i + 160)) by (split; lia).
      cbn [zalu_raw]. rewrite rf_mask by (split; lia).
      unfold r_role_file. rewrite RF, RSET. cbn [andb negb]. rewrite <- Hb0.
      destruct (b0 =? 0); reflexivity.
    * (* role_set = 0: a0 = 0 *)
      lazymatch type of HS with st_ok_pi _ _ _ ?ssx _ =>
        assert (DENT : all_disjoint Ec (rf_ent 0) (ss_mem ssx)) end.
      { cbn [ss_mem]. apply rf_ent_disj. rewrite A44, HA0', Usp3, unsigned_lit_small by (split; lia). lia. }
      lazymatch type of HS with st_ok_pi _ _ _ ?ssx _ =>
        pose proof (st_ok_pi_add_region Ec ssx _ (rf_ent 0) HS eq_refl (RENT 0 (or_introl eq_refl) VRS) DENT) as HS4 end.
      pose proof (st_ok_pi_add_fact Ec _ _ 44 (mkAF 4096 (2 ^ 47 - 4096) 2) HS4 F44) as HS5.
      pose proof (st_ok_pi_add_fact Ec _ _ 33 (mkAF 0 255 0) HS5 F33) as HS6.
      clear HS HS4 HS5. rename HS6 into HS.
      lazymatch type of HS with st_ok_pi ?a ?b ?c ?ssx ?d => let v := eval vm_compute in ssx in change ssx with v in HS end.
      (* 0x89cdc .. 0x89d38: the UBSan alignment test of s (not taken by F44, as above), the first check passes,
         role_set = 0, a0 = 0, the epilogue *)
      paj_run_tok RUN HS HJ3 SHOK4 RFspan.
      { awr_ok_tac. exact Usp3. }
      lazymatch goal with Hfr : frame_of _ _ (mrestrict (w_H W3) mem3) (mrestrict _ ?m1) |- _ =>
      assert (K3 : rf_kept (rdW W3 mem3) (rdW W3 m1) (spZ regs - 16) (spZ regs))
      by (intros a Ha Hn; apply (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun a => spZ regs - 16 <= a < spZ regs) Hfr);
        [ intros bq wlo whi a' Hin Hrr; vm_compute in Hin;
          repeat (destruct Hin as [Hq0 | Hin]; [injection Hq0 as <- <- <-; cbn [base_val] in Hrr; rewrite ?Usp3 in Hrr; lia|]);
          destruct Hin
        | exact Ha | exact Hn ]) end.
      clear HF HFr HG.
      prreg HS (1%bv : bv 5) F1. prreg HS (10%bv : bv 5) F10.
      eapply (RET W3 _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
      intros mat'. unfold apost_base.
      lazymatch goal with |- exists _ _ _ _ _, mkCfg (mkst ?r _ ?m _) ?d = _ /\ _ => exists ly, S3, r, m, d end.
      split; [rewrite F1, OLD3, E1 by lia; unfold YK0s.ret_ok in Hra; rewrite Hra; reflexivity|].
      split; [apply (ajournal_materialize SEGS B LAWS Hsegs); exact HJ3|].
      split; [eapply (aregs_preserved_of_st_ok SEGS _ _ _ _ regs (rf_extra b0) HS); [exact HAE3 | vm_compute; reflexivity]|].
      split; [|split; [exact (rf_kept_final W W3 mem (ms_mem ms) mem3 _ regs (ms_regs ms) KEEP HKF HspT K3) | exact HNA]].
      rewrite F10. unfold r_role_file. rewrite RF, RSET. reflexivity.
- (* find returned 0 *)
  psrr_branch_tok RUN BR HS SHOK3 RFspan.
  + clear Hc. paj_run_tok RUN HS HJ3 SHOK3 RFspan.
    { awr_ok_tac. exact Usp3. }
    lazymatch goal with Hfr : frame_of _ _ (mrestrict (w_H W3) mem3) (mrestrict _ ?m1) |- _ =>
    assert (K3 : rf_kept (rdW W3 mem3) (rdW W3 m1) (spZ regs - 16) (spZ regs))
    by (intros a Ha Hn; apply (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun a => spZ regs - 16 <= a < spZ regs) Hfr);
      [ intros bq wlo whi a' Hin Hrr; vm_compute in Hin;
        repeat (destruct Hin as [Hq0 | Hin]; [injection Hq0 as <- <- <-; cbn [base_val] in Hrr; rewrite ?Usp3 in Hrr; lia|]);
        destruct Hin
      | exact Ha | exact Hn ]) end.
    clear HF HFr HG.
    prreg HS (1%bv : bv 5) F1. prreg HS (10%bv : bv 5) F10.
    eapply (RET W3 _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
    intros mat'. unfold apost_base.
    lazymatch goal with |- exists _ _ _ _ _, mkCfg (mkst ?r _ ?m _) ?d = _ /\ _ => exists ly, S3, r, m, d end.
    split; [rewrite F1, OLD3, E1 by lia; unfold YK0s.ret_ok in Hra; rewrite Hra; reflexivity|].
    split; [apply (ajournal_materialize SEGS B LAWS Hsegs); exact HJ3|].
    split; [eapply (aregs_preserved_of_st_ok SEGS _ _ _ _ regs (rf_extra b0) HS); [exact HAE3 | vm_compute; reflexivity]|].
    split; [|split; [exact (rf_kept_final W W3 mem (ms_mem ms) mem3 _ regs (ms_regs ms) KEEP HKF HspT K3) | exact HNA]].
    rewrite F10, A44, HA0. reflexivity.
  + exfalso. rewrite branch_eq_U, U_SLit in Hc. rewrite (U_atom Ec 44 0) in Hc; [discriminate Hc | | split; lia].
    rewrite A44, HA0. reflexivity.
Qed.

End w.
End e.
End f.
End d.

Print Assumptions reac_segconf_role_file_walk.
About reac_segconf_role_file_walk.
