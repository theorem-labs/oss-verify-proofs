(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the ASan walk of fuzz_reply's check_shape_ends, in the form of the cgif walks of
   proofs/cgif/cgif_file_fuzzer/lib/A/AC8h.v (free sites), lib/A/AC8b.v (a counted loop) and lib/A/ACh2.v (an
   internal call to another program function). *)
(* check_shape_ends(s, prefix, at) at 0x853b0 is the harness's shape oracle for the gesture ends of one source.
   It counts, in `want`, the held gestures whose text has the prefix (loop 1, has_prefix per record); then
   - g_gone <> 0: it drops every held record with the prefix, from the last index down (loop 2: has_prefix,
     then the inlined list_drop = free(v[i].s) + __asan_memmove of the records above + n--), and returns with
     *at unchanged;
   - g_gone = 0: it reads `want` lines off the controller's stream (loop 3: next_line, a length check and a
     bcmp of the line's last four bytes against " end", list_find of the line's stem in the held list, and
     has_prefix of the line), dropping the found record each time, and leaves *at = A0 + c.
   Every abort arm (0x856cc, and the __asan_report_* arms) is refuted from the functional half, which is the
   plain contract lib/Prog/check_shape_ends_c.v:26-87 re-expressed over W_rep's asrc_at: with
   W = want_of P (hl_recs H),
     gone <> 0 -> hl_recs H' = filter (negb o prefixb P) (hl_recs H), ds = filter (prefixb P) (hl_recs H), c = 0;
     gone  = 0 -> ends_run P (hl_recs H) (skipn A0 ob) W = Some (hl_recs H', ds, c),
   and the plain pre `gone = 0 -> ends_run ... <> None`.  The pure models (prefixb, want_of, ends_run,
   find_text, drop_nth, END4, split_nul) are the plain proof's, from lib/Prog/CheckRep.v, unchanged.
   THE WALK IS GENERIC over the allocator relation ARx (route (b), step 3; CONVERSION.md (sha256 1015972e02a9; internal record), on the
   check_bounded template a working branch lib/A/W_check_bounded.v): every lemma whose statement names the
   allocator (ARx, ajournal_gx_x, afn_pre_x) is the _x lemma of Section c.  Section c's header is the interface of
   W_cshe_l2w.v and W_cshe_l3.v; W_cshe_top.v composes pb_check_shape_ends_x : cshe_spec_x and re-derives the AR
   statement pb_check_shape_ends at ARx := ARi0, PST := [].  Section hypotheses, and the lane that owes each:
     LAWS   : AR_laws_x SEGS B ARx hl                         (the allocator instance; YCbqG.v's laws record)
     HP0    : no hidden head in any ARx state                 (a Theorem Labs lane's ruling; W_journal_x's *_of_block_hp0_x)
     IMGC, BLKN : ly_img covers the image's band; a live block's size is >= 0 (W_kit_x.v Section g)
     HPST   : no image byte lies in PST                        (the generic journal's image clause; true at PST = [])
     FRMF   : the fake-frame alignment                          (W_frame_x.v Section q)
     ML     : ameter_laws MT                                  (the allocator instance)
     HG     : gx_ok SEGS B G                                  (this lane's G, W2's gx_ok)
     TL     : PALib B                                         (the allocator instance)
     ASTRLEN: astrlen_realizes_x B ARx (SIGMA WS_strlen)       (runtime lane R1; W_contract_x.v)
     ABCMP  : abcmp_realizes_x SEGS B ARx (SIGMA WS_bcmp)      (runtime lane R2; W_sites_x.v)
     AMOVE  : amemmove_realizes_x B ARx (SIGMA WS_asan_memmove) (runtime lane R3; W_sites_x.v)
     AFREE  : afree_cf_rule_c_x SEGS B PST ARx MT RP CTX_AFREE (the allocator instance; W_journal_x.v Section hc)
     NL     : nl_spec_x B PST ARx (BASE + AF_fr_next_line)     (lane W1)
     LFIND  : lfind_spec_x B PST ARx G (BASE + AF_fr_list_find) (lane W1)
     ALDROP : alist_at_drop (W1's lib/A/W_list_drop.v, verbatim; a representation lemma, not a contract)
     PLACEG0, PLACEG32 : g_gone, the GOT slot A_OBJ 0 and the shadow cell A_OBJ 32 are distinct objects
       (the placement, W_img.v; PAImg has no object-disjointness field and the entry state holds all three)
     HGR, HGRR : gx_ok / gx_rt of cshe_ro (g_gone, g_nout, g_out, g_s): the instance's statics at PB_fr
     ROMNS  : read-only bytes are not errno and are rom_pinned when owned (W_journal.v rom_out's form)
     HEND5R : " end\0" (0x20f00, loop 3's bcmp operand) is read-only (gesture_end's texts; the placement at PB_fr);
       its in_img follows (in_rom -> in_img, same segment witness)
     HEND5S : " end"'s shadow is a const cell of the instance (ashp_x; a partial granule, shadow byte 5, not zero)
     HGS    : g_s (A_OBJ 22) is writable image .bss, apart from g_gone / g_nout / g_out (the placement, W_img.v)
   has_prefix is PROVED, not assumed: W_has_prefix.pb_has_prefix_x B PST ARx LAWS ASTRLEN ABCMP. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0d YP0c YC80 YC81 YO0a YN1e.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YI00 YC5d.
(* YN0d: st_ok_chunk / chunk_bytes_cval, the readout of a region's chunk from a symbolic state (the frame's
   saved slots and the cells the walk stored).  Require only, no Import. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YN0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import HarnessRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require CheckRep RelayModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
W_syms W_listing W_pl W_kit W_journal W_rep W_contract W_sites W_frame.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require W_has_prefix.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_kit_x W_journal_x W_contract_x W_sites_x.
(* W_frame_x (frame_al64_x, shadow_hull_vis_of_frame_x) and YCe5x (amem_range_of_block_x): Require only. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require W_frame_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YCe5x.
(* YN2e: word_to_le_bytes_nth, for reading a record's two words out of the vector's bytes.  Require only. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YN2e.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YA0nH.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_contract_xR_g6.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg fr_prog_listing}.
#[local] Notation SEGS := (@pa_segs _ fr_prog_listing PI).
#[local] Notation VAL := (@pa_val _ fr_prog_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ fr_prog_listing PI).
#[local] Notation BASE := (@pa_val _ fr_prog_listing PI A_TEXT).

(* the function and its three loop heads, as offsets of the listing *)
Definition A_cshe : Z := AF_fr_check_shape_ends.
Definition A_csheP : Z := BASE + A_cshe.
Definition A_cshe_l1 : Z := AF_fr_check_shape_ends + 0xa0.    (* 0x85450, the counting loop *)
Definition A_cshe_l2 : Z := AF_fr_check_shape_ends + 0x114.   (* 0x854c4, the gone loop *)
Definition A_cshe_l3 : Z := AF_fr_check_shape_ends + 0x1ec.   (* 0x8559c, the `while (want-- > 0)` loop *)
Definition A_cshe_tst : Z := AF_fr_check_shape_ends + 0xe4.   (* 0x85494, the loop-1 test *)
Definition A_cshe_ret : Z := AF_fr_check_shape_ends + 0x2e0.  (* 0x85690, the epilogue *)

Section c.
Variable B : asyms.
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Variable MT : ameter_ops.
(* the room round (ROOM-TEXTS.md v3 sha256 767baa12f13c; internal record): cshe_spec_x's room record; check_shape_ends only frees (cshe_pk = 0), so the
   loops carry the room budget (one free per record left) and the live counts, which only fall *)
Variable RP : roomp.
Variable G : list (Z * Z).

(* ------------------------------------------------------------------ the contract *)
(* check_shape_ends' contract (CSHE_FRAME, CSHE_STK, cshe_home, cshe_ds_blks, cshe_cost, cshe_post, cshe_spec) lives
   in W_contract.v Section w3e, so mkbkit.py (sha256 999741ae2b33; internal record) twins it into lib/B (B's measured frame and stack bound come
   in as the cfg's b_facts); its generic twin (cshe_post_x, cshe_spec_x) in W_contract_x.v Section w3e.  Inside this
   Section its B, PST, ARx, MT, RP and G are this Section's. *)
Local Notation cshe_home := (cshe_home B).
Local Notation cshe_cost := (cshe_cost MT).
Local Notation cshe_post_x := (cshe_post_x B PST ARx MT RP G).
Local Notation cshe_spec_x := (cshe_spec_x B PST ARx MT RP G).

(* ------------------------------------------------------------------ the walk *)
(* THE GENERIC WALK (route (b), step 3; CONVERSION.md (sha256 1015972e02a9; internal record)): check_shape_ends over any allocator relation ARx
   with its laws.  This header is the interface of W_cshe_l2w.v and W_cshe_l3.v (their Sections mirror it).  Beyond the
   AR walk's: PST / ARx / hl / LAWS (the generic relation and its laws AR_laws_x); HP0 (no hidden head in any ARx state:
   a Theorem Labs lane's ruling, for W_journal_x's range_addressable_of_block_hp0_x / shadow_hull_vis_of_block_hp0_x); IMGC /
   BLKN (W_kit_x.v Section g, for blk_off_imgP_x; BLKN is also the size bound cgif's al_blocks carried); HPST (no image
   byte lies in PST: the generic journal's image clause keeps a byte only outside PST; it holds at PST = []); FRMF
   (W_frame_x.v Section q, the fake-frame alignment frame_al64_x / shadow_hull_vis_of_frame_x read).  The callees are
   their generic twins; the free rule is the caller-context form (W_journal_x Section hc, one CTX per allocator entry:
   a Theorem Labs lane 21:20Z), whose site facts live in the loop files that call free. *)
Context {hl : Z}.
Hypothesis LAWS : AR_laws_x SEGS B ARx hl.
Hypothesis HP0 : forall ly S Hp W mem md, ARx ly S Hp W mem md -> Hp = [].
Hypothesis IMGC : forall ly S Hp W mem md, ARx ly S Hp W mem md ->
fst (ly_img ly) <= 0x10000 /\ 0x5fb000 <= fst (ly_img ly) + snd (ly_img ly).
Hypothesis BLKN : forall ly S Hp W mem md p n, ARx ly S Hp W mem md -> In (p, n) (ablocks B ly S) -> 0 <= n.
Hypothesis HPST : forall a, in_img SEGS a -> ~ Exists (in_zr a) PST.
Hypothesis FRMF : forall ly S Hp W mem md cid pos, ARx ly S Hp W mem md -> In (cid, pos) (frames S) ->
ly_F ly mod 4096 = 0 /\ fs_frame_off cid pos mod 64 = 0 /\ 64 <= fs_frame_bytes cid /\ fs_frame_bytes cid mod 64 = 0.
Hypothesis ML : ameter_laws MT.
Hypothesis HG : gx_ok SEGS B G.
Hypothesis TL : PALib B.
Hypothesis ASTRLEN : astrlen_realizes_x B ARx (SIGMA WS_strlen).
Hypothesis ABCMP : abcmp_realizes_x SEGS B ARx (SIGMA WS_bcmp).
Hypothesis AMOVE : amemmove_realizes_x B ARx (SIGMA WS_asan_memmove).
Variable CTX_AFREE : list (list Z).
Hypothesis AFREE : afree_cf_rule_c_x SEGS B PST ARx MT RP CTX_AFREE.
Hypothesis NL : nl_spec_x B PST ARx (BASE + AF_fr_next_line).
Hypothesis LFIND : lfind_spec_x B PST ARx G (BASE + AF_fr_list_find).
(* W1's lib/A/W_list_drop.v, verbatim: the representation step of one inlined list_drop. *)
Hypothesis ALDROP : forall ly S W mem ly' S' W' mem' LA l lines i,
alist_at B ly S W mem LA l lines ->
(i < length (HarnessRep.hl_recs l))%nat ->
(exists b1 b2, ablocks B ly S = b1 ++ (fst (nth i (HarnessRep.hl_recs l) (0, [])),
   Z.of_nat (length (snd (nth i (HarnessRep.hl_recs l) (0, [])))) + 1) :: b2 /\ ablocks B ly' S' = b1 ++ b2) ->
(forall a, LA <= a < LA + 8 \/ LA + 12 <= a < LA + 16 -> aview SEGS (w_H W') mem' a = aview SEGS (w_H W) mem a) ->
awr W' mem' LA 16 ->
val_mem SEGS (arm W' mem') (LA + 8) 4 (HarnessRep.hl_n l - 1) ->
(forall k, 0 <= k < AREC * (HarnessRep.hl_n l - 1 - Z.of_nat i) ->
 aview SEGS (w_H W') mem' (HarnessRep.hl_v l + AREC * Z.of_nat i + k) =
 aview SEGS (w_H W) mem (HarnessRep.hl_v l + AREC * Z.of_nat i + AREC + k)) ->
(forall a, HarnessRep.hl_v l <= a < HarnessRep.hl_v l + AREC * Z.of_nat i \/
 HarnessRep.hl_v l + AREC * (HarnessRep.hl_n l - 1) <= a < HarnessRep.hl_v l + AREC * HarnessRep.hl_cap l ->
 aview SEGS (w_H W') mem' a = aview SEGS (w_H W) mem a) ->
(forall r, In r (HarnessRep.hl_recs (ldrop_list l i)) -> forall a, fst r <= a < fst r + Z.of_nat (length (snd r)) + 1 ->
 aview SEGS (w_H W') mem' a = aview SEGS (w_H W) mem a) ->
alist_at B ly' S' W' mem' LA (ldrop_list l i) lines.
(* the placement facts the walk needs of its three image objects (A_OBJ 30 = g_gone, A_OBJ 0 = the GOT slot of
   the shadow cell, A_OBJ 32 = the shadow cell): they are distinct objects.  Owed by the placement, W_img.v. *)
Hypothesis PLACEG0 : VAL A_g_gone + 1 <= VAL (A_OBJ 0) \/ VAL (A_OBJ 0) + 8 <= VAL A_g_gone.
Hypothesis PLACEG32 : VAL A_g_gone + 1 <= VAL (A_OBJ 32) \/ VAL (A_OBJ 32) + 8 <= VAL A_g_gone.
(* The image objects the walk keeps unchanged across the inlined frees and reads: no allocator static (gx_ok), not
   errno or the runtime's two static cells (gx_rt), discharged over the instance's statics at PB_fr; and the
   read-only bytes, rom_pinned when owned (as check_no_loss's ROMNS, W_journal.v rom_out). *)
Definition cshe_ro : list (Z * Z) :=
[(VAL A_g_gone, 1); (VAL A_g_nout, 8); (VAL A_g_out, 8); (VAL (A_OBJ 22), 384)].  (* A_OBJ 22 = g_s, 0x5d88e0 *)
Hypothesis HGR : gx_ok SEGS B cshe_ro.
Hypothesis HGRR : gx_rt B cshe_ro.
Hypothesis ROMNS : forall a, in_rom SEGS a -> ~ (as_errno B <= a < as_errno B + 4) /\
  (Exists (in_zr a) (as_owned_static B) -> rom_pinned SEGS B a).
(* " end\0" (loop 3's bcmp operand) is read-only, so ROMNS + rom_view keep it across each turn's free (gesture_end's
   HEND5R; at PB_fr: W_img_w4.v end5_in_rom_PB); its in_img follows (in_rom -> in_img, same segment witness).  Its
   shadow is a const cell of the instance, so the shadow facts of its 4 compared bytes hold in every allocator
   state (ashp_x, W_contract_x.v's twin of W_shadow_pin.v ashp; AF0m Tfib_const_shadow: 0x20f00's shadow byte is 5). *)
Hypothesis HEND5R : forall a, VAL A_lit_end5 <= a < VAL A_lit_end5 + 5 -> in_rom SEGS a.
Hypothesis HEND5S : ashp_x ARx (VAL A_lit_end5) 4.
(* g_s (A_OBJ 22, 0x5d88e0) is writable image .bss apart from g_gone / g_nout / g_out (placement at PB_fr) *)
Hypothesis HGS : forall a, VAL (A_OBJ 22) <= a < VAL (A_OBJ 22) + 384 -> in_img SEGS a /\ ~ in_rom SEGS a /\
  ~ (VAL A_g_gone <= a < VAL A_g_gone + 1) /\ ~ (VAL A_g_nout <= a < VAL A_g_nout + 8) /\
  ~ (VAL A_g_out <= a < VAL A_g_out + 8).
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL.
Let RUN := paj_run_x_x B PST ARx LAWS G HG.
Let RUNTO := paj_run_to_x_x B PST ARx LAWS G HG.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_fr) (PI := PI).

(* atoms above 31: 32 g_gone, 33 the shadow base, 34 the held vector, 35 its count, 36 its capacity *)
Definition Bx : sv := SOff 33 0.
Definition cshe_hd : YP09.region := YP09.mkRegion (Some 10%nat) 0 96 88 92
[YP09.mkChunk 80 (CVal 8 (SOff 34 0)); YP09.mkChunk 88 (CVal 4 (SOff 35 0)); YP09.mkChunk 92 (CVal 4 (SOff 36 0))].
Definition cshe_gone : YP09.region := YP09.mkRegion (Some A_g_gone) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 32 0))].
Definition cshe_regions : smem :=
[ stack_region CSHE_FRAME; got_regionP; bcell_regionP 33; cshe_hd; cshe_gone ].
Definition cshe_facts : facts :=
mkFacts [ (2%nat, mkAF (2^46) (2^47) 4); (10%nat, mkAF 4096 140737479966720 3);
(32%nat, mkAF 0 255 0); (33%nat, mkAF SB SB 0); (34%nat, mkAF 0 140737479966720 4);
(35%nat, mkAF 0 (2 ^ 26) 0); (36%nat, mkAF 0 (2 ^ 30) 0) ] [] [].
Definition ss_cshe : sstate := mkSS A_cshe sr_atoms cshe_regions None cshe_facts.
Definition cshe_SH : list shent := [ mkSHE 10 64 96 ].
Definition Bspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
Definition cshe_extra (gone V N CAP : Z) : list word := map (Z_to_bv 64) [gone; SB; V; N; CAP].

Lemma cshe_entry_x : forall W ly S hp regs mem md ch HA gone V N CAP,
afn_pre_x SEGS B ARx CSHE_STK ly S hp W regs mem md ch ->
getr regs 10 = w64 HA -> HA mod 8 = 0 -> 4096 <= HA -> HA + ASRC <= 0x5fb000 -> azs B (HA + 64) 32 ->
(HA + ASRC <= VAL (A_OBJ 0) \/ VAL (A_OBJ 0) + 8 <= HA) ->
(HA + ASRC <= VAL (A_OBJ 32) \/ VAL (A_OBJ 32) + 8 <= HA) ->
(HA + ASRC <= VAL A_g_gone \/ VAL A_g_gone + 1 <= HA) ->
val_mem SEGS (mrestrict (w_H W) mem) (VAL A_g_gone) 1 gone -> 0 <= gone < 256 ->
val_mem SEGS (mrestrict (w_H W) mem) (HA + 80) 8 V -> 0 <= V < 140737479966720 -> V mod 16 = 0 ->
val_mem SEGS (mrestrict (w_H W) mem) (HA + 88) 4 N -> 0 <= N < 2 ^ 26 ->
val_mem SEGS (mrestrict (w_H W) mem) (HA + 92) 4 CAP -> 0 <= CAP < 2 ^ 30 ->
awr W mem (HA + 80) 16 ->
st_ok_pi SEGS VAL (Eimg (Ereg regs (cshe_extra gone V N CAP))) ss_cshe
(restrict (w_H W) (mkst regs (Z_to_bv 64 A_csheP) mem (seg_rom SEGS)))
/\ sh_ok SEGS Bx cshe_SH (Eimg (Ereg regs (cshe_extra gone V N CAP))) (mrestrict (w_H W) mem).
Proof.
intros W ly S hp regs mem md ch HA gone V N CAP HPRE H10 Hal8 Hlo Hhi Hzs Hd0 Hd32 Hdg Mg Rg MV RV AV MN RN MC RC Hawr.
unfold ASRC in Hhi, Hd0, Hd32, Hdg.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : CSHE_STK = 16528) by reflexivity.
destruct (alx_const _ _ _ LAWS ly S hp W mem md HAR) as (Kcell & _ & Kgot & _).
rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell.
rewrite restrict_mkst_fx.
set (E := Eimg (Ereg regs (cshe_extra gone V N CAP))). pose proof pa_B_ok as HBASE.
assert (E2 : ew E 2 = getr regs 2) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 HA) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E32 : ew E 32 = Z_to_bv 64 gone) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 SB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 V) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 N) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 3)).
assert (E36 : ew E 36 = Z_to_bv 64 CAP) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 4)).
assert (E241 : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E273 : ew E (A_OBJ 32) = Z_to_bv 64 (VAL (A_OBJ 32))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Eg : ew E A_g_gone = Z_to_bv 64 (VAL A_g_gone)) by (subst E; apply Eimg_img; unfold A_g_gone, A_OBJ, A_TEXT, A_LIM; lia).
pose proof (pa_obj_img 32 ltac:(lia)) as HcellR. pose proof (pal_got_cell B TL) as HgcD. pose proof (pa_obj_img 0 ltac:(lia)) as HgotR.
pose proof (pa_obj_img 30 ltac:(lia)) as HgR. change (A_OBJ 30) with A_g_gone in HgR.
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (VB : forall m w, ew E m = Z_to_bv 64 w -> 0 <= w < 2 ^ 64 -> base_val E (Some m) = w).
{ intros m w Hm Hw. cbn [base_val]. rewrite Hm. apply unsigned_lit_small. exact Hw. }
split.
- unfold ss_cshe, A_csheP. apply pa_entry_st_ok_full.
+ apply regs_ok_Eimg_Ereg.
+ vm_compute. reflexivity.
+ unfold cshe_regions, stack_region, got_regionP, bcell_regionP, cshe_hd, cshe_gone.
repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
* cbn [base_val]. rewrite Usp. split; [unfold CSHE_FRAME; lia|]. split; [unfold CSHE_FRAME; lia|].
split; [|constructor]. intros o Ho. apply (apresent_writable SEGS). apply Hpres. unfold CSHE_FRAME in *. lia.
* rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E241) by (pose proof (pa_val_range (A_OBJ 0)); lia).
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 32) 0) (VAL (A_OBJ 32)));
[cbn [sv_denot]; rewrite E273, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
| pose proof (pa_val_range (A_OBJ 32)); zside | zside |].
rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kgot).
* rewrite (VB (A_OBJ 32) (VAL (A_OBJ 32)) E273) by (pose proof (pa_val_range (A_OBJ 32)); lia).
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 32)) 0 8 Bx SB);
[cbn [sv_denot Bx]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB; zside | zside |].
rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kcell).
* rewrite (VB 10%nat HA E10) by lia. unfold ASRC in *.
split; [lia|]. split; [lia|].
split; [intros o Ho; unfold arm in Hawr; replace (HA + o) with (HA + 80 + (o - 80)) by lia; apply Hawr; lia|].
repeat (constructor; [|]); [| | |constructor].
-- apply (chunk_ok_val SEGS E _ HA 80 8 _ V);
[cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact MV].
-- apply (chunk_ok_val SEGS E _ HA 88 4 _ N);
[cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact MN].
-- apply (chunk_ok_val SEGS E _ HA 92 4 _ CAP);
[cbn [sv_denot]; rewrite E36, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact MC].
* rewrite (VB A_g_gone (VAL A_g_gone) Eg) by (pose proof (pa_val_range A_g_gone); lia).
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (VAL A_g_gone) 0 1 (SOff 32 0) gone);
[cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia |].
rewrite Z.add_0_r. exact Mg.
+ apply pairwise_disjoint_of_extents.
unfold cshe_regions, stack_region, got_regionP, bcell_regionP, cshe_hd, cshe_gone, extent_of_region.
cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. rewrite (VB 10%nat HA E10) by lia.
rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E241) by (pose proof (pa_val_range (A_OBJ 0)); lia).
rewrite (VB (A_OBJ 32) (VAL (A_OBJ 32)) E273) by (pose proof (pa_val_range (A_OBJ 32)); lia).
rewrite (VB A_g_gone (VAL A_g_gone) Eg) by (pose proof (pa_val_range A_g_gone); lia).
cbn [base_val]. rewrite Usp. unfold ASRC in *.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
revert Hslo Hshi H47 Hceil Hlo Hhi Hd0 Hd32 Hdg C1 C3 WS Hstk0 HcellR HgcD HgotR HgR PLACEG0 PLACEG32. clear.
unfold zone2, off_img, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, CSHE_FRAME. intros. repeat split; lia.
+ split; [|split; [exact I | exact I]].
cbn [cshe_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite Usp, E10, E32, E33, E34, E35, E36, !unsigned_lit_small by (unfold SB; lia).
change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
revert Hslo Hshi H47 Hceil Hlo Hhi Hal8 Hal16 C1 C3 WS Hstk0 Rg RV AV RN RC. clear.
unfold SB, zone2, off_img, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL. intros.
repeat match goal with |- _ /\ _ => split end; lia.
- unfold sh_ok, cshe_SH. constructor; [|constructor].
assert (UBx : U E Bx = SHADOW_OFF).
{ unfold U, Bx. cbn [sv_denot]. rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity. }
assert (Up : U E (SOff 10 0) = HA).
{ unfold U. cbn [sv_denot]. rewrite E10, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by lia. reflexivity. }
split; cbn [she_m she_lo she_hi].
+ rewrite UBx, Up. replace (96 - 64) with 32 by lia.
  exact (azs_range_addressable_x B ARx LAWS ly S hp W mem md (HA + 64) 32 HAR Hzs).
+ unfold app_apart. cbn [she_m she_lo she_hi]. rewrite UBx, Up. unfold SHADOW_OFF, ASRC in *. intros a Ha. lia.
Qed.

(* ------------------------------------------------------------------ the epilogue (0x85690) *)
(* The thirteen cells the prologue wrote: ra at sp0 - 8, then s0 .. s11 down to sp0 - 104. *)
Definition cshe_saved (W : world SEGS) (mem : word -> option byte) (sp0 : Z) (rs : bvmap 5 word) : Prop :=
val_mem SEGS (mrestrict (w_H W) mem) (sp0 - 8) 8 (bv_unsigned (getr rs 1)) /\
val_mem SEGS (mrestrict (w_H W) mem) (sp0 - 16) 8 (bv_unsigned (getr rs 8)) /\
val_mem SEGS (mrestrict (w_H W) mem) (sp0 - 24) 8 (bv_unsigned (getr rs 9)) /\
val_mem SEGS (mrestrict (w_H W) mem) (sp0 - 32) 8 (bv_unsigned (getr rs 18)) /\
val_mem SEGS (mrestrict (w_H W) mem) (sp0 - 40) 8 (bv_unsigned (getr rs 19)) /\
val_mem SEGS (mrestrict (w_H W) mem) (sp0 - 48) 8 (bv_unsigned (getr rs 20)) /\
val_mem SEGS (mrestrict (w_H W) mem) (sp0 - 56) 8 (bv_unsigned (getr rs 21)) /\
val_mem SEGS (mrestrict (w_H W) mem) (sp0 - 64) 8 (bv_unsigned (getr rs 22)) /\
val_mem SEGS (mrestrict (w_H W) mem) (sp0 - 72) 8 (bv_unsigned (getr rs 23)) /\
val_mem SEGS (mrestrict (w_H W) mem) (sp0 - 80) 8 (bv_unsigned (getr rs 24)) /\
val_mem SEGS (mrestrict (w_H W) mem) (sp0 - 88) 8 (bv_unsigned (getr rs 25)) /\
val_mem SEGS (mrestrict (w_H W) mem) (sp0 - 96) 8 (bv_unsigned (getr rs 26)) /\
val_mem SEGS (mrestrict (w_H W) mem) (sp0 - 104) 8 (bv_unsigned (getr rs 27)).
(* atoms 32 ra, 33 the shadow base (Bx), 34 .. 45 the saved s0 .. s11 *)
Definition cshe_svextra (rs : bvmap 5 word) : list word :=
[getr rs 1; Z_to_bv 64 SB; getr rs 8; getr rs 9; getr rs 18; getr rs 19; getr rs 20; getr rs 21;
 getr rs 22; getr rs 23; getr rs 24; getr rs 25; getr rs 26; getr rs 27].
Definition cshe_frmR : YP09.region := YP09.mkRegion (Some 2%nat) 0 144 0 0
[YP09.mkChunk 40 (CVal 8 (SOff 45 0)); YP09.mkChunk 48 (CVal 8 (SOff 44 0));
 YP09.mkChunk 56 (CVal 8 (SOff 43 0)); YP09.mkChunk 64 (CVal 8 (SOff 42 0));
 YP09.mkChunk 72 (CVal 8 (SOff 41 0)); YP09.mkChunk 80 (CVal 8 (SOff 40 0));
 YP09.mkChunk 88 (CVal 8 (SOff 39 0)); YP09.mkChunk 96 (CVal 8 (SOff 38 0));
 YP09.mkChunk 104 (CVal 8 (SOff 37 0)); YP09.mkChunk 112 (CVal 8 (SOff 36 0));
 YP09.mkChunk 120 (CVal 8 (SOff 35 0)); YP09.mkChunk 128 (CVal 8 (SOff 34 0));
 YP09.mkChunk 136 (CVal 8 (SOff 32 0))].
Definition cshe_efacts : facts := mkFacts [ (2%nat, mkAF (2^46) (2^47) 4); (33%nat, mkAF SB SB 0) ] [] [].
Definition ss_cshe_ret : sstate := mkSS A_cshe_ret sr_atoms [ cshe_frmR ] None cshe_efacts.
(* a saved register's value is a 64-bit number, the chunk_ok side goal *)
Ltac cshe_v64 w :=
let H := fresh "Hbr" in pose proof (bv_unsigned_in_range 64 w) as H;
change (bv_modulus 64) with (2 ^ 64) in H; zside.

(* Two memories that agree at a byte keep its view, its writability and its presence (W_check_no_loss.v
   abyte_kept_meq, copied: that file's lemmas are inside its own Section). *)
Lemma cshe_byte_meq : forall (W1 : world SEGS) m m' a,
mrestrict (w_H W1) m' (Z_to_bv 64 a) = mrestrict (w_H W1) m (Z_to_bv 64 a) -> abyte_kept W1 m W1 m' a.
Proof.
intros W1 m m' a Hq. split.
- unfold aview, mbyte. rewrite Hq. reflexivity.
- unfold writable_at, wview, arm. rewrite Hq. exact (fun H => H).
Qed.
Lemma cshe_apres_meq : forall (W1 : world SEGS) m m' a,
mrestrict (w_H W1) m' (Z_to_bv 64 a) = mrestrict (w_H W1) m (Z_to_bv 64 a) ->
apresent (w_H W1) m a -> apresent (w_H W1) m' a.
Proof.
intros W1 m m' a Hq (Hh & b & Hb). unfold mrestrict in Hq. rewrite Hh in Hq.
split; [exact Hh|]. exists b. rewrite Hq. exact Hb.
Qed.
(* Two states that hold the same value over the same range show the same bytes there: how the walk's own store
   of held.n (the one byte range cshe_head_x leaves out of its frame clause) is carried. *)
Lemma cshe_aview_of_val : forall (W1 W2 : world SEGS) m1 m2 a n v,
val_mem SEGS (mrestrict (w_H W1) m1) a n v -> val_mem SEGS (mrestrict (w_H W2) m2) a n v ->
forall t, 0 <= t < Z.of_nat n -> aview SEGS (w_H W2) m2 (a + t) = aview SEGS (w_H W1) m1 (a + t).
Proof.
intros W1 W2 m1 m2 a n v H1 H2 t Ht.
replace (a + t) with (a + Z.of_nat (Z.to_nat t)) by lia.
unfold aview. rewrite (H1 (Z.to_nat t) ltac:(lia)), (H2 (Z.to_nat t) ltac:(lia)). reflexivity.
Qed.


(* ------------------------------------------------------------------ loop 1, the counting loop (0x85450) *)
(* At the head: s4 (x20) = v + 16 i, s11 (x27) = v + 16 i + 8, s7 (x23) = SB + (v + 16 i) / 8 (the shadow
   byte of the record's first word, carried and bumped by 2 each turn), s6 (x22) = n - i, a1 (x11) = the
   count so far, s1 (x9) = the prefix, s9 (x25) = SB.  The two shadow checks are of the 16 bytes of the
   record, which lie in the vector's block. *)
Definition cshe_elt : YP09.region := YP09.mkRegion (Some 20%nat) 0 16 0 0
[YP09.mkChunk 0 (CVal 8 (SOff 34 0)); YP09.mkChunk 8 (CVal 8 (SOff 35 0))].
(* the shadow base the loop uses is the program's own s9 (x25), so the token engine's Bx is its atom *)
Definition Bx1 : sv := SOff 25 0.
Definition cshe_l1_sr : list sv := sr_set (sr_set sr_atoms 23%bv (SAlu ALU_ADD (SOff 25 0) (SAlu ALU_SRL (SOff 20 0) (SLit 3))))
27%bv (SOff 20 8).
Definition cshe_l1_facts : facts :=
mkFacts [ (2%nat, mkAF (2^46) (2^47) 4); (20%nat, mkAF 4096 140737479966720 4); (25%nat, mkAF SB SB 0);
(34%nat, mkAF 0 140737479966720 0); (35%nat, mkAF 0 (2 ^ 26) 0); (11%nat, mkAF 0 (2 ^ 26) 0);
(22%nat, mkAF 0 (2 ^ 26) 0) ] [] [].
Definition ss_cshe_l1 : sstate := mkSS A_cshe_l1 cshe_l1_sr [ cshe_elt ] None cshe_l1_facts.
Definition cshe_l1_SH : list shent := [ mkSHE 20 0 16 ].
Definition cshe_l1_extra (s n : Z) : list word := map (Z_to_bv 64) [0; SB; s; n].

Lemma cshe_l1_state : forall (W : world SEGS) regs mem EA s n SP WANT CNT,
getr regs 2 = w64 SP -> getr regs 11 = w64 WANT -> getr regs 22 = w64 CNT ->
getr regs 20 = w64 EA -> getr regs 27 = w64 (EA + 8) -> getr regs 23 = w64 (SB + EA / 8) ->
getr regs 25 = w64 SB ->
2 ^ 46 <= SP <= 2 ^ 47 -> SP mod 16 = 0 -> 0 <= WANT < 2 ^ 26 -> 0 <= CNT < 2 ^ 26 ->
4096 <= EA -> EA + 16 <= 140737479966720 -> EA mod 16 = 0 ->
0 <= s < 140737479966720 -> 0 <= n < 2 ^ 26 ->
val_mem SEGS (mrestrict (w_H W) mem) EA 8 s -> val_mem SEGS (mrestrict (w_H W) mem) (EA + 8) 8 n ->
st_ok_pi SEGS VAL (Eimg (Ereg regs (cshe_l1_extra s n))) ss_cshe_l1
(restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + A_cshe_l1)) mem (seg_rom SEGS))).
Proof.
intros W regs mem EA s n SP WANT CNT H2 H11 H22 H20 H27 H23 H25 HSP HSPa HW HC Hlo Hhi Hal Hs Hn Ms Mn.
pose proof pa_B_ok as HBASE.
set (E := Eimg (Ereg regs (cshe_l1_extra s n))).
assert (E20 : ew E 20 = Z_to_bv 64 EA)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 20 20%bv eq_refl); exact H20).
assert (E33 : ew E 33 = Z_to_bv 64 SB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E25 : ew E 25 = Z_to_bv 64 SB)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 25 25%bv eq_refl); exact H25).
assert (E34 : ew E 34 = Z_to_bv 64 s) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 n) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 3)).
rewrite restrict_mkst_fx. unfold ss_cshe_l1. apply pa_entry_st_ok_full.
- unfold cshe_l1_sr. apply regs_ok_pin; [apply regs_ok_pin|intros X; discriminate X|].
  + subst E; apply regs_ok_Eimg_Ereg.
  + intros X; discriminate X.
  + assert (HU : U E (SAlu ALU_ADD (SOff 25 0) (SAlu ALU_SRL (SOff 20 0) (SLit 3))) = SB + EA / 8).
    { rewrite !U_SAlu. cbn [zalu_raw]. rewrite U_SLit.
      rewrite (U_atom E 25 SB E25) by (unfold SB; lia). rewrite (U_atom E 20 EA E20) by lia.
      change (Z.land (zcanon 3) 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
      assert (HD1 : 0 <= EA / 8) by (apply Z.div_pos; lia).
      assert (HD2 : EA / 8 <= EA) by (apply Z.div_le_upper_bound; lia).
      rewrite (zcanon_id (EA / 8)) by (unfold M64; lia).
      apply zcanon_id. unfold M64, SB in *. lia. }
    rewrite H23. unfold w64. rewrite <- HU. unfold U. rewrite Z_to_bv_bv_unsigned. reflexivity.
  + assert (HU2 : U E (SOff 20 8) = EA + 8) by (apply (U_atom_off E 20 EA 8 E20); lia).
    rewrite H27. unfold w64. rewrite <- HU2. unfold U. rewrite Z_to_bv_bv_unsigned. reflexivity.
- vm_compute. reflexivity.
- constructor; [|constructor]. unfold region_ok, cshe_elt.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks ms_mem mkst].
  cbn [base_val]. rewrite E20, unsigned_lit_small by lia.
  split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  repeat (apply Forall_cons); try apply Forall_nil.
  + apply (chunk_ok_val SEGS E _ EA 0 8 (SOff 34 0) s);
    [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
    rewrite Z.add_0_r. exact Ms.
  + apply (chunk_ok_val SEGS E _ EA 8 8 (SOff 35 0) n);
    [cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact Mn].
- apply pairwise_disjoint_of_extents. cbn [map]. repeat split.
- split; [|split; [exact I | exact I]].
  cbn [cshe_l1_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  assert (E2 : ew E 2 = Z_to_bv 64 SP)
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); exact H2).
  assert (E11 : ew E 11 = Z_to_bv 64 WANT)
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
  assert (E22 : ew E 22 = Z_to_bv 64 CNT)
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 22 22%bv eq_refl); exact H22).
  rewrite E2, E11, E22, E20, E25, E34, E35, !unsigned_lit_small by (unfold SB; lia).
  change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
  unfold SB. repeat match goal with |- _ /\ _ => split end; lia.
Qed.

(* Shadow facts survive a change confined to a window above alloc_ceiling: the shadow of any byte the
   program can address lies below alloc_ceiling (W_contract.v shadow_below_stack / shadow_hull_below_stack). *)
Lemma cshe_ra_kept : forall (W W' : world SEGS) (m m' : word -> option byte) a len lo hi,
alloc_ceiling <= lo -> amem_range a len -> 0 <= a ->
(forall y, 0 <= y < 2 ^ 64 -> ~ (lo <= y < hi) -> aview SEGS (w_H W') m' y = aview SEGS (w_H W) m y) ->
range_addressable (aview SEGS (w_H W) m) SHADOW_OFF a len ->
range_addressable (aview SEGS (w_H W') m') SHADOW_OFF a len.
Proof.
intros W W' m m' a len lo hi Hlo Hmr Ha0 Hk Hra x Hx. destruct (Hra x Hx) as (sv & Hsv & Hok).
exists sv. split; [|exact Hok].
destruct (shadow_below_stack lo hi x Hlo (amem_range_in a len x Hmr Ha0 ltac:(lia) ltac:(lia))) as [S1 S2].
rewrite <- Hsv. unfold shadow_of_addr. change (SHADOW_OFF + x / 8) with (shadow_addr x). apply Hk; assumption.
Qed.
Lemma cshe_shv_kept : forall (W W' : world SEGS) (m m' : word -> option byte) a len lo hi,
alloc_ceiling <= lo -> amem_range a len -> 0 <= a -> 0 < len ->
(forall y, 0 <= y < 2 ^ 64 -> ~ (lo <= y < hi) -> aview SEGS (w_H W') m' y = aview SEGS (w_H W) m y) ->
shadow_hull_vis (aview SEGS (w_H W) m) a len -> shadow_hull_vis (aview SEGS (w_H W') m') a len.
Proof.
intros W W' m m' a len lo hi Hlo Hmr Ha0 Hl Hk Hv sa Hsa.
destruct (shadow_hull_below_stack lo hi a len sa Hlo (amem_range_in a len a Hmr Ha0 ltac:(lia) ltac:(lia))
  (amem_range_in a len (a + len - 1) Hmr Ha0 ltac:(lia) ltac:(lia)) Hsa) as [S1 S2].
rewrite Hk by assumption. exact (Hv sa Hsa).
Qed.

(* One turn of loop 1: from the head, the two shadow checks of the slot, has_prefix(v[i].s, v[i].n, PF) (proved
   here: W_has_prefix.pb_has_prefix_x), `a1 += result`, the bumps of s4 / s7 / s6 / s11, and the `bnez s6` at
   0x85494: back at the head when s6 was > 1, else at 0x85498 (A_cshe_tst + 4), with s6 = CNT - 1 either way.
   Only has_prefix's scratch [sp - HP_STK, sp) changes.  ra is not a premise: the jal sets it, and after the
   call it is the callee's (hp_post does not fix it), so a turn cannot hand it to the next. *)
Lemma cshe_l1_run_x : forall (W : world SEGS) ly S hp regs mem md EA s n WANT CNT ly0 S0 hp0 (W0 : world SEGS) mem0 md0
XO AT FP sp0 kk PF lp,
getr regs 2 = w64 (sp0 - 144) -> getr regs 11 = w64 WANT -> getr regs 22 = w64 CNT ->
getr regs 20 = w64 EA -> getr regs 27 = w64 (EA + 8) -> getr regs 23 = w64 (SB + EA / 8) ->
getr regs 25 = w64 SB ->
2 ^ 46 <= sp0 - 144 <= 2 ^ 47 -> (sp0 - 144) mod 16 = 0 -> 0 <= WANT < 2 ^ 26 -> 0 <= CNT < 2 ^ 26 ->
4096 <= EA -> EA + 16 <= 140737479966720 -> EA mod 16 = 0 ->
0 <= s < 140737479966720 -> 0 <= n < 2 ^ 26 ->
val_mem SEGS (mrestrict (w_H W) mem) EA 8 s -> val_mem SEGS (mrestrict (w_H W) mem) (EA + 8) 8 n ->
range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF EA 16 -> amem_range EA 16 ->
ajournal_gx_x SEGS B PST ARx G XO [(AT, AT + 8)] CSHE_STK sp0 FP ly0 S0 hp0 W0 mem0 md0 [] ly S hp W mem md kk ->
(* the prefix, as has_prefix needs it at the call *)
getr regs 9 = w64 PF ->
0 <= lp -> lp + 1 < 2 ^ 32 -> 0 < PF -> PF + lp + 1 <= 2 ^ 63 ->
first_byte SEGS W mem PF (lp + 1) 0 lp ->
hp_vis W mem PF (lp + 1) -> amem_range PF (lp + 1) -> amem_range PF 8 ->
range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF PF (lp + 1) ->
shadow_hull_vis (aview SEGS (w_H W) mem) PF (lp + 1) ->
(forall a, PF + lp < a < PF + lp - (PF + lp) mod 8 + 8 -> aview SEGS (w_H W) mem a <> None) ->
rom_view SEGS W mem ->
(forall a, PF <= a < PF + lp + 8 -> ~ (sp0 - 144 - HP_STK <= a < sp0 - 144)) ->
(* the record's text, as has_prefix needs it *)
0 <= s -> s + lp <= 2 ^ 63 ->
(lp <= n -> hp_vis W mem s lp /\ (forall a, s <= a < s + lp -> ~ (sp0 - 144 - HP_STK <= a < sp0 - 144)) /\
  amem_range s lp /\ range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF s lp /\
  (0 < lp -> shadow_hull_vis (aview SEGS (w_H W) mem) s lp) /\
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF PF lp /\
  (0 < lp -> shadow_hull_vis (aview SEGS (w_H W) mem) PF lp)) ->
(* the frame budget and the chain *)
getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
s0Z regs < alloc_ceiling -> XO mod 16 = 0 -> alloc_ceiling + CSHE_STK <= sp0 ->
1 <= CNT -> WANT + 1 < 2 ^ 26 ->
(* the slot [EA, EA + 16) is inside the held vector's block, so it survives the call *)
forall VB VL, In (VB, VL) (ablocks B ly S) -> VB <= EA -> EA + 16 <= VB + req_size VL ->
SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + A_cshe_l1)) mem (seg_rom SEGS)) md)
(fun W' c' => exists regs' mem' md' b pc',
 c' = mkCfg (mkst regs' (Z_to_bv 64 pc') mem' (seg_rom SEGS)) md' /\
 ((1 < CNT /\ pc' = BASE + A_cshe_l1) \/ (CNT = 1 /\ pc' = BASE + A_cshe_tst + 4)) /\
 ajournal_gx_x SEGS B PST ARx G XO [(AT, AT + 8)] CSHE_STK sp0 FP ly0 S0 hp0 W0 mem0 md0 [] ly S hp W' mem' md' kk /\
 (b = 0 \/ b = 1) /\
 (b = 1 -> lp <= n /\ hp_prefix_of W mem s PF lp) /\ (b = 0 -> lp <= n -> ~ hp_prefix_of W mem s PF lp) /\
 getr regs' 11 = w64 (WANT + b) /\ getr regs' 10 = w64 b /\ getr regs' 21 = w64 WANT /\
 getr regs' 20 = w64 (EA + 16) /\ getr regs' 23 = w64 (SB + (EA + 16) / 8) /\
 getr regs' 27 = w64 (EA + 24) /\ getr regs' 22 = w64 (CNT - 1) /\
 getr regs' 2 = getr regs 2 /\ getr regs' 3 = getr regs 3 /\ getr regs' 4 = getr regs 4 /\
 getr regs' 8 = getr regs 8 /\ getr regs' 9 = getr regs 9 /\ getr regs' 18 = getr regs 18 /\
 getr regs' 19 = getr regs 19 /\ getr regs' 24 = getr regs 24 /\ getr regs' 25 = getr regs 25 /\
 getr regs' 26 = getr regs 26 /\
 (forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 144 - HP_STK <= a < sp0 - 144) ->
   aview SEGS (w_H W') mem' a = aview SEGS (w_H W) mem a) /\
 (forall a, apresent (w_H W) mem a -> apresent (w_H W') mem' a)).
Proof.
intros W ly S hp regs mem md EA s n WANT CNT ly0 S0 hp0 W0 mem0 md0 XO AT FP sp0 kk PF lp
H2 H11 H22 H20 H27 H23 H25 HSP HSPa HW HC Hlo Hhi Hal Hs Hn Ms Mn HRA HMR HJ
H9 Rlp0 Rlp32 RPF0 RPFk HFB HVIS HMRP HM8 HRAP HHVP HTAIL HROM HOFFP Rs0 Rsl HCMP Hgp Htp Hch HXO16 HCL0 HC1 HW1 VB VL HVIN HVlo HVhi.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
assert (HXO0 : 0 <= XO) by (pose proof HJ as (_ & HX & _); exact HX).
pose proof (cshe_l1_state W regs mem EA s n (sp0 - 144) WANT CNT H2 H11 H22 H20 H27 H23 H25 HSP HSPa HW HC
  Hlo Hhi Hal Hs Hn Ms Mn) as HS.
remember (Eimg (Ereg regs (cshe_l1_extra s n))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (E20 : ew E 20 = Z_to_bv 64 EA)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 20 20%bv eq_refl); exact H20).
assert (E25 : ew E 25 = Z_to_bv 64 SB)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 25 25%bv eq_refl); exact H25).
assert (E2 : ew E 2 = Z_to_bv 64 (sp0 - 144))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); exact H2).
assert (E11 : ew E 11 = Z_to_bv 64 WANT)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
assert (E22 : ew E 22 = Z_to_bv 64 CNT)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 22 22%bv eq_refl); exact H22).
assert (Usp : bv_unsigned (ew E 2) = sp0 - 144) by (rewrite E2; apply unsigned_lit_small; lia).
assert (SHOK : sh_ok SEGS Bx1 cshe_l1_SH E (mrestrict (w_H W) mem)).
{ unfold sh_ok, cshe_l1_SH. constructor; [|constructor].
  assert (UBx : U E Bx1 = SHADOW_OFF)
    by (unfold U, Bx1; cbn [sv_denot]; rewrite E25, Z.add_0_r, Z_to_bv_bv_unsigned;
        rewrite unsigned_lit_small by (unfold SB; lia); reflexivity).
  assert (Up : U E (SOff 20 0) = EA) by (apply (U_atom E 20 EA E20); lia).
  split; cbn [she_m she_lo she_hi].
  - rewrite UBx, Up, Z.add_0_r, Z.sub_0_r. exact HRA.
  - unfold app_apart. cbn [she_m she_lo she_hi]. rewrite UBx, Up.
    unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd, SHADOW_OFF in *. intros a Ha. lia. }
pose (RUNTOx := paj_run_to_x_x B PST ARx LAWS G HG XO [(AT, AT + 8)]).
paj_run_to_tok_x RUNTOx HS HJ SHOK Bspan AF_fr_has_prefix.
{ apply awr_ok_x_cons; [|apply awr_ok_x_nil].
  unfold cshe_elt. cbn [YP09.r_base YP09.r_wlo YP09.r_whi]. intros a Ha. lia. }
pmkst HS.
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (10%bv : bv 5) Q10.
prreg HS (11%bv : bv 5) Q11. prreg HS (12%bv : bv 5) Q12. prreg HS (21%bv : bv 5) Q21.
prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4. prreg HS (8%bv : bv 5) Q8.
assert (E9 : ew E 9 = Z_to_bv 64 PF)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl); exact H9).
assert (E34 : ew E 34 = Z_to_bv 64 s) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 n) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 3)).
assert (E1 : ew E 1 = getr regs 1) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (E3 : ew E 3 = getr regs 3) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 3 3%bv eq_refl)).
assert (E4 : ew E 4 = getr regs 4) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 4 4%bv eq_refl)).
assert (E8 : ew E 8 = getr regs 8) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 8 8%bv eq_refl)).
lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdq |} _ => set (mdc := mdq) in * end.
destruct (ajournal_gx_inner_x SEGS B PST ARx G XO [(AT, AT + 8)] CSHE_STK sp0 FP ly0 S0 hp0 W0 mem0 md0 [] ly S hp W _ _ kk HJ)
  as (memS & HJi & HgS).
assert (HPREh : afn_pre_x SEGS B ARx HP_STK ly S hp W (ms_regs ms) (ms_mem ms) mdc []).
{ eapply (afn_pre_x_at SEGS B PST ARx (CSHE_STK + XO) (sp0 + XO) FP ly0 S0 hp0 W0 memS md0 [] ly S hp W (ms_mem ms) mdc kk
    (ms_regs ms) HP_STK (- 144 - XO) [] HJi).
  - unfold spZ. rewrite Q2, E2. rewrite unsigned_lit_small by lia. lia.
  - apply Z.mod_divide; [lia|]. apply Z.divide_sub_r; [exists (-9); reflexivity | apply Z.mod_divide; [lia | exact HXO16]].
  - lia.
  - unfold HP_STK, ESTACK. lia.
  - unfold HP_STK, CSHE_STK, CSHE_FRAME, ASTACK, ESTACK. lia.
  - rewrite Q1. apply ret_ok_codeptr_v; [lia | reflexivity].
  - unfold raZ. rewrite Q1. rewrite unsigned_lit_small by lia. lia.
  - rewrite Q3, E3. exact Hgp.
  - rewrite Q4, E4. exact Htp.
  - apply achain_low. unfold s0Z. rewrite Q8, E8. exact Hch. }
(* the run to the call wrote nothing: the only region has no writable byte *)
assert (HAV : aview SEGS (w_H W) (ms_mem ms) = aview SEGS (w_H W) mem).
{ apply functional_extensionality. intros a.
  rewrite (aview_wrap64 (w_H W) (ms_mem ms) a), (aview_wrap64 (w_H W) mem a).
  pose proof (Z.mod_pos_bound a (2 ^ 64) ltac:(lia)) as Ha.
  lazymatch type of HFr with frame_of ?Ev ?rs _ _ => apply (aview_kept_out Ev rs (w_H W) _ _ HFr _ Ha) end.
  intros (r & Hin & Hr). cbn [ss_mem ss_cshe_l1 In] in Hin. unfold cshe_elt in Hin.
  destruct Hin as [<- | []]. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr. lia. }
assert (Usp1 : spZ (ms_regs ms) = sp0 - 144) by (unfold spZ; rewrite Q2, E2; apply unsigned_lit_small; lia).
eapply SRr_bind.
{ apply (W_has_prefix.pb_has_prefix_x B PST ARx LAWS ASTRLEN ABCMP W ly S hp (ms_regs ms) (ms_mem ms) mdc [] s n PF lp HPREh).
  - rewrite Q10, E34. reflexivity.
  - rewrite Q11, E35. reflexivity.
  - rewrite Q12, E9. reflexivity.
  - lia.
  - exact Rlp0.
  - exact Rlp32.
  - exact RPF0.
  - exact RPFk.
  - exact Rs0.
  - exact Rsl.
  - unfold first_byte in *. rewrite HAV. exact HFB.
  - unfold hp_vis in *. rewrite HAV. exact HVIS.
  - unfold hp_off. rewrite Usp1. intros a Ha. apply HOFFP. lia.
  - exact HMRP.
  - exact HM8.
  - rewrite HAV. exact HRAP.
  - rewrite HAV. exact HHVP.
  - rewrite HAV. exact HTAIL.
  - unfold rom_view in *. rewrite HAV. exact HROM.
  - intros Hle. destruct (HCMP Hle) as (C1 & C2 & C3 & C4 & C5 & C6 & C7).
    unfold hp_vis, hp_off in *. rewrite HAV, Usp1.
    split; [exact C1|]. split; [exact C2|]. split; [exact C3|]. split; [exact C4|].
    split; [exact C5|]. split; [exact C6 | exact C7]. }
cbv beta. intros W2 c2 Hwle2 (regs2 & mem2 & md2 & -> & HJc & HP2 & HPR2 & HFRc & HRES).
assert (HB : exists b, (b = 0 \/ b = 1) /\ getr regs2 10 = w64 b /\
  (b = 1 -> lp <= n /\ hp_prefix_of W (ms_mem ms) s PF lp) /\
  (b = 0 -> lp <= n -> ~ hp_prefix_of W (ms_mem ms) s PF lp)).
{ destruct HRES as [(Hle & Hpre & Hr10) | (Hnp & Hr10)].
  - exists 1. split; [right; reflexivity|]. split; [exact Hr10|].
    split; [intros _; split; assumption | intros Hc; discriminate Hc].
  - exists 0. split; [left; reflexivity|]. split; [exact Hr10|].
    split; [intros Hc; discriminate Hc | intros _; exact Hnp]. }
destruct HB as (b & Hb01 & Hb10 & Hb1 & Hb0).
(* the callee's donor journal, composed into this walk's ajournal_gx *)
assert (HJc' : ajournal_gx_x SEGS B PST ARx G 0 [] HP_STK (sp0 - 144) [] ly S hp W (ms_mem ms) mdc [] ly S hp W2 mem2 md2 0).
{ apply (ajournal_gx_G_mono_x SEGS B PST ARx [] G); [intros a Ha; exfalso; exact (inG_nil a Ha)|].
  apply ajournal_gx_nil_x. rewrite <- Usp1. exact HJc. }
pose proof (ajournal_gx_sub_x SEGS B PST ARx LAWS Hsegs G CSHE_STK sp0 XO [(AT, AT + 8)] FP ly0 S0 hp0 W0 mem0 md0 []
  ly S hp W (ms_mem ms) mdc kk HP_STK (sp0 - 144) 0 [] [] [] ly S hp W2 mem2 md2 0 HJ HJc'
  ltac:(unfold CSHE_STK, CSHE_FRAME, HP_STK, ASTACK, ESTACK; lia) ltac:(lia) ltac:(lia)
  ltac:(intros a Ha; exfalso; exact (inFP_nil a Ha)) HG
  ltac:(intros a Ha; exfalso; exact (inFP_nil a Ha))) as HJ2.
cbn [app] in HJ2. rewrite Z.add_0_r in HJ2.
(* every byte outside has_prefix's own scratch is the byte it was called with *)
pose proof HJc as (_ & _ & _ & _ & _ & _ & _ & _ & _ & KEEPb & _).
(* the vector slot is a live block's bytes, so has_prefix kept it *)
assert (KEEPe : forall a, EA <= a < EA + 16 -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) (ms_mem ms) a).
{ intros a Ha. replace a with (VB + (a - VB)) by lia.
  apply (KEEPb VB VL (a - VB) HVIN HVIN); [lia | intros Hc; exact (inFP_nil _ Hc)]. }
jafter_call_keep_pi HS 36%nat regs2 (mrestrict (w_H W2) mem2) HP2 [0]%nat HS2.
match type of HS2 with ?ty -> _ => assert (HRK : ty); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; [| apply Forall_nil].
  split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val].
  - intros a Ha. apply (mbyte_of_aview SEGS). rewrite E20, unsigned_lit_small in Ha by lia.
    apply KEEPe. lia.
  - intros a Ha _. exfalso. rewrite E20 in Ha. lia. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
prreg HS (10%bv : bv 5) R10a. cbn [CLOB map nth] in R10a.
(* has_prefix wrote nothing outside its own scratch *)
assert (HFRh : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 144 - HP_STK <= a < sp0 - 144) ->
  aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) (ms_mem ms) a).
{ intros a Ha Hno. apply HFRc; [exact Ha|]. rewrite Usp1. exact Hno. }
assert (HCEIL : alloc_ceiling <= sp0 - 144 - HP_STK).
{ unfold HP_STK, ESTACK, CSHE_STK, CSHE_FRAME, ASTACK in *. lia. }
(* the environment after the call, and the loop state again *)
remember (havoc E 36 (map (getr regs2) CLOB)) as Ea eqn:HEa in HS.
assert (HEIa : img_env VAL A_LIM Ea) by (rewrite HEa; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLDa : forall m, (m < 36)%nat -> ew Ea m = ew E m)
  by (intros m Hm; rewrite HEa; apply YN3v.ew_havoc_old; exact Hm).
assert (F40 : ew Ea 40 = w64 b)
  by (rewrite HEa; cbn [ew havoc map nth CLOB length Nat.sub Nat.ltb Nat.leb]; exact Hb10).
clear HEa.
assert (SHOKa : sh_ok SEGS Bx1 cshe_l1_SH Ea (mrestrict (w_H W2) mem2)).
{ unfold sh_ok, cshe_l1_SH. constructor; [|constructor].
  assert (UBx : U Ea Bx1 = SHADOW_OFF)
    by (unfold U, Bx1; cbn [sv_denot]; rewrite OLDa by (cbv; lia); rewrite E25, Z.add_0_r, Z_to_bv_bv_unsigned;
        rewrite unsigned_lit_small by (unfold SB; lia); reflexivity).
  assert (Up : U Ea (SOff 20 0) = EA)
    by (apply (U_atom Ea 20 EA); [rewrite OLDa by (cbv; lia); exact E20 | lia]).
  split; cbn [she_m she_lo she_hi].
  - rewrite UBx, Up, Z.add_0_r, Z.sub_0_r.
    apply (cshe_ra_kept W W2 (ms_mem ms) mem2 EA 16 (sp0 - 144 - HP_STK) (sp0 - 144) HCEIL HMR ltac:(lia));
      [intros y Hy Hno; exact (HFRh y Hy Hno) | rewrite HAV; exact HRA].
  - unfold app_apart. cbn [she_m she_lo she_hi]. rewrite UBx, Up.
    unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd, SHADOW_OFF in *. intros a Ha. lia. }
(* on to the loop test *)
rewrite Q1.
pose (RUNx := paj_run_x_x B PST ARx LAWS G HG XO [(AT, AT + 8)]).
paj_run_tok_x RUNx HS HJ2 SHOKa Bspan.
{ apply awr_ok_x_cons; [|apply awr_ok_x_nil].
  unfold cshe_elt. cbn [YP09.r_base YP09.r_wlo YP09.r_whi]. intros a Ha. lia. }
(* the state at the loop test *)
pose proof (st_ok_pi_restrict_mkst _ _ _ _ HS eq_refl) as Hms2. cbn [ss_pc] in Hms2.
prreg HS (2%bv : bv 5) N2. prreg HS (3%bv : bv 5) N3. prreg HS (4%bv : bv 5) N4.
prreg HS (10%bv : bv 5) N10b. prreg HS (21%bv : bv 5) N21.
prreg HS (8%bv : bv 5) N8. prreg HS (9%bv : bv 5) N9. prreg HS (11%bv : bv 5) N11.
prreg HS (18%bv : bv 5) N18. prreg HS (19%bv : bv 5) N19. prreg HS (20%bv : bv 5) N20.
prreg HS (22%bv : bv 5) N22. prreg HS (23%bv : bv 5) N23. prreg HS (24%bv : bv 5) N24.
prreg HS (25%bv : bv 5) N25. prreg HS (26%bv : bv 5) N26. prreg HS (27%bv : bv 5) N27.
assert (OLDk : forall m (rr : bv 5), (m < 36)%nat -> Z.of_nat m = bv_unsigned rr -> ew Ea m = getr regs rr).
{ intros m rr Hm Hrr. rewrite OLDa by exact Hm. subst E. rewrite Eimg_low by (unfold A_TEXT; lia).
  apply ew_Ereg_nat. exact Hrr. }
(* the atoms at the loop test, and the result bit *)
assert (A20 : ew Ea 20 = Z_to_bv 64 EA) by (rewrite OLDa by (cbv; lia); exact E20).
assert (A22 : ew Ea 22 = Z_to_bv 64 CNT) by (rewrite OLDa by (cbv; lia); exact E22).
assert (A25 : ew Ea 25 = Z_to_bv 64 SB) by (rewrite OLDa by (cbv; lia); exact E25).
assert (A11 : ew Ea 11 = Z_to_bv 64 WANT) by (rewrite OLDa by (cbv; lia); exact E11).

(* the second run wrote nothing either *)
assert (KEEP2 : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W2) (ms_mem ms0) a = aview SEGS (w_H W2) mem2 a).
{ intros a Ha.
  lazymatch goal with Hf : frame_of ?Ev ?rs (mrestrict (w_H W2) mem2) _ |- _ =>
    apply (aview_kept_out Ev rs (w_H W2) _ _ Hf a Ha) end.
  intros (r & Hin & Hr). cbn [ss_mem In] in Hin.
  repeat (destruct Hin as [<- | Hin];
    [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val cshe_elt] in Hr; lia|]). destruct Hin. }
assert (HD1 : 0 <= EA / 8) by (apply Z.div_pos; lia).
assert (HD2 : EA / 8 <= EA) by (apply Z.div_le_upper_bound; lia).
assert (HDE : (EA + 16) / 8 = EA / 8 + 2).
{ pose proof Hal as Hal'. apply Z.mod_divide in Hal'; [|lia]. destruct Hal' as (qq & Hq). rewrite Hq.
  replace (qq * 16 + 16) with ((2 * qq + 2) * 8) by lia. replace (qq * 16) with ((2 * qq) * 8) by lia.
  rewrite !Z_div_mult by lia. lia. }
(* the post, for any state the `bnez s6` reaches that keeps the test's registers and memory *)
pose proof HS as HSt.
lazymatch goal with |- SRr _ _ _ ?Q =>
assert (FIN : forall regs1 mem1 md1 pc1,
  (forall r, getr regs1 r = getr (ms_regs ms0) r) ->
  (forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W2) mem1 a = aview SEGS (w_H W2) (ms_mem ms0) a) ->
  mem_grows (mrestrict (w_H W2) (ms_mem ms0)) (mrestrict (w_H W2) mem1) ->
  ajournal_gx_x SEGS B PST ARx G XO [(AT, AT + 8)] CSHE_STK sp0 FP ly0 S0 hp0 W0 mem0 md0 [] ly S hp W2 mem1 md1 kk ->
  ((1 < CNT /\ pc1 = BASE + A_cshe_l1) \/ (CNT = 1 /\ pc1 = BASE + A_cshe_tst + 4)) ->
  Q W2 (mkCfg (mkst regs1 (Z_to_bv 64 pc1) mem1 (seg_rom SEGS)) md1)) end.
{ intros regs1 mem1 md1 pc1 RG1 KEEP3 HG3 HJ3 HPC. cbv beta.
  exists regs1, mem1, md1, b, pc1.
  split; [reflexivity|]. split; [exact HPC|]. split; [exact HJ3|]. split; [exact Hb01|].
  split; [intros Hb; destruct (Hb1 Hb) as [X1 X2]; split; [exact X1|];
          unfold hp_prefix_of in *; intros k Hk; rewrite <- HAV; apply X2; exact Hk|].
  split; [intros Hb Hle Hc; apply (Hb0 Hb Hle); unfold hp_prefix_of in *;
          intros k Hk; rewrite HAV; apply Hc; exact Hk|].
  rewrite !RG1.
  split.
  { rewrite N11, F40, A11. unfold w64.
    assert (HA1 : alu64 ALU_ADD (Z_to_bv 64 b) (Z_to_bv 64 WANT) = Z_to_bv 64 (zalu64 ALU_ADD b WANT))
      by apply zalu64_sound.
    rewrite (aluw_addsub_of_lit ALU_ADD _ _ (zalu64 ALU_ADD b WANT) ltac:(left; reflexivity) HA1).
    f_equal. unfold zalu32, zalu64, zalu_raw, zu32, M32, zcanon, M64.
    rewrite (Z.mod_small b) by lia. rewrite (Z.mod_small WANT) by lia. rewrite (Z.mod_small (b + WANT)) by lia.
    rewrite (Z.mod_small (b + WANT)) by lia. rewrite Z.mod_0_l by lia. rewrite Z.add_0_r.
    unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with 2147483648. change (bv_modulus 32) with 4294967296.
    rewrite (Z.mod_small (b + WANT + 2147483648)) by lia. rewrite Z.mod_small by lia. lia. }
  split; [rewrite N10b, F40; reflexivity|].
  split; [rewrite N21, A11; reflexivity|].
  split; [rewrite N20, A20, unsigned_lit_small by lia; reflexivity|].
  split.
  { rewrite N23, A20, A25.
    assert (QS3 : alu64 ALU_SRL (Z_to_bv 64 EA) (Z_to_bv 64 3) = Z_to_bv 64 (EA / 8)).
    { apply bv_eq. rewrite alu64_unsigned. cbn [zalu_raw]. rewrite !unsigned_lit_small by lia.
      change (Z.land 3 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
      unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). apply Z.mod_small. lia. }
    rewrite QS3, !zalu64_sound. unfold w64. f_equal. unfold zalu64, zalu_raw, zcanon, M64.
    rewrite (Z.mod_small SB) by (unfold SB; lia). rewrite (Z.mod_small (EA / 8)) by lia.
    rewrite (Z.mod_small (SB + EA / 8)) by (unfold SB; lia). rewrite (Z.mod_small (SB + EA / 8)) by (unfold SB; lia).
    rewrite (Z.mod_small 2) by lia. rewrite Z.mod_small by (unfold SB; lia). rewrite HDE. lia. }
  split; [rewrite N27, A20, unsigned_lit_small by lia; reflexivity|].
  split; [rewrite N22, A22, unsigned_lit_small by lia; unfold w64; f_equal; lia|].
  split; [rewrite N2; exact (OLDk 2%nat 2%bv ltac:(cbv; lia) eq_refl)|].
  split; [rewrite N3; exact (OLDk 3%nat 3%bv ltac:(cbv; lia) eq_refl)|].
  split; [rewrite N4; exact (OLDk 4%nat 4%bv ltac:(cbv; lia) eq_refl)|].
  split; [rewrite N8; exact (OLDk 8%nat 8%bv ltac:(cbv; lia) eq_refl)|].
  split; [rewrite N9; exact (OLDk 9%nat 9%bv ltac:(cbv; lia) eq_refl)|].
  split; [rewrite N18; exact (OLDk 18%nat 18%bv ltac:(cbv; lia) eq_refl)|].
  split; [rewrite N19; exact (OLDk 19%nat 19%bv ltac:(cbv; lia) eq_refl)|].
  split; [rewrite N24; exact (OLDk 24%nat 24%bv ltac:(cbv; lia) eq_refl)|].
  split; [rewrite N25; exact (OLDk 25%nat 25%bv ltac:(cbv; lia) eq_refl)|].
  split; [rewrite N26; exact (OLDk 26%nat 26%bv ltac:(cbv; lia) eq_refl)|].
  split.
  { intros a Ha Hno. rewrite (KEEP3 a Ha), (KEEP2 a Ha), (HFRh a Ha Hno), HAV. reflexivity. }
  intros a Hp. exact (apresent_grows _ _ _ _ HG3 (apresent_grows _ _ _ _ HG1 (HPR2 a (apresent_grows _ _ _ _ HG0 Hp)))). }
(* the `bnez s6` *)
psrr_branch_tok RUNx BR HS SHOKa Bspan.
- (* s6 = CNT - 1 <> 0: back to the head *)
  rewrite branch_ne_U, (U_atom_off Ea 22 CNT (-1) A22), U_lit in Hc by lia.
  assert (Hlt : 1 < CNT) by (destruct (Z.eqb_spec (CNT + -1) 0); [discriminate | lia]).
  paj_run_to_tok_x RUNTOx HS HJ2 SHOKa Bspan A_cshe_l1.
  { apply awr_ok_x_cons; [|apply awr_ok_x_nil].
    unfold cshe_elt. cbn [YP09.r_base YP09.r_wlo YP09.r_whi]. intros a Ha. lia. }
  assert (KEEP3 : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W2) (ms_mem ms1) a = aview SEGS (w_H W2) (ms_mem ms0) a).
  { intros a Ha.
    lazymatch goal with Hf : frame_of ?Ev ?rs (mrestrict (w_H W2) (ms_mem ms0)) _ |- _ =>
      apply (aview_kept_out Ev rs (w_H W2) _ _ Hf a Ha) end.
    intros (r & Hin & Hr). cbn [ss_mem In] in Hin.
    repeat (destruct Hin as [<- | Hin];
      [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val cshe_elt] in Hr; lia|]). destruct Hin. }
  pmkst HS. apply SRr_ret. apply FIN.
  + intros r. pose proof (st_ok_pi_restrict_reg _ _ _ _ r HS) as X1. pose proof (st_ok_pi_restrict_reg _ _ _ _ r HSt) as X0.
    rewrite X1, X0. reflexivity.
  + exact KEEP3.
  + lazymatch goal with Hg : mem_grows (mrestrict (w_H W2) (ms_mem ms0)) _ |- _ => exact Hg end.
  + exact HJ2.
  + left. split; [exact Hlt | unfold A_cshe_l1, AF_fr_check_shape_ends; lia].
- (* s6 = 0: on to 0x85498 *)
  rewrite branch_ne_U, (U_atom_off Ea 22 CNT (-1) A22), U_lit in Hc by lia.
  assert (Heq : CNT = 1) by (destruct (Z.eqb_spec (CNT + -1) 0); [lia | discriminate]).
  paj_run_to_tok_x RUNTOx HS HJ2 SHOKa Bspan (A_cshe_tst + 4).
  { apply awr_ok_x_cons; [|apply awr_ok_x_nil].
    unfold cshe_elt. cbn [YP09.r_base YP09.r_wlo YP09.r_whi]. intros a Ha. lia. }
  assert (KEEP3 : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W2) (ms_mem ms1) a = aview SEGS (w_H W2) (ms_mem ms0) a).
  { intros a Ha.
    lazymatch goal with Hf : frame_of ?Ev ?rs (mrestrict (w_H W2) (ms_mem ms0)) _ |- _ =>
      apply (aview_kept_out Ev rs (w_H W2) _ _ Hf a Ha) end.
    intros (r & Hin & Hr). cbn [ss_mem In] in Hin.
    repeat (destruct Hin as [<- | Hin];
      [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val cshe_elt] in Hr; lia|]). destruct Hin. }
  pmkst HS. apply SRr_ret. apply FIN.
  + intros r. pose proof (st_ok_pi_restrict_reg _ _ _ _ r HS) as X1. pose proof (st_ok_pi_restrict_reg _ _ _ _ r HSt) as X0.
    rewrite X1, X0. reflexivity.
  + exact KEEP3.
  + lazymatch goal with Hg : mem_grows (mrestrict (w_H W2) (ms_mem ms0)) _ |- _ => exact Hg end.
  + exact HJ2.
  + right. split; [exact Heq | unfold A_cshe_tst, AF_fr_check_shape_ends; lia].
Qed.

(* ------------------------------------------------------------------ loop 1, the induction over the records *)
(* The bytes of a NUL-terminated string as the walk reads them: the form cshe_spec states P in, and the form
   alist_at's garr8 gives of a record's text (cshe_bytes_of_garr8). *)
Definition cshe_bytes (W : world SEGS) (mem : word -> option byte) (a : Z) (l : list byte) : Prop :=
forall t, 0 <= t < Z.of_nat (length l) ->
aview SEGS (w_H W) mem (a + t) = Some (bv_unsigned (nth (Z.to_nat t) l (Z_to_bv 8 0))).

Lemma cshe_u8 : forall v, 0 <= v < 256 -> bv_unsigned (Z_to_bv 8 v) = v.
Proof.
intros v Hv. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. apply Z.mod_small. exact Hv.
Qed.
Lemma cshe_nth_bzs : forall (l : list byte) (j : nat),
nth j (HarnessRep.bzs l) 0 = bv_unsigned (nth j l (Z_to_bv 8 0)).
Proof.
intros l j. unfold HarnessRep.bzs, HarnessRep.bz.
rewrite <- (map_nth bv_unsigned l (Z_to_bv 8 0) j). reflexivity.
Qed.
Lemma cshe_bzs_inj : forall l1 l2 : list byte, HarnessRep.bzs l1 = HarnessRep.bzs l2 -> l1 = l2.
Proof.
induction l1 as [|a l1 IH]; intros [|b l2] H; unfold HarnessRep.bzs in H; cbn [map] in H;
  try discriminate H; [reflexivity|].
injection H as H1 H2. f_equal; [apply bv_eq; exact H1 | apply IH; exact H2].
Qed.
Lemma cshe_bytes_of_garr8 : forall (W : world SEGS) mem a (l : list byte),
garr8 SEGS (mrestrict (w_H W) mem) a (HarnessRep.bzs l) -> cshe_bytes W mem a l.
Proof.
intros W mem a l Hg t Ht.
assert (HL : length (HarnessRep.bzs l) = length l) by (unfold HarnessRep.bzs; apply length_map).
assert (Hj : (Z.to_nat t < length (HarnessRep.bzs l))%nat) by lia.
unfold aview. replace (a + t) with (a + Z.of_nat (Z.to_nat t)) by lia.
rewrite (garr8_mbyte SEGS _ a _ (Z.to_nat t) Hg Hj). cbn [option_map].
destruct (Hg (Z.to_nat t) Hj) as (_ & Hr). rewrite (cshe_u8 _ Hr). f_equal. apply cshe_nth_bzs.
Qed.
Lemma cshe_bytes_kept : forall (W W' : world SEGS) mem mem' a (l : list byte) lo hi,
(forall y, 0 <= y < 2 ^ 64 -> ~ (lo <= y < hi) -> aview SEGS (w_H W') mem' y = aview SEGS (w_H W) mem y) ->
(forall t, 0 <= t < Z.of_nat (length l) -> 0 <= a + t < 2 ^ 64 /\ ~ (lo <= a + t < hi)) ->
cshe_bytes W mem a l -> cshe_bytes W' mem' a l.
Proof.
intros W W' mem mem' a l lo hi Hk Hin Hb t Ht. destruct (Hin t Ht) as [H1 H2].
rewrite (Hk (a + t) H1 H2). exact (Hb t Ht).
Qed.

(* want_of, one record at a time: the plain model's step (lib/Prog/check_shape_ends.v cse_want_step). *)
Lemma cshe_firstn_S : forall (l : list (Z * list byte)) (j : nat) (d : Z * list byte), (j < length l)%nat ->
firstn (S j) l = firstn j l ++ [nth j l d].
Proof.
intros l. induction l as [|x l IH]; intros [|j] d Hj; cbn [length] in Hj; try lia.
- reflexivity.
- cbn [firstn nth app]. f_equal. apply IH. lia.
Qed.
(* want_of's filter is the stdpp one, as in the plain proof's ce_fcons (lib/Prog/check_shape_ends.v:580). *)
Lemma cshe_want_app : forall P (a b : list (Z * list byte)),
CheckRep.want_of P (a ++ b) = (CheckRep.want_of P a + CheckRep.want_of P b)%nat.
Proof.
intros P a b. unfold CheckRep.want_of. rewrite list_basics.list.filter_app, length_app. reflexivity.
Qed.
Lemma cshe_want_one : forall P (r : Z * list byte),
CheckRep.want_of P [r] = (if CheckRep.prefixb P (snd r) then 1 else 0)%nat.
Proof.
intros P r. unfold CheckRep.want_of. rewrite list_basics.list.filter_singleton.
destruct (CheckRep.prefixb P (snd r)) eqn:E;
  match goal with |- context [decide ?X] => destruct (decide X) as [D|D] end; cbn in D |- *;
  first [reflexivity | contradiction | (exfalso; apply D; exact I) | (rewrite E in D; cbn in D; contradiction)
        | (exfalso; apply D; rewrite E; exact I)].
Unshelve. all: exact [].
Qed.
Lemma cshe_want_le : forall P (l : list (Z * list byte)), (CheckRep.want_of P l <= length l)%nat.
Proof.
intros P l. assert (E0 : CheckRep.want_of P [] = 0%nat) by reflexivity.
induction l as [|x l IH]; [rewrite E0; cbn [length]; lia|].
change (x :: l) with ([x] ++ l). rewrite cshe_want_app, cshe_want_one, length_app. cbn [length].
destruct (CheckRep.prefixb P (snd x)); lia.
Qed.
Lemma cshe_want_step : forall P (recs : list (Z * list byte)) (j : nat), (j < length recs)%nat ->
CheckRep.want_of P (firstn (S j) recs) =
(CheckRep.want_of P (firstn j recs) +
 (if CheckRep.prefixb P (snd (nth j recs (0%Z, []))) then 1 else 0))%nat.
Proof.
intros P recs j Hj. rewrite (cshe_firstn_S recs j (0, []) Hj), cshe_want_app, cshe_want_one. reflexivity.
Qed.
Lemma cshe_leqb : forall a b : list Z, RelayModel.list_eqb a b = true <-> a = b.
Proof.
intros a b. unfold RelayModel.list_eqb. destruct (list_eq_dec Z.eq_dec a b) as [E|E].
- split; [intros _; exact E | intros _; reflexivity].
- split; [intros Hc; discriminate Hc | intros Hc; exfalso; exact (E Hc)].
Qed.
(* has_prefix's answer on a record's text is exactly the plain model's prefixb. *)
Lemma cshe_prefixb_iff : forall (W : world SEGS) mem (q PF : Z) (x P : list byte),
cshe_bytes W mem q (x ++ [Z_to_bv 8 0]) -> cshe_bytes W mem PF (P ++ [Z_to_bv 8 0]) ->
((Z.of_nat (length P) <= Z.of_nat (length x) /\ hp_prefix_of W mem q PF (Z.of_nat (length P))) <->
 CheckRep.prefixb P x = true).
Proof.
intros W mem q PF x P Hx HP.
assert (LX : forall t, 0 <= t < Z.of_nat (length x) ->
  aview SEGS (w_H W) mem (q + t) = Some (bv_unsigned (nth (Z.to_nat t) x (Z_to_bv 8 0)))).
{ intros t Ht. rewrite (Hx t ltac:(rewrite length_app; cbn [length]; lia)).
  do 2 f_equal. apply app_nth1. lia. }
assert (LP : forall t, 0 <= t < Z.of_nat (length P) ->
  aview SEGS (w_H W) mem (PF + t) = Some (bv_unsigned (nth (Z.to_nat t) P (Z_to_bv 8 0)))).
{ intros t Ht. rewrite (HP t ltac:(rewrite length_app; cbn [length]; lia)).
  do 2 f_equal. apply app_nth1. lia. }
unfold CheckRep.prefixb. split.
- intros (Hle & Hpre). apply andb_true_iff. split; [apply Nat.leb_le; lia|].
  apply cshe_leqb. f_equal.
  assert (LF : length (firstn (length P) x) = length P) by (rewrite length_firstn; lia).
  assert (NX : forall t, (t < length P)%nat -> nth t x (Z_to_bv 8 0) = nth t (firstn (length P) x) (Z_to_bv 8 0)).
  { intros t Ht. transitivity (nth t (firstn (length P) x ++ skipn (length P) x) (Z_to_bv 8 0));
    [rewrite firstn_skipn; reflexivity | apply app_nth1; lia]. }
  apply (nth_ext _ _ (Z_to_bv 8 0) (Z_to_bv 8 0)); [exact LF|].
  intros t Ht. rewrite LF in Ht. rewrite <- (NX t Ht).
  specialize (Hpre (Z.of_nat t) ltac:(lia)).
  rewrite (LX (Z.of_nat t) ltac:(lia)), (LP (Z.of_nat t) ltac:(lia)) in Hpre.
  injection Hpre as Hpre. rewrite !Nat2Z.id in Hpre. apply bv_eq. exact Hpre.
- intros Hb. apply andb_true_iff in Hb as [Hb1 Hb2]. apply Nat.leb_le in Hb1. apply cshe_leqb in Hb2.
  apply cshe_bzs_inj in Hb2.
  assert (NX : forall t, (t < length P)%nat -> nth t x (Z_to_bv 8 0) = nth t (firstn (length P) x) (Z_to_bv 8 0)).
  { intros t Ht. transitivity (nth t (firstn (length P) x ++ skipn (length P) x) (Z_to_bv 8 0));
    [rewrite firstn_skipn; reflexivity | apply app_nth1; rewrite length_firstn; lia]. }
  split; [lia|]. intros t Ht.
  rewrite (LX t ltac:(lia)), (LP t ltac:(lia)). do 2 f_equal.
  rewrite (NX (Z.to_nat t) ltac:(lia)), Hb2. reflexivity.
Qed.

(* ---- loop 1's invariant at the head 0x85450, for the records v[i..n) still to count ---- *)
(* The prefix at PF, as has_prefix's premises take it.  Every clause is an aview fact, a shadow fact of a
   range below alloc_ceiling, or pure, so the post's frame clause carries it to the next turn
   (cshe_l1_pfx_kept). *)
Definition cshe_l1_pfx (W : world SEGS) (mem : word -> option byte) (sp0 PF : Z) (P : list byte) : Prop :=
let lp := Z.of_nat (length P) in
cshe_bytes W mem PF (P ++ [Z_to_bv 8 0]) /\
(forall a, PF <= a < PF + lp + 8 -> aview SEGS (w_H W) mem a <> None) /\
(forall a, PF <= a < PF + lp + 8 -> ~ (sp0 - 144 - HP_STK <= a < sp0 - 144)) /\
amem_range PF (lp + 1) /\ amem_range PF 8 /\
range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF PF (lp + 1) /\
shadow_hull_vis (aview SEGS (w_H W) mem) PF (lp + 1) /\
range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF PF lp /\
(0 < lp -> shadow_hull_vis (aview SEGS (w_H W) mem) PF lp) /\
rom_view SEGS W mem.
(* One record of the held vector: its 16-byte slot at V + 16 j, and its text. *)
Definition cshe_l1_rec (ly : alayout) (S : astate) (W : world SEGS) (mem : word -> option byte)
(sp0 V : Z) (P : list byte) (r : Z * list byte) (j : Z) : Prop :=
let lp := Z.of_nat (length P) in
let lx := Z.of_nat (length (snd r)) in
let EA := V + AREC * j in
val_mem SEGS (mrestrict (w_H W) mem) EA 8 (fst r) /\
val_mem SEGS (mrestrict (w_H W) mem) (EA + 8) 8 lx /\
range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF EA 16 /\ amem_range EA 16 /\
(forall a, EA <= a < EA + 16 -> ~ (sp0 - 144 - HP_STK <= a < sp0 - 144)) /\
(exists VB VL, In (VB, VL) (ablocks B ly S) /\ VB <= EA /\ EA + 16 <= VB + req_size VL) /\
0 <= fst r < 140737479966720 /\ lx < 2 ^ 26 /\
cshe_bytes W mem (fst r) (snd r ++ [Z_to_bv 8 0]) /\
(forall a, fst r <= a < fst r + lx + 1 -> ~ (sp0 - 144 - HP_STK <= a < sp0 - 144)) /\
(lp <= lx -> amem_range (fst r) lp /\
   range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF (fst r) lp /\
   (0 < lp -> shadow_hull_vis (aview SEGS (w_H W) mem) (fst r) lp)).
Definition cshe_l1_vec (ly : alayout) (S : astate) (W : world SEGS) (mem : word -> option byte)
(sp0 V : Z) (P : list byte) (recs : list (Z * list byte)) (i : Z) : Prop :=
forall j, i <= j < Z.of_nat (length recs) -> cshe_l1_rec ly S W mem sp0 V P (nth (Z.to_nat j) recs (0, [])) j.

Lemma cshe_l1_pfx_kept : forall (W W' : world SEGS) mem mem' sp0 PF P,
alloc_ceiling <= sp0 - 144 - HP_STK ->
0 < PF -> PF + Z.of_nat (length P) + 1 <= 2 ^ 63 ->
(forall y, 0 <= y < 2 ^ 64 -> ~ (sp0 - 144 - HP_STK <= y < sp0 - 144) ->
   aview SEGS (w_H W') mem' y = aview SEGS (w_H W) mem y) ->
cshe_l1_pfx W mem sp0 PF P -> cshe_l1_pfx W' mem' sp0 PF P.
Proof.
intros W W' mem mem' sp0 PF P HCEIL HPF0 HPFk Hk
  (Hby & Hvis & Hoff & Hmr1 & Hmr8 & Hra1 & Hshv1 & Hra0 & Hshv0 & Hrom).
pose proof pa_segs_low as Hsegs. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HIN : forall a, PF <= a < PF + Z.of_nat (length P) + 8 ->
  0 <= a < 2 ^ 64 /\ ~ (sp0 - 144 - HP_STK <= a < sp0 - 144)) by (intros a Ha; split; [lia | apply Hoff; lia]).
split; [apply (cshe_bytes_kept W W' mem mem' PF _ (sp0 - 144 - HP_STK) (sp0 - 144) Hk);
        [intros t Ht; apply HIN; rewrite length_app in Ht; cbn [length] in Ht; lia | exact Hby]|].
split; [intros a Ha; destruct (HIN a Ha) as [X1 X2]; rewrite (Hk a X1 X2); exact (Hvis a Ha)|].
split; [exact Hoff|]. split; [exact Hmr1|]. split; [exact Hmr8|].
split; [exact (cshe_ra_kept W W' mem mem' PF (Z.of_nat (length P) + 1) _ _ HCEIL Hmr1 ltac:(lia) Hk Hra1)|].
split; [exact (cshe_shv_kept W W' mem mem' PF (Z.of_nat (length P) + 1) _ _ HCEIL Hmr1 ltac:(lia) ltac:(lia) Hk Hshv1)|].
assert (Hmr0 : amem_range PF (Z.of_nat (length P)))
  by (unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in *; lia).
split; [exact (cshe_ra_kept W W' mem mem' PF (Z.of_nat (length P)) _ _ HCEIL Hmr0 ltac:(lia) Hk Hra0)|].
split; [intros Hp; exact (cshe_shv_kept W W' mem mem' PF (Z.of_nat (length P)) _ _ HCEIL Hmr0 ltac:(lia) Hp Hk (Hshv0 Hp))|].
intros a Ha. assert (Hi : in_img SEGS a) by (destruct Ha as (sg & Hsg & _ & Hr); exists sg; split; assumption).
destruct (Hsegs a Hi) as [L1 L2]. unfold kLowMemEnd in L2.
rewrite (Hk a ltac:(lia) ltac:(lia)). exact (Hrom a Ha).
Qed.
Lemma cshe_l1_rec_kept : forall ly S (W W' : world SEGS) mem mem' sp0 V P r j,
alloc_ceiling <= sp0 - 144 - HP_STK -> 4096 <= V + AREC * j ->
(forall y, 0 <= y < 2 ^ 64 -> ~ (sp0 - 144 - HP_STK <= y < sp0 - 144) ->
   aview SEGS (w_H W') mem' y = aview SEGS (w_H W) mem y) ->
cshe_l1_rec ly S W mem sp0 V P r j -> cshe_l1_rec ly S W' mem' sp0 V P r j.
Proof.
intros ly S W W' mem mem' sp0 V P r j HCEIL HEA Hk
  (Ms & Mn & Hra16 & Hmr16 & Hoffe & Hblk & Hr0 & Hlx & Hby & Hofft & Hlp).
unfold cshe_l1_rec. cbv zeta.
assert (KEA : forall t, 0 <= t < 16 -> aview SEGS (w_H W') mem' (V + AREC * j + t) = aview SEGS (w_H W) mem (V + AREC * j + t)).
{ intros t Ht. apply Hk; [unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hmr16; lia
                         | apply Hoffe; lia]. }
split; [exact (val_mem_kept SEGS _ _ mem mem' _ 8 _ ltac:(intros t Ht; apply KEA; lia) Ms)|].
split; [refine (val_mem_kept SEGS _ _ mem mem' _ 8 _ _ Mn);
        intros t Ht; replace (V + AREC * j + 8 + t) with (V + AREC * j + (8 + t)) by lia; apply KEA; lia|].
split; [exact (cshe_ra_kept W W' mem mem' _ 16 _ _ HCEIL Hmr16 ltac:(lia) Hk Hra16)|].
split; [exact Hmr16|]. split; [exact Hoffe|]. split; [exact Hblk|].
split; [exact Hr0|]. split; [exact Hlx|].
split; [apply (cshe_bytes_kept W W' mem mem' (fst r) _ (sp0 - 144 - HP_STK) (sp0 - 144) Hk);
        [intros t Ht; rewrite length_app in Ht; cbn [length] in Ht;
         split; [lia | apply Hofft; lia] | exact Hby]|].
split; [exact Hofft|].
intros Hle. destruct (Hlp Hle) as (Hmrp & Hrap & Hshvp).
split; [exact Hmrp|].
split; [exact (cshe_ra_kept W W' mem mem' (fst r) (Z.of_nat (length P)) _ _ HCEIL Hmrp ltac:(lia) Hk Hrap)|].
intros Hp. exact (cshe_shv_kept W W' mem mem' (fst r) (Z.of_nat (length P)) _ _ HCEIL Hmrp ltac:(lia) Hp Hk (Hshvp Hp)).
Qed.

(* Loop 1 in full: from the head with i records counted to 0x85498, with a1 = want_of P (the whole vector).
   s6 = 0, s4 = v + 16 n, s11 = s4 + 8, s7 = SB + s4 / 8; every other callee-saved register is the caller's,
   and only has_prefix's scratch [sp - HP_STK, sp) changed. *)
Lemma cshe_l1_loop_x : forall (k : nat) (i : Z) (W : world SEGS) ly S hp regs mem md
ly0 S0 hp0 (W0 : world SEGS) mem0 md0 XO AT FP sp0 kk PF (P : list byte) (V N : Z) (recs : list (Z * list byte)),
Z.of_nat k = N - i -> 0 <= i < N -> N = Z.of_nat (length recs) -> N < 2 ^ 26 ->
Z.of_nat (length P) + 1 < 2 ^ 32 -> 0 < PF -> PF + Z.of_nat (length P) + 1 <= 2 ^ 63 ->
~ In (Z_to_bv 8 0) P ->
4096 <= V -> V + AREC * N <= 140737479966720 -> V mod 16 = 0 ->
getr regs 2 = w64 (sp0 - 144) ->
getr regs 11 = w64 (Z.of_nat (CheckRep.want_of P (firstn (Z.to_nat i) recs))) ->
getr regs 22 = w64 (N - i) ->
getr regs 20 = w64 (V + AREC * i) -> getr regs 27 = w64 (V + AREC * i + 8) ->
getr regs 23 = w64 (SB + (V + AREC * i) / 8) -> getr regs 25 = w64 SB -> getr regs 9 = w64 PF ->
getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) -> s0Z regs < alloc_ceiling ->
2 ^ 46 <= sp0 - 144 <= 2 ^ 47 -> (sp0 - 144) mod 16 = 0 ->
XO mod 16 = 0 -> alloc_ceiling + CSHE_STK <= sp0 ->
ajournal_gx_x SEGS B PST ARx G XO [(AT, AT + 8)] CSHE_STK sp0 FP ly0 S0 hp0 W0 mem0 md0 [] ly S hp W mem md kk ->
cshe_l1_pfx W mem sp0 PF P -> cshe_l1_vec ly S W mem sp0 V P recs i ->
SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + A_cshe_l1)) mem (seg_rom SEGS)) md)
(fun W' c' => exists regs' mem' md' a0v s5v,
 c' = mkCfg (mkst regs' (Z_to_bv 64 (BASE + A_cshe_tst + 4)) mem' (seg_rom SEGS)) md' /\
 ajournal_gx_x SEGS B PST ARx G XO [(AT, AT + 8)] CSHE_STK sp0 FP ly0 S0 hp0 W0 mem0 md0 [] ly S hp W' mem' md' kk /\
 getr regs' 11 = w64 (Z.of_nat (CheckRep.want_of P recs)) /\
 getr regs' 10 = w64 a0v /\ getr regs' 21 = w64 s5v /\
 0 <= a0v /\ a0v <= 1 /\ 0 <= s5v /\ a0v + s5v = Z.of_nat (CheckRep.want_of P recs) /\
 getr regs' 22 = w64 0 /\ getr regs' 20 = w64 (V + AREC * N) /\
 getr regs' 27 = w64 (V + AREC * N + 8) /\ getr regs' 23 = w64 (SB + (V + AREC * N) / 8) /\
 getr regs' 2 = getr regs 2 /\ getr regs' 3 = getr regs 3 /\ getr regs' 4 = getr regs 4 /\
 getr regs' 8 = getr regs 8 /\ getr regs' 9 = getr regs 9 /\ getr regs' 18 = getr regs 18 /\
 getr regs' 19 = getr regs 19 /\ getr regs' 24 = getr regs 24 /\ getr regs' 25 = getr regs 25 /\
 getr regs' 26 = getr regs 26 /\
 (forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 144 - HP_STK <= a < sp0 - 144) ->
   aview SEGS (w_H W') mem' a = aview SEGS (w_H W) mem a) /\
 (forall a, apresent (w_H W) mem a -> apresent (w_H W') mem' a)).
Proof.
induction k as [|k IH]; intros i W ly S hp regs mem md ly0 S0 hp0 W0 mem0 md0 XO AT FP sp0 kk PF P V N recs
Hk Hi HN HN26 HP32 HPF0 HPFk HPnz HV0 HVhiN HV16 H2 H11 H22 H20 H27 H23 H25 H9 Hgp Htp Hch HSP HSPa HXO16 HCL0
HJ HPFX HVEC; [lia|].
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HCEIL : alloc_ceiling <= sp0 - 144 - HP_STK)
  by (unfold HP_STK, ESTACK, CSHE_STK, CSHE_FRAME, ASTACK in *; lia).
destruct (HVEC i ltac:(lia)) as (Ms & Mn & Hra16 & Hmr16 & Hoffe & (VB & VL & HVIN & HVlo & HVhi) & Hr0 & Hlx & Hby
  & Hofft & Hlp).
pose proof HPFX as (HPby & HPvis & HPoff & HPmr1 & HPmr8 & HPra1 & HPshv1 & HPra0 & HPshv0 & HProm).
(* the bounds of the slot and of the counter *)
assert (HEAlo : 4096 <= V + AREC * i) by (unfold AREC; lia).
assert (HEAhi : V + AREC * i + 16 <= 140737479966720) by (unfold AREC in HVhiN |- *; lia).
assert (HEAal : (V + AREC * i) mod 16 = 0).
{ unfold AREC. apply Z.mod_divide in HV16; [|lia]. destruct HV16 as (qq & Hq). rewrite Hq.
  apply Z.mod_divide; [lia|]. exists (qq + i). lia. }
assert (HWlo : (CheckRep.want_of P (firstn (Z.to_nat i) recs) <= Z.to_nat i)%nat).
{ pose proof (cshe_want_le P (firstn (Z.to_nat i) recs)) as HWle. rewrite length_firstn in HWle. lia. }
(* the prefix, in the premises has_prefix takes *)
assert (HFB : first_byte SEGS W mem PF (Z.of_nat (length P) + 1) 0 (Z.of_nat (length P))).
{ split; [lia|]. split.
  - intros t Ht. rewrite (HPby t ltac:(rewrite length_app; cbn [length]; lia)).
    rewrite app_nth1 by lia.
    eexists. split; [reflexivity|]. intros Hc. apply HPnz.
    assert (Hz : nth (Z.to_nat t) P (Z_to_bv 8 0) = Z_to_bv 8 0) by (apply bv_eq; rewrite Hc; reflexivity).
    rewrite <- Hz. apply nth_In. lia.
  - intros _. rewrite (HPby (Z.of_nat (length P)) ltac:(rewrite length_app; cbn [length]; lia)).
    rewrite app_nth2 by lia.
    replace (Z.to_nat (Z.of_nat (length P)) - length P)%nat with 0%nat by lia. cbn [nth].
    reflexivity. }
assert (HVISp : hp_vis W mem PF (Z.of_nat (length P) + 1)) by (intros a Ha; apply HPvis; lia).
assert (HTAILp : forall a, PF + Z.of_nat (length P) < a <
  PF + Z.of_nat (length P) - (PF + Z.of_nat (length P)) mod 8 + 8 -> aview SEGS (w_H W) mem a <> None).
{ intros a Ha. apply HPvis. pose proof (Z.mod_pos_bound (PF + Z.of_nat (length P)) 8 ltac:(lia)). lia. }
(* one turn *)
eapply SRr_bind.
{ refine (cshe_l1_run_x W ly S hp regs mem md (V + AREC * i) (fst (nth (Z.to_nat i) recs (0, [])))
    (Z.of_nat (length (snd (nth (Z.to_nat i) recs (0, [])))))
    (Z.of_nat (CheckRep.want_of P (firstn (Z.to_nat i) recs))) (N - i) ly0 S0 hp0 W0 mem0 md0 XO AT FP sp0 kk PF
    (Z.of_nat (length P))
    H2 H11 H22 H20 H27 H23 H25 HSP HSPa ltac:(lia) ltac:(lia) HEAlo HEAhi HEAal
    ltac:(lia) ltac:(lia) Ms Mn Hra16 Hmr16 HJ H9 ltac:(lia) ltac:(lia) HPF0
    ltac:(lia) HFB HVISp HPmr1 HPmr8 HPra1 HPshv1 HTAILp HProm
    ltac:(intros a Ha; apply HPoff; lia) ltac:(lia) ltac:(lia) _ Hgp Htp Hch HXO16 HCL0
    ltac:(lia) ltac:(lia) VB VL HVIN HVlo HVhi).
  intros Hle. destruct (Hlp Hle) as (Hmrp & Hrap & Hshvp).
  split.
  { intros a Ha.
    replace a with (fst (nth (Z.to_nat i) recs (0, [])) + (a - fst (nth (Z.to_nat i) recs (0, [])))) by lia.
    rewrite (Hby (a - fst (nth (Z.to_nat i) recs (0, [])))
      ltac:(rewrite length_app; cbn [length]; lia)). discriminate. }
  split; [intros a Ha; apply Hofft; lia|].
  split; [exact Hmrp|]. split; [exact Hrap|]. split; [exact Hshvp|].
  split; [exact HPra0 | exact HPshv0]. }
cbv beta. intros W' c' Hwle (regs' & mem' & md' & b & pc' & -> & HPC & HJ' & Hb01 & Hb1 & Hb0 & R11 & R10v & R21v
  & R20 & R23 & R27 & R22 & R2 & R3 & R4 & R8 & R9 & R18 & R19 & R24 & R25 & R26 & KEEP & PRES).
(* b is the record's prefixb *)
assert (HPB : (if CheckRep.prefixb P (snd (nth (Z.to_nat i) recs (0, []))) then 1 else 0) = b).
{ destruct Hb01 as [Hb | Hb]; subst b.
  - destruct (CheckRep.prefixb P (snd (nth (Z.to_nat i) recs (0, [])))) eqn:EP; [|reflexivity]. exfalso.
    destruct (proj2 (cshe_prefixb_iff W mem (fst (nth (Z.to_nat i) recs (0, []))) PF
      (snd (nth (Z.to_nat i) recs (0, []))) P Hby HPby) EP) as (Hle & Hpre).
    exact (Hb0 eq_refl Hle Hpre).
  - destruct (Hb1 eq_refl) as (Hle & Hpre).
    rewrite (proj1 (cshe_prefixb_iff W mem (fst (nth (Z.to_nat i) recs (0, []))) PF
      (snd (nth (Z.to_nat i) recs (0, []))) P Hby HPby) (conj Hle Hpre)). reflexivity. }
assert (EQW : Z.of_nat (CheckRep.want_of P (firstn (Z.to_nat (i + 1)) recs)) =
  Z.of_nat (CheckRep.want_of P (firstn (Z.to_nat i) recs)) + b).
{ replace (Z.to_nat (i + 1)) with (Datatypes.S (Z.to_nat i)) by lia.
  rewrite (cshe_want_step P recs (Z.to_nat i) ltac:(lia)), <- HPB.
  destruct (CheckRep.prefixb P (snd (nth (Z.to_nat i) recs (0, [])))); lia. }
destruct HPC as [(HCNT & ->) | (HCNT & ->)].
- (* another record: the induction hypothesis at i + 1 *)
  assert (EQ20 : V + AREC * (i + 1) = V + AREC * i + 16) by (unfold AREC; lia).
  rewrite <- EQ20 in R20. rewrite <- EQ20 in R23.
  replace (V + AREC * i + 24) with (V + AREC * (i + 1) + 8) in R27 by (unfold AREC; lia).
  replace (N - i - 1) with (N - (i + 1)) in R22 by lia.
  rewrite <- EQW in R11.
  eapply SRr_mono.
  { apply (IH (i + 1) W' ly S hp regs' mem' md' ly0 S0 hp0 W0 mem0 md0 XO AT FP sp0 kk PF P V N recs);
    [ lia | lia | exact HN | exact HN26 | exact HP32 | exact HPF0 | exact HPFk | exact HPnz | exact HV0
    | exact HVhiN | exact HV16
    | rewrite R2; exact H2 | exact R11 | exact R22 | exact R20 | exact R27 | exact R23
    | rewrite R25; exact H25 | rewrite R9; exact H9
    | rewrite R3; exact Hgp | rewrite R4; exact Htp | unfold s0Z; rewrite R8; exact Hch
    | exact HSP | exact HSPa | exact HXO16 | exact HCL0 | exact HJ'
    | exact (cshe_l1_pfx_kept W W' mem mem' sp0 PF P HCEIL HPF0 HPFk KEEP HPFX)
    | intros j Hj; exact (cshe_l1_rec_kept ly S W W' mem mem' sp0 V P _ j HCEIL
        ltac:(unfold AREC; lia) KEEP (HVEC j ltac:(lia))) ]. }
  cbv beta. intros W'' c'' Hwle2 (regs'' & mem'' & md'' & a0v & s5v & -> & HJ'' & T11 & T10 & T21 & Ta0 & Ta1 & Ts5
    & Tsum & T22 & T20 & T27 & T23 & T2 & T3 & T4
    & T8 & T9 & T18 & T19 & T24 & T25 & T26 & KEEP2 & PRES2).
  exists regs'', mem'', md'', a0v, s5v.
  split; [reflexivity|]. split; [exact HJ''|]. split; [exact T11|].
  split; [exact T10|]. split; [exact T21|]. split; [exact Ta0|]. split; [exact Ta1|].
  split; [exact Ts5|]. split; [exact Tsum|].
  split; [exact T22|]. split; [exact T20|].
  split; [exact T27|]. split; [exact T23|].
  split; [rewrite T2; exact R2|]. split; [rewrite T3; exact R3|]. split; [rewrite T4; exact R4|].
  split; [rewrite T8; exact R8|]. split; [rewrite T9; exact R9|]. split; [rewrite T18; exact R18|].
  split; [rewrite T19; exact R19|]. split; [rewrite T24; exact R24|]. split; [rewrite T25; exact R25|].
  split; [rewrite T26; exact R26|].
  split; [intros a Ha Hno; rewrite (KEEP2 a Ha Hno); exact (KEEP a Ha Hno)|].
  intros a Hp. exact (PRES2 a (PRES a Hp)).
- (* the last record: at 0x85498 *)
  assert (HiN : i + 1 = N) by lia.
  assert (EQR : firstn (Z.to_nat (i + 1)) recs = recs)
    by (replace (Z.to_nat (i + 1)) with (length recs) by lia; apply firstn_all).
  rewrite EQR in EQW.
  apply SRr_ret. exists regs', mem', md', b, (Z.of_nat (CheckRep.want_of P (firstn (Z.to_nat i) recs))).
  split; [reflexivity|]. split; [exact HJ'|].
  split; [rewrite R11, EQW; reflexivity|].
  split; [exact R10v|]. split; [exact R21v|].
  split; [destruct Hb01 as [-> | ->]; lia|]. split; [destruct Hb01 as [-> | ->]; lia|].
  split; [lia|]. split; [rewrite EQW; lia|].
  split; [rewrite R22; unfold w64; f_equal; lia|].
  split; [replace (V + AREC * N) with (V + AREC * i + 16) by (unfold AREC; lia); exact R20|].
  split; [replace (V + AREC * N + 8) with (V + AREC * i + 24) by (unfold AREC; lia); exact R27|].
  split; [replace (V + AREC * N) with (V + AREC * i + 16) by (unfold AREC; lia); exact R23|].
  split; [exact R2|]. split; [exact R3|]. split; [exact R4|]. split; [exact R8|]. split; [exact R9|].
  split; [exact R18|]. split; [exact R19|]. split; [exact R24|]. split; [exact R25|]. split; [exact R26|].
  split; [exact KEEP | exact PRES].
Qed.

(* The write obligation of the entry's runs: the frame is the function's own window, the held list's count
   cell (the one region with a writable window outside the frame) is a byte of G, the other three regions
   have no writable byte. *)
Ltac cshe_awr_head Usp E10b HGin :=
apply awr_ok_x_cons;
[ intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val stack_region] in Ha; rewrite Usp in Ha;
  left; split; [left; unfold CSHE_STK, CSHE_FRAME, ASTACK in *; lia | lia] |];
apply awr_ok_x_cons; [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi got_regionP] in Ha; lia|];
apply awr_ok_x_cons; [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi bcell_regionP] in Ha; lia|];
apply awr_ok_x_cons_g;
[ intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val cshe_hd] in Ha;
  rewrite E10b in Ha; rewrite unsigned_lit_small in Ha by lia; apply HGin; lia |];
apply awr_ok_x_cons; [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi cshe_gone] in Ha; lia|];
apply awr_ok_x_nil.
(* Reading a region's chunk back out of a symbolic state: what the frame's saved slots and the cells the walk
   stored are worth at the state the run ended in (YN0d's st_ok_chunk / chunk_bytes_cval). *)
Lemma cshe_st_chunk : forall E ss (Hh : word -> bool) ms i r c,
st_ok_pi SEGS VAL E ss (restrict Hh ms) -> nth_error (ss_mem ss) i = Some r -> In c (YP09.r_chunks r) ->
YP09.chunk_ok SEGS E (mrestrict Hh (ms_mem ms)) (base_val E (YP09.r_base r)) c.
Proof.
intros E ss Hh ms i r c HS Hi Hc. unfold st_ok_pi in HS.
exact (YN0d.st_ok_chunk SEGS E _ (restrict Hh ms) i r c HS Hi Hc).
Qed.
Lemma cshe_chunk_val : forall E (m : word -> option byte) base off (w : N) (e : sv) (v : Z),
bv_unsigned (sv_denot E e) = v ->
YP09.chunk_ok SEGS E m base (YP09.mkChunk off (CVal w e)) -> val_mem SEGS m (base + off) (N.to_nat w) v.
Proof.
intros E m base off w e v Hv Hc k Hk.
exact (YN0d.chunk_bytes_cval SEGS E m base off w e v Hc ltac:(rewrite Hv; reflexivity) k Hk).
Qed.
(* An atom's word, as the chunk of a saved slot carries it. *)
Lemma cshe_soff_u : forall E n, bv_unsigned (sv_denot E (SOff n 0)) = bv_unsigned (ew E n).
Proof.
intros E n. change (bv_unsigned (sv_denot E (SOff n 0))) with (U E (SOff n 0)).
rewrite U_SOff, Z.add_0_r. apply zcanon_id.
pose proof (bv_unsigned_in_range 64 (ew E n)). change (bv_modulus 64) with (2 ^ 64) in *.
unfold M64. lia.
Qed.
(* Where the prologue put each callee-saved register, as an offset of the entry sp. *)
Definition cshe_slot_off (n : nat) : Z :=
match n with
| 1%nat => -8 | 8%nat => -16 | 9%nat => -24 | 18%nat => -32 | 19%nat => -40 | 20%nat => -48
| 21%nat => -56 | 22%nat => -64 | 23%nat => -72 | 24%nat => -80 | 25%nat => -88 | 26%nat => -96
| _ => -104
end.
Definition cshe_slot_regs : list nat := [1;8;9;18;19;20;21;22;23;24;25;26;27]%nat.
(* The thirteen saved slots, read back out of the frame region of a state the walk reached. *)
Lemma cshe_saved_of_state : forall E ss (W : world SEGS) ms r (regs0 : bvmap 5 word) sp0,
st_ok_pi SEGS VAL E ss (restrict (w_H W) ms) ->
nth_error (ss_mem ss) 0%nat = Some r ->
base_val E (YP09.r_base r) = sp0 ->
(forall n, In n cshe_slot_regs ->
   In (YP09.mkChunk (cshe_slot_off n) (CVal 8 (SOff n 0))) (YP09.r_chunks r) /\
   ew E n = getr regs0 (Z_to_bv 5 (Z.of_nat n))) ->
cshe_saved W (ms_mem ms) sp0 regs0.
Proof.
intros E ss W ms r regs0 sp0 HS Hi Hb Hall.
assert (SL : forall n, In n cshe_slot_regs ->
  val_mem SEGS (mrestrict (w_H W) (ms_mem ms)) (sp0 + cshe_slot_off n) 8
    (bv_unsigned (getr regs0 (Z_to_bv 5 (Z.of_nat n))))).
{ intros n Hn. destruct (Hall n Hn) as [Hin He].
  pose proof (cshe_st_chunk E ss (w_H W) ms 0%nat r _ HS Hi Hin) as HC.
  rewrite Hb in HC.
  pose proof (cshe_chunk_val E _ sp0 (cshe_slot_off n) 8 (SOff n 0) _ (cshe_soff_u E n) HC) as HV.
  rewrite He in HV. exact HV. }
unfold cshe_saved. repeat split;
  [ replace (sp0 - 8) with (sp0 + cshe_slot_off 1) by (cbn; lia)
  | replace (sp0 - 16) with (sp0 + cshe_slot_off 8) by (cbn; lia)
  | replace (sp0 - 24) with (sp0 + cshe_slot_off 9) by (cbn; lia)
  | replace (sp0 - 32) with (sp0 + cshe_slot_off 18) by (cbn; lia)
  | replace (sp0 - 40) with (sp0 + cshe_slot_off 19) by (cbn; lia)
  | replace (sp0 - 48) with (sp0 + cshe_slot_off 20) by (cbn; lia)
  | replace (sp0 - 56) with (sp0 + cshe_slot_off 21) by (cbn; lia)
  | replace (sp0 - 64) with (sp0 + cshe_slot_off 22) by (cbn; lia)
  | replace (sp0 - 72) with (sp0 + cshe_slot_off 23) by (cbn; lia)
  | replace (sp0 - 80) with (sp0 + cshe_slot_off 24) by (cbn; lia)
  | replace (sp0 - 88) with (sp0 + cshe_slot_off 25) by (cbn; lia)
  | replace (sp0 - 96) with (sp0 + cshe_slot_off 26) by (cbn; lia)
  | replace (sp0 - 104) with (sp0 + cshe_slot_off 27) by (cbn; lia) ];
  first [ exact (SL 1%nat ltac:(cbv; tauto)) | exact (SL 8%nat ltac:(cbv; tauto))
        | exact (SL 9%nat ltac:(cbv; tauto)) | exact (SL 18%nat ltac:(cbv; tauto))
        | exact (SL 19%nat ltac:(cbv; tauto)) | exact (SL 20%nat ltac:(cbv; tauto))
        | exact (SL 21%nat ltac:(cbv; tauto)) | exact (SL 22%nat ltac:(cbv; tauto))
        | exact (SL 23%nat ltac:(cbv; tauto)) | exact (SL 24%nat ltac:(cbv; tauto))
        | exact (SL 25%nat ltac:(cbv; tauto)) | exact (SL 26%nat ltac:(cbv; tauto))
        | exact (SL 27%nat ltac:(cbv; tauto)) ].
Qed.
(* The two cells cshe_head's post hands on, read out of the state the run ended in: the thirteen saved
   slots, and held.n (the one byte range the entry's state declares writable outside the frame). *)
Ltac cshe_head_saved HS Usp EEo :=
eapply (cshe_saved_of_state _ _ _ _ _ _ _ HS);
[ cbn [ss_mem]; reflexivity
| cbn [YP09.r_base base_val]; exact Usp
| intros nn Hnn; cbv [cshe_slot_regs] in Hnn; cbn [In] in Hnn;
  destruct Hnn as [Hq|[Hq|[Hq|[Hq|[Hq|[Hq|[Hq|[Hq|[Hq|[Hq|[Hq|[Hq|[Hq|[]]]]]]]]]]]]]];
  rewrite <- Hq;
  (split; [cbn [cshe_slot_off YP09.r_chunks In]; repeat first [left; reflexivity | right]
         | apply EEo; reflexivity]) ].
Ltac cshe_head_heldn HS Uha UN :=
let HCn := fresh "HCn" in
let Hin := fresh "Hin" in
assert (Hin : In (YP09.mkChunk 88 (CVal 4 (SOff 35 0))) (YP09.r_chunks cshe_hd))
  by (unfold cshe_hd; cbn [YP09.r_chunks In]; right; left; reflexivity);
pose proof (cshe_st_chunk _ _ _ _ 3%nat cshe_hd (YP09.mkChunk 88 (CVal 4 (SOff 35 0))) HS
  ltac:(cbn [ss_mem]; reflexivity) Hin) as HCn;
cbn [YP09.r_base cshe_hd] in HCn; rewrite Uha in HCn;
exact (cshe_chunk_val _ _ _ 88 4 (SOff 35 0) _ UN HCn).
(* ---- the entry 0x853b0 to loop 1's head 0x85450, or straight to the epilogue when the list is empty ---- *)
Lemma cshe_head_x : forall W ly S hp regs mem md ch HA gone V N CAP XO AT FP PF,
afn_pre_x SEGS B ARx CSHE_STK ly S hp W regs mem md ch ->
0 <= XO -> XO mod 16 = 0 -> spZ regs + XO <= ly_top ly ->
(forall a, spZ regs <= a < spZ regs + XO -> apresent (w_H W) mem a) ->
getr regs 10 = w64 HA -> getr regs 11 = w64 PF -> getr regs 12 = w64 AT ->
HA mod 8 = 0 -> 4096 <= HA -> HA + ASRC <= 0x5fb000 -> azs B (HA + 64) 32 ->
(forall a, HA + 64 <= a < HA + 96 -> inG G a) ->
(HA + ASRC <= VAL (A_OBJ 0) \/ VAL (A_OBJ 0) + 8 <= HA) ->
(HA + ASRC <= VAL (A_OBJ 32) \/ VAL (A_OBJ 32) + 8 <= HA) ->
(HA + ASRC <= VAL A_g_gone \/ VAL A_g_gone + 1 <= HA) ->
val_mem SEGS (mrestrict (w_H W) mem) (VAL A_g_gone) 1 gone -> 0 <= gone < 256 ->
val_mem SEGS (mrestrict (w_H W) mem) (HA + 80) 8 V -> 0 <= V < 140737479966720 -> V mod 16 = 0 ->
val_mem SEGS (mrestrict (w_H W) mem) (HA + 88) 4 N -> 0 <= N < 2 ^ 26 ->
val_mem SEGS (mrestrict (w_H W) mem) (HA + 92) 4 CAP -> 0 <= CAP < 2 ^ 30 ->
awr W mem (HA + 80) 16 ->
SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 A_csheP) mem (seg_rom SEGS)) md)
(fun W' c' => exists regs' mem' md' pc',
 c' = mkCfg (mkst regs' (Z_to_bv 64 pc') mem' (seg_rom SEGS)) md' /\
 ajournal_gx_x SEGS B PST ARx G XO [(AT, AT + 8)] CSHE_STK (spZ regs) FP ly S hp W mem md [] ly S hp W' mem' md' 0 /\
 getr regs' 1 = getr regs 1 /\ getr regs' 2 = w64 (spZ regs - 144) /\
 getr regs' 3 = getr regs 3 /\ getr regs' 4 = getr regs 4 /\
 (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 144 <= a < spZ regs) -> ~ (HA + 88 <= a < HA + 92) ->
   aview SEGS (w_H W') mem' a = aview SEGS (w_H W) mem a) /\
 (* the same with no hole: the entry only READS held.n, so its four bytes are the caller's too (the clause
    above has the hole because cshe_hd declares them writable) *)
 (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 144 <= a < spZ regs) ->
   aview SEGS (w_H W') mem' a = aview SEGS (w_H W) mem a) /\
 (forall a, apresent (w_H W) mem a -> apresent (w_H W') mem' a) /\
 cshe_saved W' mem' (spZ regs) regs /\
 val_mem SEGS (mrestrict (w_H W') mem') (HA + 88) 4 N /\
 ((0 < N /\ pc' = BASE + A_cshe_l1 /\
   (* the count cell the entry wrote at sp + 8 (0x8544c `sd s6,8(sp)`), which the 0x85498 state reads *)
   val_mem SEGS (mrestrict (w_H W') mem') (spZ regs - 136) 8 N /\
   (* the shadow cell of &held.n the entry wrote at sp + 16 (0x85404 `sd a2,16(sp)`), which loops 2 and 3 reload *)
   val_mem SEGS (mrestrict (w_H W') mem') (spZ regs - 128) 8 ((HA + 88) / 8 + SB) /\
   getr regs' 8 = w64 (HA + 88) /\ getr regs' 9 = w64 PF /\ getr regs' 11 = w64 0 /\
   getr regs' 18 = w64 (HA + 80) /\ getr regs' 19 = w64 AT /\ getr regs' 20 = w64 V /\
   getr regs' 22 = w64 N /\ getr regs' 23 = w64 (SB + V / 8) /\ getr regs' 24 = w64 N /\
   getr regs' 25 = w64 SB /\ getr regs' 26 = w64 ((HA + 80) / 8 + SB) /\ getr regs' 27 = w64 (V + 8)) \/
  (N = 0 /\ pc' = BASE + A_cshe_ret))).
Proof.
intros W ly S hp regs mem md ch HA gone V N CAP XO AT FP PF HPRE HXO0 HXO16 HXtop HXp H10 H11 H12
  Hal8 Hlo Hhi Hzs HGin Hd0 Hd32 Hdg Mg Rg MV RV AV MN RN MC RC Hawr.
assert (HhiA : HA + 96 <= 0x5fb000) by (unfold ASRC in Hhi; lia).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
destruct (cshe_entry_x W ly S hp regs mem md ch HA gone V N CAP HPRE H10 Hal8 Hlo Hhi Hzs Hd0 Hd32 Hdg Mg Rg
  MV RV AV MN RN MC RC Hawr) as [HS SHOK].
pose proof (ajournal_gx_init_x SEGS B PST ARx G XO [(AT, AT + 8)] CSHE_STK FP ly S hp W regs mem md ch HPRE
  HXO0 HXO16 HXtop HXp) as HJ.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hshlo & Hshhi & H47 & Hbot & Htop & Htop2).
remember (Eimg (Ereg regs (cshe_extra gone V N CAP))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (E2 : ew E 2 = getr regs 2)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (E10b : ew E 10 = Z_to_bv 64 HA)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E1 : ew E 1 = getr regs 1)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (E3 : ew E 3 = getr regs 3)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 3 3%bv eq_refl)).
assert (E4 : ew E 4 = getr regs 4)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 4 4%bv eq_refl)).
assert (E11b : ew E 11 = Z_to_bv 64 PF)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
assert (E12b : ew E 12 = Z_to_bv 64 AT)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 12 12%bv eq_refl); exact H12).
assert (E33 : ew E 33 = Z_to_bv 64 SB)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 V)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 N)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 3)).
assert (EEo : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs rr).
{ intros n rr Hn. subst E. pose proof (bv_unsigned_in_range 5 rr) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn. }
assert (Uha : base_val E (Some 10%nat) = HA)
  by (cbn [base_val]; rewrite E10b; apply unsigned_lit_small; lia).
assert (UN : bv_unsigned (sv_denot E (SOff 35 0)) = N) by exact (U_atom E 35 N E35 ltac:(lia)).
assert (SN : bv_signed (sv_denot E (SOff 35 0)) = N)
  by (rewrite bv_signed_small; [exact UN | rewrite UN; lia]).
assert (U0 : bv_unsigned (sv_denot E (SLit 0)) = 0) by exact (U_lit E 0 ltac:(lia)).
assert (S0 : bv_signed (sv_denot E (SLit 0)) = 0)
  by (rewrite bv_signed_small; [exact U0 | rewrite U0; lia]).
unfold A_csheP, A_cshe.
pose (RUNx := paj_run_x_x B PST ARx LAWS G HG XO [(AT, AT + 8)]).
paj_run_tok_x RUNx HS HJ SHOK Bspan.
{ cshe_awr_head Usp E10b HGin. }
pose (RUNTOx := paj_run_to_x_x B PST ARx LAWS G HG XO [(AT, AT + 8)]).
(* every byte the entry writes is a frame byte or the held list's count cell *)
assert (KEEP1 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 144 <= a < spZ regs) -> ~ (HA + 88 <= a < HA + 92) ->
  aview SEGS (w_H W) (ms_mem ms) a = aview SEGS (w_H W) mem a).
{ intros a Ha H1 H2.
  lazymatch goal with Hf : frame_of ?Ev ?rs (mrestrict (w_H W) mem) _ |- _ =>
    apply (aview_kept_out Ev rs (w_H W) _ _ Hf a Ha) end.
  intros (r & Hin & Hr). unfold ss_cshe, cshe_regions in Hin. cbn [ss_mem In] in Hin.
  destruct Hin as [<- | [<- | [<- | [<- | [<- | []]]]]];
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val stack_region got_regionP bcell_regionP
       cshe_hd cshe_gone CSHE_FRAME] in Hr;
  try (unfold CSHE_FRAME in Hr); rewrite ?Usp, ?E10b in Hr;
  try (rewrite unsigned_lit_small in Hr by lia). all: lia. }
pose proof HG0 as GROW1.
psrr_branch_tok RUNx BR HS SHOK Bspan.
- (* the held list is empty: straight to the epilogue *)
  assert (HN0 : N = 0).
  { cbn [branch_taken] in Hc. rewrite bv_lts_signed in Hc.
    apply (proj1 (Bool.negb_true_iff _)) in Hc. apply Z.ltb_ge in Hc. rewrite SN, S0 in Hc. lia. }
  paj_run_to_tok_x RUNTOx HS HJ SHOK Bspan A_cshe_ret.
  { cshe_awr_head Usp E10b HGin. }
  prreg HS (1%bv : bv 5) P1. prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
  assert (KEEP2 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 144 <= a < spZ regs) -> ~ (HA + 88 <= a < HA + 92) ->
    aview SEGS (w_H W) (ms_mem ms0) a = aview SEGS (w_H W) (ms_mem ms) a).
  { intros a Ha H1 H2.
    lazymatch goal with Hf : frame_of ?Ev ?rs (mrestrict (w_H W) (ms_mem ms)) _ |- _ =>
      apply (aview_kept_out Ev rs (w_H W) _ _ Hf a Ha) end.
    intros (r & Hin & Hr). cbn [ss_mem In] in Hin.
    repeat (destruct Hin as [<- | Hin];
      [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?Usp, ?E10b in Hr;
       try (rewrite unsigned_lit_small in Hr by lia); lia|]). destruct Hin. }
  pmkst HS. apply SRr_ret.
  lazymatch goal with |- context [mkCfg (mkst (ms_regs ?msx) _ _ _) ?mdx] =>
    exists (ms_regs msx), (ms_mem msx), mdx, (BASE + A_cshe_ret) end.
  split; [reflexivity|]. split; [exact HJ|].
  split; [cbn [ms_regs]; rewrite P1; exact E1|].
  split; [cbn [ms_regs]; rewrite P2, Usp; unfold w64; f_equal; lia|].
  split; [cbn [ms_regs]; rewrite P3; exact E3|].
  split; [cbn [ms_regs]; rewrite P4; exact E4|].
  assert (MNp : val_mem SEGS (mrestrict (w_H W) (ms_mem ms0)) (HA + 88) 4 N) by (cshe_head_heldn HS Uha UN).
  assert (KEEPF : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 144 <= a < spZ regs) ->
    aview SEGS (w_H W) (ms_mem ms0) a = aview SEGS (w_H W) mem a).
  { intros a Ha Hno.
    destruct (Z.le_gt_cases (HA + 88) a) as [Hl|Hl];
      [|rewrite (KEEP2 a Ha Hno ltac:(lia)); exact (KEEP1 a Ha Hno ltac:(lia))].
    destruct (Z.le_gt_cases (HA + 92) a) as [Hh|Hh];
      [rewrite (KEEP2 a Ha Hno ltac:(lia)); exact (KEEP1 a Ha Hno ltac:(lia))|].
    replace a with (HA + 88 + (a - (HA + 88))) by lia.
    exact (cshe_aview_of_val W W mem (ms_mem ms0) (HA + 88) 4 N MN MNp (a - (HA + 88)) ltac:(lia)). }
  split; [cbn [ms_mem]; intros a Ha H1 H2; rewrite (KEEP2 a Ha H1 H2); exact (KEEP1 a Ha H1 H2)|].
  split; [cbn [ms_mem]; exact KEEPF|].
  split.
  { cbn [ms_mem]. intros a Hp.
    lazymatch goal with Hg : mem_grows (mrestrict (w_H W) (ms_mem ms)) _ |- _ =>
      exact (apresent_grows _ _ _ _ Hg (apresent_grows _ _ _ _ GROW1 Hp)) end. }
  split; [cshe_head_saved HS Usp EEo|].
  split; [cbn [ms_mem]; exact MNp|].
  right. split; [exact HN0 | reflexivity].
- (* a record to count: on to the loop head *)
  assert (HNp : 0 < N).
  { cbn [branch_taken] in Hc. rewrite bv_lts_signed in Hc.
    apply (proj1 (Bool.negb_false_iff _)) in Hc. apply Z.ltb_lt in Hc. rewrite SN, S0 in Hc. lia. }
  paj_run_to_tok_x RUNTOx HS HJ SHOK Bspan A_cshe_l1.
  { cshe_awr_head Usp E10b HGin. }
  prreg HS (1%bv : bv 5) P1. prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
  prreg HS (8%bv : bv 5) P8. prreg HS (9%bv : bv 5) P9. prreg HS (11%bv : bv 5) P11.
  prreg HS (18%bv : bv 5) P18. prreg HS (19%bv : bv 5) P19. prreg HS (20%bv : bv 5) P20.
  prreg HS (22%bv : bv 5) P22. prreg HS (23%bv : bv 5) P23. prreg HS (24%bv : bv 5) P24.
  prreg HS (25%bv : bv 5) P25. prreg HS (26%bv : bv 5) P26. prreg HS (27%bv : bv 5) P27.
  assert (KEEP2 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 144 <= a < spZ regs) -> ~ (HA + 88 <= a < HA + 92) ->
    aview SEGS (w_H W) (ms_mem ms0) a = aview SEGS (w_H W) (ms_mem ms) a).
  { intros a Ha H1 H2.
    lazymatch goal with Hf : frame_of ?Ev ?rs (mrestrict (w_H W) (ms_mem ms)) _ |- _ =>
      apply (aview_kept_out Ev rs (w_H W) _ _ Hf a Ha) end.
    intros (r & Hin & Hr). cbn [ss_mem In] in Hin.
    repeat (destruct Hin as [<- | Hin];
      [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?Usp, ?E10b in Hr;
       try (rewrite unsigned_lit_small in Hr by lia); lia|]). destruct Hin. }
  (* the two shifted shadow-base registers *)
  assert (HD1 : 0 <= V / 8 <= V) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
  assert (HD2 : 0 <= (HA + 80) / 8 <= HA + 80)
    by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
  assert (QV : alu64 ALU_SRL (Z_to_bv 64 V) (Z_to_bv 64 3) = Z_to_bv 64 (V / 8)).
  { apply bv_eq. rewrite alu64_unsigned. cbn [zalu_raw]. rewrite !unsigned_lit_small by lia.
    change (Z.land 3 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
    unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). apply Z.mod_small. lia. }
  assert (QH : alu64 ALU_SRL (Z_to_bv 64 (HA + 80)) (Z_to_bv 64 3) = Z_to_bv 64 ((HA + 80) / 8)).
  { apply bv_eq. rewrite alu64_unsigned. cbn [zalu_raw]. rewrite !unsigned_lit_small by lia.
    change (Z.land 3 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
    unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). apply Z.mod_small. lia. }
  pmkst HS. apply SRr_ret.
  lazymatch goal with |- context [mkCfg (mkst (ms_regs ?msx) _ _ _) ?mdx] =>
    exists (ms_regs msx), (ms_mem msx), mdx, (BASE + A_cshe_l1) end.
  split; [reflexivity|]. split; [exact HJ|].
  split; [cbn [ms_regs]; rewrite P1; exact E1|].
  split; [cbn [ms_regs]; rewrite P2, Usp; unfold w64; f_equal; lia|].
  split; [cbn [ms_regs]; rewrite P3; exact E3|].
  split; [cbn [ms_regs]; rewrite P4; exact E4|].
  assert (MNp : val_mem SEGS (mrestrict (w_H W) (ms_mem ms0)) (HA + 88) 4 N) by (cshe_head_heldn HS Uha UN).
  assert (KEEPF : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 144 <= a < spZ regs) ->
    aview SEGS (w_H W) (ms_mem ms0) a = aview SEGS (w_H W) mem a).
  { intros a Ha Hno.
    destruct (Z.le_gt_cases (HA + 88) a) as [Hl|Hl];
      [|rewrite (KEEP2 a Ha Hno ltac:(lia)); exact (KEEP1 a Ha Hno ltac:(lia))].
    destruct (Z.le_gt_cases (HA + 92) a) as [Hh|Hh];
      [rewrite (KEEP2 a Ha Hno ltac:(lia)); exact (KEEP1 a Ha Hno ltac:(lia))|].
    replace a with (HA + 88 + (a - (HA + 88))) by lia.
    exact (cshe_aview_of_val W W mem (ms_mem ms0) (HA + 88) 4 N MN MNp (a - (HA + 88)) ltac:(lia)). }
  (* the count cell: the prologue's `sd s6,8(sp)` left the frame region's chunk at offset -136 of the entry sp
     holding atom 35, which is held.n *)
  assert (MSP8 : val_mem SEGS (mrestrict (w_H W) (ms_mem ms0)) (spZ regs - 136) 8 N).
  { replace (spZ regs - 136) with (spZ regs + (-136)) by lia.
    pose proof (cshe_st_chunk _ _ (w_H W) ms0 0%nat _ _ HS ltac:(cbn [ss_mem]; reflexivity)
      ltac:(cbn [YP09.r_chunks]; left; reflexivity)) as HC8.
    cbn [YP09.r_base base_val] in HC8. rewrite Usp in HC8.
    exact (cshe_chunk_val _ _ (spZ regs) (-136) 8 (SOff 35 0) N UN HC8). }
  (* the shadow cell of &held.n: the prologue's `sd a2,16(sp)` (0x85404) left the frame region's chunk at offset
     -128 of the entry sp holding s0 >> 3 + s9 = (HA + 88) / 8 + SB *)
  assert (MSP16 : val_mem SEGS (mrestrict (w_H W) (ms_mem ms0)) (spZ regs - 128) 8 ((HA + 88) / 8 + SB)).
  { replace (spZ regs - 128) with (spZ regs + (-128)) by lia.
    pose proof (cshe_st_chunk _ _ (w_H W) ms0 0%nat _ _ HS ltac:(cbn [ss_mem]; reflexivity)
      ltac:(cbn [YP09.r_chunks]; right; left; reflexivity)) as HC16.
    cbn [YP09.r_base base_val] in HC16. rewrite Usp in HC16.
    apply (cshe_chunk_val E (mrestrict (w_H W) (ms_mem ms0)) (spZ regs) (-128) 8
      (SAlu ALU_ADD (SAlu ALU_SRL (SOff 10 88) (SLit 3)) (SOff 33 0)) ((HA + 88) / 8 + SB)); [|exact HC16].
    change (bv_unsigned (sv_denot E (SAlu ALU_ADD (SAlu ALU_SRL (SOff 10 88) (SLit 3)) (SOff 33 0))))
      with (U E (SAlu ALU_ADD (SAlu ALU_SRL (SOff 10 88) (SLit 3)) (SOff 33 0))).
    assert (D : 0 <= (HA + 88) / 8 < 2 ^ 60) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
    rewrite !U_SAlu, (U_atom_off E 10 HA 88 E10b), (U_atom E 33 SB E33), U_lit by (unfold SB in *; lia).
    cbn [zalu_raw]. change (Z.land 3 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
    unfold zcanon, M64. rewrite (Z.mod_small ((HA + 88) / 8)) by lia.
    unfold SB in *. rewrite Z.mod_small by lia. lia. }
  split; [cbn [ms_mem]; intros a Ha H1 H2; rewrite (KEEP2 a Ha H1 H2); exact (KEEP1 a Ha H1 H2)|].
  split; [cbn [ms_mem]; exact KEEPF|].
  split.
  { cbn [ms_mem]. intros a Hp.
    lazymatch goal with Hg : mem_grows (mrestrict (w_H W) (ms_mem ms)) _ |- _ =>
      exact (apresent_grows _ _ _ _ Hg (apresent_grows _ _ _ _ GROW1 Hp)) end. }
  split; [cshe_head_saved HS Usp EEo|].
  split; [cbn [ms_mem]; exact MNp|].
  left. split; [exact HNp|]. split; [reflexivity|].
  split; [cbn [ms_mem]; exact MSP8|].
  split; [cbn [ms_mem]; exact MSP16|].
  split; [cbn [ms_regs]; rewrite P8, E10b, unsigned_lit_small by lia; reflexivity|].
  split; [cbn [ms_regs]; rewrite P9; exact E11b|].
  split; [cbn [ms_regs]; rewrite P11; reflexivity|].
  split; [cbn [ms_regs]; rewrite P18, E10b, unsigned_lit_small by lia; reflexivity|].
  split; [cbn [ms_regs]; rewrite P19; exact E12b|].
  split; [cbn [ms_regs]; rewrite P20; exact E34|].
  split; [cbn [ms_regs]; rewrite P22; exact E35|].
  split.
  { cbn [ms_regs]. rewrite P23, E33, E34, QV, !zalu64_sound. unfold w64. f_equal.
    unfold zalu64, zalu_raw, zcanon, M64.
    rewrite (Z.mod_small SB) by (unfold SB; lia). rewrite (Z.mod_small (V / 8)) by lia.
    apply Z.mod_small. unfold SB in *. lia. }
  split; [cbn [ms_regs]; rewrite P24; exact E35|].
  split; [cbn [ms_regs]; rewrite P25; exact E33|].
  split.
  { cbn [ms_regs]. rewrite P26, E33, E10b, unsigned_lit_small by lia. rewrite QH, !zalu64_sound.
    unfold w64. f_equal. unfold zalu64, zalu_raw, zcanon, M64.
    rewrite (Z.mod_small SB) by (unfold SB; lia). rewrite (Z.mod_small ((HA + 80) / 8)) by lia.
    apply Z.mod_small. unfold SB in *. lia. }
  cbn [ms_regs]. rewrite P27, E34, unsigned_lit_small by lia. reflexivity.
Qed.

(* ------------------------------------------------------------------ 0x85498: the g_gone branch *)
(* The state loop 1 leaves at 0x85498 (A_cshe_tst + 4), as the two paths out of it read it.  VE = v + 16 n is
   the vector's end, SBV its shadow byte, SBH the shadow byte of &held.v; a0v + s5v = want is what loop 3
   recomputes want from (0x8557c `add a0,a0,s5`). *)
Definition cshe_tst_regs (regs : bvmap 5 word) (sp0 HA PF AT VE SBV SBH N a0v s5v want : Z) : Prop :=
getr regs 2 = w64 (sp0 - 144) /\ getr regs 8 = w64 (HA + 88) /\ getr regs 9 = w64 PF /\
getr regs 10 = w64 a0v /\ getr regs 11 = w64 want /\ getr regs 18 = w64 (HA + 80) /\
getr regs 19 = w64 AT /\ getr regs 20 = w64 VE /\ getr regs 21 = w64 s5v /\ getr regs 22 = w64 0 /\
getr regs 23 = w64 SBV /\ getr regs 24 = w64 N /\ getr regs 25 = w64 SB /\ getr regs 26 = w64 SBH /\
getr regs 27 = w64 (VE + 8).
Definition cshe_tst_ok (sp0 HA N a0v s5v want gone : Z) : Prop :=
2 ^ 46 <= sp0 - 144 <= 2 ^ 47 /\ (sp0 - 144) mod 16 = 0 /\
4096 <= HA /\ HA + 96 <= 140737479966720 /\ HA mod 8 = 0 /\
0 <= N < 2 ^ 26 /\ 0 <= a0v <= 2 /\ 0 <= want < 2 ^ 26 /\ 0 <= s5v < 2 ^ 26 /\ 0 <= gone < 256 /\
a0v + s5v = want.
(* the frame, with the count cell the entry wrote at sp + 8; the gone <> 0 path writes nothing, the gone = 0
   path overwrites sp + 8 with (&held.n) mod 8 + 3 *)
Definition cshe_tstR0 : YP09.region := YP09.mkRegion (Some 2%nat) 0 144 0 0
[YP09.mkChunk 8 (CVal 8 (SOff 33 0))].
Definition cshe_tstRw : YP09.region := YP09.mkRegion (Some 2%nat) 0 144 8 16
[YP09.mkChunk 8 (CVal 8 (SOff 33 0))].
Definition cshe_tst_facts : facts :=
mkFacts [ (2%nat, mkAF (2^46) (2^47) 4); (8%nat, mkAF 4096 140737479966720 0); (10%nat, mkAF 0 2 0);
(11%nat, mkAF 0 (2 ^ 26) 0); (21%nat, mkAF 0 (2 ^ 26) 0); (24%nat, mkAF 0 (2 ^ 26) 0);
(32%nat, mkAF 0 255 0); (33%nat, mkAF 0 (2 ^ 26) 0) ] [] [].
Definition ss_cshe_tst0 : sstate :=
mkSS (A_cshe_tst + 4) sr_atoms [ cshe_tstR0; cshe_gone ] None cshe_tst_facts.
Definition ss_cshe_tstw : sstate :=
mkSS (A_cshe_tst + 4) sr_atoms [ cshe_tstRw; cshe_gone ] None cshe_tst_facts.
Definition cshe_tst_extra (gone N : Z) : list word := map (Z_to_bv 64) [gone; N].

Lemma cshe_tst_state : forall (W : world SEGS) regs mem sp0 HA PF AT VE SBV SBH gone N a0v s5v want,
cshe_tst_regs regs sp0 HA PF AT VE SBV SBH N a0v s5v want ->
cshe_tst_ok sp0 HA N a0v s5v want gone ->
val_mem SEGS (mrestrict (w_H W) mem) (sp0 - 136) 8 N ->
val_mem SEGS (mrestrict (w_H W) mem) (VAL A_g_gone) 1 gone ->
(forall a, sp0 - 144 <= a < sp0 -> apresent (w_H W) mem a) ->
st_ok_pi SEGS VAL (Eimg (Ereg regs (cshe_tst_extra gone N))) ss_cshe_tst0
  (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + A_cshe_tst + 4)) mem (seg_rom SEGS))) /\
st_ok_pi SEGS VAL (Eimg (Ereg regs (cshe_tst_extra gone N))) ss_cshe_tstw
  (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + A_cshe_tst + 4)) mem (seg_rom SEGS))).
Proof.
intros W regs mem sp0 HA PF AT VE SBV SBH gone N a0v s5v want
  (R2 & R8 & R9 & R10 & R11 & R18 & R19 & R20 & R21 & R22 & R23 & R24 & R25 & R26 & R27)
  (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11) MN Mg Hpres.
pose proof pa_B_ok as HBASE. pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
pose proof (pa_obj_img 30 ltac:(lia)) as HgR. change (A_OBJ 30) with A_g_gone in HgR.
pose proof (pa_val_range A_g_gone) as HgV.
set (E := Eimg (Ereg regs (cshe_tst_extra gone N))).
assert (E2 : ew E 2 = Z_to_bv 64 (sp0 - 144))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); exact R2).
assert (E8 : ew E 8 = Z_to_bv 64 (HA + 88))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 8 8%bv eq_refl); exact R8).
assert (E10 : ew E 10 = Z_to_bv 64 a0v)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact R10).
assert (E11 : ew E 11 = Z_to_bv 64 want)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact R11).
assert (E21 : ew E 21 = Z_to_bv 64 s5v)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 21 21%bv eq_refl); exact R21).
assert (E24 : ew E 24 = Z_to_bv 64 N)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 24 24%bv eq_refl); exact R24).
assert (E32 : ew E 32 = Z_to_bv 64 gone)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 N)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (Eg : ew E A_g_gone = Z_to_bv 64 (VAL A_g_gone))
  by (subst E; apply Eimg_img; unfold A_g_gone, A_OBJ, A_TEXT, A_LIM; lia).
assert (Usp : base_val E (Some 2%nat) = sp0 - 144)
  by (cbn [base_val]; rewrite E2; apply unsigned_lit_small; lia).
assert (Ugo : base_val E (Some A_g_gone) = VAL A_g_gone)
  by (cbn [base_val]; rewrite Eg; apply unsigned_lit_small; lia).
assert (HCH : Forall (YP09.chunk_ok SEGS E (mrestrict (w_H W) mem) (sp0 - 144))
  (YP09.r_chunks cshe_tstR0)).
{ unfold cshe_tstR0. cbn [YP09.r_chunks]. constructor; [|constructor].
  apply (chunk_ok_val SEGS E _ (sp0 - 144) 8 8 (SOff 33 0) N);
  [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
  replace (sp0 - 144 + 8) with (sp0 - 136) by lia. exact MN. }
assert (HCG : Forall (YP09.chunk_ok SEGS E (mrestrict (w_H W) mem) (VAL A_g_gone)) (YP09.r_chunks cshe_gone)).
{ unfold cshe_gone. cbn [YP09.r_chunks]. constructor; [|constructor].
  apply (chunk_ok_val SEGS E _ (VAL A_g_gone) 0 1 (SOff 32 0) gone);
  [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia |].
  rewrite Z.add_0_r. exact Mg. }
assert (HDJ : forall rl, rl = [ cshe_tstR0; cshe_gone ] \/ rl = [ cshe_tstRw; cshe_gone ] ->
  pairwise_disjoint E rl).
{ intros rl Hrl. apply pairwise_disjoint_of_extents.
  destruct Hrl as [-> | ->]; unfold cshe_tstR0, cshe_tstRw, cshe_gone, extent_of_region;
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi]; rewrite Usp, Ugo;
  cbn [zpairwise_disjoint zall_disjoint]; unfold zdisj; cbn [fst snd];
  revert HgR HgV K1 C1 C5; clear; unfold kLowMemEnd; intros; repeat split; lia. }
assert (HFA : atoms_ok E (f_atoms cshe_tst_facts) /\ True /\ True).
{ split; [|split; [exact I | exact I]].
  cbn [cshe_tst_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite E2, E8, E10, E11, E21, E24, E32, E33, !unsigned_lit_small by lia.
  change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
  repeat match goal with |- _ /\ _ => split end; lia. }
replace (BASE + A_cshe_tst + 4) with (BASE + (A_cshe_tst + 4)) by lia.
split.
- rewrite restrict_mkst_fx. unfold ss_cshe_tst0. apply pa_entry_st_ok_full.
  + subst E; apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + constructor; [|constructor; [|constructor]]; unfold region_ok.
    * cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi cshe_tstR0 ms_mem mkst].
      rewrite Usp. split; [lia|]. split; [lia|]. split; [intros o Ho; lia | exact HCH].
    * cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi cshe_gone ms_mem mkst].
      rewrite Ugo. split; [lia|]. split; [lia|]. split; [intros o Ho; lia | exact HCG].
  + exact (HDJ _ (or_introl eq_refl)).
  + exact HFA.
- rewrite restrict_mkst_fx. unfold ss_cshe_tstw. apply pa_entry_st_ok_full.
  + subst E; apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + constructor; [|constructor; [|constructor]]; unfold region_ok.
    * cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi cshe_tstRw ms_mem mkst].
      rewrite Usp. split; [lia|]. split; [lia|]. split; [|exact HCH].
      intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
    * cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi cshe_gone ms_mem mkst].
      rewrite Ugo. split; [lia|]. split; [lia|]. split; [intros o Ho; lia | exact HCG].
  + exact (HDJ _ (or_intror eq_refl)).
  + exact HFA.
Qed.

(* errno's four bytes are image bytes below kLowMemEnd (PALib's pal_env, W_kit.v), so below alloc_ceiling and
   below every window of this walk's frame (W4's gmm_errno_out) *)
Lemma cshe_errno_out : forall j, 0 <= j < 4 -> 0 <= as_errno B + j < 2 ^ 64 /\ as_errno B + j < alloc_ceiling.
Proof.
intros j Hj. pose proof (pal_env B TL) as ((He0 & He1) & _).
pose proof asan_consts as (C1 & _). unfold kLowMemEnd in He1. lia.
Qed.

Ltac cshe_awr_tst Usp :=
apply awr_ok_x_cons; [|apply awr_ok_x_cons; [|apply awr_ok_x_nil]];
[ intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi cshe_tstRw base_val] in Ha; rewrite Usp in Ha;
  left; split; [left; unfold CSHE_STK, CSHE_FRAME, ASTACK in *; lia | lia]
| intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi cshe_gone] in Ha; lia ].


(* ------------------------------------------------------------------ carrying the source over the walk's runs *)
(* W_check_no_loss.v's cnl_blk / cnl_vec_len / cnl_rec_len / cnl_src_low / cnl_src_kept, copied: that file's
   lemmas live in its own Section, over its own hypotheses.  What they say: every byte the source's predicate
   reads is an application byte below the allocator's ceiling, so a run that only writes its own frame keeps
   the source - once its bytes keep their ASan view and nothing it had goes absent. *)
Lemma cshe_blk_x : forall ly S hp W mem md p n, ARx ly S hp W mem md -> In (p, n) (ablocks B ly S) ->
p mod 16 = 0 /\ 4096 <= p /\ 0 <= n /\ n <= req_size n /\ 1 <= req_size n /\ p + req_size n <= alloc_ceiling /\
alloc_ceiling <= 0x7fffff800000 /\ off_img p (req_size n) /\ in_app p (req_size n) /\
(forall a, p <= a < p + req_size n -> apresent (w_H W) mem a /\ ~ aowned B ly S a).
Proof.
intros ly S hp W mem md p n HAR Hin.
destruct (alx_blocks _ _ _ LAWS ly S hp W mem md p n HAR Hin) as (H16 & H4096 & Hc & Hia & Hpr & _).
pose proof (BLKN ly S hp W mem md p n HAR Hin) as Hn.
pose proof (req_size_pos n ltac:(lia)) as [R1 R2]. pose proof asan_consts as (C1 & _).
pose proof (blk_off_imgP_x B ARx LAWS IMGC BLKN ly S hp W mem md p n HAR Hin) as Hoff.
split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
split; [exact Hoff|]. split; [exact Hia|]. exact Hpr.
Qed.
Lemma cshe_text_recs_length : forall rs, length (concat (map HarnessRep.text_rec rs)) = (16 * length rs)%nat.
Proof.
induction rs as [|r rs IH]; [reflexivity|]. cbn [map concat]. rewrite length_app, IH.
unfold HarnessRep.text_rec, OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib.Mem.le8.
rewrite length_app, !length_N_to_le_bytes. cbn [length]. lia.
Qed.
Lemma cshe_vec_len : forall l : hlist, Z.of_nat (length (hl_junk l)) = AREC * (hl_cap l - hl_n l) ->
Z.of_nat (length (bzs (concat (map HarnessRep.text_rec (hl_recs l)) ++ hl_junk l))) = AREC * hl_cap l.
Proof.
intros l Hj. unfold bzs. rewrite length_map, length_app, cshe_text_recs_length, Nat2Z.inj_add, Nat2Z.inj_mul.
unfold hl_n in Hj. change (Z.of_nat 16) with 16. unfold AREC in *. lia.
Qed.
Lemma cshe_src_low_x : forall ly1 S1 hp1 W1 mem1 md1 HA1 h1,
ARx ly1 S1 hp1 W1 mem1 md1 -> asrc_at B ly1 S1 W1 mem1 HA1 h1 -> 0x10000 <= HA1 -> HA1 + 96 <= 0x5fb000 ->
forall rr, In rr (asrc_fp HA1 h1) -> forall a, fst rr <= a < snd rr -> 4096 <= a < alloc_ceiling.
Proof.
intros ly1 S1 hp1 W1 mem1 md1 HA1 h1 HAR HS HAlo HAhi.
pose proof asan_consts as (C1 & _).
assert (LB : forall (l : hlist) LA, alist_at B ly1 S1 W1 mem1 LA l true \/ alist_at B ly1 S1 W1 mem1 LA l false ->
  0x10000 <= LA -> LA + 16 <= 0x5fb000 ->
  forall rr, In rr (alist_fp LA l) -> forall a, fst rr <= a < snd rr -> 4096 <= a < alloc_ceiling).
{ intros l LA Hl Hlo Hhi rr Hin a Ha.
  assert (HL : alist_at B ly1 S1 W1 mem1 LA l true \/ alist_at B ly1 S1 W1 mem1 LA l false) by exact Hl.
  destruct HL as [HA2 | HA2];
  (destruct HA2 as (_ & _ & _ & _ & Hcap & Hv & _ & _ & Hrec);
   unfold alist_fp in Hin; cbn [In] in Hin;
   destruct Hin as [<- | Hin]; [cbn [fst snd] in Ha; lia|];
   apply in_app_or in Hin as [Hin | Hin];
   [ destruct (hl_cap l =? 0) eqn:Ec; [destruct Hin|];
     destruct Hin as [<- | []];
     destruct Hv as [(Hc0 & _) | (Hc & Hvin & Hj & Hg)]; [apply Z.eqb_neq in Ec; lia|];
     destruct (cshe_blk_x ly1 S1 hp1 W1 mem1 md1 _ _ HAR Hvin) as (_ & H4096 & _ & Hn1 & _ & Hc2 & _);
     unfold gfp in Ha; cbn [fst snd] in Ha; rewrite (cshe_vec_len l Hj) in Ha; lia
   | apply in_map_iff in Hin as (r & <- & Hr);
     rewrite Forall_forall in Hrec; destruct (Hrec r Hr) as (Hin2 & _);
     destruct (cshe_blk_x ly1 S1 hp1 W1 mem1 md1 _ _ HAR Hin2) as (_ & H4096 & _ & Hn1 & _ & Hc2 & _);
     cbn [fst snd gfp] in Ha; unfold bzs in Ha; rewrite length_map, length_app in Ha; cbn [length] in Ha; lia ]). }
intros rr Hin a Ha.
pose proof HS as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hpend & _ & _ & _ & _ & _ & _ & _ & Hpin & Hpj & Hpg & _ & Hexp & Hheld & _).
unfold asrc_fp in Hin. cbn [In] in Hin.
destruct Hin as [<- | Hin]; [cbn [fst snd] in Ha; unfold ASRC in Ha; lia|].
destruct Hin as [<- | Hin].
{ destruct (cshe_blk_x ly1 S1 hp1 W1 mem1 md1 _ _ HAR Hpin) as (_ & H4096 & _ & Hn1 & _ & Hc2 & _).
  cbn [fst snd gfp] in Ha. unfold bzs in Ha. rewrite length_map in Ha. unfold APARTIAL in *. lia. }
apply in_app_or in Hin as [Hin | Hin].
{ exact (LB (hs_pending h1) (HA1 + 16) (or_intror Hpend) ltac:(lia) ltac:(lia) rr Hin a Ha). }
apply in_app_or in Hin as [Hin | Hin].
{ exact (LB (hs_expected h1) (HA1 + 64) (or_introl Hexp) ltac:(lia) ltac:(lia) rr Hin a Ha). }
exact (LB (hs_held h1) (HA1 + 80) (or_introl Hheld) ltac:(lia) ltac:(lia) rr Hin a Ha).
Qed.
Lemma cshe_alist_blks_in : forall ly0 S0 W0 m0 LA l lines, alist_at B ly0 S0 W0 m0 LA l lines ->
forall b, In b (alist_blks l) -> In b (ablocks B ly0 S0).
Proof.
intros ly0 S0 W0 m0 LA l lines HL0 b Hb. unfold alist_blks in Hb. apply in_app_or in Hb as [Hb|Hb].
- destruct (hl_cap l =? 0) eqn:Ec; [destruct Hb|]. destruct Hb as [<- | []].
  destruct HL0 as (_ & _ & _ & _ & _ & [(Hc & _) | (_ & Hin & _)] & _); [apply Z.eqb_neq in Ec; lia | exact Hin].
- apply in_map_iff in Hb as (x & <- & Hx). destruct HL0 as (_ & _ & _ & _ & _ & _ & _ & _ & HF).
  rewrite Forall_forall in HF. exact (proj1 (HF x Hx)).
Qed.
Lemma cshe_src_blks : forall ly0 S0 W0 m0 HA0 h0, asrc_at B ly0 S0 W0 m0 HA0 h0 ->
forall b, In b (asrc_blks h0) -> In b (ablocks B ly0 S0).
Proof.
intros ly0 S0 W0 m0 HA0 h0 HS0 b Hb.
pose proof HS0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HPd & _ & _ & _ & _ & _ & _ & _ & HPin & _ & _ & _ & HEx & HHl & _).
unfold asrc_blks in Hb. destruct Hb as [<- | Hb]; [exact HPin|].
apply in_app_or in Hb as [Hb | Hb]; [exact (cshe_alist_blks_in _ _ _ _ _ _ _ HPd b Hb)|].
apply in_app_or in Hb as [Hb | Hb];
[exact (cshe_alist_blks_in _ _ _ _ _ _ _ HEx b Hb) | exact (cshe_alist_blks_in _ _ _ _ _ _ _ HHl b Hb)].
Qed.
(* a value carried over a step that keeps its bytes (W_check_no_loss.v cnl_vm_keep, copied) *)
Lemma cshe_vm_keep : forall (W W' : world SEGS) m m' a n v,
(forall x, a <= x < a + Z.of_nat n -> aview SEGS (w_H W') m' x = aview SEGS (w_H W) m x) ->
val_mem SEGS (mrestrict (w_H W) m) a n v -> val_mem SEGS (mrestrict (w_H W') m') a n v.
Proof.
intros W W' m m' a n v Hk Hv i Hi.
rewrite (mbyte_of_aview SEGS (w_H W) (w_H W') m m' (a + Z.of_nat i) (Hk (a + Z.of_nat i) ltac:(lia))).
exact (Hv i Hi).
Qed.
Lemma cshe_set_held_id : forall h, CheckRep.set_held h (hs_held h) = h.
Proof. intros [? ? ? ? ? ? ? ? ? ? ? ? ?]. reflexivity. Qed.
(* ---- where P lives (cshe_spec's P-home premise), for loops 2 and 3 ---- *)
(* A frame's shadow bytes: x in a 64-aligned frame [f, f + bs) has its shadow byte in the frame's shadow range. *)
Lemma cshe_shadow_in_frame : forall f bs x, f mod 64 = 0 -> bs mod 64 = 0 -> f <= x < f + bs ->
shadow_addr f <= SHADOW_OFF + x / 8 < shadow_addr f + bs / 8.
Proof.
intros f bs x Hf Hb Hx. apply Z.mod_divide in Hf; [|lia]. apply Z.mod_divide in Hb; [|lia].
destruct Hf as (qf & ->). destruct Hb as (qb & ->). unfold shadow_addr.
assert (E1 : qf * 64 / 8 = qf * 8) by (replace (qf * 64) with (qf * 8 * 8) by lia; apply Z.div_mul; lia).
assert (E2 : qb * 64 / 8 = qb * 8) by (replace (qb * 64) with (qb * 8 * 8) by lia; apply Z.div_mul; lia).
rewrite E1, E2.
assert (L : qf * 8 <= x / 8) by (apply Z.div_le_lower_bound; lia).
assert (U : x / 8 < qf * 8 + qb * 8) by (apply Z.div_lt_upper_bound; lia).
lia.
Qed.

(* the thirteen saved slots over a run that writes nothing *)
Lemma cshe_saved_meq : forall (W1 : world SEGS) m m' sp0 rs,
(forall x : word, mrestrict (w_H W1) m' x = mrestrict (w_H W1) m x) ->
cshe_saved W1 m sp0 rs -> cshe_saved W1 m' sp0 rs.
Proof.
intros W1 m m' sp0 rs Hq (M1 & M8 & M9 & M18 & M19 & M20 & M21 & M22 & M23 & M24 & M25 & M26 & M27).
unfold cshe_saved. repeat split;
  (apply (cshe_vm_keep W1 W1 m m' _ 8 _);
   [intros x Hx; apply (aview_eq_of SEGS); apply Hq | assumption]).
Qed.

(* ------------------------------------------------------------------ what loop 1's invariant is built from *)
(* The vector's records as 8-byte cells (W1's garr8_val_mem8 / alist_rec_fields, through
   W_check_no_loss.v's copies cnl_garr8_val_mem8 / cnl_rec_fields). *)
Lemma cshe_garr8_val_mem8 : forall (m : word -> option byte) a (w : word),
garr8 SEGS m a (HarnessRep.bzs (word_to_le_bytes 8 w)) -> val_mem SEGS m a 8 (bv_unsigned w).
Proof.
intros m a w H k Hk.
assert (Hl : length (HarnessRep.bzs (word_to_le_bytes 8 w)) = 8%nat)
by (unfold HarnessRep.bzs; rewrite length_map; apply length_N_to_le_bytes).
rewrite (garr8_mbyte SEGS m a _ k H ltac:(lia)). f_equal.
pose proof (YN2e.word_to_le_bytes_nth 8 (bv_unsigned w) k Hk (bv_unsigned_in_range 64 w)) as Hn.
rewrite Z_to_bv_bv_unsigned in Hn.
unfold HarnessRep.bzs.
replace (nth k (map HarnessRep.bz (word_to_le_bytes 8 w)) 0)
with (HarnessRep.bz (nth k (word_to_le_bytes 8 w) (Z_to_bv 8 0))).
2: { rewrite <- (map_nth HarnessRep.bz). apply nth_indep. rewrite length_map, length_N_to_le_bytes. exact Hk. }
rewrite (nth_error_nth _ _ _ Hn). unfold HarnessRep.bz. apply Z_to_bv_bv_unsigned.
Qed.
Lemma cshe_rec_fields : forall ly S W mem LA l lines j,
alist_at B ly S W mem LA l lines -> (j < length (HarnessRep.hl_recs l))%nat ->
val_mem SEGS (arm W mem) (HarnessRep.hl_v l + 16 * Z.of_nat j) 8
  (fst (nth j (HarnessRep.hl_recs l) (0, [])) mod 2 ^ 64) /\
val_mem SEGS (arm W mem) (HarnessRep.hl_v l + 16 * Z.of_nat j + 8) 8
  (Z.of_nat (length (snd (nth j (HarnessRep.hl_recs l) (0, [])))) mod 2 ^ 64).
Proof.
intros ly S W mem LA l lines j HA Hj.
destruct HA as (_ & _ & _ & _ & Hcap & Hv & _).
destruct Hv as [(Hc0 & _) | (_ & _ & _ & Hg)].
{ unfold HarnessRep.hl_n in Hcap. lia. }
destruct (nth_split (HarnessRep.hl_recs l) (0, []) Hj) as (l1 & l2 & Hsp & Hl1).
set (r := nth j (HarnessRep.hl_recs l) (0, [])) in *.
rewrite Hsp in Hg. rewrite map_app, concat_app in Hg. cbn [map concat] in Hg.
unfold HarnessRep.bzs in Hg. rewrite !map_app in Hg. rewrite <- !app_assoc in Hg.
apply garr8_app in Hg as [_ Hg]. rewrite length_map, cshe_text_recs_length, Hl1 in Hg.
unfold HarnessRep.text_rec, OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib.Mem.le8 in Hg.
rewrite !map_app, <- !app_assoc in Hg.
apply garr8_app in Hg as [H1 Hg]. apply garr8_app in Hg as [H2 _].
rewrite length_map, length_N_to_le_bytes in H2.
apply cshe_garr8_val_mem8 in H1. apply cshe_garr8_val_mem8 in H2.
rewrite Z_to_bv_unsigned in H1, H2. unfold bv_wrap in H1, H2. change (bv_modulus 64) with (2 ^ 64) in H1, H2.
replace (HarnessRep.hl_v l + Z.of_nat (16 * j)) with (HarnessRep.hl_v l + 16 * Z.of_nat j) in H1, H2 by lia.
split; [exact H1|].
replace (HarnessRep.hl_v l + 16 * Z.of_nat j + 8) with (HarnessRep.hl_v l + 16 * Z.of_nat j + Z.of_nat 8) by lia.
exact H2.
Qed.
(* a shorter range has a shorter shadow hull *)
Lemma cshe_shv_sub : forall (rd : reader) x n n', 0 < n' -> n' <= n ->
shadow_hull_vis rd x n -> shadow_hull_vis rd x n'.
Proof.
intros rd x n n' Hn' Hle Hv s Hs. apply Hv.
pose proof (shadow_mono (x + n' - 1) (x + n - 1) ltac:(lia)) as M.
assert (HD : shadow_addr (x + n' - 1) / 8 <= shadow_addr (x + n - 1) / 8) by (apply Z.div_le_mono; [lia | exact M]).
lia.
Qed.
(* the thirteen saved slots over a run that keeps the bytes below the entry sp *)
Lemma cshe_saved_kept : forall (W W' : world SEGS) m m' sp0 rs,
(forall a, sp0 - 104 <= a < sp0 -> aview SEGS (w_H W') m' a = aview SEGS (w_H W) m a) ->
cshe_saved W m sp0 rs -> cshe_saved W' m' sp0 rs.
Proof.
intros W W' m m' sp0 rs Hk (M1 & M8 & M9 & M18 & M19 & M20 & M21 & M22 & M23 & M24 & M25 & M26 & M27).
unfold cshe_saved. repeat split;
  (apply (cshe_vm_keep W W' m m' _ 8 _);
   [intros x Hx; cbn [Z.of_nat] in Hx; apply Hk; lia | assumption]).
Qed.
(* cshe_l1_pfx_kept / cshe_l1_rec_kept over any window above the allocator's ceiling: the entry's run writes
   the frame [sp - 144, sp), not has_prefix's scratch, so the i = 0 invariant is carried over that window. *)
Lemma cshe_l1_pfx_kept2 : forall (W W' : world SEGS) mem mem' sp0 lo hi PF P,
alloc_ceiling <= lo -> 0 < PF -> PF + Z.of_nat (length P) + 1 <= 2 ^ 63 ->
(forall y, 0 <= y < 2 ^ 64 -> ~ (lo <= y < hi) -> aview SEGS (w_H W') mem' y = aview SEGS (w_H W) mem y) ->
(forall y, PF <= y < PF + Z.of_nat (length P) + 8 -> ~ (lo <= y < hi)) ->
cshe_l1_pfx W mem sp0 PF P -> cshe_l1_pfx W' mem' sp0 PF P.
Proof.
intros W W' mem mem' sp0 lo hi PF P HCEIL HPF0 HPFk Hk Hoff2
  (Hby & Hvis & Hoff & Hmr1 & Hmr8 & Hra1 & Hshv1 & Hra0 & Hshv0 & Hrom).
pose proof pa_segs_low as Hsegs. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HIN : forall a, PF <= a < PF + Z.of_nat (length P) + 8 -> 0 <= a < 2 ^ 64 /\ ~ (lo <= a < hi))
  by (intros a Ha; split; [lia | apply Hoff2; lia]).
split; [apply (cshe_bytes_kept W W' mem mem' PF _ lo hi Hk);
        [intros t Ht; apply HIN; rewrite length_app in Ht; cbn [length] in Ht; lia | exact Hby]|].
split; [intros a Ha; destruct (HIN a Ha) as [X1 X2]; rewrite (Hk a X1 X2); exact (Hvis a Ha)|].
split; [exact Hoff|]. split; [exact Hmr1|]. split; [exact Hmr8|].
split; [exact (cshe_ra_kept W W' mem mem' PF (Z.of_nat (length P) + 1) _ _ HCEIL Hmr1 ltac:(lia) Hk Hra1)|].
split; [exact (cshe_shv_kept W W' mem mem' PF (Z.of_nat (length P) + 1) _ _ HCEIL Hmr1 ltac:(lia) ltac:(lia) Hk Hshv1)|].
assert (Hmr0 : amem_range PF (Z.of_nat (length P)))
  by (unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in *; lia).
split; [exact (cshe_ra_kept W W' mem mem' PF (Z.of_nat (length P)) _ _ HCEIL Hmr0 ltac:(lia) Hk Hra0)|].
split; [intros Hp; exact (cshe_shv_kept W W' mem mem' PF (Z.of_nat (length P)) _ _ HCEIL Hmr0 ltac:(lia) Hp Hk (Hshv0 Hp))|].
intros a Ha. assert (Hi : in_img SEGS a) by (destruct Ha as (sg & Hsg & _ & Hr); exists sg; split; assumption).
destruct (Hsegs a Hi) as [L1 L2]. unfold kLowMemEnd in L2.
rewrite (Hk a ltac:(lia) ltac:(lia)). exact (Hrom a Ha).
Qed.
Lemma cshe_l1_rec_kept2 : forall ly S (W W' : world SEGS) mem mem' sp0 lo hi V P r j,
alloc_ceiling <= lo -> 4096 <= V + AREC * j ->
(forall y, 0 <= y < 2 ^ 64 -> ~ (lo <= y < hi) -> aview SEGS (w_H W') mem' y = aview SEGS (w_H W) mem y) ->
(forall y, V + AREC * j <= y < V + AREC * j + 16 -> ~ (lo <= y < hi)) ->
(forall y, fst r <= y < fst r + Z.of_nat (length (snd r)) + 1 -> ~ (lo <= y < hi)) ->
cshe_l1_rec ly S W mem sp0 V P r j -> cshe_l1_rec ly S W' mem' sp0 V P r j.
Proof.
intros ly S W W' mem mem' sp0 lo hi V P r j HCEIL HEA Hk Hoff16 Hofft2
  (Ms & Mn & Hra16 & Hmr16 & Hoffe & Hblk & Hr0 & Hlx & Hby & Hofft & Hlp).
unfold cshe_l1_rec. cbv zeta.
assert (KEA : forall t, 0 <= t < 16 ->
  aview SEGS (w_H W') mem' (V + AREC * j + t) = aview SEGS (w_H W) mem (V + AREC * j + t)).
{ intros t Ht. apply Hk; [unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hmr16; lia
                         | apply Hoff16; lia]. }
split; [exact (val_mem_kept SEGS _ _ mem mem' _ 8 _ ltac:(intros t Ht; apply KEA; lia) Ms)|].
split; [refine (val_mem_kept SEGS _ _ mem mem' _ 8 _ _ Mn);
        intros t Ht; replace (V + AREC * j + 8 + t) with (V + AREC * j + (8 + t)) by lia; apply KEA; lia|].
split; [exact (cshe_ra_kept W W' mem mem' _ 16 _ _ HCEIL Hmr16 ltac:(lia) Hk Hra16)|].
split; [exact Hmr16|]. split; [exact Hoffe|]. split; [exact Hblk|].
split; [exact Hr0|]. split; [exact Hlx|].
split; [apply (cshe_bytes_kept W W' mem mem' (fst r) _ lo hi Hk);
        [intros t Ht; rewrite length_app in Ht; cbn [length] in Ht;
         split; [lia | apply Hofft2; lia] | exact Hby]|].
split; [exact Hofft|].
intros Hle. destruct (Hlp Hle) as (Hmrp & Hrap & Hshvp).
split; [exact Hmrp|].
split; [exact (cshe_ra_kept W W' mem mem' (fst r) (Z.of_nat (length P)) _ _ HCEIL Hmrp ltac:(lia) Hk Hrap)|].
intros Hp. exact (cshe_shv_kept W W' mem mem' (fst r) (Z.of_nat (length P)) _ _ HCEIL Hmrp ltac:(lia) Hp Hk (Hshvp Hp)).
Qed.

(* ---- route R (RULE-SHAPES.md (sha256 2e856ce788dd; internal record) sec 0): the walk's segments at a world relation R.  The journal ajournal_gx_x
   becomes ajournal_gx_xR R, SRr SEGS becomes SRrG SEGS R, and cshe_post_x becomes cshe_post_xR R
   (W_contract_xR_g6.v).  No segment of this file calls the allocator (has_prefix, strlen and bcmp are strict leaf
   contracts), so none moves the world: a segment whose journal is at R is its strict walk over the R journal
   (paj_run_x_xR / paj_run_to_x_xR, W_journal_x.v Section g), lifted by SRr_SRrG; cshe_want0_xR runs at R
   (paj_run_x_xG) because it ends in the epilogue at R; a segment that starts at the entry runs the strict entry and
   loop 1, and its journal is weakened to R (cshe_aj_xR_of_x).  The strict lemmas after this Section are these at
   R := wle (wle_inst below). *)
Section wR.
Variable R : world SEGS -> world SEGS -> Prop.
Hypothesis R_refl : forall W, R W W.
Hypothesis R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3.
Hypothesis WLE_R : forall W W', @wle SEGS W W' -> R W W'.
(* (C1) g_gone <> 0: 0x85498 -> loop 2's head 0x854c4.  The run reads g_gone and the count cell at sp + 8 and
   writes nothing; `andi s11,s0,7` is 0 because &held.n = HA + 88 is 8-aligned, so s11 = 3 at the head. *)
Lemma cshe_gone_l2_xR : forall (W : world SEGS) ly S hp regs mem md ly0 S0 hp0 (W0 : world SEGS) mem0 md0
XO AT FP sp0 kk HA PF VE SBV SBH gone N a0v s5v want,
cshe_tst_regs regs sp0 HA PF AT VE SBV SBH N a0v s5v want ->
cshe_tst_ok sp0 HA N a0v s5v want gone ->
val_mem SEGS (mrestrict (w_H W) mem) (sp0 - 136) 8 N ->
val_mem SEGS (mrestrict (w_H W) mem) (VAL A_g_gone) 1 gone ->
(forall a, sp0 - 144 <= a < sp0 -> apresent (w_H W) mem a) ->
gone <> 0 -> XO mod 16 = 0 -> alloc_ceiling + CSHE_STK <= sp0 ->
ajournal_gx_xR SEGS B PST ARx R G XO [(AT, AT + 8)] CSHE_STK sp0 FP ly0 S0 hp0 W0 mem0 md0 [] ly S hp W mem md kk ->
(* errno's view at 0x85498 is the entry's (cshe_to_tst's last conjunct) *)
(forall j, 0 <= j < 4 -> aview SEGS (w_H W) mem (as_errno B + j) = aview SEGS (w_H W0) mem0 (as_errno B + j)) ->
SRrG SEGS R W (mkCfg (mkst regs (Z_to_bv 64 (BASE + A_cshe_tst + 4)) mem (seg_rom SEGS)) md)
(fun W' c' => exists regs' mem' md',
 c' = mkCfg (mkst regs' (Z_to_bv 64 (BASE + A_cshe_l2)) mem' (seg_rom SEGS)) md' /\
 ajournal_gx_xR SEGS B PST ARx R G XO [(AT, AT + 8)] CSHE_STK sp0 FP ly0 S0 hp0 W0 mem0 md0 [] ly S hp W' mem' md' kk /\
 (forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W') mem' a = aview SEGS (w_H W) mem a) /\
 (forall a, apresent (w_H W) mem a -> apresent (w_H W') mem' a) /\
 getr regs' 2 = getr regs 2 /\ getr regs' 3 = getr regs 3 /\ getr regs' 4 = getr regs 4 /\
 getr regs' 8 = getr regs 8 /\ getr regs' 9 = getr regs 9 /\ getr regs' 11 = getr regs 11 /\
 getr regs' 18 = getr regs 18 /\ getr regs' 19 = getr regs 19 /\ getr regs' 24 = getr regs 24 /\
 getr regs' 25 = getr regs 25 /\ getr regs' 26 = getr regs 26 /\
 getr regs' 20 = w64 (N + 1) /\ getr regs' 21 = w64 (- N) /\ getr regs' 22 = w64 1 /\
 getr regs' 23 = w64 (AREC * (N - 1)) /\ getr regs' 27 = w64 3 /\
 (* errno's view is the entry's (W0, mem0: the journal's start), as the premise gave it at 0x85498 *)
 (forall j, 0 <= j < 4 -> aview SEGS (w_H W') mem' (as_errno B + j) = aview SEGS (w_H W0) mem0 (as_errno B + j))).
Proof.
intros W ly S hp regs mem md ly0 S0 hp0 W0 mem0 md0 XO AT FP sp0 kk HA PF VE SBV SBH gone N a0v s5v want
  HR HK MN Mg Hpres Hgone HXO16 HCL0 HJ HERR.
(* the segment moves no world: its strict walk, over the R journal (paj_run_x_xR), lifts to R *)
apply (SRr_SRrG SEGS R WLE_R).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
pose proof HR as (R2 & R8 & R9 & R10 & R11 & R18 & R19 & R20 & R21 & R22 & R23 & R24 & R25 & R26 & R27).
pose proof HK as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11).
destruct (cshe_tst_state W regs mem sp0 HA PF AT VE SBV SBH gone N a0v s5v want HR HK MN Mg Hpres) as [HS _].
remember (Eimg (Ereg regs (cshe_tst_extra gone N))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EEo : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs rr).
{ intros n rr Hn. subst E. pose proof (bv_unsigned_in_range 5 rr) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn. }
assert (E2 : ew E 2 = Z_to_bv 64 (sp0 - 144)) by (rewrite (EEo 2%nat 2%bv eq_refl); exact R2).
assert (E8 : ew E 8 = Z_to_bv 64 (HA + 88)) by (rewrite (EEo 8%nat 8%bv eq_refl); exact R8).
assert (E24 : ew E 24 = Z_to_bv 64 N) by (rewrite (EEo 24%nat 24%bv eq_refl); exact R24).
assert (E32 : ew E 32 = Z_to_bv 64 gone)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 N)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (Usp : bv_unsigned (ew E 2) = sp0 - 144) by (rewrite E2; apply unsigned_lit_small; lia).
assert (SHOK : sh_ok SEGS Bx1 ([] : list shent) E (mrestrict (w_H W) mem)) by constructor.
pose (RUNTOx := paj_run_to_x_xR B PST ARx LAWS R G HG XO [(AT, AT + 8)]).
pose (RUNx := paj_run_x_xR B PST ARx LAWS R G HG XO [(AT, AT + 8)]).
(* the load of g_gone, up to the branch *)
paj_run_tok_x RUNx HS HJ SHOK Bspan.
{ apply awr_ok_x_cons; [|apply awr_ok_x_cons; [|apply awr_ok_x_nil]].
  - intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi cshe_tstR0] in Ha. lia.
  - intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi cshe_gone] in Ha. lia. }
assert (KEEP1 : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W) (ms_mem ms) a = aview SEGS (w_H W) mem a).
{ intros a Ha.
  lazymatch goal with Hf : frame_of ?Ev ?rs (mrestrict (w_H W) mem) _ |- _ =>
    apply (aview_kept_out Ev rs (w_H W) _ _ Hf a Ha) end.
  intros (r & Hin & Hr). cbn [ss_mem In] in Hin.
  destruct Hin as [<- | [<- | []]];
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi cshe_tstR0 cshe_gone] in Hr; lia. }
pose proof HG0 as GROW1.
psrr_branch_tok RUNx BR HS SHOK Bspan.
- (* gone = 0: refuted *)
  exfalso. rewrite branch_eq_U in Hc. rewrite (U_lit E 0 ltac:(lia)) in Hc.
  revert Hc. unfold U. cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned.
  rewrite unsigned_lit_small by lia. intros Hc. apply Z.eqb_eq in Hc. lia.
- paj_run_to_tok_x RUNTOx HS HJ SHOK Bspan A_cshe_l2.
  { apply awr_ok_x_cons; [|apply awr_ok_x_cons; [|apply awr_ok_x_nil]].
    - intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi cshe_tstR0] in Ha. lia.
    - intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi cshe_gone] in Ha. lia. }
  assert (KEEP : forall a, 0 <= a < 2 ^ 64 ->
    aview SEGS (w_H W) (ms_mem ms0) a = aview SEGS (w_H W) mem a).
  { intros a Ha. transitivity (aview SEGS (w_H W) (ms_mem ms) a); [|exact (KEEP1 a Ha)].
    lazymatch goal with Hf : frame_of ?Ev ?rs (mrestrict (w_H W) (ms_mem ms)) _ |- _ =>
      apply (aview_kept_out Ev rs (w_H W) _ _ Hf a Ha) end.
    intros (r & Hin & Hr). cbn [ss_mem In] in Hin.
    destruct Hin as [<- | [<- | []]];
      cbn [YP09.r_base YP09.r_wlo YP09.r_whi cshe_tstR0 cshe_gone] in Hr; lia. }
  prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
  prreg HS (8%bv : bv 5) P8. prreg HS (9%bv : bv 5) P9. prreg HS (11%bv : bv 5) P11.
  prreg HS (18%bv : bv 5) P18. prreg HS (19%bv : bv 5) P19. prreg HS (20%bv : bv 5) P20.
  prreg HS (21%bv : bv 5) P21. prreg HS (22%bv : bv 5) P22. prreg HS (23%bv : bv 5) P23.
  prreg HS (24%bv : bv 5) P24. prreg HS (25%bv : bv 5) P25. prreg HS (26%bv : bv 5) P26.
  prreg HS (27%bv : bv 5) P27.
  assert (HLAND : Z.land (HA + 88) 7 = 0).
  { replace 7 with (Z.ones 3) by reflexivity. rewrite Z.land_ones by lia.
    change (2 ^ 3) with 8. apply Z.mod_divide in K5; [|lia]. destruct K5 as (q & Hq).
    rewrite Hq. apply Z.mod_divide; [lia|]. exists (q + 11). lia. }
  assert (HSLL : alu64 ALU_SLL (Z_to_bv 64 N) (Z_to_bv 64 4) = Z_to_bv 64 (16 * N)).
  { apply bv_eq. rewrite alu64_unsigned. cbn [zalu_raw]. rewrite !unsigned_lit_small by lia.
    change (Z.land 4 63) with 4. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 4) with 16.
    unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite Z.mod_small by lia. lia. }
  pmkst HS. apply SRr_ret.
  lazymatch goal with |- context [mkCfg (mkst (ms_regs ?msx) _ _ _) ?mdx] =>
    exists (ms_regs msx), (ms_mem msx), mdx end.
  split; [unfold A_cshe_l2, A_cshe_tst, AF_fr_check_shape_ends; reflexivity|].
  split; [exact HJ|].
  split; [cbn [ms_mem]; exact KEEP|].
  split.
  { cbn [ms_mem]. intros a Hp.
    lazymatch goal with Hg : mem_grows (mrestrict (w_H W) (ms_mem ms)) _ |- _ =>
      exact (apresent_grows _ _ _ _ Hg (apresent_grows _ _ _ _ GROW1 Hp)) end. }
  split; [cbn [ms_regs]; rewrite P2; exact (EEo 2%nat 2%bv eq_refl)|].
  split; [cbn [ms_regs]; rewrite P3; exact (EEo 3%nat 3%bv eq_refl)|].
  split; [cbn [ms_regs]; rewrite P4; exact (EEo 4%nat 4%bv eq_refl)|].
  split; [cbn [ms_regs]; rewrite P8; exact (EEo 8%nat 8%bv eq_refl)|].
  split; [cbn [ms_regs]; rewrite P9; exact (EEo 9%nat 9%bv eq_refl)|].
  split; [cbn [ms_regs]; rewrite P11; exact (EEo 11%nat 11%bv eq_refl)|].
  split; [cbn [ms_regs]; rewrite P18; exact (EEo 18%nat 18%bv eq_refl)|].
  split; [cbn [ms_regs]; rewrite P19; exact (EEo 19%nat 19%bv eq_refl)|].
  split; [cbn [ms_regs]; rewrite P24; exact (EEo 24%nat 24%bv eq_refl)|].
  split; [cbn [ms_regs]; rewrite P25; exact (EEo 25%nat 25%bv eq_refl)|].
  split; [cbn [ms_regs]; rewrite P26; exact (EEo 26%nat 26%bv eq_refl)|].
  split; [cbn [ms_regs]; rewrite P20, E33, unsigned_lit_small by lia; reflexivity|].
  split.
  { cbn [ms_regs]. rewrite P21, E24. unfold w64. apply bv_eq.
    rewrite alu64_unsigned, Z_to_bv_unsigned. cbn [zalu_raw]. rewrite !unsigned_lit_small by lia.
    unfold bv_wrap. f_equal; lia. }
  split; [cbn [ms_regs]; rewrite P22; reflexivity|].
  split.
  { cbn [ms_regs]. rewrite P23, E33, HSLL. unfold w64, AREC. apply bv_eq.
    rewrite alu64_unsigned, !Z_to_bv_unsigned. cbn [zalu_raw]. unfold bv_wrap.
    change (bv_modulus 64) with (2 ^ 64). rewrite (Z.mod_small (16 * N)) by lia.
    rewrite Z.add_mod_idemp_r by lia. f_equal; lia. }
  assert (HAND : alu64 ALU_AND (Z_to_bv 64 (HA + 88)) (Z_to_bv 64 7) = Z_to_bv 64 0).
  { apply bv_eq. rewrite alu64_unsigned. cbn [zalu_raw]. rewrite !unsigned_lit_small by lia.
    rewrite HLAND. reflexivity. }
  split; [cbn [ms_regs]; rewrite P27, E8, HAND, zalu64_sound; unfold w64; f_equal; vm_compute; reflexivity|].
  intros jj Hjj. destruct (cshe_errno_out jj Hjj) as [Hr _]. cbn [ms_mem].
  rewrite (KEEP _ Hr). exact (HERR jj Hjj).
Qed.
(* (C2) g_gone = 0 and want <> 0: 0x85498 -> loop 3's head 0x8559c.  0x8557c recomputes want as a0 + s5,
   0x8558c sets s11 = want + 1 (the `while (want-- > 0)` counter), s4 = " end\0" (.str.4) and s8 = 4 are
   loop 3's bcmp operands, and sp + 8 is overwritten with (&held.n) mod 8 + 3 = 3. *)
Lemma cshe_gone_l3_xR : forall (W : world SEGS) ly S hp regs mem md ly0 S0 hp0 (W0 : world SEGS) mem0 md0
XO AT FP sp0 kk HA PF VE SBV SBH gone N a0v s5v want,
cshe_tst_regs regs sp0 HA PF AT VE SBV SBH N a0v s5v want ->
cshe_tst_ok sp0 HA N a0v s5v want gone ->
val_mem SEGS (mrestrict (w_H W) mem) (sp0 - 136) 8 N ->
val_mem SEGS (mrestrict (w_H W) mem) (VAL A_g_gone) 1 gone ->
(forall a, sp0 - 144 <= a < sp0 -> apresent (w_H W) mem a) ->
gone = 0 -> want <> 0 -> XO mod 16 = 0 -> alloc_ceiling + CSHE_STK <= sp0 ->
ajournal_gx_xR SEGS B PST ARx R G XO [(AT, AT + 8)] CSHE_STK sp0 FP ly0 S0 hp0 W0 mem0 md0 [] ly S hp W mem md kk ->
(* errno's view at 0x85498 is the entry's (cshe_to_tst's last conjunct) *)
(forall j, 0 <= j < 4 -> aview SEGS (w_H W) mem (as_errno B + j) = aview SEGS (w_H W0) mem0 (as_errno B + j)) ->
SRrG SEGS R W (mkCfg (mkst regs (Z_to_bv 64 (BASE + A_cshe_tst + 4)) mem (seg_rom SEGS)) md)
(fun W' c' => exists regs' mem' md',
 c' = mkCfg (mkst regs' (Z_to_bv 64 (BASE + A_cshe_l3)) mem' (seg_rom SEGS)) md' /\
 ajournal_gx_xR SEGS B PST ARx R G XO [(AT, AT + 8)] CSHE_STK sp0 FP ly0 S0 hp0 W0 mem0 md0 [] ly S hp W' mem' md' kk /\
 (forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 136 <= a < sp0 - 128) ->
   aview SEGS (w_H W') mem' a = aview SEGS (w_H W) mem a) /\
 (forall a, apresent (w_H W) mem a -> apresent (w_H W') mem' a) /\
 val_mem SEGS (mrestrict (w_H W') mem') (sp0 - 136) 8 3 /\
 getr regs' 2 = getr regs 2 /\ getr regs' 3 = getr regs 3 /\ getr regs' 4 = getr regs 4 /\
 getr regs' 8 = getr regs 8 /\ getr regs' 9 = getr regs 9 /\ getr regs' 18 = getr regs 18 /\
 getr regs' 19 = getr regs 19 /\ getr regs' 21 = getr regs 21 /\ getr regs' 22 = getr regs 22 /\
 getr regs' 23 = getr regs 23 /\ getr regs' 25 = getr regs 25 /\ getr regs' 26 = getr regs 26 /\
 getr regs' 10 = w64 want /\ getr regs' 20 = w64 (VAL A_lit_end5) /\ getr regs' 24 = w64 4 /\
 getr regs' 27 = w64 (want + 1) /\
 (* errno's view is the entry's (W0, mem0: the journal's start), as the premise gave it at 0x85498 *)
 (forall j, 0 <= j < 4 -> aview SEGS (w_H W') mem' (as_errno B + j) = aview SEGS (w_H W0) mem0 (as_errno B + j))).
Proof.
intros W ly S hp regs mem md ly0 S0 hp0 W0 mem0 md0 XO AT FP sp0 kk HA PF VE SBV SBH gone N a0v s5v want
  HR HK MN Mg Hpres Hgone Hwant HXO16 HCL0 HJ HERR.
(* the segment moves no world: its strict walk, over the R journal (paj_run_x_xR), lifts to R *)
apply (SRr_SRrG SEGS R WLE_R).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
pose proof HR as (R2 & R8 & R9 & R10 & R11 & R18 & R19 & R20 & R21 & R22 & R23 & R24 & R25 & R26 & R27).
pose proof HK as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11).
destruct (cshe_tst_state W regs mem sp0 HA PF AT VE SBV SBH gone N a0v s5v want HR HK MN Mg Hpres) as [_ HS].
remember (Eimg (Ereg regs (cshe_tst_extra gone N))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EEo : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs rr).
{ intros n rr Hn. subst E. pose proof (bv_unsigned_in_range 5 rr) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn. }
assert (E2 : ew E 2 = Z_to_bv 64 (sp0 - 144)) by (rewrite (EEo 2%nat 2%bv eq_refl); exact R2).
assert (E8 : ew E 8 = Z_to_bv 64 (HA + 88)) by (rewrite (EEo 8%nat 8%bv eq_refl); exact R8).
assert (E10 : ew E 10 = Z_to_bv 64 a0v) by (rewrite (EEo 10%nat 10%bv eq_refl); exact R10).
assert (E11 : ew E 11 = Z_to_bv 64 want) by (rewrite (EEo 11%nat 11%bv eq_refl); exact R11).
assert (E21 : ew E 21 = Z_to_bv 64 s5v) by (rewrite (EEo 21%nat 21%bv eq_refl); exact R21).
assert (E32 : ew E 32 = Z_to_bv 64 gone)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (Usp : bv_unsigned (ew E 2) = sp0 - 144) by (rewrite E2; apply unsigned_lit_small; lia).
assert (HLAND : Z.land (HA + 88) 7 = 0).
{ replace 7 with (Z.ones 3) by reflexivity. rewrite Z.land_ones by lia.
  change (2 ^ 3) with 8. apply Z.mod_divide in K5; [|lia]. destruct K5 as (q & Hq).
  rewrite Hq. apply Z.mod_divide; [lia|]. exists (q + 11). lia. }
assert (SHOK : sh_ok SEGS Bx1 ([] : list shent) E (mrestrict (w_H W) mem)) by constructor.
pose (RUNTOx := paj_run_to_x_xR B PST ARx LAWS R G HG XO [(AT, AT + 8)]).
pose (RUNx := paj_run_x_xR B PST ARx LAWS R G HG XO [(AT, AT + 8)]).
paj_run_tok_x RUNx HS HJ SHOK Bspan.
{ cshe_awr_tst Usp. }
pose proof HG0 as GROW1.
assert (KEEP1 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 136 <= a < sp0 - 128) ->
  aview SEGS (w_H W) (ms_mem ms) a = aview SEGS (w_H W) mem a).
{ intros a Ha Hno.
  lazymatch goal with Hf : frame_of ?Ev ?rs (mrestrict (w_H W) mem) _ |- _ =>
    apply (aview_kept_out Ev rs (w_H W) _ _ Hf a Ha) end.
  intros (r & Hin & Hr). cbn [ss_mem In] in Hin.
  destruct Hin as [<- | [<- | []]];
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi cshe_tstRw cshe_gone base_val] in Hr;
    rewrite ?Usp in Hr; lia. }
psrr_branch_tok RUNx BR HS SHOK Bspan.
- (* g_gone = 0: on to the want test at 0x85578 *)
  paj_run_tok_x RUNx HS HJ SHOK Bspan.
  { cshe_awr_tst Usp. }
  pose proof HG1 as GROW2.
  assert (KEEP2 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 136 <= a < sp0 - 128) ->
    aview SEGS (w_H W) (ms_mem ms0) a = aview SEGS (w_H W) (ms_mem ms) a).
  { intros a Ha Hno.
    lazymatch goal with Hf : frame_of ?Ev ?rs (mrestrict (w_H W) (ms_mem ms)) _ |- _ =>
      apply (aview_kept_out Ev rs (w_H W) _ _ Hf a Ha) end.
    intros (r & Hin & Hr). cbn [ss_mem In] in Hin.
    destruct Hin as [<- | [<- | []]];
      cbn [YP09.r_base YP09.r_wlo YP09.r_whi cshe_tstRw cshe_gone base_val] in Hr;
      rewrite ?Usp in Hr; lia. }
  psrr_branch_tok RUNx BR HS SHOK Bspan.
  + (* want = 0: not this arm *)
    exfalso. rewrite branch_eq_U, (U_lit E 0 ltac:(lia)), (U_atom E 11 want E11 ltac:(lia)) in Hc0.
    apply Z.eqb_eq in Hc0. lia.
  + paj_run_to_tok_x RUNTOx HS HJ SHOK Bspan A_cshe_l3.
    { cshe_awr_tst Usp. }
    pose proof HG2 as GROW3.
    assert (KEEP3 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 136 <= a < sp0 - 128) ->
      aview SEGS (w_H W) (ms_mem ms1) a = aview SEGS (w_H W) (ms_mem ms0) a).
    { intros a Ha Hno.
      lazymatch goal with Hf : frame_of ?Ev ?rs (mrestrict (w_H W) (ms_mem ms0)) _ |- _ =>
        apply (aview_kept_out Ev rs (w_H W) _ _ Hf a Ha) end.
      intros (r & Hin & Hr). cbn [ss_mem In] in Hin.
      destruct Hin as [<- | [<- | []]];
        cbn [YP09.r_base YP09.r_wlo YP09.r_whi cshe_tstRw cshe_gone base_val] in Hr;
        rewrite ?Usp in Hr; lia. }
    assert (E272 : ew E 272%nat = Z_to_bv 64 (VAL A_lit_end5)).
    { subst E. change (272%nat) with A_lit_end5.
      apply Eimg_img. unfold A_lit_end5, A_OBJ, A_TEXT, A_LIM. lia. }
    assert (HU3 : U E (SAlu ALU_ADD (SAlu ALU_AND (SOff 8 0) (SLit 7)) (SLit 3)) = 3).
    { rewrite !U_SAlu. cbn [zalu_raw]. rewrite !U_SLit.
      rewrite (U_atom E 8 (HA + 88) E8) by lia.
      rewrite (zcanon_id 7) by (unfold M64; lia). rewrite (zcanon_id 3) by (unfold M64; lia).
      rewrite HLAND, (zcanon_id 0) by (unfold M64; lia).
      rewrite Z.add_0_l. apply zcanon_id. unfold M64. lia. }
    assert (MC3 : val_mem SEGS (mrestrict (w_H W) (ms_mem ms1)) (sp0 - 136) 8 3).
    { replace (sp0 - 136) with (sp0 - 144 + 8) by lia.
      pose proof (cshe_st_chunk E _ (w_H W) ms1 0%nat _ _ HS ltac:(cbn [ss_mem]; reflexivity)
        ltac:(cbn [YP09.r_chunks]; left; reflexivity)) as HC.
      cbn [YP09.r_base base_val] in HC. rewrite Usp in HC.
      exact (cshe_chunk_val E _ (sp0 - 144) 8 8 _ 3 HU3 HC). }
    prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
    prreg HS (8%bv : bv 5) P8. prreg HS (9%bv : bv 5) P9. prreg HS (10%bv : bv 5) P10.
    prreg HS (18%bv : bv 5) P18. prreg HS (19%bv : bv 5) P19. prreg HS (20%bv : bv 5) P20.
    prreg HS (21%bv : bv 5) P21. prreg HS (22%bv : bv 5) P22. prreg HS (23%bv : bv 5) P23.
    prreg HS (24%bv : bv 5) P24. prreg HS (25%bv : bv 5) P25. prreg HS (26%bv : bv 5) P26.
    prreg HS (27%bv : bv 5) P27.
    pmkst HS. apply SRr_ret.
    lazymatch goal with |- context [mkCfg (mkst (ms_regs ?msx) _ _ _) ?mdx] =>
      exists (ms_regs msx), (ms_mem msx), mdx end.
    split; [unfold A_cshe_l3, AF_fr_check_shape_ends; reflexivity|].
    split; [exact HJ|].
    split; [cbn [ms_mem]; intros a Ha Hno;
            rewrite (KEEP3 a Ha Hno), (KEEP2 a Ha Hno); exact (KEEP1 a Ha Hno)|].
    split.
    { cbn [ms_mem]. intros a Hp.
      exact (apresent_grows _ _ _ _ GROW3 (apresent_grows _ _ _ _ GROW2
        (apresent_grows _ _ _ _ GROW1 Hp))). }
    split; [cbn [ms_mem]; exact MC3|].
    split; [cbn [ms_regs]; rewrite P2; exact (EEo 2%nat 2%bv eq_refl)|].
    split; [cbn [ms_regs]; rewrite P3; exact (EEo 3%nat 3%bv eq_refl)|].
    split; [cbn [ms_regs]; rewrite P4; exact (EEo 4%nat 4%bv eq_refl)|].
    split; [cbn [ms_regs]; rewrite P8; exact (EEo 8%nat 8%bv eq_refl)|].
    split; [cbn [ms_regs]; rewrite P9; exact (EEo 9%nat 9%bv eq_refl)|].
    split; [cbn [ms_regs]; rewrite P18; exact (EEo 18%nat 18%bv eq_refl)|].
    split; [cbn [ms_regs]; rewrite P19; exact (EEo 19%nat 19%bv eq_refl)|].
    split; [cbn [ms_regs]; rewrite P21; exact (EEo 21%nat 21%bv eq_refl)|].
    split; [cbn [ms_regs]; rewrite P22; exact (EEo 22%nat 22%bv eq_refl)|].
    split; [cbn [ms_regs]; rewrite P23; exact (EEo 23%nat 23%bv eq_refl)|].
    split; [cbn [ms_regs]; rewrite P25; exact (EEo 25%nat 25%bv eq_refl)|].
    split; [cbn [ms_regs]; rewrite P26; exact (EEo 26%nat 26%bv eq_refl)|].
    split; [cbn [ms_regs]; rewrite P10, E10, E21, zalu64_sound; unfold w64; f_equal;
            unfold zalu64, zalu_raw, zcanon, M64;
            rewrite (Z.mod_small a0v) by lia; rewrite (Z.mod_small s5v) by lia;
            rewrite K11; apply Z.mod_small; lia|].
    split; [cbn [ms_regs]; rewrite P20, E272; reflexivity|].
    split; [cbn [ms_regs]; rewrite P24; unfold w64;
            first [reflexivity | (f_equal; vm_compute; reflexivity)]|].
    split.
    { cbn [ms_regs]. rewrite P27, E10. rewrite unsigned_lit_small by lia. rewrite E21, zalu64_sound.
      unfold w64. f_equal. unfold zalu64, zalu_raw, zcanon, M64.
      rewrite (Z.mod_small (a0v + 1)) by lia. rewrite (Z.mod_small s5v) by lia.
      replace (a0v + 1 + s5v) with (want + 1) by lia. apply Z.mod_small. lia. }
    intros jj Hjj. destruct (cshe_errno_out jj Hjj) as [Hr Hl]. cbn [ms_mem].
    rewrite (KEEP3 _ Hr ltac:(unfold CSHE_STK, CSHE_FRAME, ASTACK in *; lia)),
      (KEEP2 _ Hr ltac:(unfold CSHE_STK, CSHE_FRAME, ASTACK in *; lia)),
      (KEEP1 _ Hr ltac:(unfold CSHE_STK, CSHE_FRAME, ASTACK in *; lia)).
    exact (HERR jj Hjj).
- (* g_gone <> 0: not this arm *)
  exfalso. rewrite branch_eq_U, (U_lit E 0 ltac:(lia)), (U_atom E 32 gone E32 ltac:(lia)) in Hc.
  rewrite Hgone in Hc. cbn in Hc. discriminate Hc.
Qed.
(* cshe_epi_m_x at R.  The epilogue calls out to nobody, so it moves no world: its strict walk over the R journal
   (paj_run_x_xR), lifted by SRr_SRrG. *)
Lemma cshe_epi_m_xR : forall W0 ly0 S0 hp0 mem0 md0 XO OUT FP ly S hp W regs0 regs mem md kk (Q : world SEGS -> config -> Prop),
ajournal_gx_xR SEGS B PST ARx R G XO OUT CSHE_STK (spZ regs0) FP ly0 S0 hp0 W0 mem0 md0 [] ly S hp W mem md kk ->
YK0s.ret_ok (getr regs0 1) ->
spZ regs0 mod 16 = 0 -> alloc_ceiling + CSHE_STK <= spZ regs0 -> spZ regs0 <= 2 ^ 47 ->
getr regs 2 = w64 (spZ regs0 - 144) ->
getr regs 3 = getr regs0 3 -> getr regs 4 = getr regs0 4 ->
cshe_saved W mem (spZ regs0) regs0 ->
(forall regs' mem' md', aregs_preserved regs0 regs' ->
  (forall x : word, mrestrict (w_H W) mem' x = mrestrict (w_H W) mem x) ->
  ajournal_gx_xR SEGS B PST ARx R G XO OUT CSHE_STK (spZ regs0) FP ly0 S0 hp0 W0 mem0 md0 [] ly S hp W mem' md' kk ->
  Q W (mkCfg (mkst regs' (getr regs0 1) mem' (seg_rom SEGS)) md')) ->
SRrG SEGS R W (cfg_at SEGS (BASE + A_cshe_ret) regs mem md) Q.
Proof.
intros W0 ly0 S0 hp0 mem0 md0 XO OUT FP ly S hp W regs0 regs mem md kk Q HJ Hra Hal16 Hceil H47 Hsp H3 H4 HFR HQ.
apply (SRr_SRrG SEGS R WLE_R).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : CSHE_STK = 16528) by reflexivity. rewrite WS in Hceil. pose proof alloc_ceiling_val as ACV.
destruct HFR as (M1 & M8 & M9 & M18 & M19 & M20 & M21 & M22 & M23 & M24 & M25 & M26 & M27).
assert (Hspv : spZ regs = spZ regs0 - 144).
{ unfold spZ. rewrite Hsp. apply unsigned_lit_small. unfold spZ in Hceil, H47. lia. }
remember (Eimg (Ereg regs (cshe_svextra regs0))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EEo : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs rr).
{ intros n rr Hn. subst E. pose proof (bv_unsigned_in_range 5 rr) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn. }
assert (E2 : ew E 2 = getr regs 2) by exact (EEo 2%nat 2%bv eq_refl).
assert (E3 : ew E 3 = getr regs 3) by exact (EEo 3%nat 3%bv eq_refl).
assert (E4 : ew E 4 = getr regs 4) by exact (EEo 4%nat 4%bv eq_refl).
assert (E32 : ew E 32 = getr regs0 1) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 SB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = getr regs0 8) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = getr regs0 9) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 3)).
assert (E36 : ew E 36 = getr regs0 18) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 4)).
assert (E37 : ew E 37 = getr regs0 19) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 5)).
assert (E38 : ew E 38 = getr regs0 20) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 6)).
assert (E39 : ew E 39 = getr regs0 21) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 7)).
assert (E40 : ew E 40 = getr regs0 22) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 8)).
assert (E41 : ew E 41 = getr regs0 23) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 9)).
assert (E42 : ew E 42 = getr regs0 24) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 10)).
assert (E43 : ew E 43 = getr regs0 25) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 11)).
assert (E44 : ew E 44 = getr regs0 26) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 12)).
assert (E45 : ew E 45 = getr regs0 27) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 13)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs0 - 144) by (rewrite E2; exact Hspv).
assert (N1 : val_mem SEGS (mrestrict (w_H W) mem) (spZ regs0 - 144 + 136) 8 (bv_unsigned (getr regs0 1)))
  by (replace (spZ regs0 - 144 + 136) with (spZ regs0 - 8) by lia; exact M1).
assert (N8 : val_mem SEGS (mrestrict (w_H W) mem) (spZ regs0 - 144 + 128) 8 (bv_unsigned (getr regs0 8)))
  by (replace (spZ regs0 - 144 + 128) with (spZ regs0 - 16) by lia; exact M8).
assert (N9 : val_mem SEGS (mrestrict (w_H W) mem) (spZ regs0 - 144 + 120) 8 (bv_unsigned (getr regs0 9)))
  by (replace (spZ regs0 - 144 + 120) with (spZ regs0 - 24) by lia; exact M9).
assert (N18 : val_mem SEGS (mrestrict (w_H W) mem) (spZ regs0 - 144 + 112) 8 (bv_unsigned (getr regs0 18)))
  by (replace (spZ regs0 - 144 + 112) with (spZ regs0 - 32) by lia; exact M18).
assert (N19 : val_mem SEGS (mrestrict (w_H W) mem) (spZ regs0 - 144 + 104) 8 (bv_unsigned (getr regs0 19)))
  by (replace (spZ regs0 - 144 + 104) with (spZ regs0 - 40) by lia; exact M19).
assert (N20 : val_mem SEGS (mrestrict (w_H W) mem) (spZ regs0 - 144 + 96) 8 (bv_unsigned (getr regs0 20)))
  by (replace (spZ regs0 - 144 + 96) with (spZ regs0 - 48) by lia; exact M20).
assert (N21 : val_mem SEGS (mrestrict (w_H W) mem) (spZ regs0 - 144 + 88) 8 (bv_unsigned (getr regs0 21)))
  by (replace (spZ regs0 - 144 + 88) with (spZ regs0 - 56) by lia; exact M21).
assert (N22 : val_mem SEGS (mrestrict (w_H W) mem) (spZ regs0 - 144 + 80) 8 (bv_unsigned (getr regs0 22)))
  by (replace (spZ regs0 - 144 + 80) with (spZ regs0 - 64) by lia; exact M22).
assert (N23 : val_mem SEGS (mrestrict (w_H W) mem) (spZ regs0 - 144 + 72) 8 (bv_unsigned (getr regs0 23)))
  by (replace (spZ regs0 - 144 + 72) with (spZ regs0 - 72) by lia; exact M23).
assert (N24 : val_mem SEGS (mrestrict (w_H W) mem) (spZ regs0 - 144 + 64) 8 (bv_unsigned (getr regs0 24)))
  by (replace (spZ regs0 - 144 + 64) with (spZ regs0 - 80) by lia; exact M24).
assert (N25 : val_mem SEGS (mrestrict (w_H W) mem) (spZ regs0 - 144 + 56) 8 (bv_unsigned (getr regs0 25)))
  by (replace (spZ regs0 - 144 + 56) with (spZ regs0 - 88) by lia; exact M25).
assert (N26 : val_mem SEGS (mrestrict (w_H W) mem) (spZ regs0 - 144 + 48) 8 (bv_unsigned (getr regs0 26)))
  by (replace (spZ regs0 - 144 + 48) with (spZ regs0 - 96) by lia; exact M26).
assert (N27 : val_mem SEGS (mrestrict (w_H W) mem) (spZ regs0 - 144 + 40) 8 (bv_unsigned (getr regs0 27)))
  by (replace (spZ regs0 - 144 + 40) with (spZ regs0 - 104) by lia; exact M27).
assert (HS : st_ok_pi SEGS VAL E ss_cshe_ret
(restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + A_cshe_ret)) mem (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_cshe_ret. apply pa_entry_st_ok_full.
  - rewrite HE. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - constructor; [|constructor]. unfold region_ok, cshe_frmR.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks ms_mem mkst].
    cbn [base_val]. rewrite Usp.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    repeat (apply Forall_cons); try apply Forall_nil.
    + apply (chunk_ok_val SEGS E _ (spZ regs0 - 144) 40 8 (SOff 45 0) (bv_unsigned (getr regs0 27)));
      [cbn [sv_denot]; rewrite E45, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cshe_v64 (getr regs0 27) | zside | exact N27].
    + apply (chunk_ok_val SEGS E _ (spZ regs0 - 144) 48 8 (SOff 44 0) (bv_unsigned (getr regs0 26)));
      [cbn [sv_denot]; rewrite E44, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cshe_v64 (getr regs0 26) | zside | exact N26].
    + apply (chunk_ok_val SEGS E _ (spZ regs0 - 144) 56 8 (SOff 43 0) (bv_unsigned (getr regs0 25)));
      [cbn [sv_denot]; rewrite E43, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cshe_v64 (getr regs0 25) | zside | exact N25].
    + apply (chunk_ok_val SEGS E _ (spZ regs0 - 144) 64 8 (SOff 42 0) (bv_unsigned (getr regs0 24)));
      [cbn [sv_denot]; rewrite E42, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cshe_v64 (getr regs0 24) | zside | exact N24].
    + apply (chunk_ok_val SEGS E _ (spZ regs0 - 144) 72 8 (SOff 41 0) (bv_unsigned (getr regs0 23)));
      [cbn [sv_denot]; rewrite E41, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cshe_v64 (getr regs0 23) | zside | exact N23].
    + apply (chunk_ok_val SEGS E _ (spZ regs0 - 144) 80 8 (SOff 40 0) (bv_unsigned (getr regs0 22)));
      [cbn [sv_denot]; rewrite E40, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cshe_v64 (getr regs0 22) | zside | exact N22].
    + apply (chunk_ok_val SEGS E _ (spZ regs0 - 144) 88 8 (SOff 39 0) (bv_unsigned (getr regs0 21)));
      [cbn [sv_denot]; rewrite E39, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cshe_v64 (getr regs0 21) | zside | exact N21].
    + apply (chunk_ok_val SEGS E _ (spZ regs0 - 144) 96 8 (SOff 38 0) (bv_unsigned (getr regs0 20)));
      [cbn [sv_denot]; rewrite E38, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cshe_v64 (getr regs0 20) | zside | exact N20].
    + apply (chunk_ok_val SEGS E _ (spZ regs0 - 144) 104 8 (SOff 37 0) (bv_unsigned (getr regs0 19)));
      [cbn [sv_denot]; rewrite E37, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cshe_v64 (getr regs0 19) | zside | exact N19].
    + apply (chunk_ok_val SEGS E _ (spZ regs0 - 144) 112 8 (SOff 36 0) (bv_unsigned (getr regs0 18)));
      [cbn [sv_denot]; rewrite E36, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cshe_v64 (getr regs0 18) | zside | exact N18].
    + apply (chunk_ok_val SEGS E _ (spZ regs0 - 144) 120 8 (SOff 35 0) (bv_unsigned (getr regs0 9)));
      [cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cshe_v64 (getr regs0 9) | zside | exact N9].
    + apply (chunk_ok_val SEGS E _ (spZ regs0 - 144) 128 8 (SOff 34 0) (bv_unsigned (getr regs0 8)));
      [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cshe_v64 (getr regs0 8) | zside | exact N8].
    + apply (chunk_ok_val SEGS E _ (spZ regs0 - 144) 136 8 (SOff 32 0) (bv_unsigned (getr regs0 1)));
      [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cshe_v64 (getr regs0 1) | zside | exact N1].
  - apply pairwise_disjoint_of_extents. cbn [map]. repeat split.
  - split; [|split; [exact I | exact I]].
    cbn [cshe_efacts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite Usp, E33, !unsigned_lit_small by (unfold SB; lia).
    change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
    revert Hceil H47 Hal16 C1 C3 WS ACV. clear.
    unfold SB, zone2, off_img, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL. intros.
    repeat match goal with |- _ /\ _ => split end; try lia.
    apply Z.mod_divide in Hal16; [|lia]. apply Z.mod_divide; [lia|].
    apply Z.divide_sub_r; [exact Hal16 | exists 9; reflexivity]. }
assert (SHOK : sh_ok SEGS Bx [] E (mrestrict (w_H W) mem)) by constructor.
pose (RUNx := paj_run_x_xR B PST ARx LAWS R G HG XO OUT).
unfold cfg_at. change (w64 (BASE + A_cshe_ret)) with (Z_to_bv 64 (BASE + A_cshe_ret)).
paj_run_tok_x RUNx HS HJ SHOK Bspan.
{ apply awr_ok_x_cons; [|apply awr_ok_x_nil].
  unfold cshe_frmR. cbn [YP09.r_base YP09.r_wlo YP09.r_whi]. intros a Ha. lia. }
prreg HS (1%bv : bv 5) R1. prreg HS (2%bv : bv 5) R2. prreg HS (3%bv : bv 5) R3. prreg HS (4%bv : bv 5) R4.
prreg HS (8%bv : bv 5) R8. prreg HS (9%bv : bv 5) R9. prreg HS (18%bv : bv 5) R18. prreg HS (19%bv : bv 5) R19.
prreg HS (20%bv : bv 5) R20. prreg HS (21%bv : bv 5) R21. prreg HS (22%bv : bv 5) R22. prreg HS (23%bv : bv 5) R23.
prreg HS (24%bv : bv 5) R24. prreg HS (25%bv : bv 5) R25. prreg HS (26%bv : bv 5) R26. prreg HS (27%bv : bv 5) R27.
eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros mat'.
assert (HR1 : getr (ms_regs ms) 1 = getr regs0 1) by (rewrite R1; exact E32).
assert (ZB : forall (z : Z) (r : bv 5), bv_unsigned r = z -> Z_to_bv 5 z = r)
  by (intros z r <-; apply Z_to_bv_bv_unsigned).
assert (HPRES : aregs_preserved regs0 (ms_regs ms)).
{ intros r Hr. unfold acallee_saved in Hr.
  destruct Hr as [-> | [-> | [-> | [-> | [-> | Hr]]]]].
  - rewrite (ZB 2 (2%bv : bv 5) eq_refl), R2, Usp.
    replace (spZ regs0 - 144 + 144) with (spZ regs0) by lia.
    unfold spZ. rewrite Z_to_bv_bv_unsigned. reflexivity.
  - rewrite (ZB 3 (3%bv : bv 5) eq_refl), R3, E3. exact H3.
  - rewrite (ZB 4 (4%bv : bv 5) eq_refl), R4, E4. exact H4.
  - rewrite (ZB 8 (8%bv : bv 5) eq_refl), R8. exact E34.
  - rewrite (ZB 9 (9%bv : bv 5) eq_refl), R9. exact E35.
  - assert (Hr18 : r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
    destruct Hr18 as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]].
    + rewrite (ZB 18 (18%bv : bv 5) eq_refl), R18. exact E36.
    + rewrite (ZB 19 (19%bv : bv 5) eq_refl), R19. exact E37.
    + rewrite (ZB 20 (20%bv : bv 5) eq_refl), R20. exact E38.
    + rewrite (ZB 21 (21%bv : bv 5) eq_refl), R21. exact E39.
    + rewrite (ZB 22 (22%bv : bv 5) eq_refl), R22. exact E40.
    + rewrite (ZB 23 (23%bv : bv 5) eq_refl), R23. exact E41.
    + rewrite (ZB 24 (24%bv : bv 5) eq_refl), R24. exact E42.
    + rewrite (ZB 25 (25%bv : bv 5) eq_refl), R25. exact E43.
    + rewrite (ZB 26 (26%bv : bv 5) eq_refl), R26. exact E44.
    + rewrite (ZB 27 (27%bv : bv 5) eq_refl), R27. exact E45. }
assert (HKEEP : forall x : word, mrestrict (w_H W) (ms_mem ms) x = mrestrict (w_H W) mem x).
{ intros x. lazymatch type of HFr with frame_of ?Ev ?rs _ _ => apply (HFr x) end.
  intros (r & Hin & Hr). cbn [ss_mem ss_cshe_ret In] in Hin. unfold cshe_frmR in Hin.
  destruct Hin as [<- | []]. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr. lia. }
cbn [ms_regs ms_mem]. rewrite HR1, Hra.
apply (HQ (ms_regs ms) (ms_mem ms) _ HPRES HKEEP).
apply (ajournal_gx_materialize_xR SEGS B PST ARx LAWS pa_segs_low). exact HJ.
Qed.
(* cshe_epi_x at R, from cshe_epi_m_xR *)
Lemma cshe_epi_xR : forall W0 ly0 S0 hp0 mem0 md0 XO OUT FP ly S hp W regs0 regs mem md kk (Q : world SEGS -> config -> Prop),
ajournal_gx_xR SEGS B PST ARx R G XO OUT CSHE_STK (spZ regs0) FP ly0 S0 hp0 W0 mem0 md0 [] ly S hp W mem md kk ->
YK0s.ret_ok (getr regs0 1) ->
spZ regs0 mod 16 = 0 -> alloc_ceiling + CSHE_STK <= spZ regs0 -> spZ regs0 <= 2 ^ 47 ->
getr regs 2 = w64 (spZ regs0 - 144) ->
getr regs 3 = getr regs0 3 -> getr regs 4 = getr regs0 4 ->
cshe_saved W mem (spZ regs0) regs0 ->
(forall regs' mem' md', aregs_preserved regs0 regs' ->
  (forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W) mem' a = aview SEGS (w_H W) mem a) ->
  (forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a) ->
  ajournal_gx_xR SEGS B PST ARx R G XO OUT CSHE_STK (spZ regs0) FP ly0 S0 hp0 W0 mem0 md0 [] ly S hp W mem' md' kk ->
  Q W (mkCfg (mkst regs' (getr regs0 1) mem' (seg_rom SEGS)) md')) ->
SRrG SEGS R W (cfg_at SEGS (BASE + A_cshe_ret) regs mem md) Q.
Proof.
intros W0 ly0 S0 hp0 mem0 md0 XO OUT FP ly S hp W regs0 regs mem md kk Q HJ Hra Hal16 Hceil H47 Hsp H3 H4 HFR HQ.
apply (cshe_epi_m_xR W0 ly0 S0 hp0 mem0 md0 XO OUT FP ly S hp W regs0 regs mem md kk Q HJ Hra Hal16 Hceil H47 Hsp H3 H4 HFR).
intros regs' mem' md' HPRES HMEQ HJ'. apply (HQ regs' mem' md' HPRES); [| |exact HJ'].
- intros a Ha. apply (aview_eq_of SEGS). apply HMEQ.
- intros a Hp. exact (cshe_apres_meq W mem mem' a (HMEQ _) Hp).
Qed.
(* cshe_writable_kept_w at R.  The world fact is not read: a byte that W' hides was hidden at W or absent there (a
   present one stays present, so not hidden), and then both sides read the segments' view only. *)
Lemma cshe_writable_kept_w_xR : forall (W W' : world SEGS) (m m' : word -> option byte) a,
(apresent (w_H W) m a -> apresent (w_H W') m' a) -> R W W' ->
writable_at SEGS (mrestrict (w_H W) m) a -> writable_at SEGS (mrestrict (w_H W') m') a.
Proof.
intros W W' m m' a Hp _ Hw. unfold writable_at, wview, mrestrict in Hw |- *.
destruct (w_H W' (Z_to_bv 64 a)) eqn:EH'.
- destruct (w_H W (Z_to_bv 64 a)) eqn:EH; [exact Hw|].
  destruct (m (Z_to_bv 64 a)) as [b|] eqn:Em; [|exact Hw].
  destruct (Hp (conj EH (ex_intro _ b Em))) as [Hf _]. rewrite EH' in Hf. discriminate Hf.
- destruct (w_H W (Z_to_bv 64 a)) eqn:EH.
  + destruct (m' (Z_to_bv 64 a)); [discriminate | exact Hw].
  + destruct (m (Z_to_bv 64 a)) as [b|] eqn:Em.
    * destruct (Hp (conj EH (ex_intro _ b Em))) as [_ [b2 Hb2]]. rewrite Hb2. discriminate.
    * destruct (m' (Z_to_bv 64 a)); [discriminate | exact Hw].
Qed.
(* cshe_src_kept_x at R (cshe_writable_kept_w_xR) *)
Lemma cshe_src_kept_xR : forall ly S hp (W W' : world SEGS) mem mem' md HA h lo,
ARx ly S hp W mem md -> asrc_at B ly S W mem HA h -> 0x10000 <= HA -> HA + 96 <= 0x5fb000 ->
alloc_ceiling <= lo -> R W W' ->
(forall a, 4096 <= a < lo -> aview SEGS (w_H W') mem' a = aview SEGS (w_H W) mem a) ->
(forall a, apresent (w_H W) mem a -> apresent (w_H W') mem' a) ->
asrc_at B ly S W' mem' HA h.
Proof.
intros ly S hp W W' mem mem' md HA h lo HAR HS HAlo HAhi Hlo Hwle Hq Hp.
apply (asrc_at_kept B ly S W mem ly S W' mem' HA h HS).
- intros rr Hin a Ha.
  destruct (cshe_src_low_x ly S hp W mem md HA h HAR HS HAlo HAhi rr Hin a Ha) as [Hl1 Hl2].
  split; [apply Hq; lia | apply (cshe_writable_kept_w_xR W W' mem mem' a); [apply Hp | exact Hwle]].
- intros b Hb. exact (cshe_src_blks ly S W mem HA h HS b Hb).
Qed.
(* cshe_P_at_x at R: the journal's conjuncts read the same over R (ajournal_gx_AR_xR, ajournal_gx_inner_xR) *)
Lemma cshe_P_at_xR : forall XO OUT STK sp0 ly S hp W mem md HA h PF PLEN,
ARx ly S hp W mem md -> asrc_at B ly S W mem HA h -> 0 <= PLEN ->
range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF PF (PLEN + 1) ->
((forall a, PF <= a < PF + PLEN + 8 -> in_rom SEGS a) /\ ashp_x ARx PF (PLEN + 1) \/
 exists cid pos, In (cid, pos) (frames S) /\ forall a, PF <= a < PF + PLEN + 8 -> in_zr a (frame_rng ly (cid, pos))) ->
forall ly1 S1 hp1 W1 mem1 md1 kk,
ajournal_gx_xR SEGS B PST ARx R G XO OUT STK sp0 (blk_FP (list_blks (hs_held h))) ly S hp W mem md [] ly1 S1 hp1 W1 mem1 md1 kk ->
(forall a, in_rom SEGS a -> aview SEGS (w_H W1) mem1 a = aview SEGS (w_H W) mem a) ->
(forall a, PF <= a < PF + PLEN + 8 -> aview SEGS (w_H W1) mem1 a = aview SEGS (w_H W) mem a) /\
range_addressable (aview SEGS (w_H W1) mem1) SHADOW_OFF PF (PLEN + 1) /\
shadow_hull_vis (aview SEGS (w_H W1) mem1) PF (PLEN + 1) /\
(forall a, PF <= a < PF + PLEN + 8 -> 4096 <= a < alloc_ceiling).
Proof.
intros XO OUT STK sp0 ly S hp W mem md HA h PF PLEN HAR0 HSRC HPL HRA HOME ly1 S1 hp1 W1 mem1 md1 kk HJ ROMK.
pose proof (ajournal_gx_AR_xR SEGS B PST ARx G XO OUT STK sp0 _ ly S hp W mem md [] ly1 S1 hp1 W1 mem1 md1 kk HJ) as HAR1.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct HOME as [(HR & HS) | (cid & pos & Hin & Hfr)].
- (* a read-only literal *)
  destruct (HS ly1 S1 hp1 W1 mem1 md1 HAR1) as [HRAP HHVP].
  split; [intros a Ha; exact (ROMK a (HR a Ha))|].
  split; [exact HRAP|]. split; [exact (HHVP ltac:(lia))|].
  intros a Ha. destruct (HR a Ha) as (sg & Hsg & _ & Hra).
  pose proof (pa_img_range a ltac:(exists sg; split; [exact Hsg | exact Hra])). lia.
- (* a local of one of the entry's fake frames *)
  assert (HBS : forall b, In b (list_blks (hs_held h)) -> In b (ablocks B ly S)).
  { intros b Hb. apply (cshe_src_blks ly S W mem HA h HSRC b). unfold asrc_blks.
    right. apply in_or_app. right. apply in_or_app. right. exact Hb. }
  destruct (ajournal_gx_inner_xR SEGS B PST ARx G XO OUT STK sp0 _ ly S hp W mem md [] ly1 S1 hp1 W1 mem1 md1 kk HJ)
    as (memS & HJi & Hag).
  pose proof HJi as (_ & Hlay & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & F4 & _).
  destruct (frames_bounds_x SEGS B ARx LAWS ly S hp W mem md cid pos HAR0 Hin) as (Hf0 & Hfc & _).
  destruct (W_frame_x.frame_al64_x SEGS ARx FRMF ly S hp W mem md cid pos HAR0 Hin) as (Hal & Hbal & _).
  assert (HPin : frame_addr ly cid pos <= PF /\ PF + PLEN + 8 <= frame_addr ly cid pos + fs_frame_bytes cid).
  { pose proof (Hfr PF ltac:(lia)) as H1. pose proof (Hfr (PF + PLEN + 7) ltac:(lia)) as H2.
    unfold in_zr, frame_rng in H1, H2. cbn [fst snd] in H1, H2. lia. }
  (* no frame byte and no shadow byte of the frame is in the free footprint, nor in G *)
  assert (NFP : forall x, inFP (blk_FP (list_blks (hs_held h))) x ->
    x < frame_addr ly cid pos \/ frame_addr ly cid pos + fs_frame_bytes cid <= x).
  { intros x (r & Hr & Hrr). unfold blk_FP in Hr. apply in_map_iff in Hr as ((p & k) & <- & Hpk). cbn [fst snd] in Hrr.
    pose proof (sep_block_frame_x SEGS B ARx LAWS ly S hp W mem md p k cid pos HAR0 (HBS _ Hpk) Hin) as Hd.
    unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia. }
  assert (NFPs : forall x, inFP (blk_FP (list_blks (hs_held h))) x -> x < SHADOW_OFF \/ SHADOW_OFF + 2 ^ 44 <= x).
  { intros x (r & Hr & Hrr). unfold blk_FP in Hr. apply in_map_iff in Hr as ((p & k) & <- & Hpk). cbn [fst snd] in Hrr.
    destruct (alx_blocks _ _ _ LAWS ly S hp W mem md p k HAR0 (HBS _ Hpk)) as (_ & _ & _ & Happ & _).
    unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ. unfold SHADOW_OFF. lia. }
  split.
  { intros a Ha. rewrite (F4 cid pos a Hin).
    - apply Hag. rewrite unsigned_lit_small by lia. intros Hg.
      exact (frm_img_x SEGS B ARx LAWS ly S hp W mem md cid pos a HAR0 Hin ltac:(lia) (proj1 (HG a Hg))).
    - left. unfold in_zr, frame_rng. cbn [fst snd]. lia.
    - intros HF. pose proof (NFP a HF). lia. }
  split.
  { apply (range_addressable_agree (aview SEGS (w_H W) mem) (aview SEGS (w_H W1) mem1) SHADOW_OFF PF (PLEN + 1));
      [|exact HRA].
    intros x Hx.
    pose proof (cshe_shadow_in_frame (frame_addr ly cid pos) (fs_frame_bytes cid) x Hal Hbal ltac:(lia)) as Hsx.
    unfold shadow_addr in Hsx. unfold shadow_of_addr.
    assert (Hx8 : 0 <= x / 8 < 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
    rewrite (F4 cid pos _ Hin).
    - apply Hag. rewrite unsigned_lit_small by (unfold SHADOW_OFF; lia). intros Hg.
      pose proof (pa_img_range _ (proj1 (HG _ Hg))). unfold SHADOW_OFF in *. lia.
    - right. unfold in_zr, shadow_addr. cbn [fst snd]. lia.
    - intros HF. pose proof (NFPs _ HF). lia. }
  split.
  { assert (EF : frame_addr ly1 cid pos = frame_addr ly cid pos).
    { destruct Hlay as (_ & _ & _ & _ & _ & HF & _). unfold frame_addr. rewrite HF. reflexivity. }
    apply (W_frame_x.shadow_hull_vis_of_frame_x SEGS B ARx LAWS FRMF ly1 S1 hp1 W1 mem1 md1 cid pos PF (PLEN + 1) HAR1);
      [rewrite Hfrs; exact Hin | rewrite EF; lia | rewrite EF; lia | lia]. }
  intros a Ha. lia.
Qed.
(* a strict journal is a journal at R (WLE_R): what the strict entry and loop 1, which call out to nobody, hand to
   the R segments after them *)
Lemma cshe_aj_xR_of_x : forall Gx XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k,
ajournal_gx_x SEGS B PST ARx Gx XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k ->
ajournal_gx_xR SEGS B PST ARx R Gx XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k.
Proof.
intros Gx XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k HJ.
eapply ajournal_gx_xR_mono; [exact WLE_R | exact HJ].
Qed.
(* cshe_n0_x at R: the strict entry (cshe_head_x), then the epilogue at R (cshe_epi_m_xR), composed by SRrG_bind;
   the source is carried over the entry by cshe_src_kept_xR *)
Lemma cshe_n0_xR : forall W ly S hp regs mem md ch XO AT HA (j : nat) PF h P A0 gone ob,
afn_pre_x SEGS B ARx CSHE_STK ly S hp W regs mem md ch ->
0 <= XO -> XO mod 16 = 0 -> spZ regs + XO <= ly_top ly ->
(forall a, spZ regs <= a < spZ regs + XO -> apresent (w_H W) mem a) ->
getr regs 10 = w64 HA -> getr regs 11 = w64 PF -> getr regs 12 = w64 AT ->
asrc_at B ly S W mem HA h ->
HA mod 8 = 0 -> 4096 <= HA ->
(forall a, HA + 64 <= a < HA + 96 -> inG G a) -> azs B (HA + 64) 32 ->
HA = VAL (A_OBJ 22) + ASRC * Z.of_nat j -> (j < 4)%nat ->
NoDup (CheckRep.texts (hs_held h)) ->
hl_n (hs_held h) < 2 ^ 26 ->
AT mod 8 = 0 -> spZ regs <= AT -> AT + 8 <= spZ regs + XO ->
val_mem SEGS (mrestrict (w_H W) mem) AT 8 A0 ->
val_mem SEGS (mrestrict (w_H W) mem) (VAL A_g_gone) 1 gone -> 0 <= gone < 256 ->
hl_n (hs_held h) = 0 ->
forall kr : nat, rp_RM RP S kr ->
SRrG SEGS R W (cfg_at SEGS A_csheP regs mem md)
  (cshe_post_xR B PST ARx R MT RP G regs ly S hp W mem md XO AT HA h P A0 gone ob kr).
Proof.
intros W ly S hp regs mem md ch XO AT HA j PF h P A0 gone ob HPRE HXO0 HXO16 HXtop HXp H10 H11 H12 HSRC
  Hal8 Hlo HGin Hzs EHA Hj HND HnH HAT8 HATlo HAThi MAT Mg Rg HN0 kr HRMk.
pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE.
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5). pose proof alloc_ceiling_val as ACV.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hshlo & Hshhi & H47 & Hbot & Htop & Htop2).
assert (WS : CSHE_STK = 16528) by reflexivity.
assert (Hj3 : Z.of_nat j <= 3) by lia.
(* the source sits inside g_s, so inside the image: the bounds cshe_head_x and cshe_src_low_x take *)
assert (HAhi : HA + 96 <= 0x5fb000).
{ pose proof (pa_img_range (HA + 95) (proj1 (HGS (HA + 95) ltac:(rewrite EHA; unfold ASRC in *; lia)))). lia. }
assert (HAlo : 0x10000 <= HA).
{ pose proof (pa_img_range HA (proj1 (HGS HA ltac:(rewrite EHA; unfold ASRC in *; lia)))). lia. }
(* every byte of the source is a byte of cshe_ro's g_s range, so HGRR keeps it off the runtime's two cells *)
assert (HAg : VAL (A_OBJ 22) <= HA /\ HA + 96 <= VAL (A_OBJ 22) + 384)
  by (rewrite EHA; unfold ASRC; lia).
assert (HROin : forall a, HA <= a < HA + 96 -> inG cshe_ro a).
{ intros a Ha. unfold inG, cshe_ro. apply Exists_exists. exists (VAL (A_OBJ 22), 384).
  split; [cbn [In]; right; right; right; left; reflexivity|].
  unfold in_zr. cbn [fst snd]. lia. }
assert (Hd0 : HA + ASRC <= VAL (A_OBJ 0) \/ VAL (A_OBJ 0) + 8 <= HA).
{ destruct (Z.le_gt_cases (HA + ASRC) (VAL (A_OBJ 0))) as [Hc|Hc]; [left; exact Hc|].
  destruct (Z.le_gt_cases (VAL (A_OBJ 0) + 8) HA) as [Hc2|Hc2]; [right; exact Hc2|].
  exfalso. unfold ASRC in Hc.
  destruct (Z.le_gt_cases HA (VAL (A_OBJ 0))) as [Hle|Hle].
  - destruct (HGRR (VAL (A_OBJ 0)) (HROin (VAL (A_OBJ 0)) ltac:(lia))) as (_ & Hx & _). apply Hx. lia.
  - destruct (HGRR HA (HROin HA ltac:(lia))) as (_ & Hx & _). apply Hx. lia. }
assert (Hd32 : HA + ASRC <= VAL (A_OBJ 32) \/ VAL (A_OBJ 32) + 8 <= HA).
{ destruct (Z.le_gt_cases (HA + ASRC) (VAL (A_OBJ 32))) as [Hc|Hc]; [left; exact Hc|].
  destruct (Z.le_gt_cases (VAL (A_OBJ 32) + 8) HA) as [Hc2|Hc2]; [right; exact Hc2|].
  exfalso. unfold ASRC in Hc.
  destruct (Z.le_gt_cases HA (VAL (A_OBJ 32))) as [Hle|Hle].
  - destruct (HGRR (VAL (A_OBJ 32)) (HROin (VAL (A_OBJ 32)) ltac:(lia))) as (_ & _ & Hx). apply Hx. lia.
  - destruct (HGRR HA (HROin HA ltac:(lia))) as (_ & _ & Hx). apply Hx. lia. }
assert (Hdg : HA + ASRC <= VAL A_g_gone \/ VAL A_g_gone + 1 <= HA).
{ destruct (Z.le_gt_cases (HA + ASRC) (VAL A_g_gone)) as [Hc|Hc]; [left; exact Hc|].
  destruct (Z.le_gt_cases (VAL A_g_gone + 1) HA) as [Hc2|Hc2]; [right; exact Hc2|].
  exfalso. unfold ASRC in Hc.
  destruct (HGS (VAL A_g_gone) ltac:(lia)) as (_ & _ & Hx & _). apply Hx. lia. }
(* g_gone is an image byte, so no byte of the frame *)
assert (HROg : inG cshe_ro (VAL A_g_gone)).
{ unfold inG, cshe_ro. apply Exists_exists. exists (VAL A_g_gone, 1).
  split; [cbn [In]; left; reflexivity|]. unfold in_zr. cbn [fst snd]. lia. }
assert (HGrange : 0x10000 <= VAL A_g_gone < 0x5fb000)
  by (pose proof (pa_img_range (VAL A_g_gone) (proj1 (HGR (VAL A_g_gone) HROg))); lia).
(* the held list's three cells, its writable head, and the bounds of its vector *)
pose proof HSRC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HHl & _).
pose proof HHl as (M80 & M88 & M92 & HAWR80 & Hcapb & Hvb & _).
replace (HA + 80 + 8) with (HA + 88) in M88 by lia.
replace (HA + 80 + 12) with (HA + 92) in M92 by lia.
assert (HNnn : 0 <= hl_n (hs_held h)) by (unfold hl_n; lia).
assert (RV : 0 <= hl_v (hs_held h) < 140737479966720 /\ hl_v (hs_held h) mod 16 = 0).
{ destruct Hvb as [(Hc0 & Hv0) | (Hc & Hvin & _)].
  - rewrite Hv0. split; [lia | reflexivity].
  - destruct (cshe_blk_x ly S hp W mem md _ _ HAR Hvin) as (H16 & H4096 & _ & _ & Hr1 & Hc2 & CC & _).
    split; [lia | exact H16]. }
(* the entry: held.n = 0, so the `blez s8` goes straight to the epilogue *)
unfold cfg_at. change (w64 A_csheP) with (Z_to_bv 64 A_csheP).
eapply (SRrG_bind SEGS R R_trans).
{ apply (SRr_SRrG SEGS R WLE_R).
  apply (cshe_head_x W ly S hp regs mem md ch HA gone (hl_v (hs_held h)) (hl_n (hs_held h)) (hl_cap (hs_held h))
    XO AT (blk_FP (list_blks (hs_held h))) PF HPRE HXO0 HXO16 HXtop HXp H10 H11 H12
    Hal8 Hlo ltac:(unfold ASRC; lia) Hzs HGin Hd0 Hd32 Hdg Mg Rg
    M80 ltac:(lia) ltac:(apply RV) M88 ltac:(lia) M92 ltac:(lia) HAWR80). }
cbv beta. intros W1 c1 Hwle1
  (regs1 & mem1 & md1 & pc1 & -> & HJ1 & Q1 & Q2 & Q3 & Q4 & KEEP1 & KEEPH & PRES1 & SAVED1 & MN1 & HARM).
destruct HARM as [(HNp & _) | (_ & ->)]; [exfalso; lia|].
assert (SRC1 : asrc_at B ly S W1 mem1 HA h).
{ apply (cshe_src_kept_xR ly S hp W W1 mem mem1 md HA h (spZ regs - 144) HAR HSRC HAlo HAhi
    ltac:(lia) Hwle1 ltac:(intros a Ha; apply KEEPH; lia) PRES1). }
(* the epilogue: it writes no byte at all *)
eapply (cshe_epi_m_xR W ly S hp mem md XO [(AT, AT + 8)] (blk_FP (list_blks (hs_held h))) ly S hp W1 regs regs1 mem1 md1 0
  _ (cshe_aj_xR_of_x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ1) Hra Hal16 ltac:(lia) ltac:(lia) Q2 Q3 Q4 SAVED1).
intros regs' mem2 md2 HPRES HMEQ HJ2.
assert (KEEPA : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 144 <= a < spZ regs) ->
  aview SEGS (w_H W1) mem2 a = aview SEGS (w_H W) mem a).
{ intros a Ha Hno. rewrite (aview_eq_of SEGS (w_H W1) mem1 mem2 a (HMEQ _)). exact (KEEPH a Ha Hno). }
assert (SRC2 : asrc_at B ly S W1 mem2 HA h).
{ apply (asrc_at_kept B ly S W1 mem1 ly S W1 mem2 HA h SRC1).
  - intros rr Hin a Ha. apply cshe_byte_meq. apply HMEQ.
  - intros b Hb. exact (cshe_src_blks ly S W1 mem1 HA h SRC1 b Hb). }
assert (HR0 : hl_recs (hs_held h) = []).
{ unfold hl_n in HN0. destruct (hl_recs (hs_held h)) as [|r rs]; [reflexivity | cbn [length] in HN0; lia]. }
unfold cshe_post_xR.
exists ly, S, hp, regs', mem2, md2, 0, (hs_held h), ([] : list (Z * list byte)), 0.
split; [reflexivity|].
split; [exact HJ2|].
split; [exact HPRES|].
split; [intros jj Hjj; destruct (cshe_errno_out jj Hjj) as [Hr Hl]; apply KEEPA;
        [exact Hr | unfold CSHE_STK, CSHE_FRAME, ASTACK in *; lia]|].
split; [rewrite cshe_set_held_id; exact SRC2|].
split; [reflexivity|]. split; [reflexivity|]. split; [exact HND|].
split.
{ destruct (Z.eq_dec gone 0) as [Hg0|Hg0].
  - right. split; [exact Hg0|]. rewrite HR0.
    assert (HW0 : CheckRep.want_of P [] = 0%nat) by reflexivity. rewrite HW0. reflexivity.
  - left. split; [exact Hg0|]. rewrite HR0. cbn [filter].
    split; [reflexivity|]. split; [reflexivity | reflexivity]. }
split; [lia|].
split.
{ replace (A0 + 0) with A0 by lia.
  apply (cshe_vm_keep W W1 mem mem2 AT 8 A0); [|exact MAT].
  intros x Hx. cbn [Z.of_nat] in Hx. apply KEEPA; lia. }
split.
{ apply (cshe_vm_keep W W1 mem mem2 (VAL A_g_gone) 1 gone); [|exact Mg].
  intros x Hx. cbn [Z.of_nat] in Hx. apply KEEPA; lia. }
split; [unfold cshe_ds_blks; cbn [map app]; intros rest Hp; exact Hp|].
split; [reflexivity|].
split; [unfold cshe_cost; rewrite HN0, Z.mul_0_l; exact (mo_le_refl MT ML S) | exact HRMk].
Qed.
(* cshe_want0_x at R: the runs conclude SRrG SEGS R (paj_run_x_xG / paj_run_to_x_xG, the branch paj_branch_xR), so
   the epilogue at R (cshe_epi_m_xR) closes the goal *)
Lemma cshe_want0_xR : forall (W : world SEGS) ly S hp regs mem md (W0 : world SEGS) regs0 mem0 md0
XO AT HA PF VE SBV SBH gone N a0v s5v (h : hsrc) (P : list byte) A0 ob,
cshe_tst_regs regs (spZ regs0) HA PF AT VE SBV SBH N a0v s5v 0 ->
cshe_tst_ok (spZ regs0) HA N a0v s5v 0 gone ->
getr regs 3 = getr regs0 3 -> getr regs 4 = getr regs0 4 ->
val_mem SEGS (mrestrict (w_H W) mem) (spZ regs0 - 136) 8 N ->
val_mem SEGS (mrestrict (w_H W) mem) (VAL A_g_gone) 1 gone ->
(forall a, spZ regs0 - 144 <= a < spZ regs0 -> apresent (w_H W) mem a) ->
gone = 0 -> CheckRep.want_of P (hl_recs (hs_held h)) = 0%nat ->
XO mod 16 = 0 -> alloc_ceiling + CSHE_STK <= spZ regs0 -> spZ regs0 <= 2 ^ 47 -> spZ regs0 mod 16 = 0 ->
YK0s.ret_ok (getr regs0 1) ->
ajournal_gx_xR SEGS B PST ARx R G XO [(AT, AT + 8)] CSHE_STK (spZ regs0) (blk_FP (list_blks (hs_held h)))
  ly S hp W0 mem0 md0 [] ly S hp W mem md 0 ->
cshe_saved W mem (spZ regs0) regs0 ->
asrc_at B ly S W mem HA h ->
NoDup (CheckRep.texts (hs_held h)) ->
val_mem SEGS (mrestrict (w_H W) mem) AT 8 A0 ->
(* errno's view at 0x85498 is the entry's (cshe_to_tst's last conjunct) *)
(forall j, 0 <= j < 4 -> aview SEGS (w_H W) mem (as_errno B + j) = aview SEGS (w_H W0) mem0 (as_errno B + j)) ->
forall kr : nat, rp_RM RP S kr ->
SRrG SEGS R W (mkCfg (mkst regs (Z_to_bv 64 (BASE + A_cshe_tst + 4)) mem (seg_rom SEGS)) md)
  (cshe_post_xR B PST ARx R MT RP G regs0 ly S hp W0 mem0 md0 XO AT HA h P A0 gone ob kr).
Proof.
intros W ly S hp regs mem md W0 regs0 mem0 md0 XO AT HA PF VE SBV SBH gone N a0v s5v h P A0 ob
  HR HK H3 H4 MN Mg Hpres Hgone HW0 HXO16 HCL0 H47 Hal16 Hra HJ HSAV HSRC HND MAT HERR kr HRMk.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
pose proof HR as (R2 & R8 & R9 & R10 & R11 & R18 & R19 & R20 & R21 & R22 & R23 & R24 & R25 & R26 & R27).
pose proof HK as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11).
destruct (cshe_tst_state W regs mem (spZ regs0) HA PF AT VE SBV SBH gone N a0v s5v 0 HR HK MN Mg Hpres) as [HS _].
remember (Eimg (Ereg regs (cshe_tst_extra gone N))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EEo : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs rr).
{ intros n rr Hn. subst E. pose proof (bv_unsigned_in_range 5 rr) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn. }
assert (E2 : ew E 2 = Z_to_bv 64 (spZ regs0 - 144)) by (rewrite (EEo 2%nat 2%bv eq_refl); exact R2).
assert (E11 : ew E 11 = Z_to_bv 64 0) by (rewrite (EEo 11%nat 11%bv eq_refl); exact R11).
assert (E32 : ew E 32 = Z_to_bv 64 gone)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs0 - 144) by (rewrite E2; apply unsigned_lit_small; lia).
assert (SHOK : sh_ok SEGS Bx1 ([] : list shent) E (mrestrict (w_H W) mem)) by constructor.
pose (RUNTOx := paj_run_to_x_xG B PST ARx LAWS R G HG XO [(AT, AT + 8)]).
pose (RUNx := paj_run_x_xG B PST ARx LAWS R G HG XO [(AT, AT + 8)]).
pose (BRx := paj_branch_xR (PI := PI) (R := R)).
(* the load of g_gone, up to the branch *)
paj_run_tok_xR RUNx HS HJ SHOK Bspan.
{ apply awr_ok_x_cons; [|apply awr_ok_x_cons; [|apply awr_ok_x_nil]].
  - intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi cshe_tstR0] in Ha. lia.
  - intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi cshe_gone] in Ha. lia. }
assert (MEQ1 : forall x : word, mrestrict (w_H W) (ms_mem ms) x = mrestrict (w_H W) mem x).
{ intros x. lazymatch goal with Hf : frame_of ?Ev ?rs (mrestrict (w_H W) mem) _ |- _ => apply (Hf x) end.
  intros (r & Hin & Hr). cbn [ss_mem In] in Hin.
  destruct Hin as [<- | [<- | []]];
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi cshe_tstR0 cshe_gone] in Hr; lia. }
psrr_branch_tok RUNx BRx HS SHOK Bspan.
- (* g_gone = 0: on to the want test at 0x85578 *)
  paj_run_tok_xR RUNx HS HJ SHOK Bspan.
  { apply awr_ok_x_cons; [|apply awr_ok_x_cons; [|apply awr_ok_x_nil]].
    - intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi cshe_tstR0] in Ha. lia.
    - intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi cshe_gone] in Ha. lia. }
  assert (MEQ2 : forall x : word, mrestrict (w_H W) (ms_mem ms0) x = mrestrict (w_H W) (ms_mem ms) x).
  { intros x. lazymatch goal with Hf : frame_of ?Ev ?rs (mrestrict (w_H W) (ms_mem ms)) _ |- _ => apply (Hf x) end.
    intros (r & Hin & Hr). cbn [ss_mem In] in Hin.
    destruct Hin as [<- | [<- | []]];
      cbn [YP09.r_base YP09.r_wlo YP09.r_whi cshe_tstR0 cshe_gone] in Hr; lia. }
  psrr_branch_tok RUNx BRx HS SHOK Bspan.
  + (* want = 0: straight to the epilogue *)
    paj_run_to_tok_xR RUNTOx HS HJ SHOK Bspan A_cshe_ret.
    { apply awr_ok_x_cons; [|apply awr_ok_x_cons; [|apply awr_ok_x_nil]].
      - intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi cshe_tstR0] in Ha. lia.
      - intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi cshe_gone] in Ha. lia. }
    assert (MEQ3 : forall x : word, mrestrict (w_H W) (ms_mem ms1) x = mrestrict (w_H W) (ms_mem ms0) x).
    { intros x. lazymatch goal with Hf : frame_of ?Ev ?rs (mrestrict (w_H W) (ms_mem ms0)) _ |- _ => apply (Hf x) end.
      intros (r & Hin & Hr). cbn [ss_mem In] in Hin.
      destruct Hin as [<- | [<- | []]];
        cbn [YP09.r_base YP09.r_wlo YP09.r_whi cshe_tstR0 cshe_gone] in Hr; lia. }
    assert (MEQ : forall x : word, mrestrict (w_H W) (ms_mem ms1) x = mrestrict (w_H W) mem x)
      by (intros x; rewrite MEQ3, MEQ2; exact (MEQ1 x)).
    prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
    pmkst HS.
    eapply (cshe_epi_m_xR W0 ly S hp mem0 md0 XO [(AT, AT + 8)] (blk_FP (list_blks (hs_held h))) ly S hp W regs0);
      [ exact HJ | exact Hra | exact Hal16 | exact HCL0 | exact H47
      | cbn [ms_regs]; rewrite P2; exact E2
      | cbn [ms_regs]; rewrite P3, (EEo 3%nat 3%bv eq_refl); exact H3
      | cbn [ms_regs]; rewrite P4, (EEo 4%nat 4%bv eq_refl); exact H4
      | cbn [ms_mem]; exact (cshe_saved_meq W mem (ms_mem ms1) (spZ regs0) regs0 MEQ HSAV) |].
    cbn [ms_mem]. intros regs' mem2 md2 HPRES HMEQ HJ2.
    assert (MEQa : forall x : word, mrestrict (w_H W) mem2 x = mrestrict (w_H W) mem x)
      by (intros x; rewrite HMEQ; exact (MEQ x)).
    unfold cshe_post_xR.
    exists ly, S, hp, regs', mem2, md2, 0, (hs_held h), ([] : list (Z * list byte)), 0.
    split; [reflexivity|].
    split; [exact HJ2|].
    split; [exact HPRES|].
    split; [intros jj Hjj; rewrite (aview_eq_of SEGS (w_H W) mem mem2 _ (MEQa _)); exact (HERR jj Hjj)|].
    split.
    { rewrite cshe_set_held_id.
      apply (asrc_at_kept B ly S W mem ly S W mem2 HA h HSRC).
      - intros rr Hin a Ha. apply cshe_byte_meq. apply MEQa.
      - intros b Hb. exact (cshe_src_blks ly S W mem HA h HSRC b Hb). }
    split; [reflexivity|]. split; [reflexivity|]. split; [exact HND|].
    split; [right; split; [exact Hgone|]; rewrite HW0; reflexivity|].
    split; [lia|].
    split.
    { replace (A0 + 0) with A0 by lia.
      apply (cshe_vm_keep W W mem mem2 AT 8 A0); [|exact MAT].
      intros x Hx. apply (aview_eq_of SEGS). apply MEQa. }
    split.
    { apply (cshe_vm_keep W W mem mem2 (VAL A_g_gone) 1 gone); [|exact Mg].
      intros x Hx. apply (aview_eq_of SEGS). apply MEQa. }
    split; [unfold cshe_ds_blks; cbn [map app]; intros rest Hp; exact Hp|].
    split; [reflexivity|].
    split; [|exact HRMk].
    apply (mle_weaken MT S S 0 (cshe_cost (hs_held h)) ML (mo_le_refl MT ML S)).
    unfold cshe_cost. apply Z.mul_nonneg_nonneg; [unfold hl_n; lia | exact (mo_free_nonneg MT ML)].
  + (* want <> 0: not this arm *)
    exfalso. rewrite branch_eq_U, (U_lit E 0 ltac:(lia)), (U_atom E 11 0 E11 ltac:(lia)) in Hc0.
    cbn in Hc0. discriminate Hc0.
- (* g_gone <> 0: not this arm *)
  exfalso. rewrite branch_eq_U, (U_lit E 0 ltac:(lia)), (U_atom E 32 gone E32 ltac:(lia)) in Hc.
  rewrite Hgone in Hc. cbn in Hc. discriminate Hc.
Qed.
(* cshe_to_tst_x at R.  The entry and loop 1 call out only to has_prefix, a strict leaf contract, so they move no
   world: the strict walk lifted by SRr_SRrG, its journal weakened to R at the end (cshe_aj_xR_of_x) *)
Lemma cshe_to_tst_xR : forall W ly S hp regs mem md ch XO AT HA (j : nat) PF h P A0 gone,
afn_pre_x SEGS B ARx CSHE_STK ly S hp W regs mem md ch ->
0 <= XO -> XO mod 16 = 0 -> spZ regs + XO <= ly_top ly ->
(forall a, spZ regs <= a < spZ regs + XO -> apresent (w_H W) mem a) ->
getr regs 10 = w64 HA -> getr regs 11 = w64 PF -> getr regs 12 = w64 AT ->
asrc_at B ly S W mem HA h ->
HA mod 8 = 0 -> 4096 <= HA ->
(forall a, HA + 64 <= a < HA + 96 -> inG G a) -> azs B (HA + 64) 32 ->
HA = VAL (A_OBJ 22) + ASRC * Z.of_nat j -> (j < 4)%nat ->
hl_n (hs_held h) < 2 ^ 26 ->
(forall a, hl_v (hs_held h) <= a < hl_v (hs_held h) + AREC * hl_cap (hs_held h) ->
  ~ (spZ regs - CSHE_STK <= a < spZ regs + XO)) ->
(forall r, In r (hl_recs (hs_held h)) -> forall a, fst r <= a < fst r + Z.of_nat (length (snd r)) + 1 ->
  ~ (spZ regs - CSHE_STK <= a < spZ regs + XO)) ->
spZ regs <= AT -> AT + 8 <= spZ regs + XO ->
val_mem SEGS (mrestrict (w_H W) mem) AT 8 A0 ->
~ In (Z_to_bv 8 0) P -> Z.of_nat (length P) + 1 < 2 ^ 32 -> 0 < PF -> PF + Z.of_nat (length P) + 8 <= 2 ^ 63 ->
(forall i, 0 <= i < Z.of_nat (length P) ->
   aview SEGS (w_H W) mem (PF + i) = Some (bv_unsigned (nth (Z.to_nat i) P (Z_to_bv 8 0)))) ->
aview SEGS (w_H W) mem (PF + Z.of_nat (length P)) = Some 0 ->
(forall a, PF <= a < PF + Z.of_nat (length P) + 8 -> aview SEGS (w_H W) mem a <> None /\
   ~ (spZ regs - CSHE_STK <= a < spZ regs + XO)) ->
amem_range PF (Z.of_nat (length P) + 1) -> amem_range PF 8 ->
range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF PF (Z.of_nat (length P) + 1) ->
shadow_hull_vis (aview SEGS (w_H W) mem) PF (Z.of_nat (length P) + 1) ->
rom_view SEGS W mem ->
val_mem SEGS (mrestrict (w_H W) mem) (VAL A_g_gone) 1 gone -> 0 <= gone < 256 ->
0 < hl_n (hs_held h) ->
SRrG SEGS R W (cfg_at SEGS A_csheP regs mem md)
(fun W' c' => exists regs' mem' md' a0v s5v,
 c' = mkCfg (mkst regs' (Z_to_bv 64 (BASE + A_cshe_tst + 4)) mem' (seg_rom SEGS)) md' /\
 ajournal_gx_xR SEGS B PST ARx R G XO [(AT, AT + 8)] CSHE_STK (spZ regs) (blk_FP (list_blks (hs_held h)))
   ly S hp W mem md [] ly S hp W' mem' md' 0 /\
 cshe_tst_regs regs' (spZ regs) HA PF AT (hl_v (hs_held h) + AREC * hl_n (hs_held h))
   (SB + (hl_v (hs_held h) + AREC * hl_n (hs_held h)) / 8) ((HA + 80) / 8 + SB)
   (hl_n (hs_held h)) a0v s5v (Z.of_nat (CheckRep.want_of P (hl_recs (hs_held h)))) /\
 cshe_tst_ok (spZ regs) HA (hl_n (hs_held h)) a0v s5v
   (Z.of_nat (CheckRep.want_of P (hl_recs (hs_held h)))) gone /\
 getr regs' 3 = getr regs 3 /\ getr regs' 4 = getr regs 4 /\
 cshe_saved W' mem' (spZ regs) regs /\
 val_mem SEGS (mrestrict (w_H W') mem') (spZ regs - 136) 8 (hl_n (hs_held h)) /\
 val_mem SEGS (mrestrict (w_H W') mem') (spZ regs - 128) 8 ((HA + 88) / 8 + SB) /\
 val_mem SEGS (mrestrict (w_H W') mem') (VAL A_g_gone) 1 gone /\
 val_mem SEGS (mrestrict (w_H W') mem') AT 8 A0 /\
 (forall a, spZ regs - 144 <= a < spZ regs -> apresent (w_H W') mem' a) /\
 asrc_at B ly S W' mem' HA h /\
 (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - CSHE_STK <= a < spZ regs) ->
   aview SEGS (w_H W') mem' a = aview SEGS (w_H W) mem a) /\
 (forall a, apresent (w_H W) mem a -> apresent (w_H W') mem' a) /\
 (* errno's view is the entry's (cshe_post's conjunct; loops 2 and 3 take it at their heads) *)
 (forall j, 0 <= j < 4 -> aview SEGS (w_H W') mem' (as_errno B + j) = aview SEGS (w_H W) mem (as_errno B + j))).
Proof.
intros W ly S hp regs mem md ch XO AT HA j PF h P A0 gone HPRE HXO0 HXO16 HXtop HXp H10 H11 H12 HSRC
  Hal8 Hlo HGin Hzs EHA Hj HnH HVoff HRoff HATlo HAThi MAT HPnz HP32 HPF0 HPFk HPby HPnul HPvis
  HPmr1 HPmr8 HPra1 HPshv1 HROM Mg Rg HNp.
apply (SRr_SRrG SEGS R WLE_R).
pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE.
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5). pose proof alloc_ceiling_val as ACV.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hshlo & Hshhi & H47 & Hbot & Htop & Htop2).
assert (WS : CSHE_STK = 16528) by reflexivity.
assert (Hj3 : Z.of_nat j <= 3) by lia.
assert (HAhi : HA + 96 <= 0x5fb000).
{ pose proof (pa_img_range (HA + 95) (proj1 (HGS (HA + 95) ltac:(rewrite EHA; unfold ASRC in *; lia)))). lia. }
assert (HAlo : 0x10000 <= HA).
{ pose proof (pa_img_range HA (proj1 (HGS HA ltac:(rewrite EHA; unfold ASRC in *; lia)))). lia. }
assert (HAg : VAL (A_OBJ 22) <= HA /\ HA + 96 <= VAL (A_OBJ 22) + 384)
  by (rewrite EHA; unfold ASRC; lia).
assert (HROin : forall a, HA <= a < HA + 96 -> inG cshe_ro a).
{ intros a Ha. unfold inG, cshe_ro. apply Exists_exists. exists (VAL (A_OBJ 22), 384).
  split; [cbn [In]; right; right; right; left; reflexivity|].
  unfold in_zr. cbn [fst snd]. lia. }
assert (Hd0 : HA + ASRC <= VAL (A_OBJ 0) \/ VAL (A_OBJ 0) + 8 <= HA).
{ destruct (Z.le_gt_cases (HA + ASRC) (VAL (A_OBJ 0))) as [Hc|Hc]; [left; exact Hc|].
  destruct (Z.le_gt_cases (VAL (A_OBJ 0) + 8) HA) as [Hc2|Hc2]; [right; exact Hc2|].
  exfalso. unfold ASRC in Hc.
  destruct (Z.le_gt_cases HA (VAL (A_OBJ 0))) as [Hle|Hle].
  - destruct (HGRR (VAL (A_OBJ 0)) (HROin (VAL (A_OBJ 0)) ltac:(lia))) as (_ & Hx & _). apply Hx. lia.
  - destruct (HGRR HA (HROin HA ltac:(lia))) as (_ & Hx & _). apply Hx. lia. }
assert (Hd32 : HA + ASRC <= VAL (A_OBJ 32) \/ VAL (A_OBJ 32) + 8 <= HA).
{ destruct (Z.le_gt_cases (HA + ASRC) (VAL (A_OBJ 32))) as [Hc|Hc]; [left; exact Hc|].
  destruct (Z.le_gt_cases (VAL (A_OBJ 32) + 8) HA) as [Hc2|Hc2]; [right; exact Hc2|].
  exfalso. unfold ASRC in Hc.
  destruct (Z.le_gt_cases HA (VAL (A_OBJ 32))) as [Hle|Hle].
  - destruct (HGRR (VAL (A_OBJ 32)) (HROin (VAL (A_OBJ 32)) ltac:(lia))) as (_ & _ & Hx). apply Hx. lia.
  - destruct (HGRR HA (HROin HA ltac:(lia))) as (_ & _ & Hx). apply Hx. lia. }
assert (Hdg : HA + ASRC <= VAL A_g_gone \/ VAL A_g_gone + 1 <= HA).
{ destruct (Z.le_gt_cases (HA + ASRC) (VAL A_g_gone)) as [Hc|Hc]; [left; exact Hc|].
  destruct (Z.le_gt_cases (VAL A_g_gone + 1) HA) as [Hc2|Hc2]; [right; exact Hc2|].
  exfalso. unfold ASRC in Hc.
  destruct (HGS (VAL A_g_gone) ltac:(lia)) as (_ & _ & Hx & _). apply Hx. lia. }
assert (HROg : inG cshe_ro (VAL A_g_gone)).
{ unfold inG, cshe_ro. apply Exists_exists. exists (VAL A_g_gone, 1).
  split; [cbn [In]; left; reflexivity|]. unfold in_zr. cbn [fst snd]. lia. }
assert (HGrange : 0x10000 <= VAL A_g_gone < 0x5fb000)
  by (pose proof (pa_img_range (VAL A_g_gone) (proj1 (HGR (VAL A_g_gone) HROg))); lia).
(* the held list: its three cells, its vector's block, and its records *)
pose proof HSRC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HHl & _).
pose proof HHl as (M80 & M88 & M92 & HAWR80 & Hcapb & Hvb & _ & _ & HFrec).
replace (HA + 80 + 8) with (HA + 88) in M88 by lia.
replace (HA + 80 + 12) with (HA + 92) in M92 by lia.
assert (HNn : hl_n (hs_held h) = Z.of_nat (length (hl_recs (hs_held h)))) by reflexivity.
destruct Hvb as [(Hc0 & Hv0) | (Hcpos & Hvin & Hjunk & Hgv)]; [unfold hl_n in *; lia|].
destruct (cshe_blk_x ly S hp W mem md _ _ HAR Hvin)
  as (Hv16 & Hv4096 & _ & Hvle & Hvreq1 & Hvceil & _ & _ & Hvapp & _).
(* the entry *)
unfold cfg_at. change (w64 A_csheP) with (Z_to_bv 64 A_csheP).
eapply SRr_bind.
{ apply (cshe_head_x W ly S hp regs mem md ch HA gone (hl_v (hs_held h)) (hl_n (hs_held h)) (hl_cap (hs_held h))
    XO AT (blk_FP (list_blks (hs_held h))) PF HPRE HXO0 HXO16 HXtop HXp H10 H11 H12
    Hal8 Hlo ltac:(unfold ASRC; lia) Hzs HGin Hd0 Hd32 Hdg Mg Rg
    M80 ltac:(lia) ltac:(exact Hv16) M88 ltac:(unfold hl_n in *; lia) M92 ltac:(lia) HAWR80). }
cbv beta. intros W1 c1 Hwle1
  (regs1 & mem1 & md1 & pc1 & -> & HJ1 & Q1 & Q2 & Q3 & Q4 & KEEP1 & KEEPF & PRES1 & SAVED1 & MN1 & HARM).
destruct HARM as
  [(_ & -> & MSP8 & MSP16 & R8 & R9 & R11 & R18 & R19 & R20 & R22 & R23 & R24 & R25 & R26 & R27) | (HN0 & _)];
  [|exfalso; unfold hl_n in *; lia].
assert (HCEIL : alloc_ceiling <= spZ regs - 144) by (unfold CSHE_STK, CSHE_FRAME, ASTACK in *; lia).
(* loop 1's prefix invariant, at the entry state and then at the loop head *)
assert (HPFX0 : cshe_l1_pfx W mem (spZ regs) PF P).
{ unfold cshe_l1_pfx. cbv zeta.
  split.
  { intros t Ht. rewrite length_app in Ht. cbn [length] in Ht.
    destruct (Z.lt_ge_cases t (Z.of_nat (length P))) as [Hlt|Hge].
    - rewrite (HPby t ltac:(lia)). do 2 f_equal. symmetry. apply app_nth1. lia.
    - assert (Ht' : t = Z.of_nat (length P)) by lia. subst t.
      rewrite HPnul. rewrite app_nth2 by lia.
      replace (Z.to_nat (Z.of_nat (length P)) - length P)%nat with 0%nat by lia. cbn [nth].
      rewrite (cshe_u8 0 ltac:(lia)). reflexivity. }
  split; [intros a Ha; exact (proj1 (HPvis a Ha))|].
  split; [intros a Ha; pose proof (proj2 (HPvis a Ha));
          unfold CSHE_STK, CSHE_FRAME, ASTACK, HP_STK, ESTACK in *; lia|].
  split; [exact HPmr1|]. split; [exact HPmr8|]. split; [exact HPra1|]. split; [exact HPshv1|].
  split; [eapply range_addressable_sub; [exact HPra1 | lia | lia]|].
  split; [intros Hp; exact (cshe_shv_sub _ PF (Z.of_nat (length P) + 1) (Z.of_nat (length P))
            ltac:(lia) ltac:(lia) HPshv1)|].
  exact HROM. }
assert (HPFX : cshe_l1_pfx W1 mem1 (spZ regs) PF P).
{ apply (cshe_l1_pfx_kept2 W W1 mem mem1 (spZ regs) (spZ regs - 144) (spZ regs) PF P
    HCEIL HPF0 ltac:(lia) ltac:(intros y Hy Hno; exact (KEEPF y Hy Hno))
    ltac:(intros y Hy; pose proof (proj2 (HPvis y Hy));
          unfold CSHE_STK, CSHE_FRAME, ASTACK in *; lia) HPFX0). }
(* loop 1's vector invariant at i = 0, likewise *)
assert (HVEC0 : cshe_l1_vec ly S W mem (spZ regs) (hl_v (hs_held h)) P (hl_recs (hs_held h)) 0).
{ intros jj Hjj.
  assert (Hjn : (Z.to_nat jj < length (hl_recs (hs_held h)))%nat) by lia.
  assert (Hin : In (nth (Z.to_nat jj) (hl_recs (hs_held h)) (0, [])) (hl_recs (hs_held h)))
    by (apply nth_In; exact Hjn).
  rewrite Forall_forall in HFrec. destruct (HFrec _ Hin) as (Hrin & Hrg & Hrlines & _).
  destruct (cshe_blk_x ly S hp W mem md _ _ HAR Hrin)
    as (_ & Hr4096 & _ & Hrle & Hrreq1 & Hrceil & _ & _ & Hrapp & _).
  destruct (cshe_rec_fields ly S W mem (HA + 80) (hs_held h) true (Z.to_nat jj) HHl Hjn) as [Mslot Mlen].
  destruct (Hrlines eq_refl) as (_ & Hrlen).
  assert (HEQ : hl_v (hs_held h) + 16 * Z.of_nat (Z.to_nat jj) = hl_v (hs_held h) + AREC * jj)
    by (unfold AREC; lia).
  rewrite HEQ in Mslot, Mlen.
  unfold cshe_l1_rec. cbv zeta.
  split.
  { replace (fst (nth (Z.to_nat jj) (hl_recs (hs_held h)) (0, [])))
    with (fst (nth (Z.to_nat jj) (hl_recs (hs_held h)) (0, [])) mod 2 ^ 64) by (apply Z.mod_small; lia).
    exact Mslot. }
  split.
  { replace (Z.of_nat (length (snd (nth (Z.to_nat jj) (hl_recs (hs_held h)) (0, [])))))
    with (Z.of_nat (length (snd (nth (Z.to_nat jj) (hl_recs (hs_held h)) (0, [])))) mod 2 ^ 64)
    by (apply Z.mod_small; unfold APARTIAL in Hrlen; lia).
    exact Mlen. }
  split.
  { apply (range_addressable_of_block_hp0_x SEGS B ARx LAWS HP0 ly S hp W mem md (hl_v (hs_held h))
      (AREC * hl_cap (hs_held h)) (hl_v (hs_held h) + AREC * jj) 16 HAR Hvin);
    unfold AREC in *; unfold hl_n in *; lia. }
  split.
  { apply (YCe5x.amem_range_of_block_x SEGS B ARx LAWS ly S hp W mem md (hl_v (hs_held h))
      (AREC * hl_cap (hs_held h)) (hl_v (hs_held h) + AREC * jj) 16 HAR Hvin);
    unfold AREC in *; unfold hl_n in *; lia. }
  split.
  { intros a Ha. pose proof (HVoff a ltac:(unfold AREC in *; unfold hl_n in *; lia)).
    unfold CSHE_STK, CSHE_FRAME, ASTACK, HP_STK, ESTACK in *. lia. }
  split.
  { exists (hl_v (hs_held h)), (AREC * hl_cap (hs_held h)).
    split; [exact Hvin|]. split; [unfold AREC; lia | unfold AREC in *; unfold hl_n in *; lia]. }
  split; [lia|].
  split; [unfold APARTIAL in Hrlen; lia|].
  split; [apply cshe_bytes_of_garr8; exact Hrg|].
  split.
  { intros a Ha. pose proof (HRoff _ Hin a ltac:(lia)).
    unfold CSHE_STK, CSHE_FRAME, ASTACK, HP_STK, ESTACK in *. lia. }
  intros Hle.
  split.
  { apply (YCe5x.amem_range_of_block_x SEGS B ARx LAWS ly S hp W mem md
      (fst (nth (Z.to_nat jj) (hl_recs (hs_held h)) (0, [])))
      (Z.of_nat (length (snd (nth (Z.to_nat jj) (hl_recs (hs_held h)) (0, [])))) + 1)
      (fst (nth (Z.to_nat jj) (hl_recs (hs_held h)) (0, []))) (Z.of_nat (length P)) HAR Hrin); lia. }
  split.
  { apply (range_addressable_of_block_hp0_x SEGS B ARx LAWS HP0 ly S hp W mem md
      (fst (nth (Z.to_nat jj) (hl_recs (hs_held h)) (0, [])))
      (Z.of_nat (length (snd (nth (Z.to_nat jj) (hl_recs (hs_held h)) (0, [])))) + 1)
      (fst (nth (Z.to_nat jj) (hl_recs (hs_held h)) (0, []))) (Z.of_nat (length P)) HAR Hrin); lia. }
  intros Hp.
  apply (shadow_hull_vis_of_block_hp0_x SEGS B ARx LAWS HP0 ly S hp W mem md
    (fst (nth (Z.to_nat jj) (hl_recs (hs_held h)) (0, [])))
    (Z.of_nat (length (snd (nth (Z.to_nat jj) (hl_recs (hs_held h)) (0, [])))) + 1)
    (fst (nth (Z.to_nat jj) (hl_recs (hs_held h)) (0, []))) (Z.of_nat (length P)) HAR Hrin); lia. }
assert (HVEC : cshe_l1_vec ly S W1 mem1 (spZ regs) (hl_v (hs_held h)) P (hl_recs (hs_held h)) 0).
{ intros jj Hjj.
  assert (Hin : In (nth (Z.to_nat jj) (hl_recs (hs_held h)) (0, [])) (hl_recs (hs_held h)))
    by (apply nth_In; lia).
  apply (cshe_l1_rec_kept2 ly S W W1 mem mem1 (spZ regs) (spZ regs - 144) (spZ regs)
    (hl_v (hs_held h)) P (nth (Z.to_nat jj) (hl_recs (hs_held h)) (0, [])) jj HCEIL
    ltac:(unfold AREC; lia)
    ltac:(intros y Hy Hno; exact (KEEPF y Hy Hno))
    ltac:(intros y Hy; pose proof (HVoff y ltac:(unfold AREC in *; unfold hl_n in *; lia));
          unfold CSHE_STK, CSHE_FRAME, ASTACK in *; lia)
    ltac:(intros y Hy; pose proof (HRoff _ Hin y ltac:(lia));
          unfold CSHE_STK, CSHE_FRAME, ASTACK in *; lia)
    (HVEC0 jj Hjj)). }
(* loop 1 *)
eapply SRr_bind.
{ apply (cshe_l1_loop_x (Z.to_nat (hl_n (hs_held h))) 0 W1 ly S hp regs1 mem1 md1 ly S hp W mem md XO AT
    (blk_FP (list_blks (hs_held h))) (spZ regs) 0 PF P (hl_v (hs_held h)) (hl_n (hs_held h))
    (hl_recs (hs_held h)));
  [ lia | lia | exact HNn | exact HnH | exact HP32 | exact HPF0 | lia | exact HPnz
  | lia | unfold AREC in *; unfold hl_n in *; lia | exact Hv16
  | exact Q2
  | rewrite R11; reflexivity
  | replace (hl_n (hs_held h) - 0) with (hl_n (hs_held h)) by lia; exact R22
  | replace (hl_v (hs_held h) + AREC * 0) with (hl_v (hs_held h)) by (unfold AREC; lia); exact R20
  | replace (hl_v (hs_held h) + AREC * 0 + 8) with (hl_v (hs_held h) + 8) by (unfold AREC; lia); exact R27
  | replace (hl_v (hs_held h) + AREC * 0) with (hl_v (hs_held h)) by (unfold AREC; lia); exact R23
  | exact R25 | exact R9
  | rewrite Q3; exact Hgp | rewrite Q4; exact Htp
  | unfold s0Z; rewrite R8; rewrite unsigned_lit_small by lia; lia
  | lia | ( apply Z.mod_divide in Hal16; [|lia]; apply Z.mod_divide; [lia|];
            apply Z.divide_sub_r; [exact Hal16 | exists 9; reflexivity] )
  | exact HXO16 | lia | exact HJ1 | exact HPFX | exact HVEC ]. }
cbv beta. intros W2 c2 Hwle2 (regs2 & mem2 & md2 & a0v & s5v & -> & HJ2 & T11 & T10 & T21 & Ta0 & Ta1 & Ts5
  & Tsum & T22 & T20 & T27 & T23 & T2 & T3 & T4 & T8 & T9 & T18 & T19 & T24 & T25 & T26 & KEEP2 & PRES2).
(* the composite keep clause and the facts the arms take *)
assert (KEEPB : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - CSHE_STK <= a < spZ regs) ->
  aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) mem a).
{ intros a Ha Hno.
  rewrite (KEEP2 a Ha ltac:(unfold CSHE_STK, CSHE_FRAME, ASTACK, HP_STK, ESTACK in *; lia)).
  exact (KEEPF a Ha ltac:(unfold CSHE_STK, CSHE_FRAME, ASTACK in *; lia)). }
assert (HWle : (CheckRep.want_of P (hl_recs (hs_held h)) <= length (hl_recs (hs_held h)))%nat)
  by apply cshe_want_le.
apply SRr_ret.
exists regs2, mem2, md2, a0v, s5v.
split; [reflexivity|].
split; [apply cshe_aj_xR_of_x; exact HJ2|].
split.
{ unfold cshe_tst_regs.
  split; [rewrite T2; exact Q2|].
  split; [rewrite T8; exact R8|].
  split; [rewrite T9; exact R9|].
  split; [exact T10|]. split; [exact T11|].
  split; [rewrite T18; exact R18|].
  split; [rewrite T19; exact R19|].
  split; [exact T20|]. split; [exact T21|]. split; [exact T22|]. split; [exact T23|].
  split; [rewrite T24; exact R24|].
  split; [rewrite T25; exact R25|].
  split; [rewrite T26; exact R26 | exact T27]. }
split.
{ unfold cshe_tst_ok.
  split; [lia|]. split; [apply Z.mod_divide in Hal16; [|lia]; apply Z.mod_divide; [lia|];
                         apply Z.divide_sub_r; [exact Hal16 | exists 9; reflexivity]|].
  split; [lia|]. split; [lia|]. split; [exact Hal8|].
  split; [unfold hl_n in *; lia|]. split; [lia|].
  split; [unfold hl_n in *; lia|]. split; [unfold hl_n in *; lia|].
  split; [lia | exact Tsum]. }
split; [rewrite T3; exact Q3|].
split; [rewrite T4; exact Q4|].
split.
{ apply (cshe_saved_kept W1 W2 mem1 mem2 (spZ regs) regs); [|exact SAVED1].
  intros a Ha. apply KEEP2; [lia | unfold CSHE_STK, CSHE_FRAME, ASTACK, HP_STK, ESTACK in *; lia]. }
split.
{ apply (cshe_vm_keep W1 W2 mem1 mem2 (spZ regs - 136) 8 (hl_n (hs_held h))); [|exact MSP8].
  intros x Hx. cbn [Z.of_nat] in Hx. apply KEEP2;
    [lia | unfold CSHE_STK, CSHE_FRAME, ASTACK, HP_STK, ESTACK in *; lia]. }
split.
{ apply (cshe_vm_keep W1 W2 mem1 mem2 (spZ regs - 128) 8 ((HA + 88) / 8 + SB)); [|exact MSP16].
  intros x Hx. cbn [Z.of_nat] in Hx. apply KEEP2;
    [lia | unfold CSHE_STK, CSHE_FRAME, ASTACK, HP_STK, ESTACK in *; lia]. }
split.
{ apply (cshe_vm_keep W W2 mem mem2 (VAL A_g_gone) 1 gone); [|exact Mg].
  intros x Hx. cbn [Z.of_nat] in Hx. apply KEEPB; [lia | unfold CSHE_STK, CSHE_FRAME, ASTACK in *; lia]. }
split.
{ apply (cshe_vm_keep W W2 mem mem2 AT 8 A0); [|exact MAT].
  intros x Hx. cbn [Z.of_nat] in Hx. apply KEEPB; [lia | lia]. }
split.
{ intros a Ha. apply PRES2. apply PRES1. apply Hpres.
  unfold CSHE_STK, CSHE_FRAME, ASTACK in *. lia. }
split.
{ assert (HAR1 : ARx ly S hp W1 mem1 md1).
  { eapply (ajournal_gx_AR_x SEGS B PST ARx). exact HJ1. }
  assert (SRC1 : asrc_at B ly S W1 mem1 HA h).
  { apply (cshe_src_kept_xR ly S hp W W1 mem mem1 md HA h (spZ regs - 144) HAR HSRC HAlo HAhi
      HCEIL (WLE_R _ _ Hwle1) ltac:(intros a Ha; apply KEEPF; lia) PRES1). }
  apply (cshe_src_kept_xR ly S hp W1 W2 mem1 mem2 md1 HA h (spZ regs - 144 - HP_STK) HAR1 SRC1 HAlo HAhi
    ltac:(unfold CSHE_STK, CSHE_FRAME, ASTACK, HP_STK, ESTACK in *; lia) (WLE_R _ _ Hwle2)
    ltac:(intros a Ha; apply KEEP2;
          unfold CSHE_STK, CSHE_FRAME, ASTACK, HP_STK, ESTACK in *; lia) PRES2). }
split; [exact KEEPB|].
split; [intros a Hp; exact (PRES2 a (PRES1 a Hp))|].
intros jj Hjj. destruct (cshe_errno_out jj Hjj) as [Hr Hl].
apply KEEPB; [exact Hr | unfold CSHE_STK, CSHE_FRAME, ASTACK in *; lia].
Qed.
End wR.
(* the strict texts are the R section's at R := wle: each R premise at wle is the strict one, and the three laws hold
   for wle *)
#[local] Ltac wle_inst := first [ eassumption | intros ? ? H; exact H | intros ?; apply wle_refl
  | intros ? ? ? H1 H2; eapply wle_trans; [exact H1 | exact H2] ].
(* (C1) g_gone <> 0: 0x85498 -> loop 2's head 0x854c4.  The run reads g_gone and the count cell at sp + 8 and
   writes nothing; `andi s11,s0,7` is 0 because &held.n = HA + 88 is 8-aligned, so s11 = 3 at the head. *)
Lemma cshe_gone_l2_x : forall (W : world SEGS) ly S hp regs mem md ly0 S0 hp0 (W0 : world SEGS) mem0 md0
XO AT FP sp0 kk HA PF VE SBV SBH gone N a0v s5v want,
cshe_tst_regs regs sp0 HA PF AT VE SBV SBH N a0v s5v want ->
cshe_tst_ok sp0 HA N a0v s5v want gone ->
val_mem SEGS (mrestrict (w_H W) mem) (sp0 - 136) 8 N ->
val_mem SEGS (mrestrict (w_H W) mem) (VAL A_g_gone) 1 gone ->
(forall a, sp0 - 144 <= a < sp0 -> apresent (w_H W) mem a) ->
gone <> 0 -> XO mod 16 = 0 -> alloc_ceiling + CSHE_STK <= sp0 ->
ajournal_gx_x SEGS B PST ARx G XO [(AT, AT + 8)] CSHE_STK sp0 FP ly0 S0 hp0 W0 mem0 md0 [] ly S hp W mem md kk ->
(* errno's view at 0x85498 is the entry's (cshe_to_tst's last conjunct) *)
(forall j, 0 <= j < 4 -> aview SEGS (w_H W) mem (as_errno B + j) = aview SEGS (w_H W0) mem0 (as_errno B + j)) ->
SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + A_cshe_tst + 4)) mem (seg_rom SEGS)) md)
(fun W' c' => exists regs' mem' md',
 c' = mkCfg (mkst regs' (Z_to_bv 64 (BASE + A_cshe_l2)) mem' (seg_rom SEGS)) md' /\
 ajournal_gx_x SEGS B PST ARx G XO [(AT, AT + 8)] CSHE_STK sp0 FP ly0 S0 hp0 W0 mem0 md0 [] ly S hp W' mem' md' kk /\
 (forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W') mem' a = aview SEGS (w_H W) mem a) /\
 (forall a, apresent (w_H W) mem a -> apresent (w_H W') mem' a) /\
 getr regs' 2 = getr regs 2 /\ getr regs' 3 = getr regs 3 /\ getr regs' 4 = getr regs 4 /\
 getr regs' 8 = getr regs 8 /\ getr regs' 9 = getr regs 9 /\ getr regs' 11 = getr regs 11 /\
 getr regs' 18 = getr regs 18 /\ getr regs' 19 = getr regs 19 /\ getr regs' 24 = getr regs 24 /\
 getr regs' 25 = getr regs 25 /\ getr regs' 26 = getr regs 26 /\
 getr regs' 20 = w64 (N + 1) /\ getr regs' 21 = w64 (- N) /\ getr regs' 22 = w64 1 /\
 getr regs' 23 = w64 (AREC * (N - 1)) /\ getr regs' 27 = w64 3 /\
 (* errno's view is the entry's (W0, mem0: the journal's start), as the premise gave it at 0x85498 *)
 (forall j, 0 <= j < 4 -> aview SEGS (w_H W') mem' (as_errno B + j) = aview SEGS (w_H W0) mem0 (as_errno B + j))).
Proof. eapply (cshe_gone_l2_xR (@wle SEGS)); wle_inst. Qed.

(* (C2) g_gone = 0 and want <> 0: 0x85498 -> loop 3's head 0x8559c.  0x8557c recomputes want as a0 + s5,
   0x8558c sets s11 = want + 1 (the `while (want-- > 0)` counter), s4 = " end\0" (.str.4) and s8 = 4 are
   loop 3's bcmp operands, and sp + 8 is overwritten with (&held.n) mod 8 + 3 = 3. *)
Lemma cshe_gone_l3_x : forall (W : world SEGS) ly S hp regs mem md ly0 S0 hp0 (W0 : world SEGS) mem0 md0
XO AT FP sp0 kk HA PF VE SBV SBH gone N a0v s5v want,
cshe_tst_regs regs sp0 HA PF AT VE SBV SBH N a0v s5v want ->
cshe_tst_ok sp0 HA N a0v s5v want gone ->
val_mem SEGS (mrestrict (w_H W) mem) (sp0 - 136) 8 N ->
val_mem SEGS (mrestrict (w_H W) mem) (VAL A_g_gone) 1 gone ->
(forall a, sp0 - 144 <= a < sp0 -> apresent (w_H W) mem a) ->
gone = 0 -> want <> 0 -> XO mod 16 = 0 -> alloc_ceiling + CSHE_STK <= sp0 ->
ajournal_gx_x SEGS B PST ARx G XO [(AT, AT + 8)] CSHE_STK sp0 FP ly0 S0 hp0 W0 mem0 md0 [] ly S hp W mem md kk ->
(* errno's view at 0x85498 is the entry's (cshe_to_tst's last conjunct) *)
(forall j, 0 <= j < 4 -> aview SEGS (w_H W) mem (as_errno B + j) = aview SEGS (w_H W0) mem0 (as_errno B + j)) ->
SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + A_cshe_tst + 4)) mem (seg_rom SEGS)) md)
(fun W' c' => exists regs' mem' md',
 c' = mkCfg (mkst regs' (Z_to_bv 64 (BASE + A_cshe_l3)) mem' (seg_rom SEGS)) md' /\
 ajournal_gx_x SEGS B PST ARx G XO [(AT, AT + 8)] CSHE_STK sp0 FP ly0 S0 hp0 W0 mem0 md0 [] ly S hp W' mem' md' kk /\
 (forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 136 <= a < sp0 - 128) ->
   aview SEGS (w_H W') mem' a = aview SEGS (w_H W) mem a) /\
 (forall a, apresent (w_H W) mem a -> apresent (w_H W') mem' a) /\
 val_mem SEGS (mrestrict (w_H W') mem') (sp0 - 136) 8 3 /\
 getr regs' 2 = getr regs 2 /\ getr regs' 3 = getr regs 3 /\ getr regs' 4 = getr regs 4 /\
 getr regs' 8 = getr regs 8 /\ getr regs' 9 = getr regs 9 /\ getr regs' 18 = getr regs 18 /\
 getr regs' 19 = getr regs 19 /\ getr regs' 21 = getr regs 21 /\ getr regs' 22 = getr regs 22 /\
 getr regs' 23 = getr regs 23 /\ getr regs' 25 = getr regs 25 /\ getr regs' 26 = getr regs 26 /\
 getr regs' 10 = w64 want /\ getr regs' 20 = w64 (VAL A_lit_end5) /\ getr regs' 24 = w64 4 /\
 getr regs' 27 = w64 (want + 1) /\
 (* errno's view is the entry's (W0, mem0: the journal's start), as the premise gave it at 0x85498 *)
 (forall j, 0 <= j < 4 -> aview SEGS (w_H W') mem' (as_errno B + j) = aview SEGS (w_H W0) mem0 (as_errno B + j))).
Proof. eapply (cshe_gone_l3_xR (@wle SEGS)); wle_inst. Qed.
(* The epilogue, in the form a caller that must carry a memory predicate over it needs: the run writes NO byte
   (cshe_frmR's writable window is empty), so it hands out the mrestrict equality, from which both the ASan view
   and writability of every byte follow (abyte_kept_meq).  cshe_epi_x, below, is this with the view alone. *)
Lemma cshe_epi_m_x : forall W0 ly0 S0 hp0 mem0 md0 XO OUT FP ly S hp W regs0 regs mem md kk (Q : world SEGS -> config -> Prop),
ajournal_gx_x SEGS B PST ARx G XO OUT CSHE_STK (spZ regs0) FP ly0 S0 hp0 W0 mem0 md0 [] ly S hp W mem md kk ->
YK0s.ret_ok (getr regs0 1) ->
spZ regs0 mod 16 = 0 -> alloc_ceiling + CSHE_STK <= spZ regs0 -> spZ regs0 <= 2 ^ 47 ->
getr regs 2 = w64 (spZ regs0 - 144) ->
getr regs 3 = getr regs0 3 -> getr regs 4 = getr regs0 4 ->
cshe_saved W mem (spZ regs0) regs0 ->
(forall regs' mem' md', aregs_preserved regs0 regs' ->
  (forall x : word, mrestrict (w_H W) mem' x = mrestrict (w_H W) mem x) ->
  ajournal_gx_x SEGS B PST ARx G XO OUT CSHE_STK (spZ regs0) FP ly0 S0 hp0 W0 mem0 md0 [] ly S hp W mem' md' kk ->
  Q W (mkCfg (mkst regs' (getr regs0 1) mem' (seg_rom SEGS)) md')) ->
SRr SEGS W (cfg_at SEGS (BASE + A_cshe_ret) regs mem md) Q.
Proof. eapply (cshe_epi_m_xR (@wle SEGS)); wle_inst. Qed.
(* the same, with the ASan view and presence: what a caller that reads bytes and needs them writable takes
   (loop 2 and loop 3 of this walk; asrc_at's awr needs presence kept) *)
Lemma cshe_epi_x : forall W0 ly0 S0 hp0 mem0 md0 XO OUT FP ly S hp W regs0 regs mem md kk (Q : world SEGS -> config -> Prop),
ajournal_gx_x SEGS B PST ARx G XO OUT CSHE_STK (spZ regs0) FP ly0 S0 hp0 W0 mem0 md0 [] ly S hp W mem md kk ->
YK0s.ret_ok (getr regs0 1) ->
spZ regs0 mod 16 = 0 -> alloc_ceiling + CSHE_STK <= spZ regs0 -> spZ regs0 <= 2 ^ 47 ->
getr regs 2 = w64 (spZ regs0 - 144) ->
getr regs 3 = getr regs0 3 -> getr regs 4 = getr regs0 4 ->
cshe_saved W mem (spZ regs0) regs0 ->
(forall regs' mem' md', aregs_preserved regs0 regs' ->
  (forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W) mem' a = aview SEGS (w_H W) mem a) ->
  (forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a) ->
  ajournal_gx_x SEGS B PST ARx G XO OUT CSHE_STK (spZ regs0) FP ly0 S0 hp0 W0 mem0 md0 [] ly S hp W mem' md' kk ->
  Q W (mkCfg (mkst regs' (getr regs0 1) mem' (seg_rom SEGS)) md')) ->
SRr SEGS W (cfg_at SEGS (BASE + A_cshe_ret) regs mem md) Q.
Proof. eapply (cshe_epi_xR (@wle SEGS)); wle_inst. Qed.
(* an address stays writable when its presence is kept and the new world hides no more (W_list_drop.v
   writable_kept_w, copied) *)
Lemma cshe_writable_kept_w : forall (W W' : world SEGS) (m m' : word -> option byte) a,
(apresent (w_H W) m a -> apresent (w_H W') m' a) -> wle W W' ->
writable_at SEGS (mrestrict (w_H W) m) a -> writable_at SEGS (mrestrict (w_H W') m') a.
Proof. exact (cshe_writable_kept_w_xR (@wle SEGS)). Qed.
(* The source over one run of this walk: the view of every byte below the ceiling kept, nothing gone absent. *)
Lemma cshe_src_kept_x : forall ly S hp (W W' : world SEGS) mem mem' md HA h lo,
ARx ly S hp W mem md -> asrc_at B ly S W mem HA h -> 0x10000 <= HA -> HA + 96 <= 0x5fb000 ->
alloc_ceiling <= lo -> wle W W' ->
(forall a, 4096 <= a < lo -> aview SEGS (w_H W') mem' a = aview SEGS (w_H W) mem a) ->
(forall a, apresent (w_H W) mem a -> apresent (w_H W') mem' a) ->
asrc_at B ly S W' mem' HA h.
Proof. exact (cshe_src_kept_xR (@wle SEGS)). Qed.
(* P at any later state of the walk's journal (its free footprint the held list's blocks): its bytes keep their entry
   view, its shadow passes has_prefix's two shadow premises, and it lies below the allocator's ceiling (so off the
   real stack).  A read-only literal: the caller's ROM keep (rom_view at both states), ashp_x, and the image's range.
   A fake-frame local: the journal's frame clause keeps the frame's bytes and its shadow bytes (none is in the free
   footprint: a frame is apart from every block (alx_sep), its shadow is not application memory, and neither is an
   image byte, so not in G), so the entry's range_addressable holds again; shadow_hull_vis holds of a live frame in
   every ARx state (W_frame_x.v shadow_hull_vis_of_frame_x); a frame lies below the ceiling (frames_bounds_x).  The
   entry-side premises come first, so a walk can take this once and clear the disjunction from lia's context. *)
Lemma cshe_P_at_x : forall XO OUT STK sp0 ly S hp W mem md HA h PF PLEN,
ARx ly S hp W mem md -> asrc_at B ly S W mem HA h -> 0 <= PLEN ->
range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF PF (PLEN + 1) ->
((forall a, PF <= a < PF + PLEN + 8 -> in_rom SEGS a) /\ ashp_x ARx PF (PLEN + 1) \/
 exists cid pos, In (cid, pos) (frames S) /\ forall a, PF <= a < PF + PLEN + 8 -> in_zr a (frame_rng ly (cid, pos))) ->
forall ly1 S1 hp1 W1 mem1 md1 kk,
ajournal_gx_x SEGS B PST ARx G XO OUT STK sp0 (blk_FP (list_blks (hs_held h))) ly S hp W mem md [] ly1 S1 hp1 W1 mem1 md1 kk ->
(forall a, in_rom SEGS a -> aview SEGS (w_H W1) mem1 a = aview SEGS (w_H W) mem a) ->
(forall a, PF <= a < PF + PLEN + 8 -> aview SEGS (w_H W1) mem1 a = aview SEGS (w_H W) mem a) /\
range_addressable (aview SEGS (w_H W1) mem1) SHADOW_OFF PF (PLEN + 1) /\
shadow_hull_vis (aview SEGS (w_H W1) mem1) PF (PLEN + 1) /\
(forall a, PF <= a < PF + PLEN + 8 -> 4096 <= a < alloc_ceiling).
Proof. exact (cshe_P_at_xR (@wle SEGS)). Qed.
(* ---- (A) the n = 0 path: 0x853b0, the entry's empty arm, the epilogue, and cshe_post ---- *)
(* With held.n = 0 the `blez s8` at 0x85418 is taken: no record is counted, no record is dropped, the stream is
   not read and *at is left alone.  So H' = held, ds = [], c = 0, the state is the entry's, and the walk costs
   nothing: cshe_cost held = 0 * mo_free MT.  The premises are cshe_spec's, minus what only the loops use. *)
Lemma cshe_n0_x : forall W ly S hp regs mem md ch XO AT HA (j : nat) PF h P A0 gone ob,
afn_pre_x SEGS B ARx CSHE_STK ly S hp W regs mem md ch ->
0 <= XO -> XO mod 16 = 0 -> spZ regs + XO <= ly_top ly ->
(forall a, spZ regs <= a < spZ regs + XO -> apresent (w_H W) mem a) ->
getr regs 10 = w64 HA -> getr regs 11 = w64 PF -> getr regs 12 = w64 AT ->
asrc_at B ly S W mem HA h ->
HA mod 8 = 0 -> 4096 <= HA ->
(forall a, HA + 64 <= a < HA + 96 -> inG G a) -> azs B (HA + 64) 32 ->
HA = VAL (A_OBJ 22) + ASRC * Z.of_nat j -> (j < 4)%nat ->
NoDup (CheckRep.texts (hs_held h)) ->
hl_n (hs_held h) < 2 ^ 26 ->
AT mod 8 = 0 -> spZ regs <= AT -> AT + 8 <= spZ regs + XO ->
val_mem SEGS (mrestrict (w_H W) mem) AT 8 A0 ->
val_mem SEGS (mrestrict (w_H W) mem) (VAL A_g_gone) 1 gone -> 0 <= gone < 256 ->
hl_n (hs_held h) = 0 ->
forall kr : nat, rp_RM RP S kr ->
SRr SEGS W (cfg_at SEGS A_csheP regs mem md)
  (cshe_post_x regs ly S hp W mem md XO AT HA h P A0 gone ob kr).
Proof. eapply (cshe_n0_xR (@wle SEGS)); wle_inst. Qed.
(* ---- (C3) g_gone = 0 and want = 0: 0x85498 -> the epilogue -> cshe_post ---- *)
(* The `beqz a2` at 0x854a0 goes to the want test at 0x85578, whose `beqz a1` goes straight to the epilogue:
   loop 3 never turns, so no record is dropped, no line is read and *at is left alone.  As in the n = 0 path
   H' = held, ds = [], c = 0, and ends_run at w = 0 is Some (recs, [], 0).  The run writes no byte (the frame
   region of ss_cshe_tst0 has an empty writable window: the store to sp + 8 at 0x85598 is past the branch). *)
Lemma cshe_want0_x : forall (W : world SEGS) ly S hp regs mem md (W0 : world SEGS) regs0 mem0 md0
XO AT HA PF VE SBV SBH gone N a0v s5v (h : hsrc) (P : list byte) A0 ob,
cshe_tst_regs regs (spZ regs0) HA PF AT VE SBV SBH N a0v s5v 0 ->
cshe_tst_ok (spZ regs0) HA N a0v s5v 0 gone ->
getr regs 3 = getr regs0 3 -> getr regs 4 = getr regs0 4 ->
val_mem SEGS (mrestrict (w_H W) mem) (spZ regs0 - 136) 8 N ->
val_mem SEGS (mrestrict (w_H W) mem) (VAL A_g_gone) 1 gone ->
(forall a, spZ regs0 - 144 <= a < spZ regs0 -> apresent (w_H W) mem a) ->
gone = 0 -> CheckRep.want_of P (hl_recs (hs_held h)) = 0%nat ->
XO mod 16 = 0 -> alloc_ceiling + CSHE_STK <= spZ regs0 -> spZ regs0 <= 2 ^ 47 -> spZ regs0 mod 16 = 0 ->
YK0s.ret_ok (getr regs0 1) ->
ajournal_gx_x SEGS B PST ARx G XO [(AT, AT + 8)] CSHE_STK (spZ regs0) (blk_FP (list_blks (hs_held h)))
  ly S hp W0 mem0 md0 [] ly S hp W mem md 0 ->
cshe_saved W mem (spZ regs0) regs0 ->
asrc_at B ly S W mem HA h ->
NoDup (CheckRep.texts (hs_held h)) ->
val_mem SEGS (mrestrict (w_H W) mem) AT 8 A0 ->
(* errno's view at 0x85498 is the entry's (cshe_to_tst's last conjunct) *)
(forall j, 0 <= j < 4 -> aview SEGS (w_H W) mem (as_errno B + j) = aview SEGS (w_H W0) mem0 (as_errno B + j)) ->
forall kr : nat, rp_RM RP S kr ->
SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + A_cshe_tst + 4)) mem (seg_rom SEGS)) md)
  (cshe_post_x regs0 ly S hp W0 mem0 md0 XO AT HA h P A0 gone ob kr).
Proof. eapply (cshe_want0_xR (@wle SEGS)); wle_inst. Qed.
(* ---- (B) the entry and loop 1: cshe_spec's premises with held.n > 0 to the 0x85498 state ---- *)
(* The post is what the three arms out of 0x85498 take: the walk's register state and its two bounds, the
   journal, the frame's saved slots and count cell, g_gone and *at, the source at the new memory, and the
   frame clause every other cshe_spec fact rides on (nothing outside [sp - CSHE_STK, sp) moved). *)
Lemma cshe_to_tst_x : forall W ly S hp regs mem md ch XO AT HA (j : nat) PF h P A0 gone,
afn_pre_x SEGS B ARx CSHE_STK ly S hp W regs mem md ch ->
0 <= XO -> XO mod 16 = 0 -> spZ regs + XO <= ly_top ly ->
(forall a, spZ regs <= a < spZ regs + XO -> apresent (w_H W) mem a) ->
getr regs 10 = w64 HA -> getr regs 11 = w64 PF -> getr regs 12 = w64 AT ->
asrc_at B ly S W mem HA h ->
HA mod 8 = 0 -> 4096 <= HA ->
(forall a, HA + 64 <= a < HA + 96 -> inG G a) -> azs B (HA + 64) 32 ->
HA = VAL (A_OBJ 22) + ASRC * Z.of_nat j -> (j < 4)%nat ->
hl_n (hs_held h) < 2 ^ 26 ->
(forall a, hl_v (hs_held h) <= a < hl_v (hs_held h) + AREC * hl_cap (hs_held h) ->
  ~ (spZ regs - CSHE_STK <= a < spZ regs + XO)) ->
(forall r, In r (hl_recs (hs_held h)) -> forall a, fst r <= a < fst r + Z.of_nat (length (snd r)) + 1 ->
  ~ (spZ regs - CSHE_STK <= a < spZ regs + XO)) ->
spZ regs <= AT -> AT + 8 <= spZ regs + XO ->
val_mem SEGS (mrestrict (w_H W) mem) AT 8 A0 ->
~ In (Z_to_bv 8 0) P -> Z.of_nat (length P) + 1 < 2 ^ 32 -> 0 < PF -> PF + Z.of_nat (length P) + 8 <= 2 ^ 63 ->
(forall i, 0 <= i < Z.of_nat (length P) ->
   aview SEGS (w_H W) mem (PF + i) = Some (bv_unsigned (nth (Z.to_nat i) P (Z_to_bv 8 0)))) ->
aview SEGS (w_H W) mem (PF + Z.of_nat (length P)) = Some 0 ->
(forall a, PF <= a < PF + Z.of_nat (length P) + 8 -> aview SEGS (w_H W) mem a <> None /\
   ~ (spZ regs - CSHE_STK <= a < spZ regs + XO)) ->
amem_range PF (Z.of_nat (length P) + 1) -> amem_range PF 8 ->
range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF PF (Z.of_nat (length P) + 1) ->
shadow_hull_vis (aview SEGS (w_H W) mem) PF (Z.of_nat (length P) + 1) ->
rom_view SEGS W mem ->
val_mem SEGS (mrestrict (w_H W) mem) (VAL A_g_gone) 1 gone -> 0 <= gone < 256 ->
0 < hl_n (hs_held h) ->
SRr SEGS W (cfg_at SEGS A_csheP regs mem md)
(fun W' c' => exists regs' mem' md' a0v s5v,
 c' = mkCfg (mkst regs' (Z_to_bv 64 (BASE + A_cshe_tst + 4)) mem' (seg_rom SEGS)) md' /\
 ajournal_gx_x SEGS B PST ARx G XO [(AT, AT + 8)] CSHE_STK (spZ regs) (blk_FP (list_blks (hs_held h)))
   ly S hp W mem md [] ly S hp W' mem' md' 0 /\
 cshe_tst_regs regs' (spZ regs) HA PF AT (hl_v (hs_held h) + AREC * hl_n (hs_held h))
   (SB + (hl_v (hs_held h) + AREC * hl_n (hs_held h)) / 8) ((HA + 80) / 8 + SB)
   (hl_n (hs_held h)) a0v s5v (Z.of_nat (CheckRep.want_of P (hl_recs (hs_held h)))) /\
 cshe_tst_ok (spZ regs) HA (hl_n (hs_held h)) a0v s5v
   (Z.of_nat (CheckRep.want_of P (hl_recs (hs_held h)))) gone /\
 getr regs' 3 = getr regs 3 /\ getr regs' 4 = getr regs 4 /\
 cshe_saved W' mem' (spZ regs) regs /\
 val_mem SEGS (mrestrict (w_H W') mem') (spZ regs - 136) 8 (hl_n (hs_held h)) /\
 val_mem SEGS (mrestrict (w_H W') mem') (spZ regs - 128) 8 ((HA + 88) / 8 + SB) /\
 val_mem SEGS (mrestrict (w_H W') mem') (VAL A_g_gone) 1 gone /\
 val_mem SEGS (mrestrict (w_H W') mem') AT 8 A0 /\
 (forall a, spZ regs - 144 <= a < spZ regs -> apresent (w_H W') mem' a) /\
 asrc_at B ly S W' mem' HA h /\
 (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - CSHE_STK <= a < spZ regs) ->
   aview SEGS (w_H W') mem' a = aview SEGS (w_H W) mem a) /\
 (forall a, apresent (w_H W) mem a -> apresent (w_H W') mem' a) /\
 (* errno's view is the entry's (cshe_post's conjunct; loops 2 and 3 take it at their heads) *)
 (forall j, 0 <= j < 4 -> aview SEGS (w_H W') mem' (as_errno B + j) = aview SEGS (w_H W) mem (as_errno B + j))).
Proof. eapply (cshe_to_tst_xR (@wle SEGS)); wle_inst. Qed.

End c.
End b.
End a.
