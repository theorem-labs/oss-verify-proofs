(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* IMAGE B (asan-ubsan) walk of gesture_end at 0x85b14, lane W4.  B's gesture_end is instruction-for-instruction A's
   (lib/A/W_gesture_end.v, 0x857d8): frame 16, strlen interceptor, send_line, tail send_line of " end\0"; it has no
   UBSan trap (no pointer arithmetic or alignment check).  So this file is A's text with B's numbers: lib.B kit,
   GE_STK 16544 (B's send_line frame 144), image top 0x5fc000, return addresses BASE + 14308 (0x85b28) and
   BASE + 14320 (0x85b34) from B's listing base 0x82344.  Checked by compiling against B's listing; the comments
   below are A's and cite A's addresses. *)
(* Modified by Theorem Labs, 2026-10-30 (a Theorem Labs lane, an internal work row): re-ported from lib/A/W_gesture_end.v at the F7 room
   re-fit (a working branch f6038f3d481) with the same B numbers as above: pb_gesture_end_x : ge_spec_x
   B PST ARx MT RP MMAX RG over any ARx and room parameter RP, and pb_gesture_end (AR) as its corollary at ARi0. *)
(* Modified by Theorem Labs, 2026-10: the ASan walk of fuzz_reply's gesture_end, in the form of the cgif walks of
   proofs/cgif/cgif_file_fuzzer/lib/A/AC8h.v (call sites), lib/A/ACh2.v (an internal call) and lib/A/ACbk.v
   (entry and return). *)
(* gesture_end(held) at 0x857d8 (relay.c:125) measures the held key with the strlen interceptor, sends it with
   send_line (an internal call), then sends " end\0" (.str.4, 5 bytes) with a tail call to send_line.
   Functional content: lib/Prog/gesture_end_b_c.v:42-119, the controller's stream after the two sends, stated with
   W_contract.v's send_line model (sl_ctl / sl_O / sl_no / sl_cap, RelayOut's send) over W_rep.v's aout_at.
   THE WALK is pb_gesture_end_x (Section c), over any allocator relation ARx with its laws (route (b), step 3;
   CONVERSION.md (sha256 1015972e02a9; internal record)), stated as W_contract_x.ge_spec_x.  Its Section hypotheses: PST / ARx / hl / LAWS
   (the generic relation), HP0 (no hidden head in any ARx state: a Theorem Labs lane's ruling; YCbqG.ARx_shadow_law's premise
   at every state), BLKN (a live block's size is non-negative, W_kit_x.v Section g's form; the live blocks are then
   pairwise distinct), ASTRLEN (W_contract_x.v astrlen_realizes_x, the strlen interceptor), SL (W_contract_x.v
   sl_spec_x, send_line, lane W7), HG (G_SL is a valid global set, W_journal.v gx_ok), HEND5I / HEND5S (" end\0" is
   in the image, and addressable with a visible shadow hull: ashp_x, the literal arm of W_contract_x.v sl_line_ok_x),
   PSTR / HEND5P (no read-only byte and no byte of " end\0" is a program static PST, so a callee's journal keeps
   them: YCbqG.ajournal_x's image clause), and MTL / HOUTLO / HEND5G / HROMO below.  strlen's word read past the
   key's NUL needs the key block's tail granule visible: the laws' alx_blocks and alx_blocks_tail (ge_tail_vis_x).
   The room premise (W_contract.v ge_room, over the plain model's request trace) gives both sends' room premises
   through W_ge_room.v ge_room_sends.  The room round (W_journal_x.v roomp RP): ge's room budget splits between the
   two sends (sl_cost at W_contract_x.MT_rk, ge_rk_split), and ge's count peak covers each send's peak plus the first
   send's net growth of live blocks (ge_acnt_step: it only moves g_out's block).
   pb_gesture_end (Section cAR) is the AR statement, a corollary of pb_gesture_end_x at ARx := ARi0 (cgif's AR with
   the head set empty), PST := []. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04 YI00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0d YP0c YC80 YC81.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import HarnessRep RelayRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_syms W_listing W_pl W_kit W_contract W_rep W_journal W_sites W_frame W_ge_room.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyGuardB.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_shadow_pin.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YCe5x.
(* acnt and its list lemmas (acnt_app, acnt_perm): the room round's one count definition, which W_journal_x.v takes *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import ReplyCnt.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_kit_x W_journal_x W_contract_x W_sites_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_contract_xR W_send_line_xR.
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
Definition A_gesture_end : Z := AF_fr_gesture_end.
Definition A_gesture_endP : Z := BASE + A_gesture_end.
(* send_line's model never makes a meter charge negative, under any meter with the laws (capacities and counts:
   W_ge_room.v); the room round's counting meter W_contract_x.MT_rk has them (ge_rk_laws). *)
Lemma sl_cost_run_nonneg : forall MT, ameter_laws MT -> forall f mx no cap rem, 0 <= mx -> 0 <= no -> 0 <= cap ->
0 <= sl_cost_run MT f mx no cap rem.
Proof.
intros MT MTL f. induction f as [|f IH]; intros mx no cap rem Hmx Hno Hcap; cbn [sl_cost_run]; [lia|].
destruct (rem <=? 0) eqn:Er; [lia|]. apply Z.leb_gt in Er.
assert (Hn : 0 <= (if negb (mx =? 0) && (mx <? rem) then mx else rem)) by (destruct (negb (mx =? 0) && (mx <? rem)); lia).
pose proof (mo_free_nonneg MT MTL) as Hf.
destruct (cap <? no + _).
- pose proof (mo_malloc_nonneg MT MTL ((no + (if negb (mx =? 0) && (mx <? rem) then mx else rem)) * 2) ltac:(lia)) as Hm.
  pose proof (IH mx (no + (if negb (mx =? 0) && (mx <? rem) then mx else rem))
    ((no + (if negb (mx =? 0) && (mx <? rem) then mx else rem)) * 2)
    (rem - (if negb (mx =? 0) && (mx <? rem) then mx else rem)) Hmx ltac:(lia) ltac:(lia)). lia.
- apply IH; lia.
Qed.
Lemma sl_cost_nonneg : forall MT, ameter_laws MT -> forall c mx no cap len, 0 <= mx -> 0 <= no -> 0 <= cap ->
0 <= sl_cost MT c mx no cap len.
Proof.
intros MT MTL c mx no cap len Hmx Hno Hcap. unfold sl_cost.
destruct (sl_live c len); [apply (sl_cost_run_nonneg MT MTL); lia | lia].
Qed.
Lemma ge_rk_laws : ameter_laws MT_rk.
Proof. constructor; unfold MT_rk; cbn; intros; try exact I; lia. Qed.
(* ge's room budget (its pre's rp_RM at ge_cost MT_rk) is the first send's budget, leaving the second send's plus kr *)
Lemma ge_rk_split : forall c mx no cap XL (kr : nat), 0 <= mx -> 0 <= no -> 0 <= cap -> 0 <= XL ->
(Z.to_nat (ge_cost MT_rk c mx no cap XL) + kr =
 Z.to_nat (sl_cost MT_rk c mx no cap XL) +
 (Z.to_nat (sl_cost MT_rk (sl_ctl c XL) mx (sl_no c no XL) (sl_cap c mx no cap XL) 5) + kr))%nat.
Proof.
intros c mx no cap XL kr Hmx Hno Hcap HXL. unfold ge_cost.
pose proof (sl_cost_nonneg MT_rk ge_rk_laws c mx no cap XL Hmx Hno Hcap) as H1.
pose proof (sl_cost_nonneg MT_rk ge_rk_laws (sl_ctl c XL) mx (sl_no c no XL) (sl_cap c mx no cap XL) 5 Hmx
  (sl_no_nonneg c no XL Hno HXL) (sl_cap_nonneg c mx no cap XL Hmx Hno Hcap)) as H2.
rewrite Z2Nat.inj_add by assumption. lia.
Qed.
(* the first send moves g_out's block only (sl_post's two permutations over one rest): each live count grows by at
   most one *)
Lemma ge_acnt_out_le1 : forall P cap out, (acnt P (aout_blks cap out) <= 1)%nat.
Proof.
intros P cap out. unfold aout_blks. destruct (cap =? 0); [rewrite acnt_nil; lia|].
rewrite acnt_cons, acnt_nil. destruct (P (snd (out, cap))); lia.
Qed.
Lemma ge_acnt_step : forall P l l3 cap out cap1 out1 rest,
Permutation l (aout_blks cap out ++ rest) -> Permutation l3 (aout_blks cap1 out1 ++ rest) ->
(acnt P l3 <= acnt P l + 1)%nat.
Proof.
intros P l l3 cap out cap1 out1 rest H1 H3. rewrite (acnt_perm P _ _ H1), (acnt_perm P _ _ H3), !acnt_app.
pose proof (ge_acnt_out_le1 P cap1 out1). lia.
Qed.
(* ---- THE GENERIC WALK (route (b), step 3; CONVERSION.md (sha256 1015972e02a9; internal record)): gesture_end over any allocator relation ARx
   with its laws, stated as W_contract_x.ge_spec_x.  The Section hypotheses beyond the AR walk's: PST / ARx / hl / LAWS
   (the generic relation), HP0 (the unit's hidden-head set is empty in every ARx state: a Theorem Labs lane's ruling, so
   YCbqG.ARx_shadow_law's premise holds at every state), BLKN (W_kit_x.v Section g's form), PSTR / HEND5P (the
   generic journal keeps an image byte only off PST). ---- *)
Section c.
Variable B : asyms.
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Context {hl : Z}.
Variable MT : ameter_ops.
Variable RP : roomp.
Variable MMAX : Z.
Variable RG : rep_globals.
Hypothesis LAWS : AR_laws_x SEGS B ARx hl.
Hypothesis HP0 : forall ly S Hp W mem md, ARx ly S Hp W mem md -> Hp = [].
Hypothesis BLKN : forall ly S Hp W mem md p n, ARx ly S Hp W mem md -> In (p, n) (ablocks B ly S) -> 0 <= n.
Hypothesis HG : gx_ok SEGS B (G_SL B RG).
Hypothesis ASTRLEN : astrlen_realizes_x B ARx (SIGMA WS_strlen).
Hypothesis SL : sl_spec_x B PST ARx MT RP MMAX RG (BASE + AF_fr_send_line).
(* " end\0" lies in the image (true: .rodata) *)
Hypothesis HEND5I : forall a, VAL A_lit_end5 <= a < VAL A_lit_end5 + 5 -> in_img SEGS a.
(* " end\0" is addressable with a visible shadow hull in every ARx state (W_shadow_pin.v ashp over ARx: W_contract_x.v
   ashp_x; at the instance W_shadow_pin_fr.v ashp_end5_5_fr).  The literal arm of W7's sl_line_ok asks exactly this
   (a working branch 6db0a9327b4); the zero-shadow claim it replaces was false (partial granule, shadow 5 at
   0x7fffc1e0). *)
Hypothesis HEND5S : ashp_x ARx (VAL A_lit_end5) 5.
(* No read-only byte is a program static (W_journal_x.v ajournal_gx_rom_view_x's premise, verbatim), and no byte of
   " end\0" is one (it is .rodata): the generic journal's image clause (YCbqG.v ajournal_x) keeps an image byte only
   off PST, so send_line's journal keeps the ROM view and the literal's bytes.  Both hold at PST := [] (every walk's
   instance, a Theorem Labs lane 16:28Z) and at the driver's G_fr_c B (W_LLVMFuzzerTestOneInput_G.v c_rom_apart). *)
Hypothesis PSTR : forall a, in_rom SEGS a -> ~ Exists (in_zr a) PST.
Hypothesis HEND5P : forall a, VAL A_lit_end5 <= a < VAL A_lit_end5 + 5 -> ~ Exists (in_zr a) PST.
Let RUN := paj_run_x_x B PST ARx LAWS (G_SL B RG) HG 0 [].
Let RUNTO := paj_run_to_x_x B PST ARx LAWS (G_SL B RG) HG 0 [].
Let RET := paj_ret_at (PL := PL_fr) (PI := PI).
Local Notation AJGX := (ajournal_gx_x SEGS B PST ARx).
Definition Bx : sv := SOff 32 0.
Definition ge_regions : smem := [ stack_region GE_FRAME ].
Definition ge_facts : facts := mkFacts [ (2%nat, mkAF (2^46) (2^47) 4); (32%nat, mkAF SB SB 0) ] [] [].
Definition ss_ge : sstate := mkSS A_gesture_end sr_atoms ge_regions None ge_facts.
Definition ge_SH : list shent := [].
Definition Bspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
Definition ge_extra : list word := map (Z_to_bv 64) [SB].
Lemma ge_entry : forall W ly S Hp regs mem md ch,
afn_pre_x SEGS B ARx GE_STK ly S Hp W regs mem md ch ->
st_ok_pi SEGS VAL (Eimg (Ereg regs ge_extra)) ss_ge
(restrict (w_H W) (mkst regs (Z_to_bv 64 A_gesture_endP) mem (seg_rom SEGS)))
/\ sh_ok SEGS Bx ge_SH (Eimg (Ereg regs ge_extra)) (mrestrict (w_H W) mem).
Proof.
intros W ly S Hp regs mem md ch HPRE.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : GE_STK = 16544) by reflexivity.
rewrite restrict_mkst_fx.
set (E := Eimg (Ereg regs ge_extra)). pose proof pa_B_ok as HBASE.
assert (E2 : ew E 2 = getr regs 2) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
split.
- unfold ss_ge, A_gesture_endP. apply pa_entry_st_ok_full.
+ apply regs_ok_Eimg_Ereg.
+ vm_compute. reflexivity.
+ unfold ge_regions, stack_region, GE_FRAME.
repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
intros o Ho. apply (apresent_writable SEGS). apply Hpres. rewrite WS. lia.
+ apply pairwise_disjoint_of_extents. unfold ge_regions, stack_region, extent_of_region.
cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. cbn [base_val]. rewrite Usp.
cbn [zpairwise_disjoint zall_disjoint]. repeat split.
+ split; [|split; [exact I | exact I]].
cbn [ge_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite Usp, E32, !unsigned_lit_small by (unfold SB; lia).
change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
revert Hslo Hshi H47 Hceil Hal16 C1 C3 WS Hstk0. clear.
unfold SB, zone2, off_img, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL. intros.
repeat match goal with |- _ /\ _ => split end; lia.
- unfold sh_ok, ge_SH. constructor.
Qed.

(* Reading a NUL-terminated key through garr8. *)
Lemma ge_garr8_aview : forall H mem a l j, garr8 SEGS (mrestrict H mem) a l -> (j < length l)%nat ->
aview SEGS H mem (a + Z.of_nat j) = Some (nth j l 0).
Proof. intros H mem a l j Hg Hj. destruct (Hg j Hj) as [Hv Hr]. exact (aview_of_val_mem1 SEGS H mem _ _ Hv Hr). Qed.
Lemma ge_garr8_kept : forall H H' (m m' : word -> option byte) a l, garr8 SEGS (mrestrict H m) a l ->
(forall b, a <= b < a + Z.of_nat (length l) -> aview SEGS H' m' b = aview SEGS H m b) -> garr8 SEGS (mrestrict H' m') a l.
Proof.
intros H H' m m' a l Hg Hk. apply (garr8_frame SEGS _ _ a l Hg). intros b Hb. apply (mbyte_of_aview SEGS). exact (Hk b Hb).
Qed.
Lemma ge_bzs_lt : forall (x s : list byte) z j, (j < length x)%nat -> nth j (bzs (x ++ z :: s)) 0 = bz (nth j x (Z_to_bv 8 0)).
Proof.
intros x s z j Hj. unfold bzs. rewrite (nth_indep _ 0 (bz (Z_to_bv 8 0))) by (rewrite length_map, length_app; cbn; lia).
rewrite map_nth, app_nth1 by exact Hj. reflexivity.
Qed.
Lemma ge_bzs_at : forall (x s : list byte) z, nth (length x) (bzs (x ++ z :: s)) 0 = bz z.
Proof.
intros x s z. unfold bzs. rewrite (nth_indep _ 0 (bz (Z_to_bv 8 0))) by (rewrite length_map, length_app; cbn; lia).
rewrite map_nth, app_nth2 by lia. rewrite Nat.sub_diag. reflexivity.
Qed.
Lemma ge_bz_nz : forall (x : list byte) j, ~ In (Z_to_bv 8 0) x -> (j < length x)%nat -> bz (nth j x (Z_to_bv 8 0)) <> 0.
Proof.
intros x j Hn Hj Hz. apply Hn. replace (Z_to_bv 8 0) with (nth j x (Z_to_bv 8 0)); [apply nth_In; exact Hj|].
apply bv_eq. unfold bz in Hz. rewrite Hz. reflexivity.
Qed.
Lemma ge_bzs_len : forall (x s : list byte) z, length (bzs (x ++ z :: s)) = (length x + S (length s))%nat.
Proof. intros. unfold bzs. rewrite length_map, length_app. reflexivity. Qed.
(* The rest of the granule of the byte at t, when [q, t] lies in a block (q, r) with q 16-aligned, is inside the
   block's granule-rounded extent. *)
Lemma ge_tail_in : forall q r t a, q mod 16 = 0 -> 1 <= r -> q <= t -> t + 1 <= q + r ->
t < a < t - t mod 8 + 8 -> q <= a < q + round_up r 8.
Proof.
intros q r t a Hq Hr Hqt Htr Ha. unfold round_up.
pose proof (Z.div_mod t 8 ltac:(lia)). pose proof (Z.mod_pos_bound t 8 ltac:(lia)).
pose proof (Z.div_mod (r + 8 - 1) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (r + 8 - 1) 8 ltac:(lia)).
pose proof (Z.div_mod q 16 ltac:(lia)). lia.
Qed.
(* A call to a program function inside a walk: the donor's cl_callS (YC85.v:383) over ajournal_gx_x with no
   out-parameter.  The callee's contract is applied at its entry (its afn_pre_x from the caller's journal), and its
   journal is composed into the caller's (W_journal_x.v ajournal_gx_sub_x); o = 0 is a tail call. *)
Lemma gx_callS : forall G W (regsc : bvmap 5 word) memc pc STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k STK1 FP1 (o : Z) raw ch1
(K : alayout -> astate -> list Z -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop),
gx_ok SEGS B G ->
AJGX G 0 [] STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memc mdc k ->
spZ regsc = sp0 + o -> o mod 16 = 0 -> o <= 0 -> 0 <= STK1 -> STK1 - o <= STK ->
getr regsc 3 = w64 (as_gp B) -> getr regsc 4 = w64 (as_tp B) ->
getr regsc 1 = raw -> YK0s.ret_ok raw -> 4096 <= bv_unsigned raw ->
achain lyc (aview SEGS (w_H W) memc) (sp0 + o) (s0Z regsc) ch1 ->
(afn_pre_x SEGS B ARx STK1 lyc Sc Hpc W regsc memc mdc ch1 ->
 SRr SEGS W (mkCfg (mkst regsc pc memc (seg_rom SEGS)) mdc)
 (fun W2 c2 => exists ly2 S2 Hp2 regs2 mem2 md2 k1,
  c2 = mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2 /\
  AJGX G 0 [] STK1 (spZ regsc) FP1 lyc Sc Hpc W memc mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 /\
  aregs_preserved regsc regs2 /\ K ly2 S2 Hp2 W2 regs2 mem2 md2)) ->
(forall a, inFP FP1 a -> (inFP FP a /\ exists b n, In (b, n) (ablocks B lyc Sc) /\ b <= a < b + req_size n) \/
 in_tmp_block (ablocks B ly S) (ablocks B lyc Sc) a) ->
SRr SEGS W (mkCfg (mkst regsc pc memc (seg_rom SEGS)) mdc)
(fun W2 c2 => exists ly2 S2 Hp2 regs2 mem2 md2 k1,
 c2 = mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2 /\
 AJGX G 0 [] STK sp0 FP ly S Hp W0 mem md own ly2 S2 Hp2 W2 mem2 md2 (k + k1) /\
 AJGX G 0 [] STK1 (sp0 + o) FP1 lyc Sc Hpc W memc mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 /\
 aregs_preserved regsc regs2 /\ K ly2 S2 Hp2 W2 regs2 mem2 md2).
Proof.
exact (gx_callS_x SEGS B PST ARx LAWS pa_segs_low).
Qed.
(* the meter's laws: send_line's model never makes a charge negative (sl_cost_nonneg) *)
Hypothesis MTL : ameter_laws MT.
Lemma aout_fp_cases : forall cap out r, In r (aout_fp B RG cap out) -> In r (aout_fp B RG 0 0) \/ (cap <> 0 /\ r = (out, out + cap)).
Proof.
intros cap out r Hr. unfold aout_fp in Hr |- *. cbn [Z.eqb] in *.
do 9 (destruct Hr as [Hr | Hr]; [left; subst r; cbn; tauto|]).
destruct (Z.eqb_spec cap 0); [destruct Hr | destruct Hr as [<- | []]; right; split; [exact n | reflexivity]].
Qed.
(* the controller's cells lie in the image, below every stack *)
Hypothesis HOUTLO : forall r, In r (aout_fp B RG 0 0) -> 0 <= fst r /\ snd r <= 0x5fc000.
(* " end\0" is none of the bytes send_line may change *)
(* HEND5G holds for EXACTLY [VAL A_lit_end5, VAL A_lit_end5 + 5) = [0x20f00, 0x20f05) on both images and MUST NOT BE
   WIDENED: its `~ owned_static` clause is TRUE (StartupTrace's tfib_lit_end5_not_owned_static, a working branch
   5fab70f4113; ZeroGlobals and W1Verify measured the same rows) only because owned_static's rows (0x20ee1, 0x1f) and
   (0x20f05, 0x1b) - the literal's two redzones - end and start exactly at its edges.  One byte more on either side,
   or rounding the range to 8 bytes or an aligned word, makes that clause FALSE. *)
Hypothesis HEND5G : forall a, VAL A_lit_end5 <= a < VAL A_lit_end5 + 5 ->
  ~ inG (G_SL B RG) a /\ ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).
(* ROM bytes are none of the bytes send_line may change (W_journal.v rom_out), so rom_view survives its journal *)
Hypothesis HROMO : rom_out SEGS B (G_SL B RG).
Lemma aout_facts : forall ly S W mem c O mx no cap out, aout_at B RG ly S W mem c O mx no cap out ->
0 <= mx <= 255 /\ Z.of_nat (length O) = no /\
((cap = 0 /\ out = 0 /\ no = 0) \/ (0 < cap /\ no <= cap /\ In (out, cap) (ablocks B ly S))).
Proof.
intros ly S W mem c O mx no cap out
(_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hmx & Hno & Hd).
split; [exact Hmx|]. split; [exact Hno|].
destruct Hd as [Hd | (H1 & H2 & H3 & _)]; [left; exact Hd | right; split; [exact H1 | split; [exact H2 | exact H3]]].
Qed.
Lemma fp_spares_blocks : forall bl a, (forall b, In b bl -> 4096 <= fst b) -> fp_spares (ablocks_fp bl) a.
Proof.
intros bl a Hb Ho. exfalso. destruct Ho as (r & Hr & H0).
unfold ablocks_fp in Hr. apply in_map_iff in Hr as (b & <- & Hin). cbn [fst snd] in H0. pose proof (Hb b Hin). lia.
Qed.

(* The live blocks are pairwise distinct (their extents are pairwise disjoint and non-empty). *)
Lemma ablocks_nodup : forall ly S Hp W mem md, ARx ly S Hp W mem md -> List.NoDup (ablocks B ly S).
Proof.
intros ly S Hp W mem md HAR.
assert (Hpos : Forall (fun b => 1 <= req_size (snd b)) (ablocks B ly S)).
{ apply Forall_forall. intros [p n] Hin. pose proof (BLKN ly S Hp W mem md p n HAR Hin) as Hn.
  cbn [snd]. apply req_size_pos. lia. }
destruct (alx_sep _ _ _ LAWS ly S Hp W mem md HAR) as [Hpw _]. apply pairwise_app_l in Hpw as [Hpw _].
revert Hpos Hpw. induction (ablocks B ly S) as [|b l IH]; intros Hpos Hpw; [constructor|].
inversion Hpos as [|b0 l0 Hb Hl]; subst.
cbn [map pairwise] in Hpw. destruct Hpw as [Hf Hpw]. constructor; [|exact (IH Hl Hpw)].
intros Hin. rewrite Forall_forall in Hf. specialize (Hf (fst b, req_size (snd b)) (in_map _ _ _ Hin)).
unfold zdisjoint in Hf. cbn [fst snd] in Hf. lia.
Qed.

(* apres_kept (W_contract.v) composes, and holds over any step that keeps every present byte present. *)
Lemma apk_trans : forall W1 (m1 : word -> option byte) W2 m2 W3 m3,
apres_kept B W1 m1 W2 m2 -> apres_kept B W2 m2 W3 m3 -> apres_kept B W1 m1 W3 m3.
Proof. intros W1 m1 W2 m2 W3 m3 H1 H2 a Hi Ho He Hp. exact (H2 a Hi Ho He (H1 a Hi Ho He Hp)). Qed.
Lemma apk_of_pres : forall W (m m' : word -> option byte),
(forall a, apresent (w_H W) m a -> apresent (w_H W) m' a) -> apres_kept B W m W m'.
Proof. intros W m m' H a _ _ _ Hp. exact (H a Hp). Qed.

(* A live block is visible up to the end of its last 8-byte granule: its own bytes are present (alx_blocks) and the
   tail granule is visible (alx_blocks_tail, the laws' field 15); strlen's word read past the key's NUL needs it. *)
Lemma ge_tail_vis_x : forall ly S Hp W mem md p n a, ARx ly S Hp W mem md -> In (p, n) (ablocks B ly S) ->
p <= a < p + round_up (req_size n) 8 -> aview SEGS (w_H W) mem a <> None.
Proof.
intros ly S Hp W mem md p n a HAR Hin Ha.
destruct (alx_blocks _ _ _ LAWS ly S Hp W mem md p n HAR Hin) as (H16 & _ & _ & _ & Hpres & _).
destruct (Z_lt_le_dec a (p + req_size n)) as [Hlt | Hge].
- apply aview_some_of_apresent. exact (proj1 (Hpres a ltac:(lia))).
- apply (alx_blocks_tail _ _ _ LAWS ly S Hp W mem md p n a HAR Hin). unfold round_up in Ha.
  pose proof (Z.div_mod p 16 ltac:(lia)) as Dp.
  assert (E : (p + req_size n + 7) / 8 = (req_size n + 8 - 1) / 8 + 2 * (p / 16)).
  { rewrite <- Z.div_add by lia. f_equal. lia. }
  lia.
Qed.

(* ---- route R (RULE-SHAPES.md (sha256 2e856ce788dd; internal record) section 0): the walk at a world relation R.  ge_spec_x -> W_contract_xR.v's ge_spec_xR
   (R right after ARx), at the address BASE + AF_fr_gesture_end; the callee spec sl_spec_x -> W_send_line_xR.v's
   sl_spec_xR (SL_R); ajournal_gx_x -> ajournal_gx_xR .. R; SRr SEGS -> SRrG SEGS R; the runs -> W_journal_x.v
   paj_run_x_xG / paj_run_to_x_xG; the strlen site -> W_sites_x.v aj_strlen_gx_at_xR (the strlen contract stays
   strict); the two send_line calls -> the engine's W_journal_x.v gx_callS_xR (in place of this file's gx_callS); the
   journal helpers ajgx_* -> their R twins below.  pb_gesture_end_x below is it at R := wle. ---- *)
Section wR.
Variable R : world SEGS -> world SEGS -> Prop.
Hypothesis R_refl : forall W, R W W.
Hypothesis R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3.
Hypothesis WLE_R : forall W W', @wle SEGS W W' -> R W W'.
Hypothesis SL_R : sl_spec_xR B PST ARx R MT RP MMAX RG (BASE + AF_fr_send_line).
Let RUNR := paj_run_x_xG B PST ARx LAWS R (G_SL B RG) HG 0 [].
Let RUNTOR := paj_run_to_x_xG B PST ARx LAWS R (G_SL B RG) HG 0 [].
Local Notation AJGXR := (ajournal_gx_xR SEGS B PST ARx R).
(* R twin of ajgx_pres *)
Lemma ajgx_pres_xR : forall G XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k,
AJGXR G XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k ->
forall a, sp0 - STK <= a < sp0 -> apresent (w_H W') mem' a.
Proof.
intros G XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k (HS0 & HX0 & (memS & HJi & _) & _) a Ha.
pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _). apply Hpres. lia.
Qed.
(* R twin of ajgx_keep_high *)
Lemma ajgx_keep_high_xR : forall G XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k,
gx_ok SEGS B G -> AJGXR G XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k ->
forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (sp0 + XO - (STK + XO) <= a < sp0 + XO) ->
aview SEGS (w_H W') mem' a = aview SEGS (w_H W) mem a.
Proof.
intros G XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k HGx (HS0 & HX0 & (memS & HJi & Hag) & _) a Ha Hno.
pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & F1 & _). rewrite (F1 a Ha Hno).
pose proof asan_consts as (C1 & _).
apply (aview_gagree SEGS G _ _ _ a Hag). apply inGb_false. rewrite unsigned_lit_small by lia. intros HGa.
pose proof (inG_low SEGS B pa_segs_low G a HGx HGa) as HL. unfold kLowMemEnd in HL. lia.
Qed.
(* R twin of ajgx_keep_img *)
Lemma ajgx_keep_img_xR : forall G XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k,
AJGXR G XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k ->
forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
~ Exists (in_zr a) PST -> fp_spares FP a -> ~ inG G a -> aview SEGS (w_H W') mem' a = aview SEGS (w_H W) mem a.
Proof.
intros G XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k (HS0 & HX0 & (memS & HJi & Hag) & _) a Hi Ho He Hpst Hf Hg.
pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _). rewrite (F3 a Hi Ho He Hpst Hf).
pose proof (pa_segs_low a Hi) as HL.
apply (aview_gagree SEGS G _ _ _ a Hag). apply inGb_false. rewrite unsigned_lit_small by (unfold kLowMemEnd in HL; lia). exact Hg.
Qed.
(* R twin of ajgx_ly_top *)
Lemma ajgx_ly_top_xR : forall G XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k,
AJGXR G XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k -> ly_top ly' = ly_top ly.
Proof.
intros G XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k (_ & _ & (memS & HJi & _) & _).
pose proof HJi as (_ & Hly & _). destruct Hly as (_ & _ & _ & _ & _ & _ & _ & _ & ET & _). exact ET.
Qed.

(* R twin of pb_gesture_end_x *)
Theorem pb_gesture_end_xR : ge_spec_xR B PST ARx R MT RP MMAX RG (BASE + AF_fr_gesture_end).
Proof.
change (ge_spec_xR B PST ARx R MT RP MMAX RG A_gesture_endP).
intros W ly S Hp regs mem md ch c O mx no cap out Hk x q m HPRE H10 HOUT GK NZ X1 Hq Hqo Hq1 Hq2 G5 HROM ROOM MOK
  kr RM0 CNT0.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (WS : GE_STK = 16544) by reflexivity. assert (Hes : ESTACK = 4096) by reflexivity.
destruct (ge_entry W ly S Hp regs mem md ch HPRE) as [HS SHOK].
assert (HJ : AJGXR (G_SL B RG) 0 [] GE_STK (spZ regs) (ablocks_fp (aout_blks cap out)) ly S Hp W mem md [] ly S Hp W mem md 0).
{ apply (ajournal_gx_init_xR SEGS B PST ARx R_refl (G_SL B RG) 0 [] GE_STK _ ly S Hp W regs mem md ch HPRE); [lia | reflexivity | lia | intros a Ha; lia]. }
remember (Eimg (Ereg regs ge_extra)) as E eqn:HE. assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (E1 : ew E 1 = getr regs 1) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (E2 : ew E 2 = getr regs 2) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E3 : ew E 3 = getr regs 3) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 3 3%bv eq_refl)).
assert (E4 : ew E 4 = getr regs 4) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 4 4%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 Hk) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (HAE : env_agree 32 (Ereg regs ge_extra) E) by (rewrite HE; split; [intros k Hk'; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
clear HE.
unfold cfg_at. change (w64 A_gesture_endP) with (Z_to_bv 64 A_gesture_endP).
unfold A_gesture_endP, A_gesture_end.
paj_run_tok_xR RUNR HS HJ SHOK Bspan. { apply awr_ok_x_of0. awr_ok_tac. exact Usp. }
pmkst HS.
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3.
prreg HS (4%bv : bv 5) Q4. prreg HS (10%bv : bv 5) Q10.
remember (Z.of_nat (length x)) as XL eqn:HXL. unfold APARTIAL in X1.
destruct (alx_blocks _ _ _ LAWS ly S Hp W mem md q m HAR Hq) as (Hq16 & Hq4096 & Hqceil & Hqh_ia & Hqpres & _).
pose proof (BLKN ly S Hp W mem md q m HAR Hq) as Hqm.
pose proof (req_size_pos m ltac:(lia)) as [Hrq1 Hrq2].
pose proof (ajournal_gx_AR_xR SEGS B PST ARx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HARc.
(* the prologue wrote only inside the 16-byte frame *)
assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 16 <= a < spZ regs) ->
aview SEGS (w_H W) (ms_mem ms) a = aview SEGS (w_H W) mem a).
{ intros a Ha Hno. apply (aview_kept_out E _ (w_H W) mem (ms_mem ms) HFr a Ha).
intros (r & Hin & Hr). cbn [In] in Hin. destruct Hin as [<-|[]].
unfold stack_region, GE_FRAME in Hr. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr.
rewrite Usp in Hr. lia. }
assert (Usp2 : spZ (ms_regs ms) = spZ regs - 16).
{ unfold spZ. rewrite Q2, Usp. rewrite unsigned_lit_small by (unfold spZ in *; lia). reflexivity. }
assert (LKEY : length (bzs (x ++ [Z_to_bv 8 0])) = (length x + 1)%nat) by (rewrite ge_bzs_len; cbn; lia).
(* the key's bytes and its NUL, as the interceptor sees them *)
assert (GA : forall j, (j <= length x)%nat ->
aview SEGS (w_H W) (ms_mem ms) (Hk + Z.of_nat j) = Some (nth j (bzs (x ++ [Z_to_bv 8 0])) 0)).
{ intros j Hj. rewrite KEEP; [apply (ge_garr8_aview (w_H W) mem); [exact GK | lia]| |].
- split; [lia|]. unfold spZ in *. lia.
- intros [HA HB]. unfold spZ in *. lia. }
eapply (YA0nH.SRrG_bind SEGS R R_trans).
{ eapply (aj_strlen_gx_at_xR B PST ARx LAWS R_trans WLE_R _ ASTRLEN (G_SL B RG) 0 [] W (ms_regs ms) (ms_mem ms) GE_STK (spZ regs)
(ablocks_fp (aout_blks cap out)) ly S Hp W mem md [] ly S Hp _ 0 Hk XL (-16) (Z_to_bv 64 (BASE + 14308)) HG eq_refl HJ).
- rewrite Q10, E10. reflexivity.
- lia.
- lia.
- lia.
- lia.
- lia.
- reflexivity.
- lia.
- rewrite WS. lia.
- rewrite Q3, E3. exact Hgp.
- rewrite Q4, E4. exact Htp.
- exact Q1.
- apply ret_ok_codeptr_v; [lia | reflexivity].
- split; [lia|]. split.
  + intros i Hi. exists (nth (Z.to_nat i) (bzs (x ++ [Z_to_bv 8 0])) 0). split.
    * replace (Hk + i) with (Hk + Z.of_nat (Z.to_nat i)) by lia. apply GA; lia.
    * rewrite ge_bzs_lt by lia. apply ge_bz_nz; [exact NZ | lia].
  + intros _. replace (Hk + XL) with (Hk + Z.of_nat (length x)) by lia. rewrite GA by lia.
    rewrite ge_bzs_at. reflexivity.
- intros a Ha. split.
  + replace a with (Hk + Z.of_nat (Z.to_nat (a - Hk))) by lia. rewrite GA by lia. discriminate.
  + rewrite Usp2. unfold spZ in *. lia.
- intros a Ha [HA HB]. unfold spZ in *. lia.
- apply (YCe5x.amem_range_of_block_x SEGS B ARx LAWS ly S Hp W _ _ q m Hk (XL + 1) HARc Hq); lia.
- apply (YCe5x.amem_range_of_block_x SEGS B ARx LAWS ly S Hp W _ _ q m Hk 8 HARc Hq); lia.
- apply (range_addressable_of_block_hp0_x SEGS B ARx LAWS HP0 ly S Hp W _ _ q m Hk (XL + 1) HARc Hq); lia.
- apply (shadow_hull_vis_of_block_hp0_x SEGS B ARx LAWS HP0 ly S Hp W _ _ q m Hk (XL + 1) HARc Hq); lia.
- intros a Ha. pose proof (Z.mod_pos_bound (Hk + XL) 8 ltac:(lia)) as Hm8. rewrite KEEP.
  + apply (ge_tail_vis_x ly S Hp W mem md q m a HAR Hq).
    apply (ge_tail_in q (req_size m) (Hk + XL) a); lia.
  + lia.
  + unfold spZ in *. lia.
- intros a Hin. rewrite KEEP.
  + apply HROM. exact Hin.
  + destruct Hin as (sg & Hsg & _ & Hr). pose proof (pa_img_range a ltac:(exists sg; split; [exact Hsg | exact Hr])) as HI. lia.
  + destruct Hin as (sg & Hsg & _ & Hr). pose proof (pa_img_range a ltac:(exists sg; split; [exact Hsg | exact Hr])) as HI.
    unfold spZ in *. lia. }
cbv beta. intros W2 c2 Hwle2 (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Hlen & Hfr2 & Hpres2).
(* back in gesture_end with a0 = |x| *)
jafter_call_keep_pi HS 33%nat regs2 (mrestrict (w_H W) mem2) HP2 [0]%nat HS2.
match type of HS2 with ?ty -> _ => assert (HRK : ty); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; [| apply Forall_nil].
unfold stack_region, GE_FRAME. split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Usp.
- intros a Ha. apply (mbyte_of_aview SEGS). apply Hfr2; unfold ESTACK in *; lia.
- intros a Ha _. apply (apresent_writable SEGS). eapply ajgx_pres_xR; [exact HJ2 | rewrite WS; lia]. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
remember (havoc E 33 (map (getr regs2) CLOB)) as Ea eqn:HEa in HS.
assert (HEIa : img_env VAL A_LIM Ea) by (rewrite HEa; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLDa : forall n, (n < 33)%nat -> ew Ea n = ew E n) by (intros n Hn; rewrite HEa; apply YN3v.ew_havoc_old; exact Hn).
assert (HAEa : env_agree 32 (Ereg regs ge_extra) Ea) by (rewrite HEa; apply env_agree_havoc_ge; [cbv; lia | exact HAE]).
clear HEa.
assert (Uspa : bv_unsigned (ew Ea 2) = spZ regs) by (rewrite OLDa by (cbv; lia); exact Usp).
assert (SHOKa : sh_ok SEGS Bx ge_SH Ea (mrestrict (w_H W) mem2)) by (unfold sh_ok, ge_SH; constructor).
prreg HS (10%bv : bv 5) R10a.
paj_run_to_tok_xR RUNTOR HS HJ2 SHOKa Bspan AF_fr_send_line. { apply awr_ok_x_of0. awr_ok_tac. exact Uspa. }
pmkst HS.
prreg HS (1%bv : bv 5) P1. prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3.
prreg HS (4%bv : bv 5) P4. prreg HS (8%bv : bv 5) P8. prreg HS (10%bv : bv 5) P10. prreg HS (11%bv : bv 5) P11.
(* the first send_line: the key's |x| bytes *)
assert (F10 : ew Ea 10 = Z_to_bv 64 Hk) by (rewrite OLDa by (cbv; lia); exact E10).
assert (F37 : ew Ea 37 = w64 XL) by (rewrite <- R10a; exact Hlen).
assert (Usp3 : spZ (ms_regs ms0) = spZ regs - 16).
{ change (spZ (ms_regs ms0)) with (bv_unsigned (getr (ms_regs ms0) 2)). rewrite P2, Uspa.
  rewrite unsigned_lit_small by (unfold spZ in *; lia). lia. }
assert (KV : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - GE_STK <= a < spZ regs) ->
aview SEGS (w_H W) (ms_mem ms0) a = aview SEGS (w_H W) mem a).
{ intros a Ha Hno.
  rewrite (aview_kept_out Ea _ (w_H W) mem2 (ms_mem ms0) HFr0 a Ha).
  - rewrite (Hfr2 a Ha) by (intros [HA HB]; apply Hno; rewrite WS; unfold ESTACK in *; lia).
    apply KEEP; [exact Ha | intros [HA HB]; apply Hno; rewrite WS; lia].
  - intros (r & Hin & Hr). cbn [ss_mem add_cond In] in Hin. destruct Hin as [<- | []].
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val] in Hr. rewrite Uspa in Hr.
    apply Hno. rewrite WS. lia. }
assert (KP : forall a, apresent (w_H W) mem a -> apresent (w_H W) (ms_mem ms0) a).
{ intros a Hpa. eapply apresent_grows; [exact HG1|]. apply Hpres2. eapply apresent_grows; [exact HG0|]. exact Hpa. }
destruct (aout_facts ly S W mem c O mx no cap out HOUT) as (Hmx & HnoO & Hblk).
assert (OUTLO : forall a, In (out, cap) (ablocks B ly S) -> out <= a < out + cap -> 0 <= a < alloc_ceiling).
{ intros a Hin Ha. destruct (alx_blocks _ _ _ LAWS ly S Hp W mem md out cap HAR Hin) as (_ & H4 & Hc & _ & _ & _).
  pose proof (BLKN ly S Hp W mem md out cap HAR Hin) as Hn.
  pose proof (req_size_pos cap ltac:(lia)) as [_ Hr]. lia. }
assert (FPLO : forall r a, In r (aout_fp B RG cap out) -> fst r <= a < snd r -> 0 <= a < alloc_ceiling).
{ intros r a Hr Ha. destruct (aout_fp_cases cap out r Hr) as [Hc | (Hc & ->)].
  - pose proof (HOUTLO r Hc). lia.
  - cbn [fst snd] in Ha. destruct Hblk as [(Hc0 & _) | (_ & _ & Hin)]; [lia|]. exact (OUTLO a Hin Ha). }
assert (HOUT0 : aout_at B RG ly S W (ms_mem ms0) c O mx no cap out).
{ apply (aout_at_kept B RG ly S W mem ly S W (ms_mem ms0) c O mx no cap out HOUT).
  - intros r Hr a Ha. pose proof (FPLO r a Hr Ha) as Hlo. split.
    + apply KV; [lia|]. unfold spZ in *. lia.
    + intros Hw. exact (writable_kept (w_H W) mem (ms_mem ms0) a (KP a) Hw).
  - intros b Hb. unfold aout_blks in Hb. destruct (Z.eqb_spec cap 0); [destruct Hb|].
    destruct Hb as [<- | []]. destruct Hblk as [(Hc0 & _) | (_ & _ & Hin)]; [lia | exact Hin]. }
assert (GK0 : garr8 SEGS (arm W (ms_mem ms0)) Hk (bzs x)).
{ unfold bzs in GK. rewrite map_app in GK. apply garr8_app in GK as [GKx _].
  apply (ge_garr8_kept (w_H W) (w_H W) mem (ms_mem ms0) Hk _ GKx). intros b Hb. unfold bzs in Hb. rewrite length_map in Hb.
  apply KV; [lia|]. unfold spZ in *. lia. }
pose proof (sl_cap_nonneg c mx no cap XL ltac:(lia) ltac:(lia) ltac:(destruct Hblk; lia)) as Hcap1.
pose proof (sl_cost_nonneg MT MTL c mx no cap XL ltac:(lia) ltac:(lia) ltac:(destruct Hblk; lia)) as Hcost1.
pose proof (sl_cost_nonneg MT MTL (sl_ctl c XL) mx (sl_no c no XL) (sl_cap c mx no cap XL) 5 ltac:(lia)
  ltac:(apply sl_no_nonneg; lia) Hcap1) as Hcost2.
pose proof (sl_cap_nonneg (sl_ctl c XL) mx (sl_no c no XL) (sl_cap c mx no cap XL) 5 ltac:(lia)
  ltac:(apply sl_no_nonneg; lia) Hcap1) as Hcap2.
destruct (ge_room_sends MMAX (blocks_bytes S) c mx no cap XL ltac:(lia) ltac:(lia) ltac:(destruct Hblk; lia) ltac:(lia) ROOM)
  as (RM1 & RM2 & RM3 & RM4).
unfold ge_cost in MOK.
(* the room round: ge's budget is the first send's, leaving the second send's plus kr (ge_rk_split) *)
pose (kr1 := (Z.to_nat (sl_cost MT_rk (sl_ctl c XL) mx (sl_no c no XL) (sl_cap c mx no cap XL) 5) + kr)%nat).
rewrite (ge_rk_split c mx no cap XL kr ltac:(lia) ltac:(lia) ltac:(destruct Hblk; lia) ltac:(lia)) in RM0.
change (rp_RM RP S (Z.to_nat (sl_cost MT_rk c mx no cap XL) + kr1)) in RM0.
(* the ROM view at the first send: the prologue, strlen and the run only wrote below sp *)
assert (ROM0 : rom_view SEGS W (ms_mem ms0)).
{ intros a Hin.
  assert (HI : 0x10000 <= a < 0x5fc000)
    by (destruct Hin as (sg & Hsg & _ & Hr); exact (pa_img_range a ltac:(exists sg; split; [exact Hsg | exact Hr]))).
  rewrite KV; [exact (HROM a Hin) | lia | unfold spZ in *; lia]. }
eapply (YA0nH.SRrG_bind SEGS R R_trans).
{ eapply (gx_callS_xR SEGS B PST ARx LAWS pa_segs_low R_trans (G_SL B RG) W (ms_regs ms0) (ms_mem ms0) _ GE_STK (spZ regs) (ablocks_fp (aout_blks cap out))
    ly S Hp W mem md [] ly S Hp _ 0 SL_STK (ablocks_fp (aout_blks cap out)) (-16) (Z_to_bv 64 (BASE + 14320)) []
    (fun ly2 S2 Hp2 W2 regs2' mem2' md2' => exists out1,
      apres_kept B W (ms_mem ms0) W2 mem2' /\
      mo_le MT S S2 (sl_cost MT c mx no cap XL) /\
      rp_RM RP S2 kr1 /\
      (exists rest, Permutation (ablocks B ly S) (aout_blks cap out ++ rest) /\
         Permutation (ablocks B ly2 S2) (aout_blks (sl_cap c mx no cap XL) out1 ++ rest)) /\
      aout_at B RG ly2 S2 W2 mem2' (sl_ctl c XL) (sl_O c O x) mx (sl_no c no XL) (sl_cap c mx no cap XL) out1)
    HG HJ2).
  - rewrite Usp3. lia.
  - reflexivity.
  - lia.
  - unfold SL_STK, SL_FRAME, ASTACK. lia.
  - unfold SL_STK, SL_FRAME, ASTACK. rewrite WS. lia.
  - rewrite P3, OLDa by (cbv; lia). rewrite E3. exact Hgp.
  - rewrite P4, OLDa by (cbv; lia). rewrite E4. exact Htp.
  - exact P1.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - rewrite unsigned_lit_small by lia. lia.
  - apply achain_low. unfold s0Z. rewrite P8, F10. rewrite unsigned_lit_small by lia. lia.
  - intros HPRE1. eapply YA0nH.SRrG_mono.
    { refine (SL_R W ly S Hp (ms_regs ms0) (ms_mem ms0) _ [] c O mx no cap out Hk x HPRE1 _ _ _ _ _ _ _ _ _ _ _ _ kr1 _ _).
      - rewrite P10, F10. reflexivity.
      - rewrite P11, F37, HXL. reflexivity.
      - exact HOUT0.
      - exact ROM0.
      - exact GK0.
      - lia.
      - lia.
      - right. left. exists q, m. rewrite <- HXL. split; [exact Hq|]. split; [exact Hqo|]. split; lia.
      - intros a Ha HinG. rewrite <- HXL in Ha. destruct (HG a HinG) as (Himg & _ & _).
        refine (blk_img_x SEGS B ARx LAWS ly S Hp W mem md q m a HAR Hq _ Himg). lia.
      - rewrite <- HXL. exact RM1.
      - rewrite <- HXL. exact RM2.
      - rewrite <- HXL. apply (mo_ok_le MT MTL S _ _ MOK). lia.
      - rewrite <- HXL. exact RM0.
      - (* send_line's count peak sl_pk at ge's own state: within ge's ge_pk (W_contract_x.v) *)
        eapply cnt_ok_pk_mono; [|exact CNT0]. intros P. cbv [sl_pk ge_pk]. lia. }
    cbv beta. intros W3 c3 _ (ly3 & S3 & Hp3 & regs3 & mem3 & md3 & k3 & out3 & -> & HJ3 & HP3 & HAK3 & HM3 & HRM3 & HPm3 & HO3 & _).
    exists ly3, S3, Hp3, regs3, mem3, md3, k3. split; [rewrite P1; reflexivity|]. split; [exact HJ3|]. split; [exact HP3|].
    exists out3. rewrite <- !HXL in *. split; [exact HAK3|]. split; [exact HM3|]. split; [exact HRM3|].
    split; [exact HPm3 | exact HO3].
  - intros a Ha. left. split; [exact Ha|]. apply inFP_ablocks_fp_inv in Ha as (p & n & Hin & Hpa).
    exists p, n. split; [|exact Hpa]. unfold aout_blks in Hin. destruct (Z.eqb_spec cap 0); [destruct Hin|].
    destruct Hin as [Hpn | []]. injection Hpn as <- <-. destruct Hblk as [(Hc0 & _) | (_ & _ & Hin)]; [lia | exact Hin]. }
cbv beta. intros W3 c3 Hwle3 (ly3 & S3 & Hp3 & regs3 & mem3 & md3 & k3 & -> & HJ3 & HJc3 & HP3 & (out1 & HAK1 & HM1 & HRM1 & (rest1 & HPa1 & HPb1) & HO1)).
(* back in gesture_end after the first send *)
pose proof (ajournal_gx_AR_xR SEGS B PST ARx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3) as HAR3.
jafter_call_keep_pi HS 49%nat regs3 (mrestrict (w_H W3) mem3) HP3 [0]%nat HS3.
match type of HS3 with ?ty -> _ => assert (HRK : ty); [|specialize (HS3 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; [| apply Forall_nil].
unfold stack_region, GE_FRAME. split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Uspa.
- intros a Ha. apply (mbyte_of_aview SEGS). eapply ajgx_keep_high_xR; [exact HG | exact HJc3 | | ].
  + unfold spZ in *. lia.
  + unfold SL_STK, SL_FRAME, ASTACK. lia.
- intros a Ha _. apply (apresent_writable SEGS). eapply ajgx_pres_xR; [exact HJ3 | rewrite WS; lia]. }
clear HS. rewrite <- restrict_mkst_fx in HS3. rename HS3 into HS.
remember (havoc Ea 49 (map (getr regs3) CLOB)) as Eb eqn:HEb in HS.
assert (HEIb : img_env VAL A_LIM Eb) by (rewrite HEb; apply img_env_havoc; [exact HEIa | cbv; lia]).
assert (OLDb : forall n, (n < 49)%nat -> ew Eb n = ew Ea n) by (intros n Hn; rewrite HEb; apply YN3v.ew_havoc_old; exact Hn).
assert (HAEb : env_agree 32 (Ereg regs ge_extra) Eb) by (rewrite HEb; apply env_agree_havoc_ge; [cbv; lia | exact HAEa]).
clear HEb.
assert (Uspb : bv_unsigned (ew Eb 2) = spZ regs) by (rewrite OLDb by (cbv; lia); exact Uspa).
assert (SHOKb : sh_ok SEGS Bx ge_SH Eb (mrestrict (w_H W3) mem3)) by (unfold sh_ok, ge_SH; constructor).
paj_run_to_tok_xR RUNTOR HS HJ3 SHOKb Bspan AF_fr_send_line. { apply awr_ok_x_of0. awr_ok_tac. exact Uspb. }
pmkst HS.
prreg HS (1%bv : bv 5) T1. prreg HS (2%bv : bv 5) T2. prreg HS (3%bv : bv 5) T3.
prreg HS (4%bv : bv 5) T4. prreg HS (8%bv : bv 5) T8. prreg HS (10%bv : bv 5) T10. prreg HS (11%bv : bv 5) T11.
(* the tail call: send_line (" end", 5) at gesture_end's own sp, returning to gesture_end's caller *)
assert (HPr1 : aregs_preserved regs (ms_regs ms1)).
{ eapply (aregs_preserved_of_st_ok SEGS _ Eb _ _ regs ge_extra HS); [exact HAEb | vm_compute; reflexivity]. }
assert (R1 : getr (ms_regs ms1) 1 = getr regs 1).
{ rewrite T1, (proj1 HAEb 1%nat ltac:(lia)). exact (ew_Ereg_nat regs _ 1 1%bv eq_refl). }
assert (R2 : getr (ms_regs ms1) 2 = getr regs 2).
{ rewrite T2, (proj1 HAEb 2%nat ltac:(lia)). exact (ew_Ereg_nat regs _ 2 2%bv eq_refl). }
assert (R3 : getr (ms_regs ms1) 3 = getr regs 3).
{ rewrite T3, (proj1 HAEb 3%nat ltac:(lia)). exact (ew_Ereg_nat regs _ 3 3%bv eq_refl). }
assert (R4 : getr (ms_regs ms1) 4 = getr regs 4).
{ rewrite T4, (proj1 HAEb 4%nat ltac:(lia)). exact (ew_Ereg_nat regs _ 4 4%bv eq_refl). }
assert (R8 : getr (ms_regs ms1) 8 = getr regs 8).
{ rewrite T8, (proj1 HAEb 8%nat ltac:(lia)). exact (ew_Ereg_nat regs _ 8 8%bv eq_refl). }
assert (Usp4 : spZ (ms_regs ms1) = spZ regs) by (unfold spZ; rewrite R2; reflexivity).
(* the bytes the epilogue and the run since the first send kept *)
assert (RUN3 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 16 <= a < spZ regs) ->
  aview SEGS (w_H W3) (ms_mem ms1) a = aview SEGS (w_H W3) mem3 a).
{ intros a Ha Hno. apply (aview_kept_out Eb _ (w_H W3) mem3 (ms_mem ms1) HFr1 a Ha).
  intros (r & Hin & Hr). cbn [ss_mem add_cond In] in Hin. destruct Hin as [<- | []].
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val] in Hr. rewrite Uspb in Hr. apply Hno. lia. }
assert (KH : forall a, spZ regs <= a < 2 ^ 64 -> aview SEGS (w_H W3) (ms_mem ms1) a = aview SEGS (w_H W) mem a).
{ intros a Ha. rewrite RUN3 by lia.
  rewrite (ajgx_keep_high_xR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HG HJc3 a) by (unfold SL_STK, SL_FRAME, ASTACK; lia).
  apply KV; lia. }
assert (FPS : forall b, fp_spares (ablocks_fp (aout_blks cap out)) b).
{ intros b. apply fp_spares_blocks. intros bb Hbb. unfold aout_blks in Hbb. destruct (Z.eqb_spec cap 0); [destruct Hbb|].
  destruct Hbb as [<- | []]. cbn [fst]. destruct Hblk as [(Hc0 & _) | (_ & _ & Hin)]; [lia|].
  destruct (alx_blocks _ _ _ LAWS ly S Hp W mem md out cap HAR Hin) as (_ & H4 & _). exact H4. }
assert (GE5 : garr8 SEGS (arm W3 (ms_mem ms1)) (VAL A_lit_end5) (bzs END5)).
{ apply (ge_garr8_kept (w_H W) (w_H W3) mem (ms_mem ms1) _ _ G5).
  intros b Hb. change (Z.of_nat (length (bzs END5))) with 5 in Hb.
  pose proof (HEND5I b Hb) as Hib.
  pose proof (pa_img_range b Hib) as HIR. destruct (HEND5G b Hb) as (Hng & Hno & Hne).
  rewrite RUN3 by lia.
  rewrite (ajgx_keep_img_xR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJc3 b Hib Hno Hne (HEND5P b Hb) (FPS b) Hng).
  apply KV; lia. }
destruct (aout_facts _ _ _ _ _ _ _ _ _ _ HO1) as (_ & _ & Hblk1).
assert (HOUT3 : aout_at B RG ly3 S3 W3 (ms_mem ms1) (sl_ctl c XL) (sl_O c O x) mx (sl_no c no XL)
  (sl_cap c mx no cap XL) out1).
{ apply (aout_at_kept B RG ly3 S3 W3 mem3 ly3 S3 W3 (ms_mem ms1) _ _ _ _ _ _ HO1).
  - intros r Hr a Ha.
    assert (Hlo : 0 <= a < alloc_ceiling).
    { destruct (aout_fp_cases _ _ r Hr) as [Hc | (Hc & ->)].
      - pose proof (HOUTLO r Hc). lia.
      - cbn [fst snd] in Ha. destruct Hblk1 as [(Hc0 & _) | (_ & _ & Hin)]; [lia|].
        destruct (alx_blocks _ _ _ LAWS ly3 S3 Hp3 W3 mem3 _ _ _ HAR3 Hin) as (_ & H4 & Hc' & _ & _ & _).
        pose proof (BLKN ly3 S3 Hp3 W3 mem3 _ _ _ HAR3 Hin) as Hn.
        pose proof (req_size_pos (sl_cap c mx no cap XL) ltac:(lia)) as [_ Hr']. lia. }
    split.
    + apply RUN3; [lia|]. lia.
    + intros Hw. apply (writable_kept (w_H W3) mem3 (ms_mem ms1) a); [|exact Hw].
      intros Hpa. eapply apresent_grows; [exact HG2 | exact Hpa].
  - intros b Hb. unfold aout_blks in Hb. destruct (Z.eqb_spec (sl_cap c mx no cap XL) 0); [destruct Hb|].
    destruct Hb as [<- | []]. destruct Hblk1 as [(Hc0 & _) | (_ & _ & Hin)]; [lia | exact Hin]. }
assert (BBx : forall l s, blocks_bytes s = bsum (ablocks B l s)) by (intros; apply blocks_bytes_bsum).
assert (BB3 : blocks_bytes S3 <= blocks_bytes S - cap + sl_cap c mx no cap XL).
{ rewrite (BBx ly S), (BBx ly3 S3), (bsum_perm _ _ HPa1), (bsum_perm _ _ HPb1), !bsum_app.
  unfold aout_blks. destruct (Z.eqb_spec cap 0), (Z.eqb_spec (sl_cap c mx no cap XL) 0); cbn [bsum fold_right snd]; lia. }
assert (DEC : forall u v : Z * Z, {u = v} + {u <> v}) by (decide equality; apply Z.eq_dec).
(* the ROM view at the second send: send_line's journal keeps it (rom_out), the epilogue writes only its frame *)
assert (ROM1 : rom_view SEGS W3 (ms_mem ms1)).
{ assert (ROM3 : rom_view SEGS W3 mem3)
    by (eapply ajournal_gx_rom_view_xR; first [exact HJc3 | exact HROMO | exact PSTR | exact ROM0 | exact LAWS | exact pa_segs_low]).
  intros a Hin.
  assert (HI : 0x10000 <= a < 0x5fc000)
    by (destruct Hin as (sg & Hsg & _ & Hr); exact (pa_img_range a ltac:(exists sg; split; [exact Hsg | exact Hr]))).
  rewrite RUN3; [exact (ROM3 a Hin) | lia | unfold spZ in *; lia]. }
eapply YA0nH.SRrG_mono.
{ eapply (gx_callS_xR SEGS B PST ARx LAWS pa_segs_low R_trans (G_SL B RG) W3 (ms_regs ms1) (ms_mem ms1) _ GE_STK (spZ regs) (ablocks_fp (aout_blks cap out))
    ly S Hp W mem md [] ly3 S3 Hp3 _ _ SL_STK (ablocks_fp (aout_blks (sl_cap c mx no cap XL) out1)) 0 (getr regs 1) ch
    (fun ly2 S2 Hp2 W2 regs2' mem2' md2' => exists out2,
      apres_kept B W3 (ms_mem ms1) W2 mem2' /\
      mo_le MT S3 S2 (sl_cost MT (sl_ctl c XL) mx (sl_no c no XL) (sl_cap c mx no cap XL) 5) /\
      rp_RM RP S2 kr /\
      (exists rest, Permutation (ablocks B ly3 S3) (aout_blks (sl_cap c mx no cap XL) out1 ++ rest) /\
         Permutation (ablocks B ly2 S2) (aout_blks (sl_cap (sl_ctl c XL) mx (sl_no c no XL) (sl_cap c mx no cap XL) 5) out2 ++ rest)) /\
      aout_at B RG ly2 S2 W2 mem2' (sl_ctl (sl_ctl c XL) 5) (sl_O (sl_ctl c XL) (sl_O c O x) END5) mx
        (sl_no (sl_ctl c XL) (sl_no c no XL) 5) (sl_cap (sl_ctl c XL) mx (sl_no c no XL) (sl_cap c mx no cap XL) 5) out2)
    HG HJ3).
  - rewrite Usp4. lia.
  - reflexivity.
  - lia.
  - unfold SL_STK, SL_FRAME, ASTACK. lia.
  - unfold SL_STK, SL_FRAME, ASTACK. rewrite WS. lia.
  - rewrite R3. exact Hgp.
  - rewrite R4. exact Htp.
  - exact R1.
  - exact Hra.
  - exact Hra4.
  - rewrite Z.add_0_r. replace (s0Z (ms_regs ms1)) with (s0Z regs) by (unfold s0Z; rewrite R8; reflexivity).
    apply (achain_ly_top ly ly3); [exact (ajgx_ly_top_xR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3)|].
    apply (achain_kept ly (aview SEGS (w_H W) mem) _ (spZ regs) (s0Z regs) ch (spZ regs) Hch); [lia | lia |].
    intros a Ha. exact (KH a Ha).
  - intros HPRE2. eapply YA0nH.SRrG_mono.
    { refine (SL_R W3 ly3 S3 Hp3 (ms_regs ms1) (ms_mem ms1) _ ch (sl_ctl c XL) (sl_O c O x) mx (sl_no c no XL)
        (sl_cap c mx no cap XL) out1 (VAL A_lit_end5) END5 HPRE2 _ _ _ _ _ _ _ _ _ _ _ _ kr _ _).
      - pose proof (HEIb 269%nat ltac:(unfold A_TEXT, A_LIM; lia)) as V269.
        rewrite T10. change (VAL A_lit_end5) with (VAL 269%nat). rewrite <- V269. unfold w64.
        rewrite Z_to_bv_bv_unsigned. reflexivity.
      - rewrite T11. reflexivity.
      - exact HOUT3.
      - exact ROM1.
      - exact GE5.
      - pose proof (pa_val_range A_lit_end5). lia.
      - change (Z.of_nat (length END5)) with 5.
        pose proof (pa_img_range _ (HEND5I (VAL A_lit_end5 + 4) ltac:(lia))). lia.
      - right. right. change (Z.of_nat (length END5)) with 5. split; [exact HEND5I|]. split; [exact HEND5S|].
        intros a Ha. exact (proj1 (proj2 (HEND5G a Ha))).
      - change (Z.of_nat (length END5)) with 5. intros a Ha. exact (proj1 (HEND5G a Ha)).
      - change (Z.of_nat (length END5)) with 5. exact RM3.
      - change (Z.of_nat (length END5)) with 5. lia.
      - change (Z.of_nat (length END5)) with 5. exact (mo_ok_step MT MTL S S3 _ _ MOK HM1).
      - change (Z.of_nat (length END5)) with 5. exact HRM1.
      - (* send_line's count peak sl_pk at S3: ge's ge_pk at S covers it plus the first send's net growth (at most
           one live block more, ge_acnt_step) *)
        eapply cnt_ok_pk_mono; [|exact CNT0]. intros P. pose proof (ge_acnt_step P _ _ _ _ _ _ _ HPa1 HPb1).
        cbv [sl_pk ge_pk]. lia. }
    cbv beta. intros W4 c4 _ (ly4 & S4 & Hp4 & regs4 & mem4 & md4 & k4 & out4 & -> & HJ4 & HP4 & HAK4 & HM4 & HRM4 & HPm4 & HO4 & _).
    exists ly4, S4, Hp4, regs4, mem4, md4, k4. split; [rewrite R1; reflexivity|]. split; [exact HJ4|]. split; [exact HP4|].
    exists out4. split; [exact HAK4|]. split; [exact HM4|]. split; [exact HRM4|]. split; [exact HPm4 | exact HO4].
  - intros a Ha. apply inFP_ablocks_fp_inv in Ha as (p & n & Hin & Hpa).
    unfold aout_blks in Hin. destruct (Z.eqb_spec (sl_cap c mx no cap XL) 0) as [Hc0 | Hc0]; [destruct Hin|].
    destruct Hin as [Hpn | []]. injection Hpn as <- <-.
    assert (IN3 : In (out1, sl_cap c mx no cap XL) (ablocks B ly3 S3)).
    { apply (Permutation_in _ (Permutation_sym HPb1)). unfold aout_blks. rewrite (proj2 (Z.eqb_neq _ _) Hc0). left. reflexivity. }
    destruct (in_dec DEC (out1, sl_cap c mx no cap XL) (ablocks B ly S)) as [IN0 | NIN0].
    + left. split; [|exists out1, (sl_cap c mx no cap XL); split; [exact IN3 | exact Hpa]].
      apply (Permutation_in _ HPa1) in IN0. apply in_app_or in IN0 as [IN0 | IN0].
      * replace a with (out1 + (a - out1)) by lia. apply (inFP_ablocks_fp _ out1 (sl_cap c mx no cap XL)); [exact IN0 | lia].
      * exfalso. pose proof (ablocks_nodup ly3 S3 Hp3 _ _ _ HAR3) as ND3. apply (Permutation_NoDup HPb1) in ND3.
        unfold aout_blks in ND3. rewrite (proj2 (Z.eqb_neq _ _) Hc0) in ND3. cbn [app] in ND3.
        inversion ND3 as [|? ? Hni _]. exact (Hni IN0).
    + right. exists out1, (sl_cap c mx no cap XL). split; [exact IN3|]. split; [exact NIN0 | exact Hpa]. }
cbv beta. intros W4 c4 Hwle4 (ly4 & S4 & Hp4 & regs4 & mem4 & md4 & k4 & -> & HJ4 & HJc4 & HP4 & (out2 & HAK2 & HM2 & HRM2 & (rest2 & HPa2 & HPb2) & HO2)).
unfold ge_post_xR. exists ly4, S4, Hp4, regs4, mem4, md4. eexists. exists out2.
split; [reflexivity|]. split; [exact HJ4|]. split; [exact (aregs_preserved_trans _ _ _ HPr1 HP4)|].
split.
{ (* present image bytes: the runs grow memory, the strlen site keeps presence, both sends keep it *)
  eapply apk_trans; [exact (apk_of_pres W mem (ms_mem ms0) KP)|].
  eapply apk_trans; [exact HAK1|].
  eapply apk_trans; [|exact HAK2].
  apply apk_of_pres. intros a Hpa. eapply apresent_grows; [exact HG2 | exact Hpa]. }
rewrite <- HXL. split.
{ unfold ge_cost. exact (mo_le_trans MT MTL _ _ _ _ _ HM1 HM2). }
split; [exact HRM2|].
split.
{ exists rest1. split; [exact HPa1|].
  eapply perm_trans; [exact HPb2|]. apply Permutation_app_head.
  apply (Permutation_app_inv_l (aout_blks (sl_cap c mx no cap XL) out1)).
  eapply perm_trans; [exact (Permutation_sym HPa2)|]. exact HPb1. }
unfold ge_ctl, ge_O, ge_no, ge_cap. rewrite <- ?HXL. exact HO2.
Qed.
End wR.
(* the strict texts are the R twins above at R := wle: each R premise at wle is the strict hypothesis of the same
   name, and the three laws hold for wle *)
Local Ltac wle_inst := first [ eassumption | intros ? ? H; exact H | intros ?; apply wle_refl
  | intros ? ? ? H1 H2; eapply wle_trans; [exact H1 | exact H2] ].

(* The caller's own window stays present through its journal. *)
Lemma ajgx_pres : forall G XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k,
AJGX G XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k ->
forall a, sp0 - STK <= a < sp0 -> apresent (w_H W') mem' a.
Proof.
eapply (ajgx_pres_xR (@wle SEGS)); wle_inst.
Qed.

(* A callee's journal keeps every byte above alloc_ceiling outside its window (G lies in the image). *)
Lemma ajgx_keep_high : forall G XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k,
gx_ok SEGS B G -> AJGX G XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k ->
forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (sp0 + XO - (STK + XO) <= a < sp0 + XO) ->
aview SEGS (w_H W') mem' a = aview SEGS (w_H W) mem a.
Proof.
eapply (ajgx_keep_high_xR (@wle SEGS)); wle_inst.
Qed.

(* A journal keeps the image bytes outside G, the allocator's statics, errno and the program statics PST. *)
Lemma ajgx_keep_img : forall G XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k,
AJGX G XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k ->
forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
~ Exists (in_zr a) PST -> fp_spares FP a -> ~ inG G a -> aview SEGS (w_H W') mem' a = aview SEGS (w_H W) mem a.
Proof.
eapply (ajgx_keep_img_xR (@wle SEGS)); wle_inst.
Qed.

(* A journal keeps the top of the stack layout. *)
Lemma ajgx_ly_top : forall G XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k,
AJGX G XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k -> ly_top ly' = ly_top ly.
Proof.
eapply (ajgx_ly_top_xR (@wle SEGS)); wle_inst.
Qed.

Theorem pb_gesture_end_x : ge_spec_x B PST ARx MT RP MMAX RG A_gesture_endP.
Proof.
eapply (pb_gesture_end_xR (@wle SEGS)); wle_inst.
Qed.
End c.

(* ---- THE AR STATEMENT, re-derived (route (b), step 3, CONVERSION.md (sha256 1015972e02a9; internal record) 3.): pb_gesture_end's statement is the AR walk's,
   byte-identical, now a corollary of pb_gesture_end_x at ARx := ARi0 (cgif's AR with the head set empty), PST := [].
   Its Section takes LX0 (the laws at ARi0, a Theorem Labs lane's rulings (a) and HP0) in place of LAWS: the instance builds it
   once, W_journal_x.AR_laws_x_ARi0 (YCbqG.AR_laws_x_of_AR ..).  The bridges: W_contract_x ge_spec_x_AR0 (the
   conclusion), sl_spec_x_of_AR0 / astrlen_realizes_x_of_AR0 / ashp_x_ARi0_of (the callees and the literal's shadow);
   HP0 at ARi0 is ARi0_hp0, BLKN is W_kit_x.AR_blkn, PSTR / HEND5P hold at PST = [].  The AR walk's ALLOC_TAIL is not
   a hypothesis any more: LX0's alx_blocks / alx_blocks_tail give it (ge_tail_vis_x). ---- *)
Section cAR.
Variable B : asyms.
Variable MT : ameter_ops.
Variable MMAX : Z.
Variable RG : rep_globals.
Hypothesis LX0 : AR_laws_x SEGS B (ARi0 SEGS B) 0.
Hypothesis HG : gx_ok SEGS B (G_SL B RG).
Hypothesis ASTRLEN : astrlen_realizes B (SIGMA WS_strlen).
Hypothesis SL : sl_spec B MT MMAX RG (BASE + AF_fr_send_line).
(* " end\0" lies in the image (true: .rodata) *)
Hypothesis HEND5I : forall a, VAL A_lit_end5 <= a < VAL A_lit_end5 + 5 -> in_img SEGS a.
(* " end\0" is addressable with a visible shadow hull in every AR state (W_shadow_pin.v ashp; at the instance
   W_shadow_pin_fr.v ashp_end5_5_fr).  The literal arm of W7's sl_line_ok asks exactly this (a working branch
   6db0a9327b4); the zero-shadow claim it replaces was false (partial granule, shadow 5 at 0x7fffc1e0). *)
Hypothesis HEND5S : ashp B (VAL A_lit_end5) 5.
Hypothesis MTL : ameter_laws MT.
(* the controller's cells lie in the image, below every stack *)
Hypothesis HOUTLO : forall r, In r (aout_fp B RG 0 0) -> 0 <= fst r /\ snd r <= 0x5fc000.
(* " end\0" is none of the bytes send_line may change *)
(* HEND5G holds for EXACTLY [VAL A_lit_end5, VAL A_lit_end5 + 5) = [0x20f00, 0x20f05) on both images and MUST NOT BE
   WIDENED: its `~ owned_static` clause is TRUE (StartupTrace's tfib_lit_end5_not_owned_static, a working branch
   5fab70f4113; ZeroGlobals and W1Verify measured the same rows) only because owned_static's rows (0x20ee1, 0x1f) and
   (0x20f05, 0x1b) - the literal's two redzones - end and start exactly at its edges.  One byte more on either side,
   or rounding the range to 8 bytes or an aligned word, makes that clause FALSE. *)
Hypothesis HEND5G : forall a, VAL A_lit_end5 <= a < VAL A_lit_end5 + 5 ->
  ~ inG (G_SL B RG) a /\ ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).
(* ROM bytes are none of the bytes send_line may change (W_journal.v rom_out), so rom_view survives its journal *)
Hypothesis HROMO : rom_out SEGS B (G_SL B RG).
Theorem pb_gesture_end : ge_spec B MT MMAX RG A_gesture_endP.
Proof.
apply ge_spec_x_AR0.
assert (HP0 : forall ly S Hp W mem md, ARi0 SEGS B ly S Hp W mem md -> Hp = []) by apply ARi0_hp0.
assert (BLKN : forall ly S Hp W mem md p n, ARi0 SEGS B ly S Hp W mem md -> In (p, n) (ablocks B ly S) -> 0 <= n)
  by (intros ly S Hp W mem md p n H Hin; destruct H as [HAR _]; exact (AR_blkn B ly S Hp W mem md p n HAR Hin)).
pose proof (astrlen_realizes_x_of_AR0 B _ ASTRLEN) as ASTRLENx.
pose proof (sl_spec_x_of_AR0 B MT MMAX RG _ SL) as SLx.
pose proof (ashp_x_ARi0_of B _ _ HEND5S) as HEND5Sx.
assert (PSTR : forall a, in_rom SEGS a -> ~ Exists (in_zr a) []) by (intros a _ H; inversion H).
assert (HEND5P : forall a, VAL A_lit_end5 <= a < VAL A_lit_end5 + 5 -> ~ Exists (in_zr a) []) by (intros a _ H; inversion H).
eapply pb_gesture_end_x; eassumption.
Qed.
End cAR.
End b.
End a.
