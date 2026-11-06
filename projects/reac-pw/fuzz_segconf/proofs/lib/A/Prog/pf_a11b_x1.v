(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the boundary states and segment statements of LLVMFuzzerTestOneInput's ASan+UBSan walk (plugin-hostd/fuzz_command image B, 0x86530), the B twin of lib/A/Prog/LLVMFuzzerTestOneInput_defs.v, in the form of proofs/cgif/cgif_file_fuzzer/lib/A/ACh6.v (the CL_*_stmtX statements: from a point of the function to its return, under the entry's context) and A/ACf5.v (rtcx, rt_base: the entry's facts bundled once). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/B/Prog/LLVMFuzzerTestOneInput_defs.v, with its module paths, module names, addresses and numbers changed; 469 of its 518 lines of code are new or changed and 289 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/A/Prog/LLVMFuzzerTestOneInput_defs.v, with its module paths and module names changed; 126 of its 152 lines of code are new or changed and 492 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/A/Prog/pf_a7_d.v, with its numbers changed; 295 of its 379 lines of code are new or changed and 68 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, image A (fuzz_segconf.asan): the PROGRAM call site of segment A11b of
   reac_segconf_parse_file's walk at KEXIT (lib/A/Prog/pf_a11b_d.v), the refusal F_badmodel (2026-10-30).
   The stream's rule that every call site is shown by its own lemma: one
   closed lemma per call site, showing that the site supplies the callee contract's premises.

     0x886c8 auipc a0,0xfff99 ; addi a2,a0,0x1b8   a2 = 0x21880 = seg_litA_rc F_badmodel
     0x886d0 ld s8,0x90(s1)      s8 = c
     0x886d4 mv a0,s8            a0 = c
     0x886d8 mv a1,s10           a1 = lineno = ln + 1
     0x886dc ld a3,0x50(s1)      a3 = cur_name = F + PF_O_CN
     0x886e0 ld a4,0x18(s1)      a4 = the value pointer vp
     0x886e4 ld a5,0x78(s1)      a5 = known    = F + PF_O_KNOWN
     0x886e8 jal 0x88da4 <refuse>

   so the call is refuse(c, ln + 1, F_badmodel, cur_name, val, known), SegModel's argument list
   [AS nm; AS val; AS known]. x1_refuse_site_ok_886e8 concludes x1_refuse_call: everything refuse_contract
   (lib/A/Prog/refuse_c.v) asks at image A's numbers (lit := seg_litA_rc, gotw := gotwA, guard := guardA,
   SegInstA.v) besides afn_pre, which the call rule PaFx.cl_callSF builds from the journal. No instruction is
   walked here.

   COPIED FROM segment A7's lib/A/Prog/pf_a7_s.v and pf_a7_d.v at commit 980fbe9c6015 (a7_refuse_call,
   a7_va, a7_apart, a7_va_ok, a7_refuse_site_ok, a7_round8, a7_le65535, a7_in, a7_room_ev; a7_sh_at, a7_sh_some,
   a7_addr_buf, a7_fframe_buf), renamed a7_ -> x1_. A7 states them over its record a7_st and over buf only; here
   they are stated over pf_pieces.v's pf_base at any scope sc and over THE WHOLE class-5 frame F (2048 bytes):
   - x1_addr_frame: a range of the frame whose shadow cells (pf_shb sc) are all 0 is addressable. The 8-byte
     shadow hull stays in the frame's 256 shadow cells, which a5_geo gives present (pf_a5_k.v); its low end stays
     at or above SH because a range with cells at 0 starts at cell 4 or later (cells 0..3 are the left redzone)
     and SH = SHADOW_OFF + F / 8 is a multiple of 4 (F mod 32 = 0).
   - x1_fframe_frame: a range of the frame lies in a LIVE side-stack frame (refuse_va_locs' frame arm).

   WHERE EACH PREMISE COMES FROM (INV_KEXIT, pf_a11b_d.v:122-130).
   - The three %s arguments all lie in F, so all three take refuse_va_locs' sa_fframe arm:
       nm    at F + 0x20 (cur_name[16], cells 4..5): pf_st's pf_nm (seg_spec.cstr_enc 16) gives its bytes and NUL
             (x1_nm_str), its tail lies in the frame (a5_geo's present bytes);
       val   at vp in buf (cells 8..71): INV_KEXIT's sa_str and pf_inb;
       known at F + 0x320 (known[240], cells 100..129): INV_KEXIT's sa_zs, seg_spec.known_nulfree and
             seg_spec.known_length (x1_known_str).
     PF_SC_KN has cur_name, buf and known in scope, so x1_addr_frame gives all three sa_addr.
   - sa_va_args keeps each argument's read span (seg_spec.cstr_span, up to the next 8-byte boundary) apart from
     [ly_stk_lo ly, sp), the slot refusal[n] and c->refused: the span stays in F (F + 2048 is 8-aligned), F is
     below alloc_ceiling <= ly_stk_lo ly (the journal's astk_ok), and the block c and F are disjoint
     (YCbq.sep_block_frame) (x1_apart).
   - c, its registers' range, sa_heap / sa_addr of the block: pf_cx (reader_pre) and pf_obj; c holds cf
     (pf_st); rc_refused cf + 1 < 2 ^ 32 from pf_cnt cf 0 (pfA_facts.pf_cnt_mono from the cut's pf_cnt).
   - the line: lineno = ln + 1 is pf_lctx's line count, at most the text's length, which reader_pre bounds by
     65535.
   - the format: pf_a11b_f.pf_badmodel_fmt / pf_badmodel_kinds / pf_in_lits_badmodel; sa_lit and refuse's own
     REFUSE_LITS (the tail of PARSE_FILE_LITS) from pf_obj; the literal's address below 2 ^ 63 from its
     sa_pinned at the cut's AR state.
   - printf's machine: sa_frm0 is pf_fi's, sa_ssp rd gotwA guardA is pf_obj's last conjunct at the site's own
     state, arodata_okP the one before it.
   - sa_room Sc and the event bound: the journal's frames clause (frames Sc = [(5, pos)] ++ frames S) and events
     clause with pf_cx's sa_room_n 2 S and its event bound (x1_room_ev).
   Section hypotheses: none. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK14 YK0s YK15 YP09 YI04 YI09 YN3v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05 YI16.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pf_pieces_spec pfA_facts.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaTable SegSyms SegList SegPa.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPgBase SegABase refuse_c
  reac_segconf_parse_file_c SegInstA pf_pieces pf_a5_d pf_a5_k pf_a11b_d pf_a11b_f.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

(* a list of formats, decided by trying each position *)
Ltac x1_in := cbn [In]; repeat (first [left; reflexivity | right]).

(* rounding up to the next multiple of 8 stays below an 8-aligned bound *)
Lemma x1_round8 : forall x M, x <= M -> M mod 8 = 0 -> x + (- x) mod 8 <= M.
Proof.
  intros x M H1 H2.
  pose proof (Z.div_mod (- x) 8 ltac:(lia)) as D1.
  pose proof (Z.mod_pos_bound (- x) 8 ltac:(lia)) as M1.
  pose proof (Z.div_mod M 8 ltac:(lia)) as D2.
  lia.
Qed.

(* reader_pre's text bound (length s <= 65535)%nat, in Z; the nat literal is too large for lia to read *)
Lemma x1_le65535 : forall m : nat, (m <= 65535)%nat -> Z.of_nat m <= 65535.
Proof.
  intros m H. apply Nat2Z.inj_le in H.
  assert (E : Z.of_nat 65535%nat = 65535) by (vm_compute; reflexivity).
  rewrite E in H. exact H.
Qed.

(* a char[16] field holding the C string nm (seg_spec.cstr_enc) holds nm's bytes and its NUL *)
Lemma x1_bytes_zs : forall (rd : reader) a f nm, sa_bytes rd a f -> seg_spec.cstr_enc 16 nm f ->
  sa_zs rd a (nm ++ [0]).
Proof.
  intros rd a f nm Hb (Hl & Hs & Hn & Hz) i Hi.
  rewrite length_app in Hi. cbn [length] in Hi.
  assert (Hif : (i < length f)%nat) by lia.
  rewrite <- Hz, nth_firstn.
  destruct (Nat.ltb_spec i (S (length nm))) as [_|]; [|lia].
  unfold seg_spec.zs.
  assert (Him : (i < length (map bv_unsigned f))%nat) by (rewrite length_map; exact Hif).
  rewrite (nth_indep (map bv_unsigned f) 0 (bv_unsigned ZB0) Him).
  rewrite map_nth. exact (Hb i Hif).
Qed.

(* the frame's shadow cells of the three objects the refusal reads, in PF_SC_KN (pf_a11b_d.v): cur_name
   (cells 4..5), buf (8..71), known (100..129) *)
Lemma x1_shb_cn : forall i, 4 <= i < 6 -> pf_shb PF_SC_KN i = 0.
Proof.
  intros i Hi. unfold pf_shb.
  destruct (Z.ltb_spec i 4) as [H|_]; [lia|].
  destruct (Z.ltb_spec i 6) as [_|H]; [reflexivity|lia].
Qed.

Lemma x1_shb_buf : forall i, 8 <= i < 72 -> pf_shb PF_SC_KN i = 0.
Proof.
  intros i Hi. unfold pf_shb.
  destruct (Z.ltb_spec i 4) as [H|_]; [lia|].
  destruct (Z.ltb_spec i 6) as [H|_]; [lia|].
  destruct (Z.ltb_spec i 8) as [H|_]; [lia|].
  destruct (Z.ltb_spec i 72) as [_|H]; [reflexivity|lia].
Qed.

Lemma x1_shb_known : forall i, 100 <= i < 130 -> pf_shb PF_SC_KN i = 0.
Proof.
  intros i Hi. unfold pf_shb.
  destruct (Z.ltb_spec i 4) as [H|_]; [lia|].
  destruct (Z.ltb_spec i 6) as [H|_]; [lia|].
  destruct (Z.ltb_spec i 8) as [H|_]; [lia|].
  destruct (Z.ltb_spec i 72) as [H|_]; [lia|].
  destruct (Z.ltb_spec i 80) as [H|_]; [lia|].
  destruct (Z.ltb_spec i 88) as [H|_]; [lia|].
  destruct (Z.ltb_spec i 92) as [H|_]; [lia|].
  destruct (Z.ltb_spec i 95) as [H|_]; [lia|].
  destruct (Z.ltb_spec i 100) as [H|_]; [lia|].
  destruct (Z.ltb_spec i 130) as [_|H]; [reflexivity|lia].
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

(* what the refuse site puts in the variadic registers a3 .. a7: each %s argument a C string in the class-5
   frame, addressable with its shadow mapped, each integer argument below 2 ^ 31 (refuse_pre's sa_va_args, in
   the shape the site has it) *)
Fixpoint x1_va (v : pfv) (pos : Z) (rd : reader) (rs : list word) (xs : list arg) : Prop :=
  match xs, rs with
  | [], _ => True
  | AS s :: xs', r :: rs' =>
      (exists q, r = w64 q /\ sa_str rd q s /\ sa_addr rd q (Z.of_nat (length s) + 1) /\
                 pf_F v pos <= q /\ q + Z.of_nat (length s) + 1 <= pf_F v pos + 2048) /\
      x1_va v pos rd rs' xs'
  | AI z :: xs', r :: rs' => (0 <= z < 2 ^ 31 /\ bv_unsigned r = z) /\ x1_va v pos rd rs' xs'
  | _ :: _, [] => False
  end.

Section e.
Variable B : asyms.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.

(** ** What refuse's contract asks besides afn_pre *)
(* everything refuse_contract asks at image A's numbers besides afn_pre (the call rule PaFx.cl_callSF
   builds afn_pre from the journal).  Copied from piece A7's pf_a7_s.v a7_refuse_call. *)
Definition x1_refuse_call (v : pfv) (lyc : alayout) (Sc : astate) (Wc : world SEGS)
  (memc : word -> option byte) (regs : bvmap 5 word) (cf : rconf) (ln : Z) (f : list Z) (args : list arg)
  : Prop :=
  arodata_okP SEGS RLO_A RHI_A B (rdW Wc memc) /\
  getr regs 10 = w64 (p_c v) /\ 0 <= p_c v < 2 ^ 64 /\
  getr regs 11 = w64 (ln + 1) /\ 0 <= ln + 1 < 2 ^ 64 /\
  getr regs 12 = w64 (seg_litA_rc f) /\ 0 <= seg_litA_rc f < 2 ^ 64 /\
  refuse_pre SEGS B seg_litA_rc gotwA guardA lyc Sc regs (rdW Wc memc) (p_c v) (ln + 1) (seg_litA_rc f)
    [getr regs 13; getr regs 14; getr regs 15; getr regs 16; getr regs 17] cf (ln + 1) f args /\
  sa_room Sc /\ st_nev Sc + EV_refuse <= EV_MAX.

(** ** The class-5 frame at a cut *)
(* the frame's shadow cell of an address of an object whose cells cl .. ch - 1 are 0 *)
Lemma x1_sh_at : forall v pos lyc Sc Wc rX memc mdc sc (cl ch : Z) x,
  pf_base B v pos lyc Sc Wc rX memc mdc sc ->
  0 <= cl -> ch <= 144 -> (forall i, cl <= i < ch -> pf_shb sc i = 0) ->
  pf_F v pos + 8 * cl <= x < pf_F v pos + 8 * ch ->
  rdW Wc memc (shadow_of_addr SHADOW_OFF x) = Some 0.
Proof.
  intros v pos lyc Sc Wc rX memc mdc sc cl ch x H Hcl Hch Hz Hx.
  pose proof H as (_ & _ & _ & _ & HFSH).
  destruct (a5_geo B v pos lyc Sc Wc rX memc mdc sc H) as (_ & _ & _ & G & _ & _).
  destruct G as (_ & _ & _ & _ & _ & H1 & _ & H4 & _).
  assert (HF8 : pf_F v pos mod 8 = 0) by (pose proof (Z.div_mod (pf_F v pos) 32 ltac:(lia)); lia).
  replace x with (pf_F v pos + (x - pf_F v pos)) by lia.
  rewrite (shadow_of_addr_aligned_off SHADOW_OFF (pf_F v pos) (x - pf_F v pos) HF8).
  change (shadow_of_addr SHADOW_OFF (pf_F v pos)) with (pf_SH v pos).
  rewrite (HFSH ((x - pf_F v pos) / 8)).
  - f_equal. apply Hz.
    split; [apply Z.div_le_lower_bound; lia | apply Z.div_lt_upper_bound; lia].
  - split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia].
Qed.

(* every one of the frame's 256 shadow cells is mapped *)
Lemma x1_sh_some : forall v pos lyc Sc Wc rX memc mdc sc s, pf_base B v pos lyc Sc Wc rX memc mdc sc ->
  pf_SH v pos <= s < pf_SH v pos + 256 -> rdW Wc memc s <> None.
Proof.
  intros v pos lyc Sc Wc rX memc mdc sc s H Hs.
  destruct (a5_geo B v pos lyc Sc Wc rX memc mdc sc H) as (_ & _ & _ & _ & _ & HSP).
  replace s with (pf_SH v pos + (s - pf_SH v pos)) by lia.
  exact (aview_some_of_apresent SEGS (w_H Wc) memc _ (HSP (s - pf_SH v pos) ltac:(lia))).
Qed.

(* a range of the class-5 frame whose shadow cells are all 0 is addressable: the generalisation of A7's
   a7_addr_buf from buf to any object of the frame *)
Lemma x1_addr_frame : forall v pos lyc Sc Wc rX memc mdc sc q n (cl ch : Z),
  pf_base B v pos lyc Sc Wc rX memc mdc sc ->
  0 <= cl -> ch <= 144 -> (forall i, cl <= i < ch -> pf_shb sc i = 0) ->
  pf_F v pos + 8 * cl <= q -> 0 <= n -> q + n <= pf_F v pos + 8 * ch ->
  sa_addr (rdW Wc memc) q n.
Proof.
  intros v pos lyc Sc Wc rX memc mdc sc q n cl ch H Hcl Hch Hz Hq Hn Hqn.
  destruct (a5_geo B v pos lyc Sc Wc rX memc mdc sc H) as (_ & _ & _ & G & _ & _).
  destruct G as (_ & _ & _ & _ & _ & H1 & H2 & H4 & H3 & ESH & _ & _).
  pose proof alloc_ceiling_lt as HC.
  assert (HF8 : pf_F v pos mod 8 = 0) by (pose proof (Z.div_mod (pf_F v pos) 32 ltac:(lia)); lia).
  split; [lia|]. split; [lia|].
  split.
  { apply amem_range_high; [lia| |lia].
    destruct H3 as [_ [Hlo | [Hhi1 Hhi2]]]; unfold kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *;
    [left; lia | right; lia]. }
  split.
  - intros x Hx. exists 0. split; [|left; reflexivity].
    apply (x1_sh_at v pos lyc Sc Wc rX memc mdc sc cl ch x H Hcl Hch Hz). lia.
  - intros Hn0 s Hs.
    (* a non-empty range with its cells at 0 starts at cell 4 or later: cells 0 .. 3 are the left redzone *)
    assert (Hcl4 : 4 <= cl).
    { destruct (Z.lt_ge_cases cl 4) as [Hlt|Hge]; [|exact Hge].
      exfalso. specialize (Hz cl ltac:(lia)). unfold pf_shb in Hz.
      rewrite (proj2 (Z.ltb_lt cl 4) Hlt) in Hz. discriminate. }
    (* the 8-byte hull of [q, q + n) stays inside the frame's 256 shadow cells *)
    assert (E1 : shadow_addr q = pf_SH v pos + (q - pf_F v pos) / 8).
    { unfold shadow_addr. replace q with (pf_F v pos + (q - pf_F v pos)) at 1 by lia.
      change (SHADOW_OFF + (pf_F v pos + (q - pf_F v pos)) / 8)
        with (shadow_of_addr SHADOW_OFF (pf_F v pos + (q - pf_F v pos))).
      rewrite (shadow_of_addr_aligned_off SHADOW_OFF (pf_F v pos) (q - pf_F v pos) HF8). reflexivity. }
    assert (E2 : shadow_addr (q + n - 1) = pf_SH v pos + (q + n - 1 - pf_F v pos) / 8).
    { unfold shadow_addr. replace (q + n - 1) with (pf_F v pos + (q + n - 1 - pf_F v pos)) at 1 by lia.
      change (SHADOW_OFF + (pf_F v pos + (q + n - 1 - pf_F v pos)) / 8)
        with (shadow_of_addr SHADOW_OFF (pf_F v pos + (q + n - 1 - pf_F v pos))).
      rewrite (shadow_of_addr_aligned_off SHADOW_OFF (pf_F v pos) (q + n - 1 - pf_F v pos) HF8). reflexivity. }
    assert (B1 : cl <= (q - pf_F v pos) / 8)
      by (apply Z.div_le_lower_bound; lia).
    assert (B2 : (q + n - 1 - pf_F v pos) / 8 < ch)
      by (apply Z.div_lt_upper_bound; lia).
    (* SH = SHADOW_OFF + F / 8 is a multiple of 4 *)
    assert (HSH4 : pf_SH v pos = 4 * (0x1fffe000 + pf_F v pos / 32)).
    { rewrite ESH. unfold SHADOW_OFF.
      pose proof (Z.div_mod (pf_F v pos) 8 ltac:(lia)) as D8.
      pose proof (Z.div_mod (pf_F v pos) 32 ltac:(lia)) as D32. lia. }
    rewrite E1, E2 in Hs.
    apply (x1_sh_some v pos lyc Sc Wc rX memc mdc sc s H).
    pose proof (Z.div_mod (pf_SH v pos + (q - pf_F v pos) / 8) 8 ltac:(lia)) as D1.
    pose proof (Z.mod_pos_bound (pf_SH v pos + (q - pf_F v pos) / 8) 8 ltac:(lia)) as M1.
    pose proof (Z.div_mod (pf_SH v pos + (q + n - 1 - pf_F v pos) / 8) 8 ltac:(lia)) as D2.
    pose proof (Z.mod_pos_bound (pf_SH v pos + (q + n - 1 - pf_F v pos) / 8) 8 ltac:(lia)) as M2.
    lia.
Qed.

(* a range of the class-5 frame lies in a live side-stack frame *)
Lemma x1_fframe_frame : forall v pos lyc Sc Wc rX memc mdc sc q n,
  pf_base B v pos lyc Sc Wc rX memc mdc sc ->
  pf_F v pos <= q -> 0 <= n -> q + n <= pf_F v pos + 2048 -> sa_fframe lyc Sc q n.
Proof.
  intros v pos lyc Sc Wc rX memc mdc sc q n H Hq Hn Hqn.
  destruct (a5_geo B v pos lyc Sc Wc rX memc mdc sc H) as (_ & Ely & Hin & _).
  exists 5, pos. split; [exact Hin|].
  split; [lia|].
  unfold pf_F in Hq, Hqn. rewrite <- Ely in Hq, Hqn.
  change (fs_frame_bytes 5) with 2048. lia.
Qed.

(* the cur_name text as a C string, out of pf_st's pf_nm *)
Lemma x1_nm_str : forall v pos lyc Sc Wc rX memc mdc sc cf cur nm k,
  pf_base B v pos lyc Sc Wc rX memc mdc sc ->
  pf_st v pos (rdW Wc memc) cf cur nm k ->
  (length nm <= 15)%nat /\ sa_str (rdW Wc memc) (pf_F v pos + PF_O_CN) nm.
Proof.
  intros v pos lyc Sc Wc rX memc mdc sc cf cur nm k H (_ & _ & (f & Hb & Henc) & _).
  pose proof Henc as (Hl & Hs & Hn & Hz).
  destruct (a5_geo B v pos lyc Sc Wc rX memc mdc sc H) as (_ & _ & _ & _ & HFP & _).
  split; [lia|].
  split; [split; [exact (x1_bytes_zs _ _ _ _ Hb Henc) | exact Hn]|].
  intros x Hx.
  pose proof (Z.mod_pos_bound (pf_F v pos + PF_O_CN + Z.of_nat (length nm)) 8 ltac:(lia)) as M.
  exact (aview_some_of_apresent SEGS (w_H Wc) memc x (HFP x ltac:(unfold PF_O_CN in *; lia))).
Qed.

(* the known text as a C string, out of INV_KEXIT's sa_zs *)
Lemma x1_known_str : forall v pos lyc Sc Wc rX memc mdc sc,
  pf_base B v pos lyc Sc Wc rX memc mdc sc ->
  sa_zs (rdW Wc memc) (pf_F v pos + PF_O_KNOWN) (known ++ [0]) ->
  sa_str (rdW Wc memc) (pf_F v pos + PF_O_KNOWN) known.
Proof.
  intros v pos lyc Sc Wc rX memc mdc sc H HZ.
  destruct (a5_geo B v pos lyc Sc Wc rX memc mdc sc H) as (_ & _ & _ & _ & HFP & _).
  split; [split; [exact HZ | exact seg_spec.known_nulfree]|].
  replace (Z.of_nat (length known)) with 77 by (rewrite seg_spec.known_length; reflexivity).
  intros x Hx.
  pose proof (Z.mod_pos_bound (pf_F v pos + PF_O_KNOWN + 77) 8 ltac:(lia)) as M.
  exact (aview_some_of_apresent SEGS (w_H Wc) memc x (HFP x ltac:(unfold PF_O_KNOWN in *; lia))).
Qed.

(** ** The facts the site shares with A7's *)
(* the frame's room for refuse's class-0 frame, and the events: the journal from parse_file's entry *)
Lemma x1_room_ev : forall v pos lyc Sc Wc rX memc mdc sc, pf_base B v pos lyc Sc Wc rX memc mdc sc ->
  sa_room Sc /\ st_nev Sc <= EV_MAX.
Proof.
  intros v pos lyc Sc Wc rX memc mdc sc H.
  pose proof H as (HCX & (HJ & _) & _).
  pose proof HCX as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HROOM & HEV).
  pose proof HJ as (_ & _ & _ & _ & _ & Hfr & Hnev & _).
  unfold sa_room_n in HROOM. unfold EV_reac_segconf_parse_file in HEV.
  split; [|lia].
  unfold sa_room. rewrite Hfr, length_app. cbn [length]. lia.
Qed.

(* a %s argument in the frame is apart from the three ranges refuse_pre forbids *)
Lemma x1_apart : forall v pos lyc Sc Wc rX memc mdc sc (k : nat) sp q s,
  pf_base B v pos lyc Sc Wc rX memc mdc sc -> (k <= 8)%nat ->
  pf_F v pos <= q -> q + Z.of_nat (length s) + 1 <= pf_F v pos + 2048 ->
  sa_apart_all q (seg_spec.cstr_span q s)
    [(ly_stk_lo lyc, sp);
     (seg_spec.refusal_addr (p_c v) k, seg_spec.refusal_addr (p_c v) k + seg_spec.RC_REFUSAL_LEN);
     (p_c v + seg_spec.RC_REFUSED, p_c v + seg_spec.RC_REFUSED + 4)].
Proof.
  intros v pos lyc Sc Wc rX memc mdc sc k sp q s H Hk HI1 HI2.
  pose proof H as (_ & (HJ & HLY & _) & HOBJ & _).
  pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HSTK & _).
  destruct HSTK as (_ & _ & Hceil & _).
  destruct (a5_geo B v pos lyc Sc Wc rX memc mdc sc H) as (_ & _ & Hfin & G & _).
  destruct G as (_ & _ & _ & _ & _ & H1 & H2 & H4 & _).
  assert (HF8 : (pf_F v pos + 2048) mod 8 = 0)
    by (pose proof (Z.div_mod (pf_F v pos) 32 ltac:(lia)); lia).
  pose proof (x1_round8 (q + Z.of_nat (length s) + 1) (pf_F v pos + 2048) HI2 HF8) as HR.
  assert (HSP : q + seg_spec.cstr_span q s <= pf_F v pos + 2048) by (unfold seg_spec.cstr_span; lia).
  (* the block c and the class-5 frame do not meet *)
  pose proof HOBJ as (_ & _ & _ & _ & (b & m & Hin & Hb & Hm) & _).
  pose proof (sep_block_frame SEGS B LAWS lyc Sc Wc memc mdc b m 5 pos HAR Hin Hfin) as Hsep.
  pose proof (req_size_pos m ltac:(unfold seg_spec.SEG_C_SIZE in Hm; lia)) as [_ Hrq].
  unfold zdisjoint in Hsep. cbn [fst snd] in Hsep. change (fs_frame_bytes 5) with 2048 in Hsep.
  replace (frame_addr lyc 5 pos) with (pf_F v pos) in Hsep by (unfold pf_F; rewrite HLY; reflexivity).
  assert (HAP : q + seg_spec.cstr_span q s <= p_c v \/ p_c v + seg_spec.SEG_C_SIZE <= q)
    by (destruct Hsep as [Hs|Hs]; [right|left]; lia).
  rewrite HLY.
  unfold sa_apart_all, seg_spec.refusal_addr, seg_spec.RC_REFUSAL, seg_spec.RC_REFUSAL_LEN,
    seg_spec.RC_REFUSED, seg_spec.SEG_C_SIZE in *.
  apply Forall_cons; [cbn [fst snd]; lia|].
  apply Forall_cons; [cbn [fst snd]; lia|].
  apply Forall_cons; [cbn [fst snd]; lia|].
  apply Forall_nil.
Qed.

(* the variadic registers of the site give sa_va_args and refuse_va_locs (the frame arm) *)
Lemma x1_va_ok : forall v pos lyc Sc Wc rX memc mdc sc (k : nat) sp rs xs,
  pf_base B v pos lyc Sc Wc rX memc mdc sc -> (k <= 8)%nat ->
  x1_va v pos (rdW Wc memc) rs xs ->
  sa_va_args (rdW Wc memc)
    [(ly_stk_lo lyc, sp);
     (seg_spec.refusal_addr (p_c v) k, seg_spec.refusal_addr (p_c v) k + seg_spec.RC_REFUSAL_LEN);
     (p_c v + seg_spec.RC_REFUSED, p_c v + seg_spec.RC_REFUSED + 4)] rs xs /\
  refuse_va_locs (fun q n => sa_heap B lyc Sc q n \/ sa_fframe lyc Sc q n) rs xs.
Proof.
  intros v pos lyc Sc Wc rX memc mdc sc k sp rs xs H Hk.
  destruct (a5_geo B v pos lyc Sc Wc rX memc mdc sc H) as (_ & _ & _ & G & _).
  destruct G as (_ & _ & _ & _ & _ & H1 & H2 & _).
  pose proof alloc_ceiling_lt as HC.
  revert rs. induction xs as [|x xs IH]; intros rs HV.
  - destruct rs; split; exact I.
  - destruct rs as [|r rs]; [destruct x; cbn in HV; contradiction|].
    destruct x as [s|z]; cbn [x1_va] in HV; destruct HV as [Hx HV]; destruct (IH rs HV) as [IH1 IH2].
    + destruct Hx as (q & -> & HS & HA & HI1 & HI2).
      assert (EQ : bv_unsigned (w64 q) = q).
      { unfold w64. rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 64) with (2 ^ 64). lia. }
      cbn [sa_va_args refuse_va_locs sa_va_arg]. rewrite EQ.
      split; [split; [|exact IH1] | split; [|exact IH2]].
      * split; [lia|]. split; [exact HS|].
        split; [apply (Nat.le_trans _ 2048%nat); [lia | apply Nat.leb_le; vm_compute; reflexivity]|].
        split; [exact HA|].
        exact (x1_apart v pos lyc Sc Wc rX memc mdc sc k sp q s H Hk HI1 HI2).
      * right. exact (x1_fframe_frame v pos lyc Sc Wc rX memc mdc sc q (Z.of_nat (length s) + 1) H HI1
          ltac:(lia) ltac:(lia)).
    + cbn [sa_va_args refuse_va_locs sa_va_arg].
      split; [split; [exact Hx | exact IH1] | exact IH2].
Qed.

(** ** refuse: the rule of a site in the frame *)
Lemma x1_refuse_site_ok : forall v pos lyc Sc Wc rX memc mdc sc (regs : bvmap 5 word) cf o ln d n f args,
  pf_base B v pos lyc Sc Wc rX memc mdc sc ->
  sa_rconf (rdW Wc memc) (p_c v) cf -> pf_cnt cf 0 -> pf_mid v o ln d n ->
  In f seg_spec.REFUSE_FORMATS -> In f PARSE_FILE_LITS ->
  seg_spec.conv_kinds f = map seg_spec.arg_is_s args ->
  getr regs 10 = w64 (p_c v) -> getr regs 11 = w64 (ln + 1) -> getr regs 12 = w64 (seg_litA_rc f) ->
  x1_va v pos (rdW Wc memc) [getr regs 13; getr regs 14; getr regs 15; getr regs 16; getr regs 17] args ->
  x1_refuse_call v lyc Sc Wc memc regs cf ln f args.
Proof.
  intros v pos lyc Sc Wc rX memc mdc sc regs cf o ln d n f args H HRC HCNT HMID HINF HINL HKND R10 R11 R12 HVA.
  pose proof H as (HCX & (HJ & _ & _ & _ & _ & _ & HFRM & _) & HOBJ & _).
  pose proof HCX as (_ & _ & _ & HcB & _ & _ & _ & _ & (fe & HPRE) & _ & _).
  destruct HPRE as ((C0 & C16 & _ & _ & _ & _ & _ & _ & _ & _ & LS & _) & _).
  pose proof HOBJ as (_ & _ & _ & Ac & Hc & _ & LITS & HROD & SSP).
  pose proof HJ as (HAR & _).
  destruct HMID as (_ & _ & Hle & _ & Hlnd & Hlno).
  pose proof (LITS f HINL) as HLF.
  pose proof HLF as (Hfp & _ & Hpin & _).
  pose proof (Hpin lyc Sc Wc memc mdc HAR) as (_ & Hfp63 & _).
  pose proof HRC as (bs & _ & (_ & _ & _ & _ & HK8 & _)).
  destruct (x1_room_ev v pos lyc Sc Wc rX memc mdc sc H) as [HROOM HEV].
  destruct (x1_va_ok v pos lyc Sc Wc rX memc mdc sc (length (rc_refusal cf)) (spZ regs) _ args H HK8 HVA)
    as [HVA1 HVA2].
  pose proof (x1_le65535 _ LS) as LSZ.
  assert (HLN : 0 <= ln + 1 < 2 ^ 31) by lia.
  unfold x1_refuse_call.
  split; [exact HROD|]. split; [exact R10|]. split; [exact HcB|].
  split; [exact R11|]. split; [lia|]. split; [exact R12|]. split; [lia|].
  split; [|split; [exact HROOM | unfold EV_refuse; lia]].
  unfold refuse_pre.
  split; [exact C0|]. split; [exact C16|]. split; [exact HRC|]. split; [exact Hc|]. split; [exact Ac|].
  split; [destruct HCNT as [HC1 _]; lia|].
  split; [exact HLN|]. split; [reflexivity|].
  split; [exact HINF|]. split; [exact HKND|].
  split; [lia|]. split; [reflexivity|]. split; [exact HLF|].
  split; [exact HVA1|]. split; [exact HVA2|].
  split; [exact HFRM|]. split; [exact SSP|].
  intros x Hx. apply LITS. unfold PARSE_FILE_LITS. apply in_or_app. right. exact Hx.
Qed.

(** ** refuse at 0x886e8 (VERIFY rule 1j-bis) *)
(* refuse(c, lineno, F_badmodel, cur_name, val, known): cur_name at F + 0x20 (slot 0x50), val at vp in buf
   (slot 0x18), known at F + 0x320 (slot 0x78) *)
Theorem x1_refuse_site_ok_886e8 :
  forall n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val (regs : bvmap 5 word),
  INV_KEXIT B n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val ->
  getr regs 10 = w64 (p_c v) ->
  getr regs 11 = w64 (ln + 1) ->
  getr regs 12 = w64 (seg_litA_rc F_badmodel) ->
  getr regs 13 = w64 (pf_F v pos + PF_O_CN) ->
  getr regs 14 = w64 vp ->
  getr regs 15 = w64 (pf_F v pos + PF_O_KNOWN) ->
  x1_refuse_call v lyc Sc Wc memc regs cf ln F_badmodel [AS nm; AS val; AS known].
Proof.
  intros n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val regs H R10 R11 R12 R13 R14 R15.
  destruct H as (HB & HMID & HST & HVS & HVI & HKN & _ & _).
  pose proof HST as (HRC & _ & _ & HCNT).
  pose proof (pf_cnt_mono cf _ 0%nat (Nat.le_0_l _) HCNT) as HCNT0.
  destruct (x1_nm_str v pos lyc Sc Wc rX memc mdc PF_SC_KN cf (Some gi) nm _ HB HST) as [HNL HNS].
  pose proof (x1_known_str v pos lyc Sc Wc rX memc mdc PF_SC_KN HB HKN) as HKS.
  pose proof HVI as [HV1 HV2]. unfold PF_O_BUF in HV1, HV2.
  apply (x1_refuse_site_ok v pos lyc Sc Wc rX memc mdc PF_SC_KN regs cf o ln d n F_badmodel _ HB HRC HCNT0
           HMID pf_badmodel_fmt pf_in_lits_badmodel (pf_badmodel_kinds nm val known) R10 R11 R12).
  cbn [x1_va].
  split; [|split; [|split; [|exact I]]].
  - (* cur_name: cells 4 .. 5 *)
    exists (pf_F v pos + PF_O_CN). split; [exact R13|]. split; [exact HNS|].
    split; [exact (x1_addr_frame v pos lyc Sc Wc rX memc mdc PF_SC_KN (pf_F v pos + PF_O_CN)
                     (Z.of_nat (length nm) + 1) 4 6 HB ltac:(lia) ltac:(lia) x1_shb_cn
                     ltac:(unfold PF_O_CN; lia) ltac:(lia) ltac:(unfold PF_O_CN; lia))|].
    unfold PF_O_CN. split; lia.
  - (* val in buf: cells 8 .. 71 *)
    exists vp. split; [exact R14|]. split; [exact HVS|].
    split; [exact (x1_addr_frame v pos lyc Sc Wc rX memc mdc PF_SC_KN vp (Z.of_nat (length val) + 1) 8 72 HB
                     ltac:(lia) ltac:(lia) x1_shb_buf ltac:(lia) ltac:(lia) ltac:(lia))|].
    split; lia.
  - (* known: cells 100 .. 129 *)
    exists (pf_F v pos + PF_O_KNOWN). split; [exact R15|]. split; [exact HKS|].
    replace (Z.of_nat (length known)) with 77 by (rewrite seg_spec.known_length; reflexivity).
    split; [exact (x1_addr_frame v pos lyc Sc Wc rX memc mdc PF_SC_KN (pf_F v pos + PF_O_KNOWN) (77 + 1)
                     100 130 HB ltac:(lia) ltac:(lia) x1_shb_known ltac:(unfold PF_O_KNOWN; lia) ltac:(lia)
                     ltac:(unfold PF_O_KNOWN; lia))|].
    unfold PF_O_KNOWN. split; lia.
Qed.

End e.
End f.
End d.
