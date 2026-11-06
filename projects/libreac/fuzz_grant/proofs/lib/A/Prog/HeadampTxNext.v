(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the contract of reac_headamp_tx_next for fuzz_grant.asan; tnext_kept and tnext_post adapted from proofs/cgif/cgif_file_fuzzer/lib/YC20.v (tlzw_kept, tlzw_post). *)
(* reac_headamp_tx_next (fuzz_grant.asan 0x850cc, 452 instructions, 37 instrumented
   accesses, no call): the contract of the ASan build's code, its entry state and the
   interface its walk is cut at.

   The function is the head-amp scheduler's step. It reads and writes the 460-byte table
   the harness allocated, and it writes three bytes the caller holds on its own side-stack
   frame: the channel, the parameter and the value of the record it emits. The
   memory-checking runtime lets a call write only its own machine-stack window, heap bytes
   in the journal's footprint, blocks it allocates itself, and frames it owns
   (lib/Reusable/YCbq.v:460-464), so a contract whose journal starts empty cannot write the
   caller's frame. The contract is therefore stated in the caller-journal form cgif_file
   uses for the one call of its own that writes into its caller's frame
   (proofs/cgif/cgif_file_fuzzer/lib/YC20.v:311-365): it takes the caller's journal and the
   caller's right to write those bytes, and it extends that journal.

   The table's layout is a Theorem Labs lane's LAY_TX (lib/A/Prog/HeadampTxEffective.v); the new table
   state is Pau Aliagas's model function next_model (lib/Prog/NextModel.v), with the facts
   about it from lib/Prog/{NextLemmas,HeadampI1,HeadampModel}.v. *)
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0s.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG0s.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A.Prog Require Import PaRun PaShadow GrantSyms GrantList GrantPa.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A.Prog Require Import PaJournal GrantPaLib GrantBase.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Lib Require Import Mem.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require Import
HeadampModel NextModel NextLemmas SlotNeeds_c HeadampI1.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A.Prog Require Import NextArith HeadampTxEffective.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YImgTop.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* The addresses this call may change outside its own machine-stack window. *)
Definition nx_touch (tx chp parp valp a : Z) : Prop :=
  (tx <= a < tx + TX_SIZE) \/ a = chp \/ a = parp \/ a = valp.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg grant_listing}.
#[local] Notation SEGS := (@pa_segs _ grant_listing PI).
#[local] Notation VAL := (@pa_val _ grant_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ grant_listing PI).
#[local] Notation BASE := (@pa_val _ grant_listing PI A_TEXT).

Definition A_reac_headamp_tx_nextP : Z := BASE + AF_reac_headamp_tx_next.
(* Its own frame, and nothing more: the function calls nothing. *)
Definition NEXT_STK : Z := 80.
Definition SB_NX : Z := 0x7fff8000.
Definition BxN : sv := SOff 32 0.
Definition BspanN : Z * Z := (SB_NX, SB_NX + 2 ^ 44 - 1).

(* The four slots the walk is cut at, as offsets from the listing's base:
   LOOPD 0x8514c is the head of the edge scan over the 144 cells, AFTR 0x85228 is where
   that scan found none, LOOPR 0x852e4 is the head of the replay scan over the cursor,
   and RSWP 0x85374 is the re-assert tail. *)
Definition LOOPD : Z := AF_reac_headamp_tx_next + 0x80.
Definition AFTR : Z := AF_reac_headamp_tx_next + 0x15c.
Definition LOOPR : Z := AF_reac_headamp_tx_next + 0x218.
Definition RSWP : Z := AF_reac_headamp_tx_next + 0x2a8.

(* The listing's atoms this walk adds to the 32 registers:
   32 the shadow base, 33..42 the table's ten scalar fields, 46 the dirty-scan index,
   47 the address of its dirty byte, 48 the address of its value byte, 49 and 50 those
   two bytes, 51 the replay cursor, 52..55 the replay scan's cell addresses and bytes. *)
Definition nx_extra (tx : Z) (T : list byte) : list word :=
  map (Z_to_bv 64)
    [ SB_NX; u32at T 432; tb T 436; tb T 437; s32at T 440; s32at T 444;
      tb T 448; tb T 449; tb T 450; u32at T 452; u32at T 456;
      0; 0; 0; 0; tx + 432; tx; 0; 0; 0; tx + 144; 0; tx; 0 ].

Definition TXS : YP09.region := YP09.mkRegion (Some 10%nat) 432 460 432 460
  [ YP09.mkChunk 432 (CVal 4 (SOff 33 0)); YP09.mkChunk 436 (CVal 1 (SOff 34 0));
    YP09.mkChunk 437 (CVal 1 (SOff 35 0)); YP09.mkChunk 440 (CVal 4 (SOff 36 0));
    YP09.mkChunk 444 (CVal 4 (SOff 37 0)); YP09.mkChunk 448 (CVal 1 (SOff 38 0));
    YP09.mkChunk 449 (CVal 1 (SOff 39 0)); YP09.mkChunk 450 (CVal 1 (SOff 40 0));
    YP09.mkChunk 452 (CVal 4 (SOff 41 0)); YP09.mkChunk 456 (CVal 4 (SOff 42 0)) ].
Definition OUTC : YP09.region := YP09.mkRegion (Some 11%nat) 0 1 0 1 [].
Definition OUTP : YP09.region := YP09.mkRegion (Some 12%nat) 0 1 0 1 [].
Definition OUTV : YP09.region := YP09.mkRegion (Some 13%nat) 0 1 0 1 [].

Definition PTRN (al : Z) : afact := mkAF 4096 140737479966720 al.
(* A caller's byte: its shadow byte must lie in the shadow span, so below 2^47. *)
Definition OUTF : afact := mkAF 4096 (2 ^ 47 - 1) 0.

Definition nx_atoms : list (nat * afact) :=
  [ (2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (10%nat, PTRN 4); (11%nat, OUTF); (12%nat, OUTF); (13%nat, OUTF);
    (32%nat, mkAF SB_NX SB_NX 0);
    (33%nat, mkAF 0 1 0); (34%nat, mkAF 0 255 0); (35%nat, mkAF 0 255 0);
    (36%nat, mkAF 0 2147483647 0); (37%nat, mkAF 0 11 0); (38%nat, mkAF 0 1 0);
    (39%nat, mkAF 0 255 0); (40%nat, mkAF 0 255 0); (41%nat, mkAF 0 4294967295 0);
    (42%nat, mkAF 0 4294967295 0) ].

Definition nx_SH : list shent := [ mkSHE 10 0 460; mkSHE 11 0 1; mkSHE 12 0 1; mkSHE 13 0 1 ].

Definition nx_regs0 : list YP09.region :=
  [ stack_region NEXT_STK; got_regionP; bcell_regionP 32; TXS; OUTC; OUTP; OUTV ].

Definition ss_nx : sstate :=
  mkSS AF_reac_headamp_tx_next sr_atoms nx_regs0 None (mkFacts nx_atoms [] []).

Section h.
Variable B : asyms.

(* What the call keeps, stated against the memory at the call (cgif lib/YC20.v:311-323). *)
Definition tnext_kept (lyc : alayout) (Sc : astate) (W : world SEGS) (memc : word -> option byte)
  (W2 : world SEGS) (mem2 : word -> option byte) (sp : Z) (Ex : Z -> Prop) : Prop :=
  (forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (sp - NEXT_STK <= a < sp) -> ~ Ex a ->
     aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) memc a) /\
  (forall b m i, In (b, m) (ablocks B lyc Sc) -> 0 <= i < req_size m -> ~ Ex (b + i) ->
     aview SEGS (w_H W2) mem2 (b + i) = aview SEGS (w_H W) memc (b + i)) /\
  (forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) ->
     ~ (as_errno B <= a < as_errno B + 4) ->
     aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) memc a) /\
  (forall cid pos a, In (cid, pos) (frames Sc) ->
     (in_zr a (frame_rng lyc (cid, pos))
      \/ in_zr a (shadow_addr (frame_addr lyc cid pos), fs_frame_bytes cid / 8)) ->
     ~ Ex a -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) memc a) /\
  (forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (sp - NEXT_STK <= a < sp) ->
     apresent (w_H W) memc a -> apresent (w_H W2) mem2 a) /\
  (forall a, sp - NEXT_STK <= a < sp -> apresent (w_H W2) mem2 a).

Definition tnext_post (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate)
  (W0 : world SEGS) (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
  (lyc : alayout) (Sc : astate) (W : world SEGS) (memc : word -> option byte) (k : Z)
  (regs : bvmap 5 word) (tx chp parp valp : Z) (T : list byte)
  : world SEGS -> config -> Prop :=
  fun W2 c2 => exists regs2 mem2 md2,
    c2 = mkCfg (mkst regs2 (getr regs 1) mem2 (seg_rom SEGS)) md2 /\
    ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W2 mem2 md2 k /\
    aregs_preserved regs regs2 /\
    tnext_kept lyc Sc W memc W2 mem2 (spZ regs) (nx_touch tx chp parp valp) /\
    (* The three bytes carry the record only when the answer is 1: the harness sets
       them to 0xff before each call and reads them only then (fuzz_grant.c:397-416). *)
    match next_model T tx with
    | (r, (c, p, v), T') =>
        getr regs2 10 = w64 r /\
        obj_at SEGS (mrestrict (w_H W2) mem2) tx LAY_TX (tx_vals T') /\
        (r = 1 -> aview SEGS (w_H W2) mem2 chp = Some c
                  /\ aview SEGS (w_H W2) mem2 parp = Some p
                  /\ aview SEGS (w_H W2) mem2 valp = Some v)
    end.

(* The caller's right to write a byte it holds. *)
Definition nx_may_write (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate)
  (lyc : alayout) (Sc : astate) (own : list (Z * Z)) (a : Z) : Prop :=
  awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a.

(* Where one of the three bytes the caller holds must lie: clear of the table, of the
   call's own machine-stack window, of the image, and of the shadow. *)
Definition nx_out_ok (sp tx p : Z) : Prop :=
  4096 <= p /\ p + 1 <= 2 ^ 47 /\
  ~ (tx <= p < tx + TX_SIZE) /\
  (p + 1 <= sp - NEXT_STK \/ sp <= p) /\
  (p + 1 <= IMG_LO \/ IMG_TOP <= p) /\
  ~ (SHADOW_OFF <= p < SHADOW_OFF + 17592186044416).

Definition theadamp_tx_next_spec : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k
       (regs : bvmap 5 word) (tx chp parp valp : Z) (T : list byte) ch,
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) memc) ->
  YK0s.ret_ok (getr regs 1) -> 4096 <= raZ regs ->
  getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
  getr regs 10 = w64 tx -> getr regs 11 = w64 chp ->
  getr regs 12 = w64 parp -> getr regs 13 = w64 valp ->
  achain lyc (aview SEGS (w_H W) memc) (spZ regs) (s0Z regs) ch ->
  spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - NEXT_STK -> spZ regs <= sp0 ->
  (forall a, spZ regs - NEXT_STK <= a < spZ regs -> apresent (w_H W) memc a) ->
  (* the table the harness allocated *)
  In (tx, TX_SIZE) (ablocks B lyc Sc) ->
  length T = 460%nat -> I1 T ->
  obj_at SEGS (mrestrict (w_H W) memc) tx LAY_TX (tx_vals T) ->
  (forall a, tx <= a < tx + TX_SIZE -> nx_may_write STK sp0 FP ly S lyc Sc own a) ->
  (* the three bytes the caller holds, each marked usable for one byte *)
  nx_out_ok (spZ regs) tx chp -> nx_out_ok (spZ regs) tx parp -> nx_out_ok (spZ regs) tx valp ->
  chp <> parp -> chp <> valp -> parp <> valp ->
  nx_may_write STK sp0 FP ly S lyc Sc own chp ->
  nx_may_write STK sp0 FP ly S lyc Sc own parp ->
  nx_may_write STK sp0 FP ly S lyc Sc own valp ->
  apresent (w_H W) memc chp -> apresent (w_H W) memc parp -> apresent (w_H W) memc valp ->
  range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF chp 1 ->
  range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF parp 1 ->
  range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF valp 1 ->
  SRr SEGS W (cfg_at SEGS A_reac_headamp_tx_nextP regs memc mdc)
    (tnext_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs tx chp parp valp T).

Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_grant) (PI := PI).

(* The table's bytes, as the memory-checking runtime's view gives them. *)
Definition nx_bytes (m : word -> option byte) (tx : Z) (T : list byte) : Prop :=
  forall i, tx_fbyte i = true -> mbyte SEGS m (tx + i) = Some (nth (Z.to_nat i) T (Z_to_bv 8 0)).

Lemma nx_val1 : forall m tx T k,
  nx_bytes m tx T -> tx_fbyte k = true -> val_mem SEGS m (tx + k) 1 (tb T k).
Proof.
  intros m tx T k HB Hk j Hj. destruct j as [|j]; [|lia].
  pose proof (HeadampTxEffective.tb_range T k) as Hr.
  rewrite le_byte_small by (cbn; lia).
  change (Z.of_nat 0%nat) with 0. rewrite Z.mul_0_r, Z.shiftr_0_r, Z.add_0_r.
  rewrite Z_to_bv8_tb. exact (HB k Hk).
Qed.

Lemma nx_val4 : forall m tx T k,
  nx_bytes m tx T -> (forall d, 0 <= d < 4 -> tx_fbyte (k + d) = true) ->
  val_mem SEGS m (tx + k) 4 (u32at T k).
Proof.
  intros m tx T k HB Hk j Hj.
  pose proof (HeadampTxEffective.tb_range T k). pose proof (HeadampTxEffective.tb_range T (k + 1)).
  pose proof (HeadampTxEffective.tb_range T (k + 2)). pose proof (HeadampTxEffective.tb_range T (k + 3)).
  assert (Hu : 0 <= u32at T k < 2 ^ (8 * Z.of_nat 4)).
  { change (2 ^ (8 * Z.of_nat 4)) with 4294967296. unfold u32at. lia. }
  rewrite (le_byte_small (u32at T k) 4 j Hu Hj).
  replace (Z_to_bv 8 (Z.shiftr (u32at T k) (8 * Z.of_nat j)))
    with (Z_to_bv 8 (tb T (k + Z.of_nat j))).
  2:{ apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
      change (2 ^ Z.of_N 8) with 256. rewrite Z.shiftr_div_pow2 by lia.
      destruct j as [|[|[|[|j]]]]; try lia.
      - change (8 * Z.of_nat 0%nat) with 0. change (Z.of_nat 0%nat) with 0.
        rewrite Z.add_0_r, Z.pow_0_r, Z.div_1_r. unfold u32at. Z.div_mod_to_equations. lia.
      - change (8 * Z.of_nat 1%nat) with 8. change (Z.of_nat 1%nat) with 1.
        change (2 ^ 8) with 256. unfold u32at. Z.div_mod_to_equations. lia.
      - change (8 * Z.of_nat 2%nat) with 16. change (Z.of_nat 2%nat) with 2.
        change (2 ^ 16) with 65536. unfold u32at. Z.div_mod_to_equations. lia.
      - change (8 * Z.of_nat 3%nat) with 24. change (Z.of_nat 3%nat) with 3.
        change (2 ^ 24) with 16777216. unfold u32at. Z.div_mod_to_equations. lia. }
  rewrite Z_to_bv8_tb.
  replace (tx + k + Z.of_nat j) with (tx + (k + Z.of_nat j)) by lia.
  apply HB, Hk. lia.
Qed.

Lemma s32at_small : forall T k, 0 <= s32at T k -> 0 <= s32at T k < 2147483648.
Proof.
  intros T k H. split; [exact H|]. unfold s32at, u32at in *.
  pose proof (HeadampTxEffective.tb_range T k). pose proof (HeadampTxEffective.tb_range T (k + 1)).
  pose proof (HeadampTxEffective.tb_range T (k + 2)). pose proof (HeadampTxEffective.tb_range T (k + 3)).
  destruct (Z.ltb_spec (tb T k + 256 * tb T (k + 1) + 65536 * tb T (k + 2) + 16777216 * tb T (k + 3))
                       2147483648); lia.
Qed.

Lemma u32at_range : forall T k, 0 <= u32at T k < 4294967296.
Proof.
  intros T k. unfold u32at.
  pose proof (HeadampTxEffective.tb_range T k). pose proof (HeadampTxEffective.tb_range T (k + 1)).
  pose proof (HeadampTxEffective.tb_range T (k + 2)). pose proof (HeadampTxEffective.tb_range T (k + 3)).
  lia.
Qed.

Lemma s32at_u32at : forall T k, 0 <= s32at T k -> s32at T k = u32at T k.
Proof.
  intros T k H. pose proof (u32at_range T k) as Hr. unfold s32at in *. cbv zeta in *.
  destruct (Z.ltb_spec (u32at T k) 2147483648); [reflexivity | lia].
Qed.

Lemma nx_entry : forall lyc Sc (W : world SEGS) (regs : bvmap 5 word) memc mdc
    (tx chp parp valp : Z) (T : list byte),
  AR SEGS B lyc Sc W memc mdc ->
  getr regs 10 = w64 tx -> getr regs 11 = w64 chp ->
  getr regs 12 = w64 parp -> getr regs 13 = w64 valp ->
  spZ regs mod 16 = 0 -> 2 ^ 46 <= spZ regs <= 2 ^ 47 ->
  alloc_ceiling <= spZ regs - NEXT_STK ->
  (forall a, spZ regs - NEXT_STK <= a < spZ regs -> apresent (w_H W) memc a) ->
  In (tx, TX_SIZE) (ablocks B lyc Sc) ->
  length T = 460%nat -> I1 T ->
  obj_at SEGS (mrestrict (w_H W) memc) tx LAY_TX (tx_vals T) ->
  nx_out_ok (spZ regs) tx chp -> nx_out_ok (spZ regs) tx parp -> nx_out_ok (spZ regs) tx valp ->
  chp <> parp -> chp <> valp -> parp <> valp ->
  apresent (w_H W) memc chp -> apresent (w_H W) memc parp -> apresent (w_H W) memc valp ->
  range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF chp 1 ->
  range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF parp 1 ->
  range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF valp 1 ->
  st_ok_pi SEGS VAL (Eimg (Ereg regs (nx_extra tx T))) ss_nx
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_reac_headamp_tx_next)) memc (seg_rom SEGS)))
  /\ sh_ok SEGS BxN nx_SH (Eimg (Ereg regs (nx_extra tx T))) (mrestrict (w_H W) memc).
Proof.
  intros lyc Sc W regs memc mdc tx chp parp valp T HAR H10 H11 H12 H13 Hsp16 Hspr Hceil Hpres
    Hg HL HI Hobj Hoc Hop Hov Dcp Dcv Dpv Pc Pp Pv Rc Rp Rv.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  destruct (al_blocks _ _ LAWS lyc Sc W memc mdc tx TX_SIZE HAR Hg)
    as (Hg16 & Hg4096 & Hgceil & Hgh_ia & Hgpres & _).
  pose proof (proj1 Hgh_ia) as Hgh.
  pose proof (blk_off_imgP B lyc Sc W memc mdc tx TX_SIZE HAR Hg) as Hgh_img.
  change (req_size TX_SIZE) with 460 in Hgceil, Hgh_ia, Hgpres, Hgh_img.
  destruct (al_const _ _ LAWS lyc Sc W memc mdc HAR) as (Kcell & _ & Kgot & _).
  rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell.
  pose proof (pa_obj_img 32 ltac:(lia)) as HcellR.
  pose proof (pal_got_cell B TL) as HgcD.
  pose proof (pa_obj_img 1 ltac:(lia)) as HgotR.
  pose proof (proj1 (tx_obj_bytes SEGS _ _ _) Hobj) as HBY.
  destruct Hoc as (Hc0 & Hc1 & Hc2 & Hc3 & Hc4 & Hc5).
  destruct Hop as (Hp0 & Hp1 & Hp2 & Hp3 & Hp4 & Hp5).
  destruct Hov as (Hv0 & Hv1 & Hv2 & Hv3 & Hv4 & Hv5).
  pose proof HI as (P1 & P2 & P3 & (P4a & P4b) & P5 & P6 & (P7a & P7b & P7c & P7d) & P8).
  pose proof (s32at_small T 440 P7a) as R36.
  pose proof (u32at_range T 452) as R41. pose proof (u32at_range T 456) as R42.
  pose proof (HeadampTxEffective.tb_range T 436) as R34.
  pose proof (HeadampTxEffective.tb_range T 437) as R35.
  pose proof (HeadampTxEffective.tb_range T 449) as R39.
  pose proof (HeadampTxEffective.tb_range T 450) as R40.
  rewrite restrict_mkst_fx.
  set (E := Eimg (Ereg regs (nx_extra tx T))).
  assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs (nx_extra tx T)) n)
    by (intros n Hn; subst E; apply Eimg_low; exact Hn).
  assert (E2 : ew E 2 = getr regs 2)
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
  assert (E10 : ew E 10 = Z_to_bv 64 tx)
    by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
  assert (E11 : ew E 11 = Z_to_bv 64 chp)
    by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
  assert (E12 : ew E 12 = Z_to_bv 64 parp)
    by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 12 12%bv eq_refl); exact H12).
  assert (E13 : ew E 13 = Z_to_bv 64 valp)
    by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 13 13%bv eq_refl); exact H13).
  assert (E32 : ew E 32 = Z_to_bv 64 SB_NX)
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
  assert (E33 : ew E 33 = Z_to_bv 64 (u32at T 432))
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
  assert (E34 : ew E 34 = Z_to_bv 64 (tb T 436))
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
  assert (E35 : ew E 35 = Z_to_bv 64 (tb T 437))
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 3)).
  assert (E36 : ew E 36 = Z_to_bv 64 (s32at T 440))
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 4)).
  assert (E37 : ew E 37 = Z_to_bv 64 (s32at T 444))
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 5)).
  assert (E38 : ew E 38 = Z_to_bv 64 (tb T 448))
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 6)).
  assert (E39 : ew E 39 = Z_to_bv 64 (tb T 449))
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 7)).
  assert (E40 : ew E 40 = Z_to_bv 64 (tb T 450))
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 8)).
  assert (E41 : ew E 41 = Z_to_bv 64 (u32at T 452))
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 9)).
  assert (E42 : ew E 42 = Z_to_bv 64 (u32at T 456))
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 10)).
  assert (EO1 : ew E (A_OBJ 1) = Z_to_bv 64 (VAL (A_OBJ 1)))
    by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
  assert (EO32 : ew E (A_OBJ 32) = Z_to_bv 64 (VAL (A_OBJ 32)))
    by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
  assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
  assert (VB : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v).
  { intros n v Hn Hv. cbn [base_val]. rewrite Hn. apply unsigned_lit_small. exact Hv. }
  split.
  - unfold ss_nx. apply pa_entry_st_ok_full.
    + apply regs_ok_Eimg_Ereg.
    + vm_compute. reflexivity.
    + unfold nx_regs0, stack_region, got_regionP, bcell_regionP, TXS, OUTC, OUTP, OUTV.
      repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
      * cbn [base_val]. rewrite Usp. split; [unfold NEXT_STK; lia|]. split; [lia|].
        split; [|constructor]. intros o Ho. apply (apresent_writable SEGS). apply Hpres.
        unfold NEXT_STK in *. lia.
      * rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) EO1) by (pose proof (pa_val_range (A_OBJ 1)); lia).
        split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        constructor; [|constructor].
        apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 1)) 0 8 (SOff (A_OBJ 32) 0) (VAL (A_OBJ 32)));
          [cbn [sv_denot]; rewrite EO32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
          | pose proof (pa_val_range (A_OBJ 32)); zside | zside |].
        rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) memc _ _ Kgot).
      * rewrite (VB (A_OBJ 32) (VAL (A_OBJ 32)) EO32) by (pose proof (pa_val_range (A_OBJ 32)); lia).
        split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        constructor; [|constructor].
        apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 32)) 0 8 BxN SB_NX);
          [cbn [sv_denot BxN]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
          | unfold SB_NX; zside | zside |].
        rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) memc _ _ Kcell).
      * rewrite (VB 10%nat tx E10) by lia. split; [lia|]. split; [lia|].
        split; [intros o Ho; apply (apresent_writable SEGS); apply Hgpres; lia|].
        assert (E440 : s32at T 440 = u32at T 440) by (apply s32at_u32at; exact P7a).
        assert (E444 : s32at T 444 = u32at T 444) by (apply s32at_u32at; lia).
        pose proof (u32at_range T 432). pose proof (u32at_range T 440).
        pose proof (u32at_range T 444). pose proof (u32at_range T 452).
        pose proof (u32at_range T 456).
        pose proof (HeadampTxEffective.tb_range T 448) as R38.
        repeat apply Forall_cons; try apply Forall_nil.
        -- apply (chunk_ok_val SEGS E _ tx 432 4 _ (u32at T 432));
             [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
             | cbn; lia | cbn; lia
             | apply (nx_val4 (mrestrict (w_H W) memc) tx T 432 HBY);
               intros d Hd; assert (d = 0 \/ d = 1 \/ d = 2 \/ d = 3) as [-> | [-> | [-> | ->]]] by lia;
               vm_compute; reflexivity].
        -- apply (chunk_ok_val SEGS E _ tx 436 1 _ (tb T 436));
             [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
             | cbn; lia | cbn; lia
             | apply (nx_val1 (mrestrict (w_H W) memc) tx T 436 HBY); vm_compute; reflexivity].
        -- apply (chunk_ok_val SEGS E _ tx 437 1 _ (tb T 437));
             [cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
             | cbn; lia | cbn; lia
             | apply (nx_val1 (mrestrict (w_H W) memc) tx T 437 HBY); vm_compute; reflexivity].
        -- apply (chunk_ok_val SEGS E _ tx 440 4 _ (u32at T 440));
             [cbn [sv_denot]; rewrite E36, E440, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
             | cbn; lia | cbn; lia
             | apply (nx_val4 (mrestrict (w_H W) memc) tx T 440 HBY);
               intros d Hd; assert (d = 0 \/ d = 1 \/ d = 2 \/ d = 3) as [-> | [-> | [-> | ->]]] by lia;
               vm_compute; reflexivity].
        -- apply (chunk_ok_val SEGS E _ tx 444 4 _ (u32at T 444));
             [cbn [sv_denot]; rewrite E37, E444, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
             | cbn; lia | cbn; lia
             | apply (nx_val4 (mrestrict (w_H W) memc) tx T 444 HBY);
               intros d Hd; assert (d = 0 \/ d = 1 \/ d = 2 \/ d = 3) as [-> | [-> | [-> | ->]]] by lia;
               vm_compute; reflexivity].
        -- apply (chunk_ok_val SEGS E _ tx 448 1 _ (tb T 448));
             [cbn [sv_denot]; rewrite E38, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
             | cbn; lia | cbn; lia
             | apply (nx_val1 (mrestrict (w_H W) memc) tx T 448 HBY); vm_compute; reflexivity].
        -- apply (chunk_ok_val SEGS E _ tx 449 1 _ (tb T 449));
             [cbn [sv_denot]; rewrite E39, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
             | cbn; lia | cbn; lia
             | apply (nx_val1 (mrestrict (w_H W) memc) tx T 449 HBY); vm_compute; reflexivity].
        -- apply (chunk_ok_val SEGS E _ tx 450 1 _ (tb T 450));
             [cbn [sv_denot]; rewrite E40, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
             | cbn; lia | cbn; lia
             | apply (nx_val1 (mrestrict (w_H W) memc) tx T 450 HBY); vm_compute; reflexivity].
        -- apply (chunk_ok_val SEGS E _ tx 452 4 _ (u32at T 452));
             [cbn [sv_denot]; rewrite E41, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
             | cbn; lia | cbn; lia
             | apply (nx_val4 (mrestrict (w_H W) memc) tx T 452 HBY);
               intros d Hd; assert (d = 0 \/ d = 1 \/ d = 2 \/ d = 3) as [-> | [-> | [-> | ->]]] by lia;
               vm_compute; reflexivity].
        -- apply (chunk_ok_val SEGS E _ tx 456 4 _ (u32at T 456));
             [cbn [sv_denot]; rewrite E42, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
             | cbn; lia | cbn; lia
             | apply (nx_val4 (mrestrict (w_H W) memc) tx T 456 HBY);
               intros d Hd; assert (d = 0 \/ d = 1 \/ d = 2 \/ d = 3) as [-> | [-> | [-> | ->]]] by lia;
               vm_compute; reflexivity].
      * rewrite (VB 11%nat chp E11) by lia. split; [lia|]. split; [lia|].
        split; [|constructor]. intros o Ho.
        replace (chp + o) with chp by lia. apply (apresent_writable SEGS). exact Pc.
      * rewrite (VB 12%nat parp E12) by lia. split; [lia|]. split; [lia|].
        split; [|constructor]. intros o Ho.
        replace (parp + o) with parp by lia. apply (apresent_writable SEGS). exact Pp.
      * rewrite (VB 13%nat valp E13) by lia. split; [lia|]. split; [lia|].
        split; [|constructor]. intros o Ho.
        replace (valp + o) with valp by lia. apply (apresent_writable SEGS). exact Pv.
    + apply pairwise_disjoint_of_extents.
      unfold nx_regs0, stack_region, got_regionP, bcell_regionP, TXS, OUTC, OUTP, OUTV,
        extent_of_region.
      cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
      rewrite (VB 10%nat tx E10), (VB 11%nat chp E11), (VB 12%nat parp E12),
        (VB 13%nat valp E13) by lia.
      rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) EO1) by (pose proof (pa_val_range (A_OBJ 1)); lia).
      rewrite (VB (A_OBJ 32) (VAL (A_OBJ 32)) EO32) by (pose proof (pa_val_range (A_OBJ 32)); lia).
      cbn [base_val]. rewrite Usp.
      cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
      revert Hgceil Hgh Hgh_img Hg4096 Hg16 Hspr Hceil HgcD HcellR HgotR
        Hc0 Hc2 Hc3 Hc4 Hp0 Hp2 Hp3 Hp4 Hv0 Hv2 Hv3 Hv4 Dcp Dcv Dpv C1.
      clear. unfold off_img, TX_SIZE, NEXT_STK. intros. repeat split; lia.
    + split; [|split; [exact I | exact I]].
      cbn [nx_atoms f_atoms atoms_ok]. unfold afact_ok, PTRN, OUTF.
      cbn [af_lo af_hi af_al2].
      rewrite Usp, E10, E11, E12, E13, E32, E33, E34, E35, E36, E37, E38, E39, E40, E41, E42.
      pose proof (u32at_range T 432). pose proof (u32at_range T 452). pose proof (u32at_range T 456).
      pose proof (HeadampTxEffective.tb_range T 448) as R38.
      rewrite !unsigned_lit_small by (unfold SB_NX; lia).
      change (2 ^ 4) with 16. rewrite ?Z.pow_0_r, ?Z.mod_1_r.
      unfold TX_SIZE, NEXT_STK in *.
      repeat match goal with |- _ /\ _ => split end; try lia.
  - unfold sh_ok, nx_SH.
    assert (UBx : U E BxN = SHADOW_OFF).
    { unfold U, BxN. cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned.
      rewrite unsigned_lit_small by (unfold SB_NX; lia). reflexivity. }
    constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]].
    + apply (shent_ok_of_block SEGS B LAWS lyc Sc W memc mdc E BxN 10 tx TX_SIZE 0 460 HAR Hg).
      * exact UBx.
      * unfold U. cbn [sv_denot]. rewrite E10, Z.add_0_r, Z_to_bv_bv_unsigned.
        apply unsigned_lit_small. lia.
      * lia.
      * change (req_size TX_SIZE) with 460. lia.
    + apply (shent_ok_of_range SEGS (w_H W) memc E BxN 11 chp 1 chp 0 1 Rc UBx).
      * unfold U. cbn [sv_denot]. rewrite E11, Z.add_0_r, Z_to_bv_bv_unsigned.
        apply unsigned_lit_small. lia.
      * lia.
      * lia.
      * cbn [Z.min Z.max]. intros x Hx. replace x with chp by lia. exact Hc5.
    + apply (shent_ok_of_range SEGS (w_H W) memc E BxN 12 parp 1 parp 0 1 Rp UBx).
      * unfold U. cbn [sv_denot]. rewrite E12, Z.add_0_r, Z_to_bv_bv_unsigned.
        apply unsigned_lit_small. lia.
      * lia.
      * lia.
      * cbn [Z.min Z.max]. intros x Hx. replace x with parp by lia. exact Hp5.
    + apply (shent_ok_of_range SEGS (w_H W) memc E BxN 13 valp 1 valp 0 1 Rv UBx).
      * unfold U. cbn [sv_denot]. rewrite E13, Z.add_0_r, Z_to_bv_bv_unsigned.
        apply unsigned_lit_small. lia.
      * lia.
      * lia.
      * cbn [Z.min Z.max]. intros x Hx. replace x with valp by lia. exact Hv5.
Qed.

(* The regions the two scans add: the dirty byte the edge clears (atom 47, one byte,
   written), the value byte it reads (atom 48), and the replay scan's set and value bytes
   (atoms 52 and 54), which it only reads. *)
Definition DREG : YP09.region := YP09.mkRegion (Some 47%nat) 0 1 0 1 [YP09.mkChunk 0 (CVal 1 (SOff 49 0))].
Definition VREG : YP09.region := YP09.mkRegion (Some 48%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 50 0))].
Definition SREG : YP09.region := YP09.mkRegion (Some 52%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 53 0))].
Definition RVREG : YP09.region := YP09.mkRegion (Some 54%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 55 0))].
Definition nx_regs_all : list YP09.region := nx_regs0 ++ [DREG; VREG; SREG; RVREG].

(* The bytes this walk may write: its own machine-stack window, the table's ten scalar
   fields, the three bytes the caller holds, and the one array byte the edge clears. *)
Definition nx_touch2 (tx chp parp valp d a : Z) : Prop :=
  (tx + 432 <= a < tx + 460) \/ a = chp \/ a = parp \/ a = valp \/ a = d.

Lemma nx_wrange : forall (E : env) (rs : smem) (sp tx chp parp valp d a : Z),
  (forall r, In r rs -> In (skel r) (skeleton nx_regs_all)) ->
  bv_unsigned (ew E 2) = sp -> bv_unsigned (ew E 10) = tx ->
  bv_unsigned (ew E 11) = chp -> bv_unsigned (ew E 12) = parp ->
  bv_unsigned (ew E 13) = valp -> bv_unsigned (ew E 47) = d ->
  in_wrange E rs a -> (sp - NEXT_STK <= a < sp) \/ nx_touch2 tx chp parp valp d a.
Proof.
  intros E rs sp tx chp parp valp d a Hsk E2 E10 E11 E12 E13 E47 (r & Hin & Ha).
  pose proof (Hsk r Hin) as Hs.
  unfold nx_regs_all, nx_regs0, stack_region, got_regionP, bcell_regionP, TXS,
    OUTC, OUTP, OUTV, DREG, VREG, SREG, RVREG, skeleton in Hs.
  cbn [map app skel YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi] in Hs.
  unfold nx_touch2, NEXT_STK.
  destruct Hs as [Hs|[Hs|[Hs|[Hs|[Hs|[Hs|[Hs|[Hs|[Hs|[Hs|[Hs|Hs]]]]]]]]]]];
    try (exfalso; exact Hs);
    symmetry in Hs; unfold skel in Hs;
    injection Hs as H1 H2 H3 H4 H5;
    rewrite ?H1, ?H2, ?H3, ?H4, ?H5 in Ha; cbn [base_val] in Ha.
  - unfold NEXT_STK in Ha. rewrite E2 in Ha. left. lia.
  - lia.
  - lia.
  - rewrite E10 in Ha. right. left. lia.
  - rewrite E11 in Ha. right. right. left. lia.
  - rewrite E12 in Ha. right. right. right. left. lia.
  - rewrite E13 in Ha. right. right. right. right. left. lia.
  - rewrite E47 in Ha. right. right. right. right. right. lia.
  - lia.
  - lia.
  - lia.
Qed.

Lemma nx_awr : forall (E : env) STK sp0 FP ly S lyc Sc own (rs : smem)
    (sp tx chp parp valp d : Z),
  (forall r, In r rs -> In (skel r) (skeleton nx_regs_all)) ->
  bv_unsigned (ew E 2) = sp -> bv_unsigned (ew E 10) = tx ->
  bv_unsigned (ew E 11) = chp -> bv_unsigned (ew E 12) = parp ->
  bv_unsigned (ew E 13) = valp -> bv_unsigned (ew E 47) = d ->
  sp0 - STK <= sp - NEXT_STK -> sp <= sp0 -> tx <= d < tx + TX_SIZE ->
  (forall a, tx <= a < tx + TX_SIZE ->
     awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a) ->
  awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own chp ->
  awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own parp ->
  awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own valp ->
  awr_ok E rs STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own.
Proof.
  intros E STK sp0 FP ly S lyc Sc own rs sp tx chp parp valp d
    Hsk E2 E10 E11 E12 E13 E47 Hlo Hhi Hd Htab Hc Hp Hv a Hw.
  destruct (nx_wrange E rs sp tx chp parp valp d a Hsk E2 E10 E11 E12 E13 E47 Hw)
    as [Hst | [Htb | [-> | [-> | [-> | ->]]]]].
  - left. unfold NEXT_STK in *. lia.
  - apply Htab. unfold TX_SIZE in *. lia.
  - exact Hc.
  - exact Hp.
  - exact Hv.
  - apply Htab. exact Hd.
Qed.

(* What the walk has changed so far: nothing outside its own machine-stack window, the
   table's ten scalar fields, the three bytes and the one array byte of the edge. *)
Definition nx_same (W : world SEGS) (memc m : word -> option byte)
  (sp tx chp parp valp d : Z) : Prop :=
  forall x : word, ~ (sp - NEXT_STK <= bv_unsigned x < sp) ->
    ~ nx_touch2 tx chp parp valp d (bv_unsigned x) ->
    mrestrict (w_H W) m x = mrestrict (w_H W) memc x.

Lemma nx_same_refl : forall W memc sp tx chp parp valp d,
  nx_same W memc memc sp tx chp parp valp d.
Proof. intros. intros x _ _. reflexivity. Qed.

Lemma nx_same_step : forall (E : env) (rs : smem) W memc m1 m2 (sp tx chp parp valp d : Z),
  (forall r, In r rs -> In (skel r) (skeleton nx_regs_all)) ->
  bv_unsigned (ew E 2) = sp -> bv_unsigned (ew E 10) = tx ->
  bv_unsigned (ew E 11) = chp -> bv_unsigned (ew E 12) = parp ->
  bv_unsigned (ew E 13) = valp -> bv_unsigned (ew E 47) = d ->
  frame_of E rs (mrestrict (w_H W) m1) (mrestrict (w_H W) m2) ->
  nx_same W memc m1 sp tx chp parp valp d ->
  nx_same W memc m2 sp tx chp parp valp d.
Proof.
  intros E rs W memc m1 m2 sp tx chp parp valp d Hsk E2 E10 E11 E12 E13 E47 HF HS x Hst Htc.
  rewrite (HF x); [apply HS; assumption|].
  intros Hw. destruct (nx_wrange E rs sp tx chp parp valp d (bv_unsigned x)
    Hsk E2 E10 E11 E12 E13 E47 Hw) as [H|H]; [exact (Hst H) | exact (Htc H)].
Qed.

(* The facts about the call that hold at every slot of the walk. *)
Definition nx_ctx (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate)
    (lyc : alayout) (Sc : astate) (own : list (Z * Z)) (W : world SEGS)
    (memc : word -> option byte) (mdc : Model) (regs : bvmap 5 word)
    (tx chp parp valp : Z) (T : list byte) : Prop :=
  AR SEGS B lyc Sc W memc mdc /\
  In (tx, TX_SIZE) (ablocks B lyc Sc) /\
  nx_out_ok (spZ regs) tx chp /\ nx_out_ok (spZ regs) tx parp /\ nx_out_ok (spZ regs) tx valp /\
  chp <> parp /\ chp <> valp /\ parp <> valp /\
  apresent (w_H W) memc chp /\ apresent (w_H W) memc parp /\ apresent (w_H W) memc valp /\
  range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF chp 1 /\
  range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF parp 1 /\
  range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF valp 1 /\
  2 ^ 46 <= spZ regs <= 2 ^ 47 /\ alloc_ceiling <= spZ regs - NEXT_STK /\
  spZ regs mod 16 = 0 /\ sp0 - STK <= spZ regs - NEXT_STK /\ spZ regs <= sp0 /\
  (forall a, tx <= a < tx + TX_SIZE -> nx_may_write STK sp0 FP ly S lyc Sc own a) /\
  nx_may_write STK sp0 FP ly S lyc Sc own chp /\
  nx_may_write STK sp0 FP ly S lyc Sc own parp /\
  nx_may_write STK sp0 FP ly S lyc Sc own valp /\
  YK0s.ret_ok (getr regs 1) /\ 4096 <= raZ regs /\
  getr regs 3 = w64 (as_gp B) /\ getr regs 4 = w64 (as_tp B) /\
  getr regs 10 = w64 tx /\ getr regs 11 = w64 chp /\
  getr regs 12 = w64 parp /\ getr regs 13 = w64 valp /\
  length T = 460%nat /\ I1 T /\
  obj_at SEGS (mrestrict (w_H W) memc) tx LAY_TX (tx_vals T) /\
  (forall a, spZ regs - NEXT_STK <= a < spZ regs -> apresent (w_H W) memc a).

(* What the walk carries from one slot to the next: the caller's journal as it now
   stands, what the call has left untouched, and that its own stack window is present. *)
Definition nx_mid (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate)
    (W0 : world SEGS) (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
    (lyc : alayout) (Sc : astate) (W : world SEGS) (memc : word -> option byte) (k : Z)
    (regs : bvmap 5 word) (memj : word -> option byte) (mdj : Model)
    (tx chp parp valp d : Z) : Prop :=
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memj mdj k /\
  nx_same W memc memj (spZ regs) tx chp parp valp d /\
  (forall a, spZ regs - NEXT_STK <= a < spZ regs -> apresent (w_H W) memj a) /\
  (forall a, apresent (w_H W) memc a -> apresent (w_H W) memj a).

(* The ten callee-saved registers the prologue put on the machine stack: a cut in the
   middle of the function has clobbered the registers themselves, and the epilogue reads
   them back from these slots. *)
Definition nx_saved (W : world SEGS) (m : word -> option byte) (regs : bvmap 5 word)
    (sp : Z) : Prop :=
  val_mem SEGS (mrestrict (w_H W) m) (sp - 8) 8 (bv_unsigned (getr regs 1)) /\
  val_mem SEGS (mrestrict (w_H W) m) (sp - 16) 8 (bv_unsigned (getr regs 8)) /\
  val_mem SEGS (mrestrict (w_H W) m) (sp - 24) 8 (bv_unsigned (getr regs 9)) /\
  val_mem SEGS (mrestrict (w_H W) m) (sp - 32) 8 (bv_unsigned (getr regs 18)) /\
  val_mem SEGS (mrestrict (w_H W) m) (sp - 40) 8 (bv_unsigned (getr regs 19)) /\
  val_mem SEGS (mrestrict (w_H W) m) (sp - 48) 8 (bv_unsigned (getr regs 20)) /\
  val_mem SEGS (mrestrict (w_H W) m) (sp - 56) 8 (bv_unsigned (getr regs 21)) /\
  val_mem SEGS (mrestrict (w_H W) m) (sp - 64) 8 (bv_unsigned (getr regs 22)) /\
  val_mem SEGS (mrestrict (w_H W) m) (sp - 72) 8 (bv_unsigned (getr regs 23)) /\
  val_mem SEGS (mrestrict (w_H W) m) (sp - 80) 8 (bv_unsigned (getr regs 24)).

Lemma nx_same_aview : forall W memc m (sp tx chp parp valp d a : Z),
  nx_same W memc m sp tx chp parp valp d -> 0 <= a < 2 ^ 64 ->
  tx <= d < tx + TX_SIZE ->
  ~ (sp - NEXT_STK <= a < sp) -> ~ nx_touch tx chp parp valp a ->
  aview SEGS (w_H W) m a = aview SEGS (w_H W) memc a.
Proof.
  intros W memc m sp tx chp parp valp d a HS Ha Hd Hst Htc.
  assert (Hu : bv_unsigned (Z_to_bv 64 a) = a) by (apply unsigned_lit_small; exact Ha).
  assert (Htc2 : ~ nx_touch2 tx chp parp valp d a).
  { unfold nx_touch2. unfold nx_touch, TX_SIZE in Htc, Hd.
    intros [H|[H|[H|[H|H]]]]; apply Htc; unfold nx_touch, TX_SIZE; lia. }
  unfold aview, mbyte. rewrite (HS (Z_to_bv 64 a) ltac:(rewrite Hu; exact Hst)
    ltac:(rewrite Hu; exact Htc2)).
  reflexivity.
Qed.

(* Which case of Pau Aliagas's next_model the machine takes, from the branches the walk
   has settled. SlotNeeds_c's u32at and s32at are NextModel's u32 and s32. *)
Lemma u32at_u32 : forall T k, u32at T k = u32 T k. Proof. reflexivity. Qed.
Lemma s32at_s32 : forall T k, s32at T k = s32 T k. Proof. reflexivity. Qed.

Lemma fd_none : forall n T i0,
  (forall l, i0 <= l < i0 + Z.of_nat n -> tb T (288 + l) = 0) ->
  first_dirty_from T i0 n = None.
Proof.
  induction n as [|n IH]; intros T i0 H; [reflexivity|].
  cbn [first_dirty_from]. rewrite (proj2 (Z.eqb_eq _ 0) (H i0 ltac:(lia))).
  apply IH. intros l Hl. apply H. lia.
Qed.

Lemma fd_some : forall n T i0 i,
  i0 <= i < i0 + Z.of_nat n ->
  (forall l, i0 <= l < i -> tb T (288 + l) = 0) -> tb T (288 + i) <> 0 ->
  first_dirty_from T i0 n = Some i.
Proof.
  induction n as [|n IH]; intros T i0 i Hr Hz Hnz; [lia|].
  cbn [first_dirty_from].
  destruct (Z.eqb_spec (tb T (288 + i0)) 0) as [E|E].
  - apply (IH T (i0 + 1) i); [|intros l Hl; apply Hz; lia | exact Hnz].
    assert (i <> i0) by (intros Heq; rewrite Heq in Hnz; exact (Hnz E)). lia.
  - assert (i = i0) as ->; [|reflexivity].
    destruct (Z.eq_dec i i0) as [Heq|Hne]; [exact Heq|].
    exfalso. apply E. apply Hz. lia.
Qed.

Lemma nx_model_silent : forall T t,
  u32at T 432 = 0 -> tb T 437 = 0 -> next_model T t = silent T.
Proof.
  intros T t H1 H2. rewrite u32at_u32 in H1. unfold next_model.
  rewrite (proj2 (Z.eqb_eq _ 0) H1), (proj2 (Z.eqb_eq _ 0) H2). reflexivity.
Qed.

Lemma nx_model_edge : forall T t i,
  ~ (u32at T 432 = 0 /\ tb T 437 = 0) -> 0 <= i < 144 ->
  (forall l, 0 <= l < i -> tb T (288 + l) = 0) -> tb T (288 + i) <> 0 ->
  next_model T t = edge_res T i.
Proof.
  intros T t i Hact Hi Hz Hnz. rewrite u32at_u32 in Hact. unfold next_model.
  replace ((u32 T 432 =? 0) && (tb T 437 =? 0))%bool with false.
  2:{ symmetry. apply andb_false_iff.
      destruct (Z.eqb_spec (u32 T 432) 0) as [E1|E1]; [|left; reflexivity].
      destruct (Z.eqb_spec (tb T 437) 0) as [E2|E2]; [exfalso; exact (Hact (conj E1 E2))
        | right; reflexivity]. }
  rewrite (fd_some 144%nat T 0 i ltac:(cbn; lia) Hz Hnz). reflexivity.
Qed.

Lemma nx_model_after : forall T t,
  ~ (u32at T 432 = 0 /\ tb T 437 = 0) ->
  (forall l, 0 <= l < 144 -> tb T (288 + l) = 0) ->
  next_model T t = after_scan T t.
Proof.
  intros T t Hact Hz. rewrite u32at_u32 in Hact. unfold next_model.
  replace ((u32 T 432 =? 0) && (tb T 437 =? 0))%bool with false.
  2:{ symmetry. apply andb_false_iff.
      destruct (Z.eqb_spec (u32 T 432) 0) as [E1|E1]; [|left; reflexivity].
      destruct (Z.eqb_spec (tb T 437) 0) as [E2|E2]; [exfalso; exact (Hact (conj E1 E2))
        | right; reflexivity]. }
  rewrite (fd_none 144%nat T 0); [reflexivity|]. intros l Hl. apply Hz. cbn in Hl. lia.
Qed.

Lemma nx_after_w0 : forall T t, tb T 437 = 0 -> after_scan T t = resweep T.
Proof.
  intros T t H. unfold after_scan. rewrite (proj2 (Z.eqb_eq _ 0) H). reflexivity.
Qed.

Lemma nx_after_wait : forall T t, tb T 437 <> 0 -> 0 < s32at T 444 ->
  after_scan T t = silent (set4 T 444 (s32 T 444 - 1)).
Proof.
  intros T t H1 H2. rewrite s32at_s32 in H2. unfold after_scan.
  rewrite (proj2 (Z.eqb_neq _ 0) H1), (proj2 (Z.ltb_lt 0 _) H2). reflexivity.
Qed.

Lemma nx_after_done : forall T t, tb T 437 <> 0 -> s32at T 444 <= 0 ->
  3 * tb T 437 <= s32at T 440 -> after_scan T t = resweep (setb T 437 0).
Proof.
  intros T t H1 H2 H3. rewrite s32at_s32 in H2, H3. unfold after_scan.
  rewrite (proj2 (Z.eqb_neq _ 0) H1), (proj2 (Z.ltb_ge 0 _) H2),
    (proj2 (Z.leb_le _ _) H3). reflexivity.
Qed.

Lemma nx_after_walk : forall T t, tb T 437 <> 0 -> s32at T 444 <= 0 ->
  s32at T 440 < 3 * tb T 437 ->
  after_scan T t =
    walk T t (tb T 436) (tb T 448) (3 * tb T 437) (s32 T 440)
      (Z.to_nat (3 * tb T 437 - s32 T 440)).
Proof.
  intros T t H1 H2 H3. rewrite s32at_s32 in H2, H3. unfold after_scan.
  rewrite (proj2 (Z.eqb_neq _ 0) H1), (proj2 (Z.ltb_ge 0 _) H2),
    (proj2 (Z.leb_gt _ _) H3). reflexivity.
Qed.

(* Every return site of the walk ends the same way: the caller's journal, the registers it
   kept, what the call left untouched, and the table and the three bytes as the model
   gives them. *)
Lemma nx_finish : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world SEGS) memc mdc k
    (regs regs2 : bvmap 5 word) mem2 md2 (tx chp parp valp d : Z) (T T' : list byte) (r c p v : Z),
  tx <= d < tx + TX_SIZE ->
  AR SEGS B lyc Sc W memc mdc ->
  In (tx, TX_SIZE) (ablocks B lyc Sc) ->
  nx_out_ok (spZ regs) tx chp -> nx_out_ok (spZ regs) tx parp -> nx_out_ok (spZ regs) tx valp ->
  2 ^ 46 <= spZ regs <= 2 ^ 47 -> alloc_ceiling <= spZ regs - NEXT_STK ->
  next_model T tx = (r, (c, p, v), T') ->
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem2 md2 k ->
  aregs_preserved regs regs2 ->
  nx_same W memc mem2 (spZ regs) tx chp parp valp d ->
  (forall a, spZ regs - NEXT_STK <= a < spZ regs -> apresent (w_H W) mem2 a) ->
  (forall a, apresent (w_H W) memc a -> apresent (w_H W) mem2 a) ->
  getr regs2 10 = w64 r ->
  obj_at SEGS (mrestrict (w_H W) mem2) tx LAY_TX (tx_vals T') ->
  (r = 1 -> aview SEGS (w_H W) mem2 chp = Some c
            /\ aview SEGS (w_H W) mem2 parp = Some p
            /\ aview SEGS (w_H W) mem2 valp = Some v) ->
  tnext_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs tx chp parp valp T
    W (mkCfg (mkst regs2 (getr regs 1) mem2 (seg_rom SEGS)) md2).
Proof.
  intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs regs2 mem2 md2
    tx chp parp valp d T T' r c p v Hd HAR Hg Hoc Hop Hov Hspr Hac Hmodel HJ2 HP HSAME
    HpresS HpresK H10 Hobj Hr1.
  destruct Hoc as (Hc0 & Hc1 & Hc2 & Hc3 & Hc4 & Hc5).
  destruct Hop as (Hp0 & Hp1 & Hp2 & Hp3 & Hp4 & Hp5).
  destruct Hov as (Hv0 & Hv1 & Hv2 & Hv3 & Hv4 & Hv5).
  pose proof (blk_off_imgP B lyc Sc W memc mdc tx TX_SIZE HAR Hg) as Hgimg.
  change (req_size TX_SIZE) with 460 in Hgimg. unfold off_img in Hgimg.
  unfold TX_SIZE in Hc2, Hp2, Hv2.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  unfold tnext_post. exists regs2, mem2, md2.
  split; [reflexivity|]. split; [exact HJ2|]. split; [exact HP|].
  split.
  { unfold tnext_kept. split; [|split; [|split; [|split; [|split]]]].
    - intros a Ha Hst Htc. apply (nx_same_aview W memc mem2 (spZ regs) tx chp parp valp d a);
        [exact HSAME | lia | exact Hd | exact Hst | exact Htc].
    - intros b m i Hb Hi Htc.
      destruct (al_blocks _ _ LAWS lyc Sc W memc mdc b m HAR Hb) as (_ & Hb4096 & Hbceil & _ & _ & _).
      apply (nx_same_aview W memc mem2 (spZ regs) tx chp parp valp d (b + i));
        [exact HSAME | lia | exact Hd | unfold NEXT_STK in *; lia | exact Htc].
    - intros a Hi Ho He.
      pose proof (pa_img_range a Hi) as Hir.
      apply (nx_same_aview W memc mem2 (spZ regs) tx chp parp valp d a);
        [exact HSAME | lia | exact Hd | unfold NEXT_STK in *; lia |].
      unfold nx_touch, TX_SIZE. intros [Hx | [Hx | [Hx | Hx]]]; lia.
    - intros cid pos a Hf Hzr Htc.
      destruct (frames_bounds SEGS B LAWS lyc Sc W memc mdc cid pos HAR Hf) as (Hf0 & Hfc & Hfa).
      pose proof (fs_frame_bytes_nonneg cid) as Hfb.
      apply (nx_same_aview W memc mem2 (spZ regs) tx chp parp valp d a);
        [exact HSAME | | exact Hd | | exact Htc].
      + destruct Hzr as [Hzr | Hzr]; unfold in_zr, frame_rng, shadow_addr, SHADOW_OFF in Hzr;
          cbn [fst snd] in Hzr; [lia|]. pose proof (Z.div_le_mono 0 (fs_frame_bytes cid) 8). lia.
      + destruct Hzr as [Hzr | Hzr]; unfold in_zr, frame_rng, shadow_addr, SHADOW_OFF in Hzr;
          cbn [fst snd] in Hzr; unfold NEXT_STK in *; [lia|].
        pose proof (Z.div_le_mono 0 (fs_frame_bytes cid) 8).
        assert (fs_frame_bytes cid / 8 <= fs_frame_bytes cid) by (apply Z.div_le_upper_bound; lia).
        lia.
    - intros a Ha Hst Hp. apply HpresK. exact Hp.
    - exact HpresS. }
  rewrite Hmodel.
  split; [exact H10|]. split; [exact Hobj | exact Hr1].
Qed.

End h.
End f.
End d.
