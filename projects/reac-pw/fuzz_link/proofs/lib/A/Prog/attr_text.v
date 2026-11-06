(* attr_text (fuzz_link.c:168-172) on image A (fuzz_link.asan 0x86b18, 820 bytes; listing
   (internal path) (internal record, sha256 03340ee12716)): the walk of
   lib/A/Prog/attr_text_c.v `attr_text_acontract`, top lemma `attr_text_aproof`. This file holds the ENTRY phase (+0x00
   .. the join +0xec) and the top lemma; the shared machinery and the epilogue are lib/A/Prog/attr_text_base.v, the
   phases lib/A/Prog/attr_text_p1.v (+0xec .. +0x170), attr_text_p2.v (+0x170 .. +0x1d4), attr_text_p3.v
   (+0x1d4 .. +0x244).

   The entry phase: +0x00..+0x20 push the 64-byte frame and save ra, s0..s6; +0x24..+0x44 s3 := bare, s2 := s,
   s4 := type, s1 := w, s6 := the shadow base (loaded through the .got cell 0xa19d0 -> 0xaa438, which AR's const
   law fixes), s0 := w + 4096; +0x48..+0x4c wrapper_strlen(s) (LinkWalkStrS.aj_gx_strlen_atS over ASTRLEN: its
   string, read and tail premises are the Pre's string, NUL and slack, which the prologue did not write, and its
   read-only view is the Pre's arodata_okP); then, on the struct (a region at atom 10 = w, with its shadow
   entry), +0x50..+0x5c the check C1 of n, +0x60..+0x78 len := strlen(s) + (bare = 0), a1 := 2 ^ 64 - 4095, and
   the room test +0x7c `bltu 2 ^ 64 - 4098, n - 4095`:
   - no room: +0x80..+0x9c check C2 of full, full := 1, the join +0xec;
   - room: through the alias (w + n, SOff 35 0) the checks C3 and the two bytes of len + 4 into b at w + n
     (+0xa0..+0xd4), C1, n := n + 2 (+0xd8..+0xe8), the join +0xec.
   At +0xec the invariant is attr_text_p1.v's `at_inv1` (a1 = 2 ^ 64 - 4095 pinned).

   Section hypotheses (callee contracts and the image, each proved elsewhere):
   - LAWS : AR_laws pa_segs B (the lib/A frame; at the image lib/A/PcapBFacts.v at PcapB);
   - LV : LinkVals and TL : PALib B (lib/A/Prog/LinkWalk.v, LinkPaLib.v; by computation at the certified link
     instance);
   - ASTRLEN : RtString.astrlen_realizes pa_segs B (pa_sigma LS___interceptor_trampoline_strlen) (0x43044),
     discharged by lib/A/Rt/RtClosed.v cmd_strlen_closed;
   - AMEMCPY : aintrin_realizes pa_segs B OCpy (pa_sigma LS___asan_memcpy) (0x52d78), discharged by
     lib/A/AE2q.v asan_memcpy_realizes;
   - AMEMSET : aintrin_realizes pa_segs B OSet (pa_sigma LS___asan_memset) (0x53214), discharged by
     lib/A/AE2r.v asan_memset_realizes.
   The top lemma is generic in the sink head SK and stated at the relro window PCAP_RLO / PCAP_RHI; every phase
   holds at any window.

   Released proofs (rule 24): none of attr_text (lookups/walk-lookups.md (internal record, sha256 98fff7967d93),
   disposition none: written new; confirmed by the rule-24 walk check at 14:56Z).
   Proves function attr_text (image A, the asan build). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import PcapImgEnd.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YImgTop.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YN3v YI04 YI16 YG0s YA0d YA0j.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC5d YC20 YK0e.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import YC85G.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkSyms LinkList LinkAddr LinkPa LinkPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import YC4b.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PcapRelro.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Rt Require RtString.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import
link_aaddr link_amem link_ajkit LinkWalk LinkWalkLeaf LinkWalkNlw LinkWalkSide LinkWalkStrS attr_text_c
attr_text_base attr_text_p3 attr_text_p2 attr_text_p1.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

(* the frame region after the prologue: the eight saved words at their offsets below the entry sp *)
Definition at_fr0 : YP09.region := YP09.mkRegion (Some 2%nat) (-64) 0 (-64) 0
  [YP09.mkChunk (-64) (CVal 8 (SOff 22 0)); YP09.mkChunk (-56) (CVal 8 (SOff 21 0));
   YP09.mkChunk (-48) (CVal 8 (SOff 20 0)); YP09.mkChunk (-40) (CVal 8 (SOff 19 0));
   YP09.mkChunk (-32) (CVal 8 (SOff 18 0)); YP09.mkChunk (-24) (CVal 8 (SOff 9 0));
   YP09.mkChunk (-16) (CVal 8 (SOff 8 0)); YP09.mkChunk (-8) (CVal 8 (SOff 1 0))].
(* the entry state: the frame to push, the .got cell of the shadow base and the base's cell *)
Definition at_facts0 : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0)] [] [].
Definition at_ss0 : sstate := mkSS AF_attr_text sr_atoms [stack_region 64; got_regionP; bcell_regionP 32] None at_facts0.
(* the struct's fields at the entry, w = atom 10 *)
Definition at_flE : YP09.region :=
  YP09.mkRegion (Some 10%nat) 4096 4112 4096 4112
    [YP09.mkChunk 4096 (CVal 8 (SOff 33 0)); YP09.mkChunk 4104 (CVal 4 (SOff 34 0))].

Lemma at_nth_some : forall (l : list byte) i d, (i < length l)%nat -> nth_error l i = Some (nth i l d).
Proof. induction l as [|x l IH]; intros [|i] d H; cbn in *; try lia; [reflexivity | apply IH; lia]. Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.

Section b.
Context {PI : PAImg link_listing}.
Variable B : asyms.
Hypothesis LAWS : AR_laws pa_segs B.
Hypothesis LV : LinkVals.
Hypothesis TL : PALib B.
Hypothesis ASTRLEN : RtString.astrlen_realizes pa_segs B (pa_sigma LS___interceptor_trampoline_strlen).
Hypothesis AMEMCPY : aintrin_realizes pa_segs B OCpy (pa_sigma LS___asan_memcpy).
Hypothesis AMEMSET : aintrin_realizes pa_segs B OSet (pa_sigma LS___asan_memset).
#[local] Notation SEGS := (pa_segs).
#[local] Notation BASE := (pa_val A_TEXT).
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).

Section c.
Variables rlo rhi : Z.

(* the window of the journal is present at every memory the journal reaches *)
Lemma at_win : forall G XO OUT STK sp0 FP ly S W0 mem0 md0 own ly' S' W' mem' md' k,
  ajournal_gx SEGS B G XO OUT STK sp0 FP ly S W0 mem0 md0 own ly' S' W' mem' md' k ->
  forall x, sp0 - STK <= x < sp0 -> apresent (w_H W') mem' x.
Proof.
  intros G XO OUT STK sp0 FP ly S W0 mem0 md0 own ly' S' W' mem' md' k (_ & HXO & (memS & HJi & _) & _) x Hx.
  pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _). apply Hpres. lia.
Qed.

(* a register whose symbolic value is an atom holds the atom's value *)
Lemma at_reg_atom_ok : forall E ss (H : word -> bool) msc (r : bv 5) (j : nat) x,
  st_ok SEGS E ss (restrict H msc) -> sr_get (ss_regs ss) r = SOff j 0 -> ew E j = x -> getr (ms_regs msc) r = x.
Proof.
  intros E ss H msc r j x HS Hr Hj. rewrite (st_ok_restrict_reg SEGS H E ss msc r HS), Hr.
  cbn [sv_denot]. rewrite Z.add_0_r, Hj. apply Z_to_bv_bv_unsigned.
Qed.

Lemma at_reg_atom_pi : forall E ss (H : word -> bool) msc (r : bv 5) (j : nat) x,
  st_ok_pi SEGS pa_val E ss (restrict H msc) -> sr_get (ss_regs ss) r = SOff j 0 -> ew E j = x ->
  getr (ms_regs msc) r = x.
Proof.
  intros E ss H msc r j x HS Hr Hj. rewrite (st_ok_pi_restrict_reg H E ss msc r HS), Hr.
  cbn [sv_denot]. rewrite Z.add_0_r, Hj. apply Z_to_bv_bv_unsigned.
Qed.

(* the kept clause at the call *)
Lemma at_kept_init : forall cx, at_base SK B rlo rhi cx -> at_kept cx (c_memc cx).
Proof.
  intros cx HB. destruct HB as (HPRE & _). destruct HPRE as (HJ0 & _ & _ & _ & _ & _ & _ & _ & Hwlo & Hwhi & _).
  split; [|split].
  - intros a _ _ _. reflexivity.
  - intros a Ha. exact Ha.
  - intros a Ha. apply (at_win _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ0). unfold c_sp in Ha. lia.
Qed.

(* the prologue writes the frame only *)
Lemma at_kept_frame_run : forall cx m1 m2,
  at_kept cx m1 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (c_sp cx - 64 <= a < c_sp cx) ->
     aview SEGS (w_H (c_W cx)) m2 a = aview SEGS (w_H (c_W cx)) m1 a) ->
  mem_grows (rdW (c_W cx) m1) (rdW (c_W cx) m2) ->
  at_kept cx m2.
Proof.
  intros cx m1 m2 (K1 & K2 & K3) UN HG. assert (HAK : ATTR_TEXT_AK = 4160) by reflexivity.
  split; [|split].
  - intros a Ha Hw He. rewrite (UN a Ha ltac:(rewrite HAK in Hw; lia)). exact (K1 a Ha Hw He).
  - intros a Ha. exact (at_apres_grows _ _ _ a HG (K2 a Ha)).
  - intros a Ha. exact (at_apres_grows _ _ _ a HG (K3 a Ha)).
Qed.

(* a run that writes the frame and the struct only *)
Lemma at_kept_run2 : forall cx m1 m2 (Zs : Z -> Prop),
  at_kept cx m1 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ Zs a -> aview SEGS (w_H (c_W cx)) m2 a = aview SEGS (w_H (c_W cx)) m1 a) ->
  (forall a, Zs a -> (c_sp cx - 64 <= a < c_sp cx) \/ (c_w cx <= a < c_w cx + NW_SIZE)) ->
  mem_grows (rdW (c_W cx) m1) (rdW (c_W cx) m2) ->
  at_kept cx m2.
Proof.
  intros cx m1 m2 Zs (K1 & K2 & K3) UN HZ HG. assert (HAK : ATTR_TEXT_AK = 4160) by reflexivity.
  split; [|split].
  - intros a Ha Hw He. rewrite (UN a Ha); [exact (K1 a Ha Hw He)|].
    intros Hz. destruct (HZ a Hz) as [Hf | Hs]; [rewrite HAK in Hw; lia | exact (He (at_E_in cx a Hs))].
  - intros a Ha. exact (at_apres_grows _ _ _ a HG (K2 a Ha)).
  - intros a Ha. exact (at_apres_grows _ _ _ a HG (K3 a Ha)).
Qed.

(* the strlen wrapper's string, read and tail premises, and its read-only view *)
Lemma at_astr_at : forall cx m3, at_base SK B rlo rhi cx -> at_kept cx m3 ->
  astr_at SEGS (c_W cx) m3 (c_s cx) (c_str cx).
Proof.
  intros cx m3 HB HK. pose proof HB as HB0.
  destruct HB as (_ & _ & _ & _ & _ & HSTR & _). destruct HSTR as ((_ & _ & Hb) & Hnz).
  split; [|exact Hnz].
  intros i Hi. rewrite length_app in Hi. cbn [length] in Hi.
  rewrite (at_str_kept SK B rlo rhi cx m3 _ HB0 HK) by (unfold c_slen; pose proof (at_s_range cx); lia).
  unfold aview. unfold c_mem in Hb.
  rewrite (Hb i ltac:(rewrite length_app; cbn [length]; lia)).
  rewrite (at_nth_some _ i (Z_to_bv 8 0)) by (rewrite length_app; cbn [length]; lia). reflexivity.
Qed.

Lemma at_aread_ok : forall cx m3 (regsT : bvmap 5 word),
  at_base SK B rlo rhi cx -> at_kept cx m3 -> spZ regsT = c_sp cx - 64 ->
  aread_ok SEGS ESTACK (c_W cx) regsT m3 (c_s cx) (astr_len (c_str cx) + 1).
Proof.
  intros cx m3 regsT HB HK Hsp. pose proof HB as HB0.
  destruct HB as (HPRE & _ & _ & _ & _ & _ & HSLEN & _ & _ & _ & HAPF2 & _ & _ & _ & HMR2 & HRA2 & HHV2).
  pose proof (at_s_range cx) as Rs.
  assert (HAK : ATTR_TEXT_AK = 4160) by reflexivity.
  assert (Hsmr : c_s cx + c_slen cx + 1 <= 2 ^ 47)
    by (unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in *; lia).
  unfold aread_ok, astr_len. fold (c_slen cx).
  split; [lia|]. split; [lia|]. split; [unfold c_slen in *; lia|]. split.
  - intros a Ha. split.
    + rewrite (at_str_kept SK B rlo rhi cx m3 a HB0 HK ltac:(lia)). exact (at_str_vis SK B rlo rhi cx a HB0 ltac:(lia)).
    + unfold ascratch_stk. rewrite Hsp. unfold apart_frame, c_sp, ESTACK in *. rewrite HAK in HAPF2. lia.
  - split; [exact HMR2|]. split.
    + exact (at_ra_keep2 SK B rlo rhi cx m3 (c_s cx) (c_slen cx + 1) HB0 HK HMR2 (proj1 Rs) HRA2).
    + intros Hpos. exact (at_hull_keep SK B rlo rhi cx m3 (c_s cx) (c_slen cx + 1) HB0 HK HMR2 (proj1 Rs) Hpos HHV2).
Qed.

Lemma at_tail_vis : forall cx m3, at_base SK B rlo rhi cx ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (c_sp cx - 64 <= a < c_sp cx) ->
     aview SEGS (w_H (c_W cx)) m3 a = aview SEGS (w_H (c_W cx)) (c_memc cx) a) ->
  atail_vis SEGS (c_W cx) m3 (c_s cx + astr_len (c_str cx)).
Proof.
  intros cx m3 HB UN. pose proof HB as HB0.
  destruct HB as (_ & _ & _ & _ & _ & _ & _ & HSLACK & _ & _ & HAPF2 & _ & _ & _ & HMR2 & _).
  destruct HSLACK as (slack & (Hs0 & Hsl & Hb) & Hlen).
  pose proof (at_s_range cx) as Rs.
  assert (HAK : ATTR_TEXT_AK = 4160) by reflexivity.
  assert (Hsmr : c_s cx + c_slen cx + 1 <= 2 ^ 47)
    by (unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in *; lia).
  assert (Hsl0 : 0 <= c_slen cx) by (unfold c_slen; lia).
  unfold atail_vis, astr_len. fold (c_slen cx). intros a Ha.
  assert (Hi : a - (c_s cx + c_slen cx + 1) < Z.of_nat (length slack)) by lia.
  rewrite UN.
  - unfold aview. unfold c_mem in Hb.
    replace a with (c_s cx + c_slen cx + 1 + Z.of_nat (Z.to_nat (a - (c_s cx + c_slen cx + 1)))) by lia.
    rewrite (Hb (Z.to_nat (a - (c_s cx + c_slen cx + 1))) ltac:(lia)).
    destruct (nth_error slack (Z.to_nat (a - (c_s cx + c_slen cx + 1)))) eqn:Eb; [discriminate|].
    apply nth_error_None in Eb. lia.
  - lia.
  - unfold apart_frame, c_sp in *. rewrite HAK in HAPF2. lia.
Qed.

Lemma at_rom_kept : forall cx m3, at_base SK B rlo rhi cx ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (c_sp cx - 64 <= a < c_sp cx) ->
     aview SEGS (w_H (c_W cx)) m3 a = aview SEGS (w_H (c_W cx)) (c_memc cx) a) ->
  rt_rom_view SEGS B (c_W cx) m3.
Proof.
  intros cx m3 HB UN a Hrom Hno Herr.
  destruct HB as (HPRE & _). destruct HPRE as (HJ0 & _ & HROD & _ & _ & _ & _ & _ & Hwlo & _).
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  assert (Hceil : alloc_ceiling <= c_sp0 cx - c_STK cx) by (eapply (aj_stk_ceiling SK SEGS B); exact HJ0).
  assert (HAK : ATTR_TEXT_AK = 4160) by reflexivity.
  assert (Hi : in_img SEGS a) by (destruct Hrom as (sg & Hin & _ & Hr); exists sg; split; [exact Hin | exact Hr]).
  pose proof (pa_segs_low a Hi) as Hlow.
  rewrite UN by (unfold c_sp in *; unfold kLowMemEnd, SHADOW_OFF in *; lia).
  exact (HROD a (or_introl Hrom) Hno Herr).
Qed.

(* the fields of the struct at a later memory, from the Pre's struct *)
Lemma at_fields_entry : forall cx mX n f,
  at_base SK B rlo rhi cx ->
  (forall a, apresent (w_H (c_W cx)) (c_memc cx) a -> apresent (w_H (c_W cx)) mX a) ->
  val_mem SEGS (rdW (c_W cx) mX) (c_w cx + NW_N) 8 n ->
  val_mem SEGS (rdW (c_W cx) mX) (c_w cx + NW_FULL) 4 f ->
  0 <= n <= NL_CHUNK_MAX -> 0 <= f <= 1 ->
  nlw_fields SEGS (rdW (c_W cx) mX) (c_w cx) n f.
Proof.
  intros cx mX n f HB PG HVN HVF Hn Hf.
  destruct HB as (_ & _ & HNLW & HWF & _).
  destruct (fields_of_anlw SEGS (c_mem cx) (c_w cx) (c_bs cx) HNLW HWF) as (_ & _ & _ & _ & Hw0 & Hwl & HP).
  split; [exact Hw0|]. split; [exact Hwl|].
  split; [|split; [exact HVN | split; [exact HVF | split; [exact Hn | exact Hf]]]].
  intros i Hi. destruct (HP i Hi) as ((b & Hb) & Hw). split.
  - exact (lw_mbyte_some_kept SEGS (w_H (c_W cx)) (c_memc cx) mX _ b PG Hb).
  - exact (writable_kept (segs := SEGS) (w_H (c_W cx)) (c_memc cx) mX _ (PG _) Hw).
Qed.

(* the saved words, from the frame region of the engine's state *)
Lemma at_saved_of_ss : forall cx E ss msc i,
  st_ok_pi SEGS pa_val E ss (restrict (w_H (c_W cx)) msc) ->
  nth_error (ss_mem ss) i = Some at_fr0 ->
  bv_unsigned (ew E 2%nat) = c_sp cx ->
  (forall (j : nat) (r : bv 5), (j < 32)%nat -> Z.of_nat j = bv_unsigned r -> ew E j = getr (c_regs cx) r) ->
  at_saved cx (ms_mem msc).
Proof.
  intros cx E ss msc i HS Hi Hsp ER.
  assert (V : forall (j : nat) (r : bv 5) od, (j < 32)%nat -> Z.of_nat j = bv_unsigned r ->
    In (YP09.mkChunk od (CVal 8 (SOff j 0))) (YP09.r_chunks at_fr0) ->
    val_mem SEGS (rdW (c_W cx) (ms_mem msc)) (c_sp cx + od) 8 (bv_unsigned (getr (c_regs cx) r))).
  { intros j r od Hj Hr Hin.
    exact (at_val_of_ss E ss (w_H (c_W cx)) msc i 2 (c_sp cx) (-64) 0 (-64) 0 _ od 8 (SOff j 0)
      (bv_unsigned (getr (c_regs cx) r)) HS Hi Hsp Hin
      ltac:(cbn [sv_denot]; rewrite Z.add_0_r, (ER j r Hj Hr); reflexivity)
      ltac:(pose proof (u64_range (getr (c_regs cx) r)); cbn; lia) ltac:(cbn; lia)). }
  unfold at_saved, raZ.
  replace (c_sp cx - 8) with (c_sp cx + -8) by lia. replace (c_sp cx - 16) with (c_sp cx + -16) by lia.
  replace (c_sp cx - 24) with (c_sp cx + -24) by lia. replace (c_sp cx - 32) with (c_sp cx + -32) by lia.
  replace (c_sp cx - 40) with (c_sp cx + -40) by lia. replace (c_sp cx - 48) with (c_sp cx + -48) by lia.
  replace (c_sp cx - 56) with (c_sp cx + -56) by lia. replace (c_sp cx - 64) with (c_sp cx + -64) by lia.
  repeat split;
    [ apply (V 1%nat 1%bv) | apply (V 8%nat 8%bv) | apply (V 9%nat 9%bv) | apply (V 18%nat 18%bv)
    | apply (V 19%nat 19%bv) | apply (V 20%nat 20%bv) | apply (V 21%nat 21%bv) | apply (V 22%nat 22%bv) ];
    first [lia | reflexivity | cbn [YP09.r_chunks at_fr0 In]; repeat (first [left; reflexivity | right])].
Qed.

(* the invariant at the first join, from the entry *)
Lemma at_inv_J1_of : forall cx len n f regsX memX mdX,
  at_base SK B rlo rhi cx ->
  getr regsX 2 = w64 (c_sp cx - 64) ->
  getr regsX 3 = getr (c_regs cx) 3 -> getr regsX 4 = getr (c_regs cx) 4 ->
  getr regsX 23 = getr (c_regs cx) 23 -> getr regsX 24 = getr (c_regs cx) 24 ->
  getr regsX 25 = getr (c_regs cx) 25 -> getr regsX 26 = getr (c_regs cx) 26 ->
  getr regsX 27 = getr (c_regs cx) 27 ->
  at_saved cx memX -> at_live cx len regsX ->
  ajournal_gx SEGS B (c_G cx) (c_XO cx) (c_OUT cx) (c_STK cx) (c_sp0 cx) (c_FP cx)
    (c_ly cx) (c_S cx) (c_W0 cx) (c_mem0 cx) (c_md0 cx) (c_own cx)
    (c_lyc cx) (c_Sc cx) (c_W cx) memX mdX (c_k cx) ->
  m_fds mdX = m_fds (c_mdc cx) -> m_fs mdX = m_fs (c_mdc cx) ->
  nlw_fields SEGS (rdW (c_W cx) memX) (c_w cx) n f -> c_n0 cx <= n -> 0 <= len <= c_slen cx + 1 ->
  at_kept cx memX ->
  at_inv SK B cx AT_J1 len n f (mkst regsX (Z_to_bv 64 (BASE + AT_J1)) memX (seg_rom SEGS)) mdX.
Proof.
  intros cx len n f regsX memX mdX HB R2 R3 R4 R23 R24 R25 R26 R27 HSAV HLV HJ HFD HFS HF Hn0 Hlen HK.
  destruct HB as (HPRE & _). destruct HPRE as (HJ0 & _ & _ & _ & _ & _ & _ & _ & Hwlo & Hwhi & _).
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  assert (Hceil : alloc_ceiling <= c_sp0 cx - c_STK cx) by (eapply (aj_stk_ceiling SK SEGS B); exact HJ0).
  assert (HSPhi : c_sp cx < 2 ^ 64)
    by (unfold c_sp, spZ; pose proof (u64_range (getr (c_regs cx) 2)); lia).
  assert (HAK : ATTR_TEXT_AK = 4160) by reflexivity.
  unfold at_inv, at_shape. cbn [ms_pc_val ms_resv ms_svc_pending ms_rom ms_fregs ms_fcsr ms_regs ms_mem mkst].
  split; [|split; [exact HLV|]].
  - split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split; [reflexivity|]. split; [reflexivity|].
    split; [unfold spZ; rewrite R2; unfold w64, AT_FRAME; apply unsigned_lit_small; unfold c_sp in *; lia|].
    split; [|exact HSAV].
    unfold at_regs_kept. rewrite R3, R4, R23, R24, R25, R26, R27. repeat split.
  - split; [exact HJ|]. split; [exact HFD|]. split; [exact HFS|]. split; [exact HF|].
    split; [exact Hn0|]. split; [lia|]. split; [lia|]. exact HK.
Qed.

(* THE ENTRY STATE: the frame to push, the .got slot of the shadow base and its cell (copy_attr.v ca_entry's
   proof at attr_text's frame) *)
Lemma at_entry0 : forall cx (EXT : list word),
  at_base SK B rlo rhi cx ->
  nth 0 EXT (Z_to_bv 64 0) = Z_to_bv 64 SHADOW_OFF ->
  st_ok_pi SEGS pa_val (Eimg (Ereg (c_regs cx) EXT)) at_ss0
    (restrict (w_H (c_W cx)) (mkst (c_regs cx) (Z_to_bv 64 (BASE + AF_attr_text)) (c_memc cx) (seg_rom SEGS))) /\
  sh_ok SEGS at_Bx [] (Eimg (Ereg (c_regs cx) EXT)) (mrestrict (w_H (c_W cx)) (c_memc cx)).
Proof.
  intros cx EXT HB H32.
  destruct HB as (HPRE & _). destruct HPRE as (HJ & _ & _ & _ & _ & _ & _ & Hal16 & Hwlo & Hwhi & _).
  pose proof HJ as (HSTK & HXO & (memS & HJi & _) & _).
  pose proof HJi as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
  pose proof Hstk as (_ & _ & Hceil & Hslo & Hshi & H47 & _).
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  assert (HK : ATTR_TEXT_AK = 4160) by reflexivity. rewrite HK in Hwlo.
  destruct (al_const _ _ LAWS (c_lyc cx) (c_Sc cx) (c_W cx) (c_memc cx) (c_mdc cx) HAR) as (Kcell & _ & Kgot & _).
  rewrite (pal_got_shadow B TL), (pal_cell B TL) in Kgot. rewrite (pal_cell B TL) in Kcell.
  pose proof (pa_obj_img 64 ltac:(lia)) as HcellR. pose proof (pal_got_cell B TL) as HgcD.
  pose proof (pa_obj_img 1 ltac:(lia)) as HgotR.
  pose proof (pa_val_range (A_OBJ 1)) as Vg. pose proof (pa_val_range (A_OBJ 64)) as Vc.
  unfold pcap_img_end, YImgTop.IMG_TOP in HcellR, HgotR.
  set (regs := c_regs cx) in *. set (W := c_W cx) in *. set (memc := c_memc cx) in *.
  set (E := Eimg (Ereg regs EXT)).
  assert (EL : forall nn, (nn < A_TEXT)%nat -> ew E nn = ew (Ereg regs EXT) nn)
    by (intros nn Hn; subst E; apply Eimg_low; exact Hn).
  assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
  assert (E32 : ew E 32 = Z_to_bv 64 SHADOW_OFF) by (rewrite EL by (unfold A_TEXT; lia); exact (eq_trans (ew_Ereg_extra regs EXT 0) H32)).
  assert (Egot : ew E (A_OBJ 1) = Z_to_bv 64 (pa_val (A_OBJ 1))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
  assert (Ecell : ew E (A_OBJ 64) = Z_to_bv 64 (pa_val (A_OBJ 64))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
  assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
  assert (VB : forall nn v, ew E nn = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some nn) = v).
  { intros nn v Hn Hv. cbn [base_val]. rewrite Hn. apply unsigned_lit_small. exact Hv. }
  split.
  - rewrite restrict_mkst_fx. unfold at_ss0. apply pa_entry_st_ok_full.
    + apply regs_ok_Eimg_Ereg.
    + vm_compute. reflexivity.
    + unfold stack_region, got_regionP, bcell_regionP.
      repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
      * cbn [base_val]. fold E. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
        intros o Ho. apply (lw_apresent_writable SEGS). apply Hpres. lia.
      * fold E. rewrite (VB (A_OBJ 1) (pa_val (A_OBJ 1)) Egot Vg).
        split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        constructor; [|constructor].
        apply (chunk_ok_val SEGS E _ (pa_val (A_OBJ 1)) 0 8 (SOff (A_OBJ 64) 0) (pa_val (A_OBJ 64)));
          [cbn [sv_denot]; rewrite Ecell, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
          | change (8 * Z.of_N 8) with 64; lia | cbn; lia |].
        rewrite Z.add_0_r. exact (val_mem_of_rdword_g SEGS (w_H W) memc _ _ Kgot).
      * fold E. rewrite (VB (A_OBJ 64) (pa_val (A_OBJ 64)) Ecell Vc).
        split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        constructor; [|constructor].
        apply (chunk_ok_val SEGS E _ (pa_val (A_OBJ 64)) 0 8 at_Bx SHADOW_OFF);
          [cbn [sv_denot at_Bx]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; unfold SHADOW_OFF; lia | cbn; lia |].
        rewrite Z.add_0_r. exact (val_mem_of_rdword_g SEGS (w_H W) memc _ _ Kcell).
    + apply pairwise_disjoint_of_extents.
      unfold stack_region, got_regionP, bcell_regionP, extent_of_region.
      cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
      fold E. rewrite (VB (A_OBJ 1) (pa_val (A_OBJ 1)) Egot Vg), (VB (A_OBJ 64) (pa_val (A_OBJ 64)) Ecell Vc).
      cbn [base_val]. rewrite Usp.
      cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
      revert Hslo Hshi H47 Hceil C1a HcellR HgcD HgotR Hwlo Hwhi HSTK HXO.
      clear. intros. repeat split; lia.
    + split; [|split; [exact I | exact I]].
      cbn [at_facts0 f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      fold E. rewrite Usp, E32, unsigned_lit_small by (unfold SHADOW_OFF; lia).
      change (2 ^ 4) with 16. rewrite ?Z.pow_0_r, ?Z.mod_1_r.
      revert Hslo Hshi H47 Hceil C1a Hwlo Hwhi HSTK HXO Hal16.
      clear. unfold SHADOW_OFF. intros. repeat match goal with |- _ /\ _ => split end; first [exact I | lia].
  - apply Forall_nil.
Qed.

(* THE ENTRY PHASE: from the call to the first join +0xec *)
Theorem at_p0 : forall cx, at_base SK B rlo rhi cx ->
  SRr SEGS (c_W cx) (mkCfg (mkst (c_regs cx) (Z_to_bv 64 (BASE + AF_attr_text)) (c_memc cx) (seg_rom SEGS))
    (c_mdc cx)) (at_post SK B cx).
Proof.
intros cx HB.
pose proof (at_p1 SK B rlo rhi LAWS (at_p2 SK B rlo rhi LAWS AMEMCPY (at_p3 SK B rlo rhi LAWS AMEMSET
  (at_p4 SK B rlo rhi LAWS)))) as HNEXT.
pose proof HB as HB0.
destruct HB as (HPRE & HRD & HNLW & HWF & Hs0 & HSTR & HSLEN & HSLACK & HAP & HAPF1 & HAPF2 &
  HMR1 & HRA1 & HHV1 & HMR2 & HRA2 & HHV2).
destruct HPRE as (HJ & HGok & HROD & Hraw & Hra4 & Hgp & Htp & Hal16 & Hwlo & Hwhi & Hev & Hside & Hajw & Hro).
destruct (fields_of_anlw SEGS (c_mem cx) (c_w cx) (c_bs cx) HNLW HWF) as (VN0 & VF0 & Rn0 & Rf0 & Hw0 & Hwl & HPRES0).
pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
assert (Hceil : alloc_ceiling <= c_sp0 cx - c_STK cx) by (eapply (aj_stk_ceiling SK SEGS B); exact HJ).
assert (HAK : ATTR_TEXT_AK = 4160) by reflexivity.
assert (Hwlo' : c_sp0 cx - c_STK cx <= c_sp cx - 4160) by (unfold c_sp; lia).
assert (Hwhi' : c_sp cx <= c_sp0 cx) by (unfold c_sp; lia).
assert (Hal16' : c_sp cx mod 16 = 0) by exact Hal16.
assert (HSPhi : c_sp cx < 2 ^ 64) by (unfold c_sp, spZ; pose proof (u64_range (getr (c_regs cx) 2)); lia).
pose proof (at_w_range cx) as Rw. pose proof (at_s_range cx) as Rs.
assert (Hsl0 : 0 <= c_slen cx) by (unfold c_slen; lia).
unfold NL_CHUNK_MAX in Rn0.
assert (Hamr : c_w cx + 4113 <= 2 ^ 47) by (unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd, NW_SIZE in *; lia).
assert (Hsmr : c_s cx + c_slen cx + 1 <= 2 ^ 47) by (unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in *; lia).
assert (Hs0' : 0 < c_s cx) by lia.
set (n0 := nw_n (c_bs cx)) in *. set (f0 := nw_full (c_bs cx)) in *.
set (bare := bv_unsigned (getr (c_regs cx) 13)).
assert (Rbare : 0 <= bare < 2 ^ 64) by (unfold bare; apply u64_range).
remember (if bare =? 0 then 1 else 0) as bz eqn:Hbz.
assert (Hbz01 : 0 <= bz <= 1) by (subst bz; destruct (bare =? 0); lia).
remember (c_slen cx + bz) as len eqn:Hlen.
assert (G10 : getr (c_regs cx) 10%bv = w64 (c_w cx))
  by (unfold c_w, aarg, argZ, w64; rewrite Z_to_bv_bv_unsigned; f_equal; apply bv_eq; reflexivity).
assert (G12 : getr (c_regs cx) 12%bv = w64 (c_s cx))
  by (unfold c_s, aarg, argZ, w64; rewrite Z_to_bv_bv_unsigned; f_equal; apply bv_eq; reflexivity).
set (EXT := [w64 SHADOW_OFF; w64 n0; w64 f0; w64 (c_w cx + n0)]).
destruct (at_entry0 cx EXT HB0 eq_refl) as [HS SHOK].
remember (Eimg (Ereg (c_regs cx) EXT)) as E eqn:HEdef.
assert (HEI : img_env pa_val A_LIM E) by (subst E; apply Eimg_env).
assert (ER : forall (j : nat) (r : bv 5), (j < 32)%nat -> Z.of_nat j = bv_unsigned r -> ew E j = getr (c_regs cx) r)
  by (intros j r Hj Hr; subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ j r Hr)).
assert (EX : forall j, (j < 4)%nat -> ew E (32 + j)%nat = nth j EXT (Z_to_bv 64 0))
  by (intros j Hj; subst E; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
clear HEdef.
pose proof (EX 0%nat ltac:(lia)) as E32. pose proof (EX 1%nat ltac:(lia)) as E33.
pose proof (EX 2%nat ltac:(lia)) as E34. pose proof (EX 3%nat ltac:(lia)) as E35.
unfold EXT in E32, E33, E34, E35. cbn [nth Nat.add] in E32, E33, E34, E35.
assert (EW : forall (j : nat) (r : bv 5), (j < 32)%nat -> Z.of_nat j = bv_unsigned r ->
          ew E j = w64 (bv_unsigned (getr (c_regs cx) r)))
  by (intros j r Hj Hr; rewrite (ER j r Hj Hr); unfold w64; symmetry; apply Z_to_bv_bv_unsigned).
assert (E2 : ew E 2%nat = w64 (c_sp cx)) by exact (EW 2%nat 2%bv ltac:(lia) eq_refl).
assert (Usp : bv_unsigned (ew E 2%nat) = c_sp cx) by (rewrite E2; unfold w64; apply unsigned_lit_small; lia).
assert (E10 : ew E 10%nat = w64 (c_w cx)) by (rewrite (ER 10%nat 10%bv ltac:(lia) eq_refl); exact G10).
assert (E12 : ew E 12%nat = w64 (c_s cx)) by (rewrite (ER 12%nat 12%bv ltac:(lia) eq_refl); exact G12).
assert (E13 : ew E 13%nat = w64 bare) by exact (EW 13%nat 13%bv ltac:(lia) eq_refl).
pose (RUN := paj_run_x SK B LAWS (c_G cx) HGok (c_XO cx) (c_OUT cx)).
pose (RUNTO := paj_run_to_x SK B LAWS (c_G cx) HGok (c_XO cx) (c_OUT cx)).
pose (BR := paj_branch (PI := PI)).
(* +0x00 .. +0x4c: the prologue, the arguments, the shadow base, the call of wrapper_strlen *)
paj_run_tok RUN HS HJ SHOK at_span.
{ unfold at_ss0, stack_region, got_regionP, bcell_regionP. cbn [ss_mem]. at_awr_tac Hajw. }
pose proof (kept_of_frame (segs := SEGS) _ _ _ _ _ (fun a => c_sp cx - 64 <= a < c_sp cx) HFr
  ltac:(at_frame_tac)) as UN1.
cbv beta in UN1.
pose proof (at_kept_frame_run cx _ _ (at_kept_init cx HB0) UN1 HG) as HK1.
clear HF HFr HG.
pmkst HS.
prreg HS (1%bv : bv 5) R1.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdx) _ =>
  assert (Q2 : getr rg 2 = w64 (c_sp cx - 64)) by (at_reg_val HS (2%bv : bv 5); at_U);
  assert (Qsp : spZ rg = c_sp cx - 64) by (unfold spZ; rewrite Q2; unfold w64; apply unsigned_lit_small; lia);
  assert (Q3 : getr rg 3 = w64 (as_gp B))
    by (rewrite <- Hgp; exact (at_reg_atom_ok E _ _ _ 3%bv 3 _ HS ltac:(vm_compute; reflexivity)
                                 (ER 3%nat 3%bv ltac:(lia) eq_refl)));
  assert (Q4 : getr rg 4 = w64 (as_tp B))
    by (rewrite <- Htp; exact (at_reg_atom_ok E _ _ _ 4%bv 4 _ HS ltac:(vm_compute; reflexivity)
                                 (ER 4%nat 4%bv ltac:(lia) eq_refl)));
  assert (Q10 : getr rg 10 = w64 (c_s cx))
    by exact (at_reg_atom_ok E _ _ _ 10%bv 12 _ HS ltac:(vm_compute; reflexivity) E12)
end.
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdx) _ =>
    eapply (aj_gx_strlen_atS SK SEGS B LAWS pa_segs_low (pa_sigma LS___interceptor_trampoline_strlen) ASTRLEN
      (c_G cx) (c_XO cx) (c_OUT cx) (c_W cx) rg mm (c_STK cx) (c_sp0 cx) (c_FP cx) (c_ly cx) (c_S cx) (c_W0 cx)
      (c_mem0 cx) (c_md0 cx) (c_own cx) (c_lyc cx) (c_Sc cx) mdx (c_k cx) (c_s cx) (c_str cx) _ HGok HJ);
    [ rewrite Qsp; replace (c_sp cx - 64) with (c_sp cx + (-4) * 16) by lia; rewrite Z_mod_plus_full; exact Hal16'
    | rewrite Qsp; unfold ESTACK; lia
    | rewrite Qsp; lia
    | exact Q3 | exact Q4 | exact R1 | apply ret_ok_codeptr_v; [lia | reflexivity]
    | exact Q10 | exact Hs0'
    | exact (at_astr_at cx mm HB0 HK1)
    | exact (at_aread_ok cx mm rg HB0 HK1 Qsp)
    | exact (at_tail_vis cx mm HB0 UN1)
    | exact (at_rom_kept cx mm HB0 UN1) ]
  end. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & HL2 & Hfr2 & Hpres2 & Hsm2).
lazymatch goal with HS : st_ok _ _ _ (restrict _ ?msc) |- _ =>
  assert (FD2 : m_fds md2 = m_fds (c_mdc cx) /\ m_fs md2 = m_fs (c_mdc cx));
  [ unfold same_but_materialized in Hsm2; rewrite Hsm2;
    repeat rewrite (proj1 (wvb_fds_fs _ _ _)); repeat rewrite (proj2 (wvb_fds_fs _ _ _)); split; reflexivity |];
  assert (HK2 : at_kept cx mem2);
  [ apply (at_kept_step cx (ms_mem msc) mem2 HK1);
    apply (at_step_call cx _ _ (c_w cx) 0); [| exact Hpres2 | lia | unfold NW_SIZE; lia];
    intros a Ha _ Hw; apply Hfr2; [exact Ha | rewrite Qsp; unfold AT_FRAME in Hw; exact Hw] |];
  assert (SK2 : forall x, c_w cx <= x < c_w cx + NW_SIZE ->
            aview SEGS (w_H (c_W cx)) mem2 x = aview SEGS (w_H (c_W cx)) (c_memc cx) x);
  [ intros x Hx; rewrite Hfr2;
    [ apply UN1; [unfold NW_SIZE in *; lia | unfold apart_frame, c_sp, NW_SIZE in *; rewrite HAK in HAPF1; lia]
    | unfold NW_SIZE in *; lia
    | rewrite Qsp; unfold apart_frame, c_sp, ESTACK, NW_SIZE in *; rewrite HAK in HAPF1; lia ] |]
end.
clear Hsm2.
jafter_call_keep_pi HS 48%nat regs2 (mrestrict (w_H (c_W cx)) mem2) HP2 [0]%nat HS2.
lazymatch type of HS2 with ?tq -> _ => assert (HRK : tq); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. apply Forall_cons; [|apply Forall_nil].
  split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Usp; intros x Hx.
  - apply (lw_mbyte_of_aview SEGS). apply Hfr2; [lia | rewrite Qsp; unfold ESTACK; lia].
  - intros _. apply (lw_apresent_writable SEGS). apply (at_win _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2). lia. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
remember (havoc E 48 (map (getr regs2) CLOB)) as E3 eqn:HE3 in HS.
assert (HEI3 : img_env pa_val A_LIM E3) by (rewrite HE3; apply img_env_havoc; [assumption | cbv; lia]).
assert (HA3 : env_agree 48 E E3) by (rewrite HE3; apply env_agree_havoc_ge; [lia | apply env_agree_refl]).
assert (F52 : ew E3 52%nat = w64 (c_slen cx)) by (rewrite HE3; cbn; exact HL2).
clear HE3.

assert (FR : forall (j : nat) (r : bv 5), (j < 32)%nat -> Z.of_nat j = bv_unsigned r -> ew E3 j = getr (c_regs cx) r)
  by (intros j r Hj Hr; rewrite (proj1 HA3 j ltac:(lia)); exact (ER j r Hj Hr)).
assert (F2 : ew E3 2%nat = w64 (c_sp cx)) by (rewrite (proj1 HA3 2%nat ltac:(lia)); exact E2).
assert (V2 : bv_unsigned (ew E3 2%nat) = c_sp cx) by (rewrite (proj1 HA3 2%nat ltac:(lia)); exact Usp).
assert (F10 : ew E3 10%nat = w64 (c_w cx)) by (rewrite (proj1 HA3 10%nat ltac:(lia)); exact E10).
assert (V10 : bv_unsigned (ew E3 10%nat) = c_w cx) by (rewrite F10; unfold w64; apply unsigned_lit_small; lia).
assert (F12 : ew E3 12%nat = w64 (c_s cx)) by (rewrite (proj1 HA3 12%nat ltac:(lia)); exact E12).
assert (F13 : ew E3 13%nat = w64 bare) by (rewrite (proj1 HA3 13%nat ltac:(lia)); exact E13).
assert (F32 : ew E3 32%nat = w64 SHADOW_OFF) by (rewrite (proj1 HA3 32%nat ltac:(lia)); exact E32).
assert (F33 : ew E3 33%nat = w64 n0) by (rewrite (proj1 HA3 33%nat ltac:(lia)); exact E33).
assert (F34 : ew E3 34%nat = w64 f0) by (rewrite (proj1 HA3 34%nat ltac:(lia)); exact E34).
assert (F35 : ew E3 35%nat = w64 (c_w cx + n0)) by (rewrite (proj1 HA3 35%nat ltac:(lia)); exact E35).
assert (V33 : bv_unsigned (ew E3 33%nat) = n0) by (rewrite F33; unfold w64; apply unsigned_lit_small; lia).
assert (V34 : bv_unsigned (ew E3 34%nat) = f0) by (rewrite F34; unfold w64; apply unsigned_lit_small; lia).
clear E2 Usp E10 E12 E13 E32 E33 E34 E35 ER EW EX.
(* the struct's fields: the ranges of w, n, full, and their region with its shadow entry *)
pose proof (st_ok_pi_add_fact E3 _ _ 10 (mkAF 0 (2 ^ 47 - 4113) 0) HS) as HSa.
lazymatch type of HSa with ?t -> _ =>
  assert (HR : t) by (unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite V10, Z.pow_0_r, Z.mod_1_r; lia);
  specialize (HSa HR); clear HR end.
clear HS.
pose proof (st_ok_pi_add_fact E3 _ _ 33 (mkAF 0 4096 0) HSa) as HSb.
lazymatch type of HSb with ?t -> _ =>
  assert (HR : t) by (unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite V33, Z.pow_0_r, Z.mod_1_r; lia);
  specialize (HSb HR); clear HR end.
clear HSa.
pose proof (st_ok_pi_add_fact E3 _ _ 34 (mkAF 0 1 0) HSb) as HSc.
lazymatch type of HSc with ?t -> _ =>
  assert (HR : t) by (unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite V34, Z.pow_0_r, Z.mod_1_r; lia);
  specialize (HSc HR); clear HR end.
clear HSb.
lazymatch type of HSc with st_ok_pi _ _ _ ?s _ => let v := eval vm_compute in s in change s with v in HSc end.
pose proof (st_ok_pi_add_region E3 _ _ at_flE HSc eq_refl) as HSd.
lazymatch type of HSd with ?t -> _ -> _ => assert (HR : t); [|specialize (HSd HR); clear HR] end.
{ unfold region_ok, at_flE. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite V10. split; [lia|]. split; [lia|]. split.
  - intros o Ho. cbn [ms_mem restrict mkst].
    apply (writable_kept (segs := SEGS) (w_H (c_W cx)) (c_memc cx) mem2 _ (proj1 (proj2 HK2) _)).
    exact (proj2 (HPRES0 o ltac:(unfold NW_SIZE; lia))).
  - cbn [ms_mem restrict mkst]. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    + apply (chunk_ok_val SEGS E3 _ (c_w cx) 4096 8%N (SOff 33 0) n0);
        [ cbn [sv_denot]; rewrite Z.add_0_r, V33; reflexivity | cbn [Z.of_N]; lia | cbn [Z.of_N]; lia |].
      apply (at_val_mem_keep (rdW (c_W cx) (c_memc cx))); [|exact VN0].
      intros i Hi. apply (mbyte_of_aview SEGS (w_H (c_W cx)) (w_H (c_W cx))). apply SK2.
      cbn in Hi. unfold NW_SIZE. lia.
    + apply (chunk_ok_val SEGS E3 _ (c_w cx) 4104 4%N (SOff 34 0) f0);
        [ cbn [sv_denot]; rewrite Z.add_0_r, V34; reflexivity | cbn [Z.of_N]; lia | cbn [Z.of_N]; lia |].
      apply (at_val_mem_keep (rdW (c_W cx) (c_memc cx))); [|exact VF0].
      intros i Hi. apply (mbyte_of_aview SEGS (w_H (c_W cx)) (w_H (c_W cx))). apply SK2.
      cbn in Hi. unfold NW_SIZE. lia. }
lazymatch type of HSd with ?t -> _ => assert (HR : t); [|specialize (HSd HR); clear HR] end.
{ cbv [ss_mem all_disjoint extent_disjoint at_flE YP09.r_base YP09.r_lo YP09.r_hi]. cbn [base_val].
  rewrite V10, V2. unfold apart_frame, c_sp, NW_SIZE in *. rewrite HAK in HAPF1. split; [lia | exact I]. }
clear HSc. rename HSd into HS.
lazymatch type of HS with st_ok_pi _ _ _ ?s _ => let v := eval vm_compute in s in change s with v in HS end.
clear SHOK.
assert (SHOK : sh_ok SEGS at_Bx [mkSHE 10 4096 4112] E3 (mrestrict (w_H (c_W cx)) mem2))
  by (apply Forall_cons; [|apply Forall_nil];
      apply (at_she_ok SK B rlo rhi cx mem2 E3 10 (c_w cx) 4096 4112 HB0 HK2 F10 F32); unfold NW_SIZE; lia).
(* +0x50 .. +0x7c: s5, C1, n, len, a1, up to the room test *)
paj_run_to_tok RUNTO HS HJ2 SHOK at_span AT_J1.
{ at_awr_tac Hajw. }
pose proof (kept_of_frame (segs := SEGS) _ _ _ _ _
  (fun a => (c_sp cx - 64 <= a < c_sp cx) \/ (c_w cx + 4096 <= a < c_w cx + 4112)) HFr ltac:(at_frame_tac)) as UN3.
lazymatch goal with HS : st_ok_pi _ _ _ _ (restrict _ ?msc) |- _ =>
  pose proof (at_kept_run2 cx mem2 (ms_mem msc) _ HK2 UN3
    ltac:(intros a Ha; cbv beta in Ha; unfold NW_SIZE; lia) HG) as HK3
end.
clear HF HFr HG UN3.
assert (U4095 : U E3 (SOff 33 (-4095)) = (n0 - 4095) mod 2 ^ 64).
{ rewrite U_SOff, F33. unfold w64. rewrite unsigned_lit_small by lia. unfold zcanon, M64. f_equal; lia. }
psrr_branch_tok RUN BR HS SHOK at_span.

- (* room: n <= 4094; the two bytes of len + 4 at w + n through the alias atom 35 *)
  rewrite branch_ltu_U, (U_lit E3 18446744073709547518), U4095 in Hc by lia. apply Z.ltb_lt in Hc.
  assert (Hn94 : n0 <= 4094) by lia. clear Hc.
  assert (V35 : bv_unsigned (ew E3 35%nat) = c_w cx + n0) by (rewrite F35; unfold w64; apply unsigned_lit_small; lia).
  pose proof (st_ok_pi_add_alias SEGS pa_val E3 _ _ (SAlu ALU_ADD (SOff 10 0) (SOff 33 0)) (SOff 35 0) HS) as HS5.
  lazymatch type of HS5 with ?t -> _ =>
    assert (HR : t) by (apply U_inj; transitivity (c_w cx + n0); [at_U | symmetry; at_U]);
    specialize (HS5 HR); clear HR end.
  clear HS.
  pose proof (st_ok_pi_add_fact E3 _ _ 35 (mkAF 0 (2 ^ 47 - 19) 0) HS5) as HS6.
  lazymatch type of HS6 with ?t -> _ =>
    assert (HR : t) by (unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite V35, Z.pow_0_r, Z.mod_1_r; lia);
    specialize (HS6 HR); clear HR end.
  clear HS5.
  lazymatch type of HS6 with st_ok_pi _ _ _ ?s _ => let v := eval vm_compute in s in change s with v in HS6 end.
  pose proof (st_ok_pi_add_region E3 _ _ at_b2 HS6 eq_refl) as HS7.
  lazymatch type of HS7 with ?t -> _ -> _ => assert (HR : t); [|specialize (HS7 HR); clear HR] end.
  { unfold region_ok, at_b2.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite V35.
    split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
    intros o Ho. cbn [ms_mem restrict].
    apply (writable_kept (segs := SEGS) (w_H (c_W cx)) (c_memc cx) _ _ (proj1 (proj2 HK3) _)).
    replace (c_w cx + n0 + o) with (c_w cx + (n0 + o)) by lia.
    exact (proj2 (HPRES0 (n0 + o) ltac:(unfold NW_SIZE; lia))). }
  lazymatch type of HS7 with ?t -> _ => assert (HR : t); [|specialize (HS7 HR); clear HR] end.
  { cbv [ss_mem all_disjoint extent_disjoint at_b2 YP09.r_base YP09.r_lo YP09.r_hi]. cbn [base_val].
    rewrite V35, V10, V2.
    unfold apart_frame, c_w, c_sp, NW_SIZE in *. rewrite HAK in HAPF1.
    split; [lia|]. split; [lia|]. exact I. }
  clear HS6. rename HS7 into HS.
  lazymatch type of HS with st_ok_pi _ _ _ ?s _ => let v := eval vm_compute in s in change s with v in HS end.
  lazymatch goal with HS : st_ok_pi _ _ _ _ (restrict _ ?msc) |- _ =>
    assert (SHOK1 : sh_ok SEGS at_Bx [mkSHE 10 4096 4112; mkSHE 35 0 2] E3 (mrestrict (w_H (c_W cx)) (ms_mem msc)));
    [ apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]];
      [ apply (at_she_ok SK B rlo rhi cx (ms_mem msc) E3 10 (c_w cx) 4096 4112 HB0 HK3 F10 F32); unfold NW_SIZE; lia
      | apply (at_she_ok SK B rlo rhi cx (ms_mem msc) E3 35 (c_w cx + n0) 0 2 HB0 HK3 F35 F32); unfold NW_SIZE; lia ]
    | ]
  end.
  clear SHOK. rename SHOK1 into SHOK.
  (* +0xa0 .. +0xe8: C3 twice, the two bytes, C1, n := n + 2 *)
  paj_run_to_tok RUNTO HS HJ2 SHOK at_span AT_J1.
  { at_awr_tac Hajw. }
  pose proof (kept_of_frame (segs := SEGS) _ _ _ _ _
    (fun a => (c_sp cx - 64 <= a < c_sp cx) \/ (c_w cx + 4096 <= a < c_w cx + 4112) \/
              (c_w cx + n0 <= a < c_w cx + n0 + 2)) HFr ltac:(at_frame_tac)) as UN4.
  lazymatch goal with HS : st_ok_pi _ _ _ _ (restrict _ ?msc) |- _ =>
    pose proof (at_kept_run2 cx _ (ms_mem msc) _ HK3 UN4
      ltac:(intros a Ha; cbv beta in Ha; unfold NW_SIZE; lia) HG) as HK4
  end.
  clear HF HFr HG UN4.
  lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ => remember Ex as E4 eqn:HE4 in HS end.
  assert (HA4 : env_agree 512 E3 E4) by (rewrite HE4; at_agree).
  clear HE4.
    assert (FR4 : forall (j : nat) (r : bv 5), (j < 32)%nat -> Z.of_nat j = bv_unsigned r -> ew E4 j = getr (c_regs cx) r)
      by (intros j r Hj Hr; rewrite (proj1 HA4 j ltac:(lia)); exact (FR j r Hj Hr));
    assert (Z2 : ew E4 2%nat = w64 (c_sp cx)) by (rewrite (proj1 HA4 2%nat ltac:(lia)); exact F2);
    assert (Z10 : ew E4 10%nat = w64 (c_w cx)) by (rewrite (proj1 HA4 10%nat ltac:(lia)); exact F10);
    assert (Z12 : ew E4 12%nat = w64 (c_s cx)) by (rewrite (proj1 HA4 12%nat ltac:(lia)); exact F12);
    assert (Z13 : ew E4 13%nat = w64 bare) by (rewrite (proj1 HA4 13%nat ltac:(lia)); exact F13);
    assert (Z32 : ew E4 32%nat = w64 SHADOW_OFF) by (rewrite (proj1 HA4 32%nat ltac:(lia)); exact F32);
    assert (Z33 : ew E4 33%nat = w64 n0) by (rewrite (proj1 HA4 33%nat ltac:(lia)); exact F33);
    assert (Z34 : ew E4 34%nat = w64 f0) by (rewrite (proj1 HA4 34%nat ltac:(lia)); exact F34);
    assert (Z52 : ew E4 52%nat = w64 (c_slen cx)) by (rewrite (proj1 HA4 52%nat ltac:(lia)); exact F52);
    assert (W2 : bv_unsigned (ew E4 2%nat) = c_sp cx) by (rewrite (proj1 HA4 2%nat ltac:(lia)); exact V2);
    assert (W10 : bv_unsigned (ew E4 10%nat) = c_w cx) by (rewrite (proj1 HA4 10%nat ltac:(lia)); exact V10);
    lazymatch goal with HS : st_ok_pi _ _ _ ?ssx (restrict _ ?msc) |- _ =>
      pmkst HS;
      eapply (HNEXT cx len (n0 + 2) f0); [exact HB0|];
      split;
      [ eapply (at_inv_J1_of cx len (n0 + 2) f0);
        [ exact HB0
        | at_reg_val HS (2%bv : bv 5); at_U
        | exact (at_reg_atom_pi E4 _ _ _ 3%bv 3 _ HS ltac:(vm_compute; reflexivity) (FR4 3%nat 3%bv ltac:(lia) eq_refl))
        | exact (at_reg_atom_pi E4 _ _ _ 4%bv 4 _ HS ltac:(vm_compute; reflexivity) (FR4 4%nat 4%bv ltac:(lia) eq_refl))
        | exact (at_reg_atom_pi E4 _ _ _ 23%bv 23 _ HS ltac:(vm_compute; reflexivity) (FR4 23%nat 23%bv ltac:(lia) eq_refl))
        | exact (at_reg_atom_pi E4 _ _ _ 24%bv 24 _ HS ltac:(vm_compute; reflexivity) (FR4 24%nat 24%bv ltac:(lia) eq_refl))
        | exact (at_reg_atom_pi E4 _ _ _ 25%bv 25 _ HS ltac:(vm_compute; reflexivity) (FR4 25%nat 25%bv ltac:(lia) eq_refl))
        | exact (at_reg_atom_pi E4 _ _ _ 26%bv 26 _ HS ltac:(vm_compute; reflexivity) (FR4 26%nat 26%bv ltac:(lia) eq_refl))
        | exact (at_reg_atom_pi E4 _ _ _ 27%bv 27 _ HS ltac:(vm_compute; reflexivity) (FR4 27%nat 27%bv ltac:(lia) eq_refl))
        | exact (at_saved_of_ss cx E4 ssx msc 2%nat HS eq_refl W2 FR4)
        | unfold at_live;
          split; [at_reg_val HS (8%bv : bv 5); unfold NW_N; at_U|];
          split; [at_reg_val HS (9%bv : bv 5); at_U|];
          split; [at_reg_val HS (18%bv : bv 5); at_U|];
          split; [at_reg_val HS (19%bv : bv 5);
                  eapply at_U_add; [at_U | eapply at_U_seqz; [at_U | exact (eq_sym Hbz)] | lia | lia]|];
          split; [exact (at_reg_atom_pi E4 _ _ _ 20%bv 11 _ HS ltac:(vm_compute; reflexivity)
                           (FR4 11%nat 11%bv ltac:(lia) eq_refl))|];
          split;
          [ rewrite (st_ok_pi_restrict_reg _ E4 ssx msc (21%bv : bv 5) HS),
              (st_ok_pi_restrict_reg _ E4 ssx msc (8%bv : bv 5) HS), (st_ok_pi_restrict_reg _ E4 ssx msc (22%bv : bv 5) HS);
            let e21 := eval vm_compute in (sr_get (ss_regs ssx) (21%bv : bv 5)) in
            change (sr_get (ss_regs ssx) (21%bv : bv 5)) with e21;
            let e8 := eval vm_compute in (sr_get (ss_regs ssx) (8%bv : bv 5)) in
            change (sr_get (ss_regs ssx) (8%bv : bv 5)) with e8;
            let e22 := eval vm_compute in (sr_get (ss_regs ssx) (22%bv : bv 5)) in
            change (sr_get (ss_regs ssx) (22%bv : bv 5)) with e22;
            reflexivity
          |];
          at_reg_val HS (22%bv : bv 5); unfold SHADOW_OFF in *; at_U
        | exact HJ2
        | repeat rewrite (proj1 (wvb_fds_fs _ _ _)); exact (proj1 FD2)
        | repeat rewrite (proj2 (wvb_fds_fs _ _ _)); exact (proj2 FD2)
        | apply (at_fields_entry cx (ms_mem msc) (n0 + 2) f0 HB0 (proj1 (proj2 HK4)));
          [ eapply (at_val_of_ss E4 ssx (w_H (c_W cx)) msc 1%nat 10 (c_w cx) 4096 4112 4096 4112 _ 4096 8);
            [ exact HS | reflexivity | exact W10 | cbn [In]; first [left; reflexivity | right; left; reflexivity]
            | apply at_denot; at_U | cbn; lia | cbn; lia ]
          | eapply (at_val_of_ss E4 ssx (w_H (c_W cx)) msc 1%nat 10 (c_w cx) 4096 4112 4096 4112 _ 4104 4);
            [ exact HS | reflexivity | exact W10 | cbn [In]; first [left; reflexivity | right; left; reflexivity]
            | apply at_denot; at_U | cbn; lia | cbn; lia ]
          | unfold NL_CHUNK_MAX; lia | lia ]
        | change (c_n0 cx) with n0; lia
        | lia
        | exact HK4 ]
      | cbn [ms_regs mkst]; at_reg_val HS (11%bv : bv 5); at_U ]
    end.
- (* no room: full := 1 *)
  rewrite branch_ltu_U, (U_lit E3 18446744073709547518), U4095 in Hc by lia. apply Z.ltb_ge in Hc. clear Hc.
  paj_run_to_tok RUNTO HS HJ2 SHOK at_span AT_J1.
  { at_awr_tac Hajw. }
  pose proof (kept_of_frame (segs := SEGS) _ _ _ _ _
    (fun a => (c_sp cx - 64 <= a < c_sp cx) \/ (c_w cx + 4096 <= a < c_w cx + 4112)) HFr ltac:(at_frame_tac)) as UN4.
  lazymatch goal with HS : st_ok_pi _ _ _ _ (restrict _ ?msc) |- _ =>
    pose proof (at_kept_run2 cx _ (ms_mem msc) _ HK3 UN4
      ltac:(intros a Ha; cbv beta in Ha; unfold NW_SIZE; lia) HG) as HK4
  end.
  clear HF HFr HG UN4.
  lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ => remember Ex as E4 eqn:HE4 in HS end.
  assert (HA4 : env_agree 512 E3 E4) by (rewrite HE4; at_agree).
  clear HE4.
    assert (FR4 : forall (j : nat) (r : bv 5), (j < 32)%nat -> Z.of_nat j = bv_unsigned r -> ew E4 j = getr (c_regs cx) r)
      by (intros j r Hj Hr; rewrite (proj1 HA4 j ltac:(lia)); exact (FR j r Hj Hr));
    assert (Z2 : ew E4 2%nat = w64 (c_sp cx)) by (rewrite (proj1 HA4 2%nat ltac:(lia)); exact F2);
    assert (Z10 : ew E4 10%nat = w64 (c_w cx)) by (rewrite (proj1 HA4 10%nat ltac:(lia)); exact F10);
    assert (Z12 : ew E4 12%nat = w64 (c_s cx)) by (rewrite (proj1 HA4 12%nat ltac:(lia)); exact F12);
    assert (Z13 : ew E4 13%nat = w64 bare) by (rewrite (proj1 HA4 13%nat ltac:(lia)); exact F13);
    assert (Z32 : ew E4 32%nat = w64 SHADOW_OFF) by (rewrite (proj1 HA4 32%nat ltac:(lia)); exact F32);
    assert (Z33 : ew E4 33%nat = w64 n0) by (rewrite (proj1 HA4 33%nat ltac:(lia)); exact F33);
    assert (Z34 : ew E4 34%nat = w64 f0) by (rewrite (proj1 HA4 34%nat ltac:(lia)); exact F34);
    assert (Z52 : ew E4 52%nat = w64 (c_slen cx)) by (rewrite (proj1 HA4 52%nat ltac:(lia)); exact F52);
    assert (W2 : bv_unsigned (ew E4 2%nat) = c_sp cx) by (rewrite (proj1 HA4 2%nat ltac:(lia)); exact V2);
    assert (W10 : bv_unsigned (ew E4 10%nat) = c_w cx) by (rewrite (proj1 HA4 10%nat ltac:(lia)); exact V10);
    lazymatch goal with HS : st_ok_pi _ _ _ ?ssx (restrict _ ?msc) |- _ =>
      pmkst HS;
      eapply (HNEXT cx len n0 1); [exact HB0|];
      split;
      [ eapply (at_inv_J1_of cx len n0 1);
        [ exact HB0
        | at_reg_val HS (2%bv : bv 5); at_U
        | exact (at_reg_atom_pi E4 _ _ _ 3%bv 3 _ HS ltac:(vm_compute; reflexivity) (FR4 3%nat 3%bv ltac:(lia) eq_refl))
        | exact (at_reg_atom_pi E4 _ _ _ 4%bv 4 _ HS ltac:(vm_compute; reflexivity) (FR4 4%nat 4%bv ltac:(lia) eq_refl))
        | exact (at_reg_atom_pi E4 _ _ _ 23%bv 23 _ HS ltac:(vm_compute; reflexivity) (FR4 23%nat 23%bv ltac:(lia) eq_refl))
        | exact (at_reg_atom_pi E4 _ _ _ 24%bv 24 _ HS ltac:(vm_compute; reflexivity) (FR4 24%nat 24%bv ltac:(lia) eq_refl))
        | exact (at_reg_atom_pi E4 _ _ _ 25%bv 25 _ HS ltac:(vm_compute; reflexivity) (FR4 25%nat 25%bv ltac:(lia) eq_refl))
        | exact (at_reg_atom_pi E4 _ _ _ 26%bv 26 _ HS ltac:(vm_compute; reflexivity) (FR4 26%nat 26%bv ltac:(lia) eq_refl))
        | exact (at_reg_atom_pi E4 _ _ _ 27%bv 27 _ HS ltac:(vm_compute; reflexivity) (FR4 27%nat 27%bv ltac:(lia) eq_refl))
        | exact (at_saved_of_ss cx E4 ssx msc 1%nat HS eq_refl W2 FR4)
        | unfold at_live;
          split; [at_reg_val HS (8%bv : bv 5); unfold NW_N; at_U|];
          split; [at_reg_val HS (9%bv : bv 5); at_U|];
          split; [at_reg_val HS (18%bv : bv 5); at_U|];
          split; [at_reg_val HS (19%bv : bv 5);
                  eapply at_U_add; [at_U | eapply at_U_seqz; [at_U | exact (eq_sym Hbz)] | lia | lia]|];
          split; [exact (at_reg_atom_pi E4 _ _ _ 20%bv 11 _ HS ltac:(vm_compute; reflexivity)
                           (FR4 11%nat 11%bv ltac:(lia) eq_refl))|];
          split;
          [ rewrite (st_ok_pi_restrict_reg _ E4 ssx msc (21%bv : bv 5) HS),
              (st_ok_pi_restrict_reg _ E4 ssx msc (8%bv : bv 5) HS), (st_ok_pi_restrict_reg _ E4 ssx msc (22%bv : bv 5) HS);
            let e21 := eval vm_compute in (sr_get (ss_regs ssx) (21%bv : bv 5)) in
            change (sr_get (ss_regs ssx) (21%bv : bv 5)) with e21;
            let e8 := eval vm_compute in (sr_get (ss_regs ssx) (8%bv : bv 5)) in
            change (sr_get (ss_regs ssx) (8%bv : bv 5)) with e8;
            let e22 := eval vm_compute in (sr_get (ss_regs ssx) (22%bv : bv 5)) in
            change (sr_get (ss_regs ssx) (22%bv : bv 5)) with e22;
            reflexivity
          |];
          at_reg_val HS (22%bv : bv 5); unfold SHADOW_OFF in *; at_U
        | exact HJ2
        | repeat rewrite (proj1 (wvb_fds_fs _ _ _)); exact (proj1 FD2)
        | repeat rewrite (proj2 (wvb_fds_fs _ _ _)); exact (proj2 FD2)
        | apply (at_fields_entry cx (ms_mem msc) n0 1 HB0 (proj1 (proj2 HK4)));
          [ eapply (at_val_of_ss E4 ssx (w_H (c_W cx)) msc 0%nat 10 (c_w cx) 4096 4112 4096 4112 _ 4096 8);
            [ exact HS | reflexivity | exact W10 | cbn [In]; first [left; reflexivity | right; left; reflexivity]
            | apply at_denot; at_U | cbn; lia | cbn; lia ]
          | eapply (at_val_of_ss E4 ssx (w_H (c_W cx)) msc 0%nat 10 (c_w cx) 4096 4112 4096 4112 _ 4104 4);
            [ exact HS | reflexivity | exact W10 | cbn [In]; first [left; reflexivity | right; left; reflexivity]
            | apply at_denot; at_U | cbn; lia | cbn; lia ]
          | unfold NL_CHUNK_MAX; lia | lia ]
        | change (c_n0 cx) with n0; lia
        | lia
        | exact HK4 ]
      | cbn [ms_regs mkst]; at_reg_val HS (11%bv : bv 5); at_U ]
    end.
Qed.

End c.

(* THE TOP LEMMA, at the relro window PCAP_RLO / PCAP_RHI and generic in the sink head SK *)
Theorem attr_text_aproof : attr_text_acontract SK pa_segs PCAP_RLO PCAP_RHI B.
Proof.
unfold attr_text_acontract, aleaf_rd.
intros G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs HPRE HRD HP.
destruct HP as (bs & str & HNLW & HWF & Hs0 & HSTR & HSLEN & HSLACK & HAP & HAPF1 & HAPF2 &
  HMR1 & HRA1 & HHV1 & HMR2 & HRA2 & HHV2).
pose (cx := mkATCX G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs bs str).
assert (HB : at_base SK B PCAP_RLO PCAP_RHI cx)
  by exact (conj HPRE (conj HRD (conj HNLW (conj HWF (conj Hs0 (conj HSTR (conj HSLEN (conj HSLACK
    (conj HAP (conj HAPF1 (conj HAPF2 (conj HMR1 (conj HRA1 (conj HHV1 (conj HMR2 (conj HRA2 HHV2)))))))))))))))).
assert (HCFG : cfg_at pa_segs ATTR_TEXT_A regs memc mdc =
  mkCfg (mkst regs (Z_to_bv 64 (pa_val A_TEXT + AF_attr_text)) memc (seg_rom pa_segs)) mdc)
  by (unfold cfg_at; rewrite (lv_text LV); reflexivity).
rewrite HCFG.
exact (at_p0 PCAP_RLO PCAP_RHI cx HB).
Qed.

End b.
End a.

About attr_text_aproof.
Print Assumptions attr_text_aproof.
