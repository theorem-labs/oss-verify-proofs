(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libpcap/fuzz_pcap/lib/E2/Lib/Tac.v; 978 of its 1011 lines of code are new or changed and 2109 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/A4.v, with its module paths, module names, addresses and numbers changed; 2962 of its 3089 lines of code are new or changed and 884 lines of the source are left out. *)
(* Segment F36 of fuzz_ctrl LLVMFuzzerTestOneInput (asan, image A): 0x8289c-0x828d4 (plan-asan section 2 row F36,
   call CATM@0x828d4 = reac_box_catalogue_match by its contract; ubsan twin C04).  rule 24: no function proved.

   The segment has six entries (each pc that code outside the segment jumps to, and the join 0x828cc) and four exits
   (the row_of_block head 0x8286c with row i + 1, the matched-row cut 0x82964, the no-match cut 0x828bc and the
   call's return cut 0x828d8):
     0x8289c  beqz a0,82964     -- a0 is the bcmp wrapper's result of F35: 0 exactly when the block is row i's
                                  declaration.  Taken: exit 0x82964 (F38's range) with s4 = T + 296 i, which is
                                  row_of_block blk because the rows before i did not match.  Not taken: on to 0x828a0.
     0x828a0  sb s11,8(s3) .. sb s11,11(s3)   -- entered also from 0x82888 (F35): the four shadow bytes of the row
                                  slot [fr + 64, fr + 96);
              addi s8,s8,-1 ; addi s4,s4,296 ; bnez s8,8286c
                               -- s8 = 11 - i: row i + 1 at the row_of_block head 0x8286c (exit) when i < 10; for
                                  i = 10 no row matched (t_want_m = 0) and the run goes on to 0x828bc.
     0x828bc  li s4,0           -- entered also from 0x8285c / 0x82864 (F33): s4 = 0 = t_want_m.
     0x828c0  sb s11,4(s3) ; j 828cc   -- entered also from 0x82974 (F38): the shadow byte of the count at fr + 32.
     0x828c8  li s4,0           -- entered from 0x82804 / 0x82824 / 0x82844 (F32, row not selected): t_want_m = 0.
     0x828cc  mv a0,s7 ; mv a1,s2 ; jal reac_box_catalogue_match  -> exit 0x828d8 with a0 = t_want, s4 = t_want_m.

   The four and the one shadow stores change only shadow bytes of the frame (S(fr) + 8 .. 11, S(fr) + 4): FRA moves by
   Tac_slot.sl_fr_meta, the heap invariant by Tac_fs.a_fs_ok_store_AH, ENT by Tac_slot.ent_store; every other carried
   fact reads application memory, the image, bytes at or above HighMem, or the shadow of bytes outside the frame
   (f36_store_step).  The callee reads the 50 bytes at Phi and the 3256 catalogue bytes (both addressable), writes
   its own stack window [sp - 9136, sp), the side-stack bytes of the classes 0, 1, 2 and the shadow of its window;
   its side-stack premises (fp, the thread cells apart) are read off FRA (f36_fp_call), and its mem_inv premise is
   met on the normalized memory (f36_call_norm).

   Cuts: every cut is SlotInv.v's official Inv_A<pc>_at (bundles FLSI, FLS, FLSX, RL, LT of SlotInv.v); no cut or
   bundle is defined here.  seg_F36_828b8 also proves the block 0x82964-0x82974 from the cut 0x828d8, through
   0x828c0, and seg_F36_82810 proves the cut 0x828bc from the cut 0x828d8.  seg_F36_827f0 / seg_F36_827f4 (the
   assembly's S_F36_827f0 / S_F36_827f4) take the exit 0x828bc from 0x828d8 through seg_F36_82810; their _810 forms
   take it as a premise.

   v1.9 (libreac v1.9.0): every pc is the v1.8 one + 0xac and the cuts carry a Theorem Labs lane's v1.9 names (a working branch
   0a1d413d7c3); the seg_F36_* lemma NAMES keep their v1.8 pcs, so no caller changes.  PRO gains [A + 32] = fr + 2880
   as its 16th conjunct and FLC gains [A + 56] = fr + 2889 and [A + 48] = fr + 2890 as its 13th and 14th (both at the
   end); FSb takes fr and its positions 3 / 4 are the 35 body bytes at fr + 2880 and their addressability; the frame
   is FRAME_BYTES = 3136 bytes with 392 shadow bytes; frame_RELRO is the one range (0x9e348, 9344).
   v1.9 STATUS (2026-10-28): UNVERIFIED.  No build without probes has checked this file on v1.9.0.  It closed only in
   ITERATION-ONLY builds on the v1.9 bytes (FACTS 0bfe9aa0d452) with Seg/Tac_slot.v and Seg/Tac_fsfree.v probed; it
   waits for those two files' re-fit to the regenerated Contract.v / FrameAPI.v. *)
From Stdlib Require Import ZArith List Bool Lia Permutation Setoid.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT AsanRTInv AsanRTFacts PContract MemNorm
  AsanLift KindBGlue BzBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcParse RcIdentModel RcFrag RcMatch.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import SlotModel SlotInv RcAsanFP RcAsanFPLib
  asan_stack_malloc_c reac_box_catalogue_match_c reac_ctrl_parse_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require Import Tac_slot Tac_fs.
Import ListNotations.
(* The plain lib/Prog files the catalogue-match contract rests on also load lib/Reusable/YK11, so the short name
   YK11 is the plain one here; the slot's cuts are stated with the image-A one, which this alias names. *)
Module AYK := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.
Import AYK.
Open Scope Z_scope.

(* Proof speed (common.md (a working note, not in this delivery)): `lia` case-splits every disjunction and `mod` fact of the
   context; seg_F36_82820's post-call goals sit under ~150 hypotheses.  rs_hide_all wraps those in rs_hold, so lia
   no longer sees them; a use site unfolds rs_hold first.  Proofs only: no statement uses these names. *)
Definition rs_hold (A : Prop) : Prop := A.
Lemma rs_hide : forall A : Prop, A -> rs_hold A. Proof. intros A H. exact H. Qed.
Ltac rs_hide_all := repeat match goal with
  | H : _ \/ _ |- _ => apply rs_hide in H
  | H : _ mod _ = _ |- _ => apply rs_hide in H end.

Module AC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Contract.
Module AF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.FrameAPI.
Module LE := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Exec.

(* The wrapper cells the callee's contract names (bcmp_wrap_c's / memcmp_c's v1.9 values, as in F35; GOT_CF / CF /
   VERBOSITY come from asan_stack_malloc_c, which RcAsanFP's fp_tls is stated with). *)
Local Definition BCMP : Z := 0x97b0c.
Local Definition REAL_BCMP : Z := 0xa17f0.
Local Definition REAL_MEMCMP : Z := 0xa17e8.
Local Definition MEMCMP : Z := 0x97bdc.

(* ===================== pure helpers ===================== *)

(* A one-byte store of a register writes its low byte. *)
Lemma f36_le1_byte : forall v : word, le1 v = [Z_to_bv 8 (bv_unsigned v)].
Proof. intros v. unfold le1. cbn [Z_to_le_bytes]. reflexivity. Qed.

Lemma f36_ba_sub : forall m A bs k jj, bytes_at rsegs m A bs -> (k + jj <= length bs)%nat ->
  bytes_at rsegs m (A + Z.of_nat k) (firstn jj (skipn k bs)).
Proof.
  intros m A bs k jj (HA & HL & H) Hkj.
  assert (Lf : length (firstn jj (skipn k bs)) = jj) by (rewrite length_firstn, length_skipn; lia).
  split; [lia|]. split; [rewrite Lf; lia|].
  intros i Hi. rewrite Lf in Hi.
  replace (A + Z.of_nat k + Z.of_nat i) with (A + Z.of_nat (k + i)) by lia.
  rewrite H by lia. rewrite nth_error_firstn. destruct (Nat.ltb_spec0 i jj) as [_|C]; [|lia].
  rewrite nth_error_skipn. reflexivity.
Qed.

(* n bytes that are all present form a list. *)
Lemma f36_ba_present : forall m n a, 0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
  (forall i, (i < n)%nat -> exists b, mrd rsegs m (wa (a + Z.of_nat i)) = Some b) ->
  exists bs, bytes_at rsegs m a bs /\ length bs = n.
Proof.
  intros m n. induction n as [|n IH]; intros a Ha Hn H.
  - exists []. split; [|reflexivity]. split; [exact Ha|]. split; [cbn [length Z.of_nat]; lia|].
    intros i Hi. cbn [length] in Hi. lia.
  - destruct (H 0%nat ltac:(lia)) as (b0 & Hb0).
    assert (Hrest : forall i, (i < n)%nat -> exists b, mrd rsegs m (wa (a + 1 + Z.of_nat i)) = Some b).
    { intros i Hi. destruct (H (S i) ltac:(lia)) as (b & Hb). exists b.
      replace (a + 1 + Z.of_nat i) with (a + Z.of_nat (S i)) by lia. exact Hb. }
    destruct (IH (a + 1) ltac:(lia) ltac:(lia) Hrest) as (bs & (Ha' & Hl' & Hb') & Hlen).
    exists (b0 :: bs). split; [|cbn [length]; lia].
    split; [exact Ha|]. split; [cbn [length]; lia|].
    intros i Hi. destruct i as [|i].
    + cbn [nth_error]. exact Hb0.
    + cbn [nth_error]. replace (a + Z.of_nat (S i)) with (a + 1 + Z.of_nat i) by lia.
      apply Hb'. cbn [length] in Hi. lia.
Qed.

(* A present byte of a list read at its address. *)
Lemma f36_ba_some : forall m a bs i, bytes_at rsegs m a bs -> 0 <= i < Z.of_nat (length bs) ->
  exists b, mrd rsegs m (wa (a + i)) = Some b.
Proof.
  intros m a bs i (_ & _ & H) Hi.
  specialize (H (Z.to_nat i) ltac:(lia)). rewrite Z2Nat.id in H by lia. rewrite H.
  destruct (nth_error bs (Z.to_nat i)) as [b|] eqn:E; [exists b; reflexivity|].
  apply nth_error_None in E. lia.
Qed.

Lemma f36_sh_frame_of : forall fr k, 0 <= fr -> fr mod 8 = 0 -> 0 <= k ->
  shadow_addr (fr + 8 * k) = shadow_addr fr + k.
Proof. unfold shadow_addr. intros fr k H0 H8 Hk. Z.div_mod_to_equations. lia. Qed.

Lemma f36_sh_frame : forall fr y k, 0 <= fr -> fr mod 8 = 0 -> 0 <= y -> shadow_addr y = shadow_addr fr + k ->
  fr + 8 * k <= y < fr + 8 * k + 8.
Proof. unfold shadow_addr. intros fr y k H0 H8 Hy E. Z.div_mod_to_equations. lia. Qed.

Lemma f36_sh_mono : forall y z, y <= z -> shadow_addr y <= shadow_addr z.
Proof. intros y z H. unfold shadow_addr. Z.div_mod_to_equations. lia. Qed.

(* Below an 8-aligned bound, the shadow byte is below the bound's shadow byte. *)
Lemma f36_sh_lt : forall y z, z mod 8 = 0 -> y < z -> shadow_addr y < shadow_addr z.
Proof. intros y z H8 H. unfold shadow_addr. Z.div_mod_to_equations. lia. Qed.

(* A frame byte's shadow byte is one of the frame's 392 shadow bytes; the 6 bytes OUR at fr + 2624 share the
   shadow byte S(fr) + 328. *)
Lemma f36_sh_in_frame : forall fr x, 0 <= fr -> fr mod 8 = 0 -> fr <= x < fr + 3136 ->
  Sfr fr <= shadow_addr x < Sfr fr + 392.
Proof. intros fr x H0 H8 Hx. unfold Sfr, shadow_addr in *. Z.div_mod_to_equations. lia. Qed.

Lemma f36_sh_ours : forall fr i, 0 <= fr -> fr mod 8 = 0 -> 0 <= i < 6 ->
  shadow_addr (fr + 2624 + i) = Sfr fr + 328.
Proof. intros fr i H0 H8 Hi. unfold Sfr, shadow_addr in *. Z.div_mod_to_equations. lia. Qed.

(* The frame records [fr + 2688, fr + 2840) (the identity record at fr + 2688 with FLSH's 17-byte search window at
   fr + 2691, and the fragment record at fragb fr = fr + 2768; FLSH and FLC) have the shadow bytes S(fr) + 336 ..
   S(fr) + 354. *)
Lemma f36_sh_idr : forall fr i, 0 <= fr -> fr mod 8 = 0 -> 0 <= i < 152 ->
  Sfr fr + 336 <= shadow_addr (fr + 2688 + i) < Sfr fr + 355.
Proof. intros fr i H0 H8 Hi. unfold Sfr, shadow_addr in *. Z.div_mod_to_equations. lia. Qed.

Lemma f36_in_shadow_bnd : forall x, in_shadow x -> LOWMEM_END <= x < HIGHMEM_BEG.
Proof. unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG. intros; lia. Qed.

(* addressable survives writes apart from the shadow bytes of its range. *)
Lemma f36_addr_keep : forall W m m' p n, addressable m p n -> munch W m m' ->
  (forall i, 0 <= i < n -> outside W (shadow_addr (p + i))) -> addressable m' p n.
Proof.
  intros W m m' p n (H0 & Hn & He & HA) MU HW. split; [exact H0|]. split; [exact Hn|]. split; [exact He|].
  intros i Hi. destruct (HA i Hi) as (Hap & b & Hb & Hok). split; [exact Hap|]. exists b. split; [|exact Hok].
  pose proof (shadow_of_app (p + i) Hap) as Hs. pose proof (in_shadow_range _ Hs) as Hbd.
  unfold mrd in *. rewrite MU; [exact Hb|]. rewrite wa_unsigned by lia. apply HW. exact Hi.
Qed.

(* A range addressable byte by byte is addressable. *)
Lemma f36_addr_bytes : forall m lo n, 0 <= lo -> 0 <= n -> lo + n <= APPMEM_END ->
  (forall a, lo <= a < lo + n -> addressable m a 1) -> addressable m lo n.
Proof.
  intros m lo n Hlo Hn Hend H.
  split; [exact Hlo|]. split; [exact Hn|]. split; [exact Hend|].
  intros i Hi. destruct (H (lo + i) ltac:(lia)) as (_ & _ & _ & HA).
  pose proof (HA 0 ltac:(lia)) as H0. rewrite Z.add_0_r in H0. exact H0.
Qed.

Lemma f36_rg_mod : forall regs r a b, rg regs r a -> rg regs r b -> a mod 2 ^ 64 = b mod 2 ^ 64.
Proof.
  unfold rg. intros regs r a b Ha Hb. rewrite Ha in Hb. apply (f_equal bv_unsigned) in Hb.
  rewrite !Z_to_bv_unsigned in Hb. exact Hb.
Qed.

(* Two in-range values of one register are the same value. *)
Lemma f36_reg_eq : forall (regs : bvmap 5 word) (r : bv 5) a b,
  getr regs r = Z_to_bv 64 a -> getr regs r = Z_to_bv 64 b -> 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 -> a = b.
Proof.
  intros regs r a b Ha Hb Ra Rb.
  assert (E : Z_to_bv 64 a = Z_to_bv 64 b) by congruence.
  apply (f_equal (bv_unsigned (n := 64))) in E. rewrite !unsigned_lit in E by lia. exact E.
Qed.

(* A readable-and-writable stack window survives a run that keeps every byte of it backed. *)
Lemma f36_stk_tr : forall W m m' lo hi, stk rsegs m lo hi -> munch W m m' -> wmono rsegs m m' ->
  (forall x, lo <= x < hi -> outside W x \/ exists b, mrd rsegs m' (wa x) = Some b) -> stk rsegs m' lo hi.
Proof.
  intros W m m' lo hi (H1 & H2 & H) MU WM Hc. split; [lia|]. split; [lia|].
  intros a Ha. destruct (H a Ha) as (Hw & b & Hb). split; [exact (WM _ Hw)|].
  destruct (Hc a Ha) as [Ho|Hr]; [|exact Hr].
  exists b. unfold mrd in *. rewrite (MU (wa a)); [exact Hb|].
  rewrite wa_unsigned by lia. exact Ho.
Qed.

(* A value of s1 within 416 bytes of the spill base A (both read through rg) is A. *)
Lemma f36_rg_near : forall (regs : bvmap 5 word) (r : bv 5) a b, rg regs r a -> rg regs r b ->
  416 <= a -> a + 416 <= 2 ^ 64 -> -400 <= b -> b + 8 <= 2 ^ 64 -> b = a.
Proof.
  intros regs r a b Ha Hb H1 H2 H3 H4.
  pose proof (f36_rg_mod regs r b a Hb Ha) as E. rewrite (Z.mod_small a) in E by lia.
  pose proof (Z.div_mod b (2 ^ 64) ltac:(lia)) as D. rewrite E in D. lia.
Qed.

(* The thread-pointer word read in m' is the one of m when the run kept its 8 bytes. *)
Lemma f36_word_mem_back : forall W m m' a v, munch W m m' ->
  (forall x, a <= x < a + 8 -> outside W (bv_unsigned (Z_to_bv 64 x))) ->
  word_mem rsegs m' a v -> word_mem rsegs m a v.
Proof.
  intros W m m' a v MU HW H k Hk. rewrite <- (H k Hk). unfold mbyte.
  rewrite (MU (Z_to_bv 64 (a + Z.of_nat k))); [reflexivity|]. apply HW. lia.
Qed.

(* The side stack's metadata cells lie in its first 36864 bytes. *)
Lemma f36_fs_meta_ge : forall FS q, fs_meta FS q -> FS <= q.
Proof.
  intros FS q H. unfold fs_meta in H.
  destruct H as [H | [H | [[c [Hc Hr]] | [c [jj [Hc [Hj Heq]]]]]]].
  - lia.
  - lia.
  - unfold AC.a_fs_hint in Hr. lia.
  - subst q. pose proof (a_fs_flag_range FS c jj Hc Hj). lia.
Qed.

(* The registered globals (AF.frame_AG) lie in [0x21140, 0x9f8e8), below the image top GT. *)
Lemma f36_ag_bound : forall a, in_globals AF.frame_AG a -> 0x21140 <= a < 0x9f8e8.
Proof.
  intros a (lo & len & Hil & Hr). unfold AF.frame_AG in Hil. cbn [In] in Hil.
  repeat (destruct Hil as [E | Hil]; [injection E as <- <-; lia |]). destruct Hil.
Qed.

(* A registered global of frame_AG is addressable over its whole length (AGc is per byte). *)
Lemma f36_ag_addr : forall (m : word -> option byte) lo len,
  (forall a, in_globals AF.frame_AG a -> addressable m a 1) ->
  In (lo, len) AF.frame_AG -> 0 <= lo -> 0 <= len -> lo + len <= APPMEM_END ->
  addressable m lo len.
Proof.
  intros m lo len HAG Hin Hlo Hlen Hend.
  apply f36_addr_bytes; [exact Hlo | exact Hlen | exact Hend |].
  intros a Ha. apply HAG. exists lo, len. split; [exact Hin | lia].
Qed.

Lemma f36_eqb_lit : forall x y, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 ->
  bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y) = (x =? y).
Proof. intros x y Hx Hy. unfold bv_eqb. rewrite !unsigned_lit by lia. reflexivity. Qed.

(* A branch arm the facts in context exclude. *)
Ltac f36_bad HC :=
  exfalso;
  first [ congruence
        | discriminate HC
        | (rewrite ?f36_eqb_lit in HC by lia; cbn [negb] in HC;
           first [ (apply Bool.negb_true_iff in HC; apply Z.eqb_neq in HC; lia)
                 | (apply Bool.negb_false_iff in HC; apply Z.eqb_eq in HC; lia)
                 | (apply Z.eqb_eq in HC; lia) | (apply Z.eqb_neq in HC; lia) ])
        | (vm_compute in HC; discriminate HC) ].
Ltac f36_nt := let H := fresh "HC" in first [ if_cases H; [f36_bad H | clear H] | idtac ].
Ltac f36_tk := let H := fresh "HC" in first [ if_cases H; [clear H | f36_bad H] | idtac ].

(* ===================== model facts of turn j ===================== *)

Lemma f36_bz_range : forall b : byte, 0 <= bz b < 256.
Proof.
  intros b. unfold bz. pose proof (bv_unsigned_in_range 8 b) as H. unfold bv_modulus in H.
  change (2 ^ Z.of_N 8) with 256 in H. exact H.
Qed.

Lemma f36_fL_nonneg : forall inp c, 0 <= f_L inp c.
Proof.
  intros inp c. unfold f_L, inb.
  pose proof (f36_bz_range (nthb inp (Z.to_nat c))). pose proof (f36_bz_range (nthb inp (Z.to_nat (c + 1)))).
  destruct (2 <=? f_left inp c); lia.
Qed.

Lemma f36_fc_range : forall inp j, 0 <= fc inp j <= nlen inp.
Proof.
  intros inp j. induction j as [|j IH].
  - cbn [fc]. unfold c0, nlen. lia.
  - change (fc inp (S j)) with (f_next inp (fc inp j)). pose proof (f36_fL_nonneg inp (fc inp j)).
    unfold f_next, f_body, f_len, f_h, f_left in *. lia.
Qed.

Lemma f36_t_facts : forall inp j,
  0 <= t_c inp j <= nlen inp /\ t_left inp j = nlen inp - t_c inp j /\
  0 <= t_h inp j <= t_left inp j /\ 0 <= t_len inp j <= t_left inp j - t_h inp j /\
  t_body inp j = t_c inp j + t_h inp j.
Proof.
  intros inp j. pose proof (f36_fc_range inp j) as R. pose proof (f36_fL_nonneg inp (fc inp j)) as L.
  unfold t_c, t_left, t_h, t_len, t_body. unfold f_body, f_len, f_h, f_left in *. lia.
Qed.

Lemma f36_len_nonneg : forall inp j, 0 <= t_len inp j.
Proof. intros inp j. pose proof (f36_t_facts inp j) as (_ & _ & _ & (H & _) & _). exact H. Qed.

Lemma f36_phi_length : forall inp j, length (t_phi inp j) = Z.to_nat (t_len inp j).
Proof.
  intros inp j. pose proof (f36_t_facts inp j) as (R & EL & (H1 & H2) & (H3 & H4) & EB).
  unfold t_phi, f_phi. rewrite length_firstn, length_skipn.
  change (f_len inp (fc inp j)) with (t_len inp j). change (f_body inp (fc inp j)) with (t_body inp j).
  unfold nlen in *. lia.
Qed.

Lemma f36_phi_lenZ : forall inp j, Z.of_nat (length (t_phi inp j)) = t_len inp j.
Proof. intros inp j. rewrite f36_phi_length. apply Z2Nat.id. apply f36_len_nonneg. Qed.

Lemma f36_fr50_firstn : forall bs, (50 <= length bs)%nat -> fr50 bs = firstn 50 bs.
Proof.
  intros bs H. unfold fr50. rewrite firstn_app.
  replace (50 - length bs)%nat with 0%nat by lia. cbn [firstn]. apply app_nil_r.
Qed.

(* With len >= 50 the 50 bytes t_g of turn j are the first 50 bytes of Phi. *)
Lemma f36_tg_bytes : forall m phi inp j, 50 <= t_len inp j -> bytes_at rsegs m phi (t_phi inp j) ->
  bytes_at rsegs m phi (t_g inp j).
Proof.
  intros m phi inp j H50 Hb. unfold t_g.
  rewrite f36_fr50_firstn by (rewrite f36_phi_length; lia).
  pose proof (f36_ba_sub m phi (t_phi inp j) 0 50 Hb ltac:(rewrite f36_phi_length; lia)) as Hs.
  rewrite Z.add_0_r, skipn_O in Hs. exact Hs.
Qed.

(* row_of_block: the first matching row, or 0. *)
Lemma f36_rob_hit : forall blk fuel k i, (k <= i < k + fuel)%nat ->
  (forall i', (k <= i' < i)%nat -> decl_i (Z.of_nat i') <> blk) -> decl_i (Z.of_nat i) = blk ->
  rob blk k fuel = CAT + CAT_ROW * Z.of_nat i.
Proof.
  intros blk fuel. induction fuel as [|f IH]; intros k i Hk Hprev Hi; [lia|].
  cbn [rob]. destruct (bool_decide (decl_i (Z.of_nat k) = blk)) eqn:E.
  - apply bool_decide_eq_true in E. destruct (Nat.eq_dec k i) as [->|Hne]; [reflexivity|].
    exfalso. apply (Hprev k); [lia | exact E].
  - apply bool_decide_eq_false in E. apply IH; [| intros i' Hi'; apply Hprev; lia | exact Hi].
    destruct (Nat.eq_dec k i) as [->|Hne]; [exfalso; apply E; exact Hi | lia].
Qed.

Lemma f36_rob_miss : forall blk fuel k, (forall i', (k <= i' < k + fuel)%nat -> decl_i (Z.of_nat i') <> blk) ->
  rob blk k fuel = 0.
Proof.
  intros blk fuel. induction fuel as [|f IH]; intros k H; [reflexivity|].
  cbn [rob]. destruct (bool_decide (decl_i (Z.of_nat k) = blk)) eqn:E.
  - apply bool_decide_eq_true in E. exfalso. exact (H k ltac:(lia) E).
  - apply IH. intros i' Hi'. apply H. lia.
Qed.

Lemma f36_want_m_hit : forall inp j i, t_rowsel inp j = true -> (i <= 10)%nat ->
  (forall i', (i' < i)%nat -> t_blk inp j <> decl_i (Z.of_nat i')) -> t_blk inp j = decl_i (Z.of_nat i) ->
  t_want_m inp j = CAT + CAT_ROW * Z.of_nat i.
Proof.
  intros inp j i Hsel Hi Hprev Hhit. unfold t_want_m, row_of_block. rewrite Hsel.
  apply f36_rob_hit; [lia | | symmetry; exact Hhit].
  intros i' Hi' E. apply (Hprev i'); [lia | symmetry; exact E].
Qed.

Lemma f36_want_m_miss : forall inp j, t_rowsel inp j = true ->
  (forall i', (i' < 11)%nat -> t_blk inp j <> decl_i (Z.of_nat i')) -> t_want_m inp j = 0.
Proof.
  intros inp j Hsel H. unfold t_want_m, row_of_block. rewrite Hsel.
  apply f36_rob_miss. intros i' Hi' E. apply (H i'); [lia | symmetry; exact E].
Qed.

Lemma f36_want_m_unsel : forall inp j, t_rowsel inp j = false -> t_want_m inp j = 0.
Proof. intros inp j H. unfold t_want_m. rewrite H. reflexivity. Qed.

(* ===================== the machine runs ===================== *)

(* 0x8289c with a0 = 0: beqz is taken to 0x82964. *)
Lemma f36_evt_hit :
  forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
          x26 x27 x28 x29 x30 x31 : word) (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
    x10 = Z_to_bv 64 0 ->
    LE.evt rsegs
      (fun ms' => ms' = MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23
                              x24 x25 x26 x27 x28 x29 x30 x31) Fr (Z_to_bv 64 0x82964) fc None m (seg_rom rsegs))
      (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26
               x27 x28 x29 x30 x31) Fr (Z_to_bv 64 0x8289c) fc None m (seg_rom rsegs)).
Proof.
  intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
    x26 x27 x28 x29 x30 x31 Fr fc m E10. subst x10.
  step. f36_tk. apply evt_done. reflexivity.
Qed.

(* 0x8289c with a0 = v <> 0: beqz is not taken; the run is at 0x828a0. *)
Lemma f36_evt_miss :
  forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
          x26 x27 x28 x29 x30 x31 : word) (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (v : Z),
    x10 = Z_to_bv 64 v -> 0 < v < 2 ^ 64 ->
    LE.evt rsegs
      (fun ms' => ms' = MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23
                              x24 x25 x26 x27 x28 x29 x30 x31) Fr (Z_to_bv 64 0x828a0) fc None m (seg_rom rsegs))
      (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26
               x27 x28 x29 x30 x31) Fr (Z_to_bv 64 0x8289c) fc None m (seg_rom rsegs)).
Proof.
  intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
    x26 x27 x28 x29 x30 x31 Fr fc m v E10 Hv. subst x10.
  step. f36_nt. apply evt_done. reflexivity.
Qed.

(* 0x828a0 -> 0x828b8: the four shadow stores to S3 + 8 .. S3 + 11, s8 = c - 1, s4 = s + 296; with c >= 2 the
   back branch is taken to 0x8286c. *)
Lemma f36_evt_back :
  forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
          x26 x27 x28 x29 x30 x31 : word) (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (S3 c s : Z) (bs : list byte),
    x19 = Z_to_bv 64 S3 -> x24 = Z_to_bv 64 c -> x20 = Z_to_bv 64 s ->
    2 <= c <= 11 -> 0 <= s -> s + 296 < 2 ^ 64 ->
    rw_cells rsegs m (S3 + 8) [CB 4 bs] -> 0 <= S3 -> S3 + 12 <= 2 ^ 64 ->
    LE.evt rsegs
      (fun ms' => exists m', ms' = MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19
                                          (Z_to_bv 64 (s + 296)) x21 x22 x23 (Z_to_bv 64 (c - 1)) x25 x26 x27 x28
                                          x29 x30 x31)
                                     Fr (Z_to_bv 64 0x8286c) fc None m' (seg_rom rsegs) /\
         munch [(S3 + 8, S3 + 12)] m m' /\ wmono rsegs m m' /\
         exists cs, rw_cells rsegs m' (S3 + 8) cs /\ cells_size cs = 4%nat)
      (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26
               x27 x28 x29 x30 x31) Fr (Z_to_bv 64 0x828a0) fc None m (seg_rom rsegs)).
Proof.
  intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
    x26 x27 x28 x29 x30 x31 Fr fc m S3 c s bs -> -> -> Hc Hs0 Hs1 HRW H0 H1.
  pose proof (munch_refl [(S3 + 8, S3 + 12)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  step. rewrite f36_le1_byte. mem_after_store.
  step. rewrite f36_le1_byte. mem_after_store.
  step. rewrite f36_le1_byte. mem_after_store.
  step. rewrite f36_le1_byte. mem_after_store.
  step. step. step. f36_tk.
  match goal with |- LE.evt _ _ (MS _ _ _ _ _ ?mm _) =>
    match goal with H : rw_cells rsegs mm (S3 + 8) ?cs |- _ =>
      apply evt_done; exists mm; split; [reflexivity|];
      split; [assumption|]; split; [assumption|];
      exists cs; split; [exact H | reflexivity]
    end
  end.
Qed.

(* The same run with c = 1 (the last row): the back branch falls through to 0x828bc. *)
Lemma f36_evt_out :
  forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
          x26 x27 x28 x29 x30 x31 : word) (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (S3 s : Z) (bs : list byte),
    x19 = Z_to_bv 64 S3 -> x24 = Z_to_bv 64 1 -> x20 = Z_to_bv 64 s ->
    0 <= s -> s + 296 < 2 ^ 64 ->
    rw_cells rsegs m (S3 + 8) [CB 4 bs] -> 0 <= S3 -> S3 + 12 <= 2 ^ 64 ->
    LE.evt rsegs
      (fun ms' => exists m', ms' = MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19
                                          (Z_to_bv 64 (s + 296)) x21 x22 x23 (Z_to_bv 64 0) x25 x26 x27 x28
                                          x29 x30 x31)
                                     Fr (Z_to_bv 64 0x828bc) fc None m' (seg_rom rsegs) /\
         munch [(S3 + 8, S3 + 12)] m m' /\ wmono rsegs m m' /\
         exists cs, rw_cells rsegs m' (S3 + 8) cs /\ cells_size cs = 4%nat)
      (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26
               x27 x28 x29 x30 x31) Fr (Z_to_bv 64 0x828a0) fc None m (seg_rom rsegs)).
Proof.
  intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
    x26 x27 x28 x29 x30 x31 Fr fc m S3 s bs -> -> -> Hs0 Hs1 HRW H0 H1.
  pose proof (munch_refl [(S3 + 8, S3 + 12)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  step. rewrite f36_le1_byte. mem_after_store.
  step. rewrite f36_le1_byte. mem_after_store.
  step. rewrite f36_le1_byte. mem_after_store.
  step. rewrite f36_le1_byte. mem_after_store.
  step. step. step. f36_nt.
  match goal with |- LE.evt _ _ (MS _ _ _ _ _ ?mm _) =>
    match goal with H : rw_cells rsegs mm (S3 + 8) ?cs |- _ =>
      apply evt_done; exists mm; split; [reflexivity|];
      split; [assumption|]; split; [assumption|];
      exists cs; split; [exact H | reflexivity]
    end
  end.
Qed.

(* 0x828bc li s4,0 -> 0x828c0. *)
Lemma f36_evt_82810 :
  forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
          x26 x27 x28 x29 x30 x31 : word) (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
    LE.evt rsegs
      (fun ms' => ms' = MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 (Z_to_bv 64 0)
                              x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) Fr (Z_to_bv 64 0x828c0) fc None m
                           (seg_rom rsegs))
      (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26
               x27 x28 x29 x30 x31) Fr (Z_to_bv 64 0x828bc) fc None m (seg_rom rsegs)).
Proof. intros. step. apply evt_done. reflexivity. Qed.

(* 0x828c8 li s4,0 -> 0x828cc. *)
Lemma f36_evt_8281c :
  forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
          x26 x27 x28 x29 x30 x31 : word) (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
    LE.evt rsegs
      (fun ms' => ms' = MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 (Z_to_bv 64 0)
                              x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) Fr (Z_to_bv 64 0x828cc) fc None m
                           (seg_rom rsegs))
      (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26
               x27 x28 x29 x30 x31) Fr (Z_to_bv 64 0x828c8) fc None m (seg_rom rsegs)).
Proof. intros. step. apply evt_done. reflexivity. Qed.

(* 0x828c0 sb s11,4(s3) ; j 828cc: the shadow byte S3 + 4. *)
Lemma f36_evt_82814 :
  forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
          x26 x27 x28 x29 x30 x31 : word) (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (S3 : Z) (bs : list byte),
    x19 = Z_to_bv 64 S3 -> rw_cells rsegs m (S3 + 4) [CB 1 bs] ->
    0 <= S3 -> S3 + 5 <= 2 ^ 64 ->
    LE.evt rsegs
      (fun ms' => exists m', ms' = MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20
                                          x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                                     Fr (Z_to_bv 64 0x828cc) fc None m' (seg_rom rsegs) /\
         munch [(S3 + 4, S3 + 5)] m m' /\ wmono rsegs m m' /\
         exists cs, rw_cells rsegs m' (S3 + 4) cs /\ cells_size cs = 1%nat)
      (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26
               x27 x28 x29 x30 x31) Fr (Z_to_bv 64 0x828c0) fc None m (seg_rom rsegs)).
Proof.
  intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
    x26 x27 x28 x29 x30 x31 Fr fc m S3 bs -> HRW H0 H1.
  pose proof (munch_refl [(S3 + 4, S3 + 5)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  step. rewrite f36_le1_byte. mem_after_store.
  step.
  match goal with |- LE.evt _ _ (MS _ _ _ _ _ ?mm _) =>
    match goal with H : rw_cells rsegs mm (S3 + 4) ?cs |- _ =>
      apply evt_done; exists mm; split; [reflexivity|];
      split; [assumption|]; split; [assumption|];
      exists cs; split; [exact H | reflexivity]
    end
  end.
Qed.

(* 0x82964 sb s11,8(s3) .. sb s11,11(s3) ; j 828c0: the row-matched arm marks the row slot's four shadow bytes
   (F38 leaves the block 0x82964-0x82974 to this segment). *)
Lemma f36_evt_828b8 :
  forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
          x26 x27 x28 x29 x30 x31 : word) (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (S3 : Z) (bs : list byte),
    x19 = Z_to_bv 64 S3 -> rw_cells rsegs m (S3 + 8) [CB 4 bs] -> 0 <= S3 -> S3 + 12 <= 2 ^ 64 ->
    LE.evt rsegs
      (fun ms' => exists m', ms' = MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20
                                          x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                                     Fr (Z_to_bv 64 0x828c0) fc None m' (seg_rom rsegs) /\
         munch [(S3 + 8, S3 + 12)] m m' /\ wmono rsegs m m' /\
         exists cs, rw_cells rsegs m' (S3 + 8) cs /\ cells_size cs = 4%nat)
      (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26
               x27 x28 x29 x30 x31) Fr (Z_to_bv 64 0x82964) fc None m (seg_rom rsegs)).
Proof.
  intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
    x26 x27 x28 x29 x30 x31 Fr fc m S3 bs -> HRW H0 H1.
  pose proof (munch_refl [(S3 + 8, S3 + 12)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  step. rewrite f36_le1_byte. mem_after_store.
  step. rewrite f36_le1_byte. mem_after_store.
  step. rewrite f36_le1_byte. mem_after_store.
  step. rewrite f36_le1_byte. mem_after_store.
  step.
  match goal with |- LE.evt _ _ (MS _ _ _ _ _ ?mm _) =>
    match goal with H : rw_cells rsegs mm (S3 + 8) ?cs |- _ =>
      apply evt_done; exists mm; split; [reflexivity|];
      split; [assumption|]; split; [assumption|];
      exists cs; split; [exact H | reflexivity]
    end
  end.
Qed.

(* The call's write set: the callee's stack window, the class-0/1/2 side-stack bytes and the window's shadow (the
   munch of reac_box_catalogue_match_contract). *)
Definition f36_W (S FS : Z) : list ivl :=
  [(S - CM_K, S)] ++ fp_w [0%nat; 1%nat; 2%nat] FS ++ [(shadow_addr (S - CM_K), shadow_addr S)].

(* 0x828cc mv a0,s7 ; mv a1,s2 ; jal reac_box_catalogue_match -> 0x828d8, by the callee's contract. *)
Lemma f36_evt_call : reac_box_catalogue_match_contract ->
  forall (ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (phi len S FS : Z) (fb : list byte),
    s7 = Z_to_bv 64 phi -> s2 = Z_to_bv 64 len -> sp = Z_to_bv 64 S ->
    0 <= phi < 2 ^ 64 -> 0 <= len < 2 ^ 64 -> S < 2 ^ 64 -> S mod 16 = 0 ->
    CM_K <= S -> stk rsegs m (S - CM_K) S ->
    (forall a, S - CM_K <= a < S -> seg_rom rsegs (wa a) = None) ->
    length fb = 50%nat ->
    (50 <= len -> 0 < phi /\ phi + 50 <= 2 ^ 64 /\ bytes_at rsegs m phi fb /\ (phi + 50 <= S - CM_K \/ S <= phi)) ->
    (forall a, CM_T <= a < CM_T + 3256 -> mrd rsegs m (wa a) = seg_rom rsegs (wa a)) ->
    mem_inv rsegs m -> asan_cells m -> shadow_rw m ->
    HIGHMEM_BEG <= S - CM_K -> S <= APPMEM_END -> addressable m (S - CM_K) CM_K ->
    (50 <= len -> addressable m phi 50 /\ app_mem (phi + 50)) ->
    addressable m CM_T 3256 -> addressable m REAC_CTRL_PARSE_BC 6 ->
    bytes_at rsegs m REAL_BCMP (le8 (wa BCMP)) -> bytes_at rsegs m REAL_MEMCMP (le8 (wa MEMCMP)) ->
    bytes_at rsegs m GOT_CF (le8 (wa CF)) ->
    bytes_at rsegs m (CF + 254) [Z_to_bv 8 1] -> bytes_at rsegs m (CF + 255) [Z_to_bv 8 1] ->
    fp [0%nat; 1%nat; 2%nat] m (bv_unsigned tp) FS (S - CM_K) S (reac_box_catalogue_match_W S)
      (reac_box_catalogue_match_D phi len) ->
    reac_box_catalogue_match_tls m (bv_unsigned tp) FS (S - CM_K) S ->
    LE.evt rsegs
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                         (m' : word -> option byte),
         ms' = MS (mkR (Z_to_bv 64 0x828d8) sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (want CM_T len fb))
                       a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (Z_to_bv 64 0x828d8) fc None m' (seg_rom rsegs) /\
         munch (f36_W S FS) m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' (S - CM_K) S /\
         asan_cells m' /\ shadow_rw m' /\ addressable m' (S - CM_K) CM_K /\
         fp [0%nat; 1%nat; 2%nat] m' (bv_unsigned tp) FS (S - CM_K) S (reac_box_catalogue_match_W S)
            (reac_box_catalogue_match_D phi len))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x828cc) fc None m (seg_rom rsegs)).
Proof.
  intros CMC ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m phi len S FS fb -> -> -> Hphi Hlen HS Hmod HKS HST HROM Hfb HFB HROc HMI HAC HSW
    Hhi Hsp HADW HADf HADT HADB HRB HRM HGC HC254 HC255 HFP HTLS.
  step. (* 0x828cc mv a0,s7 *)
  step. (* 0x828d0 mv a1,s2 *)
  step. (* 0x828d4 jal 843d0 <reac_box_catalogue_match> *)
  pose proof CMC as HC. unfold reac_box_catalogue_match_contract, REAC_BOX_CATALOGUE_MATCH in HC.
  eapply evt_cut.
  { eapply HC with (f := phi) (len := len) (S := S) (FS := FS) (fb := fb).
    all: cbv zeta.
    all: first [ exact HST | exact HROM | exact Hfb | exact HFB | exact HROc | exact HMI | exact HAC | exact HSW
               | exact HADW | exact HADf | exact HADT | exact HADB | exact HRB | exact HRM | exact HGC
               | exact HC254 | exact HC255 | exact HFP | exact HTLS | exact Hmod
               | reflexivity | (f_equal; lia) | lia ]. }
  intros ms' PO.
  destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
                  E & MU & WM & MI' & ST' & AC' & SW' & AD' & FP' & TL').
  subst ms'.
  lazymatch goal with
  | |- LE.evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?k)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 k)) with (Z_to_bv 64 k) by (symmetry; apply ret_pc_even; [ lia | reflexivity ])
  end.
  apply evt_done. cbv beta. do 15 eexists.
  split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI'|]. split; [exact ST'|].
  split; [exact AC'|]. split; [exact SW'|]. split; [exact AD' | exact FP'].
Qed.

(* ===================== the call on the normalized memory ===================== *)

(* The callee's contract asks mem_inv of the caller's memory; a cut carries only ro_agree (FRA, push 5b).  The run
   is made on the normalized memory (MemNorm.evt_normalize, as SlotInv.v:165-166 says), and every premise and
   every post fact moves across mem_rel: they read bytes through mrd (equal everywhere, mrd_rel) and the
   writability of bytes at or above GT = 0x5fe000 (no read-only byte is there, f36_ro_lo). *)
Local Definition f36_tops (segs : list Segment) (top : Z) : bool :=
  forallb (fun s => Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? top) segs.

Local Lemma f36_rsegs_top : f36_tops rsegs 0x5fe000 = true.
Proof. vm_compute. reflexivity. Qed.

Local Lemma f36_find_below : forall segs top x n s,
  f36_tops segs top = true -> find_segment segs x n = Some s -> 0 <= n -> x < top \/ n = 0.
Proof.
  induction segs as [|s0 r IH]; intros top x n s Hb H Hn; cbn in H; [discriminate H|].
  unfold f36_tops in Hb. cbn [forallb] in Hb. apply andb_prop in Hb as [H0 Hr].
  apply Z.leb_le in H0.
  destruct (Z.leb (Z.of_N (seg_base s0)) x && Z.leb (x + n) (Z.of_N (seg_base s0) + Z.of_N (seg_size s0))) eqn:E.
  - apply andb_prop in E as [_ E]. apply Z.leb_le in E. lia.
  - exact (IH top x n s Hr H Hn).
Qed.

Lemma f36_ro_lo : forall a : word, ro_addr rsegs a = true -> bv_unsigned a < 0x5fe000.
Proof.
  intros a H. unfold ro_addr in H.
  destruct (find_segment rsegs (bv_unsigned a) 1) as [s|] eqn:E; [|discriminate H].
  destruct (f36_find_below rsegs 0x5fe000 (bv_unsigned a) 1 s f36_rsegs_top E ltac:(lia)) as [L|L];
    [exact L | discriminate L].
Qed.

Lemma f36_ro_false : forall a, 0x5fe000 <= a < 2 ^ 64 -> ro_addr rsegs (wa a) = false.
Proof.
  intros a Ha. destruct (ro_addr rsegs (wa a)) eqn:E; [|reflexivity].
  pose proof (f36_ro_lo _ E) as L. rewrite wa_unsigned in L by lia. lia.
Qed.

Lemma f36_stk_rel : forall m m0 lo hi, mem_rel rsegs m m0 -> 0x5fe000 <= lo ->
  (stk rsegs m lo hi <-> stk rsegs m0 lo hi).
Proof.
  intros m m0 lo hi R Hlo.
  split; intros (H0 & H1 & H); (split; [exact H0|]); (split; [exact H1|]); intros a Ha;
    destruct (H a Ha) as (Hw & b & Hb);
    (assert (E : ro_addr rsegs (wa a) = false) by (apply f36_ro_false; lia)).
  - split; [rewrite (wview_rel_rw rsegs m m0 _ R E); exact Hw|].
    exists b. rewrite <- (mrd_rel rsegs m m0 _ R). exact Hb.
  - split; [rewrite <- (wview_rel_rw rsegs m m0 _ R E); exact Hw|].
    exists b. rewrite (mrd_rel rsegs m m0 _ R). exact Hb.
Qed.

Lemma f36_srw_rel : forall m m0, mem_rel rsegs m m0 -> (shadow_rw m <-> shadow_rw m0).
Proof.
  intros m m0 R. unfold shadow_rw.
  split; intros H a Ha; destruct (H a Ha) as (Hw & b & Hb);
    (assert (E : ro_addr rsegs (wa a) = false)
       by (apply f36_ro_false; unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Ha;
           lia)).
  - split; [rewrite (wview_rel_rw rsegs m m0 _ R E); exact Hw|].
    exists b. rewrite <- (mrd_rel rsegs m m0 _ R). exact Hb.
  - split; [rewrite <- (wview_rel_rw rsegs m m0 _ R E); exact Hw|].
    exists b. rewrite (mrd_rel rsegs m m0 _ R). exact Hb.
Qed.

Lemma f36_addr_rel : forall m m0 p n, mem_rel rsegs m m0 -> (addressable m p n <-> addressable m0 p n).
Proof.
  intros m m0 p n R.
  assert (MR : forall a, mrd rsegs m a = mrd rsegs m0 a) by (intros a; exact (mrd_rel rsegs m m0 a R)).
  unfold addressable, addr_byte. setoid_rewrite MR. reflexivity.
Qed.

Lemma f36_cells_rel : forall m m0, mem_rel rsegs m m0 -> (asan_cells m <-> asan_cells m0).
Proof.
  intros m m0 R.
  assert (BR : forall a bs, bytes_at rsegs m a bs <-> bytes_at rsegs m0 a bs)
    by (intros a bs; exact (bytes_at_rel rsegs m m0 a bs R)).
  unfold asan_cells. setoid_rewrite BR. reflexivity.
Qed.

Lemma f36_tls_rel : forall m m0 TP DT TS C T DB k, mem_rel rsegs m m0 ->
  (asan_tls_cells m TP DT TS C T DB k <-> asan_tls_cells m0 TP DT TS C T DB k).
Proof.
  intros m m0 TP DT TS C T DB k R.
  assert (BR : forall a bs, bytes_at rsegs m a bs <-> bytes_at rsegs m0 a bs)
    by (intros a bs; exact (bytes_at_rel rsegs m m0 a bs R)).
  unfold asan_tls_cells. setoid_rewrite BR. reflexivity.
Qed.

Lemma f36_fp_rel : forall cs m m0 TP FS lo hi W D, mem_rel rsegs m m0 ->
  (fp cs m TP FS lo hi W D <-> fp cs m0 TP FS lo hi W D).
Proof.
  intros cs m m0 TP FS lo hi W D R.
  assert (BR : forall a bs, bytes_at rsegs m a bs <-> bytes_at rsegs m0 a bs)
    by (intros a bs; exact (bytes_at_rel rsegs m m0 a bs R)).
  assert (CR : forall c, fp_cls m FS c <-> fp_cls m0 FS c)
    by (intros c; unfold fp_cls; setoid_rewrite BR; reflexivity).
  assert (FR : Forall (fp_cls m FS) cs <-> Forall (fp_cls m0 FS) cs)
    by (split; apply Forall_impl; intros c; apply CR).
  assert (PR : fs_place m FS <-> fs_place m0 FS).
  { unfold fs_place. split; intros (H1 & H2 & H3 & H4 & H5);
      (split; [exact H1|]); (split; [exact H2|]); (split; [exact H3|]); (split; [exact H4|]).
    - apply (proj1 (f36_stk_rel m m0 FS (FS + FS_SIZE) R ltac:(unfold ASAN_GT in H3; lia))). exact H5.
    - apply (proj2 (f36_stk_rel m m0 FS (FS + FS_SIZE) R ltac:(unfold ASAN_GT in H3; lia))). exact H5. }
  unfold fp. split; intros (DT & TS & C & T & DB & k & HT & HB1 & HP & HB2 & HB3 & HC & Hrest);
    exists DT, TS, C, T, DB, k.
  - split; [apply (f36_tls_rel m m0 _ _ _ _ _ _ _ R); exact HT|].
    split; [apply BR; exact HB1|]. split; [apply PR; exact HP|].
    split; [apply BR; exact HB2|]. split; [apply BR; exact HB3|].
    split; [apply FR; exact HC | exact Hrest].
  - split; [apply (f36_tls_rel m m0 _ _ _ _ _ _ _ R); exact HT|].
    split; [apply BR; exact HB1|]. split; [apply PR; exact HP|].
    split; [apply BR; exact HB2|]. split; [apply BR; exact HB3|].
    split; [apply FR; exact HC | exact Hrest].
Qed.

Lemma f36_cmtls_rel : forall m m0 TP FS lo hi, mem_rel rsegs m m0 ->
  (reac_box_catalogue_match_tls m TP FS lo hi <-> reac_box_catalogue_match_tls m0 TP FS lo hi).
Proof.
  intros m m0 TP FS lo hi R. unfold reac_box_catalogue_match_tls.
  split; intros H DT TS C T DB k HT; apply H; apply (f36_tls_rel m m0 _ _ _ _ _ _ _ R); exact HT.
Qed.

(* The call of 0x828cc from a memory that agrees with the image on its read-only bytes: f36_evt_call run on the
   normalized memory, with every premise and post fact moved across mem_rel. *)
Lemma f36_call_norm : reac_box_catalogue_match_contract ->
  forall (ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (phi len S FS : Z) (fb : list byte),
    s7 = Z_to_bv 64 phi -> s2 = Z_to_bv 64 len -> sp = Z_to_bv 64 S ->
    0 <= phi < 2 ^ 64 -> 0 <= len < 2 ^ 64 -> S < 2 ^ 64 -> S mod 16 = 0 ->
    CM_K <= S -> stk rsegs m (S - CM_K) S ->
    (forall a, S - CM_K <= a < S -> seg_rom rsegs (wa a) = None) ->
    length fb = 50%nat ->
    (50 <= len -> 0 < phi /\ phi + 50 <= 2 ^ 64 /\ bytes_at rsegs m phi fb /\ (phi + 50 <= S - CM_K \/ S <= phi)) ->
    (forall a, CM_T <= a < CM_T + 3256 -> mrd rsegs m (wa a) = seg_rom rsegs (wa a)) ->
    ro_agree rsegs m -> asan_cells m -> shadow_rw m ->
    HIGHMEM_BEG <= S - CM_K -> S <= APPMEM_END -> addressable m (S - CM_K) CM_K ->
    (50 <= len -> addressable m phi 50 /\ app_mem (phi + 50)) ->
    addressable m CM_T 3256 -> addressable m REAC_CTRL_PARSE_BC 6 ->
    bytes_at rsegs m REAL_BCMP (le8 (wa BCMP)) -> bytes_at rsegs m REAL_MEMCMP (le8 (wa MEMCMP)) ->
    bytes_at rsegs m GOT_CF (le8 (wa CF)) ->
    bytes_at rsegs m (CF + 254) [Z_to_bv 8 1] -> bytes_at rsegs m (CF + 255) [Z_to_bv 8 1] ->
    fp [0%nat; 1%nat; 2%nat] m (bv_unsigned tp) FS (S - CM_K) S (reac_box_catalogue_match_W S)
      (reac_box_catalogue_match_D phi len) ->
    reac_box_catalogue_match_tls m (bv_unsigned tp) FS (S - CM_K) S ->
    LE.evt rsegs
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                         (m' : word -> option byte),
         ms' = MS (mkR (Z_to_bv 64 0x828d8) sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (want CM_T len fb))
                       a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (Z_to_bv 64 0x828d8) fc None m' (seg_rom rsegs) /\
         munch (f36_W S FS) m m' /\ wmono rsegs m m' /\ ro_agree rsegs m' /\ stk rsegs m' (S - CM_K) S /\
         asan_cells m' /\ shadow_rw m' /\ addressable m' (S - CM_K) CM_K /\
         fp [0%nat; 1%nat; 2%nat] m' (bv_unsigned tp) FS (S - CM_K) S (reac_box_catalogue_match_W S)
            (reac_box_catalogue_match_D phi len))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x828cc) fc None m (seg_rom rsegs)).
Proof.
  intros CMC ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m phi len S FS fb E7 E2 Esp Hphi Hlen HS Hmod HKS HST HROM Hfb HFB HROc HRO HAC HSW
    Hhi Hsp HADW HADf HADT HADB HRB HRM HGC HC254 HC255 HFP HTLS.
  pose proof (mem_rel_normalize rsegs m HRO) as R.
  assert (BR : forall a bs, bytes_at rsegs m a bs <-> bytes_at rsegs (normalize rsegs m) a bs)
    by (intros a bs; exact (bytes_at_rel rsegs m (normalize rsegs m) a bs R)).
  assert (Hlo : 0x5fe000 <= S - CM_K) by (unfold HIGHMEM_BEG in Hhi; lia).
  eapply LE.evt_mono.
  { eapply (evt_normalize rsegs _ _ F _ fc None m (seg_rom rsegs) wx_apart_asan HRO).
    apply (f36_evt_call CMC ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
             t3 t4 t5 t6 F fc (normalize rsegs m) phi len S FS fb E7 E2 Esp Hphi Hlen HS Hmod HKS).
    - apply (proj1 (f36_stk_rel m _ _ _ R Hlo)). exact HST.
    - exact HROM.
    - exact Hfb.
    - intros H50. destruct (HFB H50) as (P1 & P2 & P3 & P4).
      split; [exact P1|]. split; [exact P2|]. split; [apply BR; exact P3 | exact P4].
    - intros a Ha. rewrite <- (mrd_rel rsegs m (normalize rsegs m) _ R). exact (HROc a Ha).
    - exact (mem_inv_normalize rsegs m).
    - apply (proj1 (f36_cells_rel m _ R)). exact HAC.
    - apply (proj1 (f36_srw_rel m _ R)). exact HSW.
    - exact Hhi.
    - exact Hsp.
    - apply (proj1 (f36_addr_rel m _ _ _ R)). exact HADW.
    - intros H50. destruct (HADf H50) as (P1 & P2).
      split; [apply (proj1 (f36_addr_rel m _ _ _ R)); exact P1 | exact P2].
    - apply (proj1 (f36_addr_rel m _ _ _ R)). exact HADT.
    - apply (proj1 (f36_addr_rel m _ _ _ R)). exact HADB.
    - apply BR. exact HRB.
    - apply BR. exact HRM.
    - apply BR. exact HGC.
    - apply BR. exact HC254.
    - apply BR. exact HC255.
    - apply (proj1 (f36_fp_rel _ m _ _ _ _ _ _ _ R)). exact HFP.
    - apply (proj1 (f36_cmtls_rel m _ _ _ _ _ R)). exact HTLS. }
  intros s (s0' & HQ & REL & SAME).
  destruct HQ as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m0' &
                  E0 & MU & WM & MI & ST & AC' & SW' & AD' & FP').
  subst s0'.
  destruct s as [R' F' pc' sv' rv' fc' m' ro'].
  unfold ms_rel, MS in REL.
  cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_mem ms_rom] in REL, SAME.
  destruct REL as (ER & EF & Epc & Esv & Erv & Efc & Erom & RM).
  subst R' F' pc' sv' rv' fc' ro'.
  exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'.
  split; [reflexivity|].
  split; [exact (munch_rel rsegs _ m (normalize rsegs m) m' m0' R RM SAME MU)|].
  split; [exact (wmono_rel rsegs m (normalize rsegs m) m' m0' R RM SAME WM)|].
  split; [exact (ro_agree_same rsegs m m' HRO SAME)|].
  split; [apply (proj2 (f36_stk_rel m' m0' _ _ RM Hlo)); exact ST|].
  split; [apply (proj2 (f36_cells_rel m' m0' RM)); exact AC'|].
  split; [apply (proj2 (f36_srw_rel m' m0' RM)); exact SW'|].
  split; [apply (proj2 (f36_addr_rel m' m0' _ _ RM)); exact AD'|].
  apply (proj2 (f36_fp_rel _ m' m0' _ _ _ _ _ _ RM)). exact FP'.
Qed.

(* ===================== the hand-on bundle LT ===================== *)

(* The frame records of turn j (SlotInv's IDBe at fr + 2688, FGBe at fr + 2768) keep their sizes: the identity
   record is ID_SIZE = 38 bytes (ING keeps it) and the fragment state 72 bytes (fg_first / fg_join / fg_clear keep
   it under fg_fr's 1 <= n <= 22 and fg_keep's T <= 64), so both lie in [fr + 2688, fr + 2840). *)
Lemma f36_tID_len : forall inp j, length (t_ID inp j) = ID_SIZE.
Proof.
  intros inp j. unfold t_ID. induction j as [|j IH].
  - cbn [fst_at fs0 fs_id]. unfold ID0. apply repeat_length.
  - rewrite fst_at_S. set (s := fst_at inp j) in *.
    assert (E : fs_id (turn s (t_len inp j) (t_g inp j)) =
                fg_id (rp_id (fs_id s) (t_len inp j) (t_g inp j)) (t_len inp j) (fs_fg s) (t_g inp j))
      by (unfold turn; destruct (f_opens (t_len inp j) (t_g inp j)); reflexivity).
    rewrite E.
    assert (E1 : length (rp_id (fs_id s) (t_len inp j) (t_g inp j)) = ID_SIZE).
    { unfold rp_id. match goal with |- context [if ?b then _ else _] => destruct b end;
        [apply ING_length; exact IH | exact IH]. }
    unfold fg_id. match goal with |- context [if ?b then _ else _] => destruct b end;
      [apply ING_length; exact E1 | exact E1].
Qed.

Lemma f36_fg_st_len : forall len st g, length st = 72%nat -> length g = 50%nat ->
  length (fg_st len st g) = 72%nat.
Proof.
  intros len st g Hs Hg.
  assert (Hlf : 0 <= fg_lf st).
  { unfold fg_lf, bat. pose proof (bv_unsigned_in_range 8 (nth (Z.to_nat 7) st (Z_to_bv 8 0))) as R. lia. }
  assert (Hnn : forall len', fg_fr len' g = true -> 1 <= fg_n g <= 22).
  { intros len' Ef. unfold fg_fr in Ef. apply andb_prop in Ef as [Ef _]. apply andb_prop in Ef as [Ef E2].
    apply andb_prop in Ef as [_ E1]. apply Z.leb_le in E1. apply Z.leb_le in E2. lia. }
  assert (HJ : 1 <= fg_n g <= 22 -> fg_T st g <= 64 -> length (fg_join st g) = 72%nat).
  { intros Hn HT. unfold fg_T in HT. unfold fg_join, fg_body, bsl.
    rewrite !length_app, !length_firstn, !length_skipn. rewrite Hs, Hg. unfold fg_T. lia. }
  assert (HC : forall l, length l = 72%nat -> length (fg_clear l) = 72%nat).
  { intros l Hl. unfold fg_clear. rewrite !length_app, length_firstn, length_skipn. cbn [length]. lia. }
  unfold fg_st. destruct (fcls len st g) eqn:Ec; cbn [fg_next].
  - exact Hs.
  - exact Hs.
  - unfold fcls, fg_class in Ec. cbn [Z.eqb orb] in Ec.
    destruct (fg_fr len g) eqn:Ef; cbn [negb] in Ec; [|discriminate Ec].
    pose proof (Hnn len Ef) as Hn.
    unfold fg_first, fg_body, bsl. rewrite !length_app, !length_firstn, !length_skipn. cbn [length].
    rewrite Hs, Hg. lia.
  - exact (HC st Hs).
  - unfold fcls, fg_class in Ec. cbn [Z.eqb orb] in Ec.
    destruct (fg_fr len g) eqn:Ef; cbn [negb] in Ec; [|discriminate Ec].
    destruct (bat g 19 =? 1); [discriminate Ec|].
    destruct (fg_keep st g) eqn:Ek; cbn [negb] in Ec; [|discriminate Ec].
    unfold fg_keep in Ek. apply andb_prop in Ek as [_ E3]. apply Z.leb_le in E3.
    exact (HC _ (HJ (Hnn len Ef) E3)).
  - unfold fcls, fg_class in Ec. cbn [Z.eqb orb] in Ec.
    destruct (fg_fr len g) eqn:Ef; cbn [negb] in Ec; [|discriminate Ec].
    destruct (bat g 19 =? 1); [discriminate Ec|].
    destruct (fg_keep st g) eqn:Ek; cbn [negb] in Ec; [|discriminate Ec].
    unfold fg_keep in Ek. apply andb_prop in Ek as [_ E3]. apply Z.leb_le in E3.
    exact (HC _ (HJ (Hnn len Ef) E3)).
Qed.

Lemma f36_tFG_len : forall inp j, length (t_FG inp j) = 72%nat.
Proof.
  intros inp j. unfold t_FG. induction j as [|j IH].
  - cbn [fst_at fs0 fs_fg]. exact z72_length.
  - rewrite fst_at_S. set (s := fst_at inp j) in *.
    assert (E : fs_fg (turn s (t_len inp j) (t_g inp j)) = fg_st (t_len inp j) (fs_fg s) (t_g inp j))
      by (unfold turn; destruct (f_opens (t_len inp j) (t_g inp j)); reflexivity).
    rewrite E. apply f36_fg_st_len; [exact IH | unfold t_g; apply fr50_length].
Qed.

(* v1.9 FSb: the first fragment's body is at most the 23 bytes block[9 ..] of a 50-byte record (fs0's is empty),
   so it lies in [fr + 2880, fr + 2915), the 35 bytes FSb makes addressable.  (F29's fs_body_len.) *)
Lemma f36_fs_body_len : forall inp j, (length (fs_body (fst_at inp j)) <= 23)%nat.
Proof.
  intros inp j. induction j as [|j IH].
  - cbn [fst_at fs0 fs_body length]. lia.
  - rewrite fst_at_S. unfold turn. cbv beta zeta.
    destruct (f_opens (t_len inp j) (t_g inp j)); cbn [fs_body]; [|exact IH].
    rewrite length_firstn, length_skipn. unfold t_g. rewrite fr50_length. lia.
Qed.

(* LT (SlotInv: IFS g fr (S j), the frame records of turn j + 1 at fr + 2688 / fr + 2768, the spills [A+104] /
   [A+112] and, v1.9, FSb's body bytes at fr + 2880 and their addressability) across a run whose writes miss the
   spill area [A, A + 416), the frame records [fr + 2688, fr + 2840) and the body [fr + 2880, fr + 2915) with its
   shadow. *)
Lemma f36_lt_keep : forall g fr j regs regs' mem mem' W A,
  LT g fr j regs mem -> munch W mem mem' -> getr regs' 9 = getr regs 9 ->
  rg regs 9 A -> 416 <= A -> A + 416 <= 2 ^ 64 ->
  (forall x, A <= x < A + 416 -> outside W x) ->
  (forall x, fr + 2688 <= x < fr + 2840 -> outside W x) ->
  (forall x, fr + 2880 <= x < fr + 2915 -> outside W x /\ outside W (shadow_addr x)) ->
  LT g fr j regs' mem'.
Proof.
  intros g fr j regs regs' mem mem' W A (HID & HFG & HFS) MU E9 Hr9 HA0 HA1 HWA HWF HWB.
  assert (SP : forall off v, 0 <= off <= 400 -> spill regs mem off v -> spill regs' mem' off v).
  { intros off v Ho (A1 & HA1' & Hq).
    pose proof Hq as (Hq0 & Hq1 & _). rewrite length_le8 in Hq1. cbn [Z.of_nat] in Hq1.
    assert (EA : A1 = A) by (apply (f36_rg_near regs 9 A A1 Hr9 HA1'); lia).
    subst A1. exists A. split; [unfold rg in *; rewrite E9; exact HA1'|].
    unfold q64 in *. apply (fl_bytes _ mem mem' _ _ Hq MU). rewrite length_le8.
    intros x Hx. apply HWA. cbn [Z.of_nat] in Hx. lia. }
  split; [|split].
  - destruct HID as (HIDB & Hok). split; [|exact Hok]. unfold IDBe in *.
    apply (fl_bytes _ mem mem' _ _ HIDB MU). rewrite f36_tID_len. unfold ID_SIZE.
    intros x Hx. apply HWF. lia.
  - destruct HFG as (HFGB & Hok). split; [|exact Hok]. unfold FGBe in *.
    apply (fl_bytes _ mem mem' _ _ HFGB MU). rewrite f36_tFG_len.
    intros x Hx. apply HWF. lia.
  - destruct HFS as (H104 & H112 & Hbody & Had & HFI).
    split; [apply SP; [lia | exact H104]|].
    split; [apply SP; [lia | exact H112]|].
    split.
    { apply (fl_bytes _ mem mem' _ _ Hbody MU). pose proof (f36_fs_body_len (g_in g) (S j)) as Hl.
      intros x Hx. exact (proj1 (HWB x ltac:(lia))). }
    split; [|exact HFI].
    apply (f36_addr_keep W mem mem' _ _ Had MU). intros i Hi. exact (proj2 (HWB (fr + 2880 + i) ltac:(lia))).
Qed.

(* A spill at the spill base A (reg 9) moves across a run that misses [A, A + 416) and keeps reg 9. *)
Lemma f36_spill_keep : forall regs regs' mem mem' W A off v,
  spill regs mem off v -> munch W mem mem' -> getr regs' 9 = getr regs 9 ->
  rg regs 9 A -> 416 <= A -> A + 416 <= 2 ^ 64 -> 0 <= off <= 400 ->
  (forall x, A <= x < A + 416 -> outside W x) ->
  spill regs' mem' off v.
Proof.
  intros regs regs' mem mem' W A off v (A1 & HA1 & Hq) MU E9 Hr9 HA0 HA1' Ho HWA.
  pose proof Hq as (Hq0 & Hq1 & _). rewrite length_le8 in Hq1. cbn [Z.of_nat] in Hq1.
  assert (EA : A1 = A) by (apply (f36_rg_near regs 9 A A1 Hr9 HA1); lia).
  subst A1. exists A. split; [unfold rg in *; rewrite E9; exact HA1|].
  unfold q64 in *. apply (fl_bytes _ mem mem' _ _ Hq MU). rewrite length_le8.
  intros x Hx. apply HWA. cbn [Z.of_nat] in Hx. lia.
Qed.

(* FLSI (SlotInv: FLSH = PRO's thirteen spills, the 6 bytes at fr + 2624 and the input facts, [A+128], the frame
   backed, [A+144] and the 17 bytes at fr + 2691 addressable; the spills [A+216] / [A+224] / [A+248]; f1_IN, the
   harness input block; FLC, the frame-loop pointer spills and the two frame records at fr + 2688 / fragb fr
   addressable) across such a run that also misses the frame, the shadow of [fr + 2624, fr + 2630) and of the frame
   records [fr + 2688, fr + 2840), and the harness block with its shadow bytes. *)
Lemma f36_flsi_keep : forall g j fr regs regs' mem mem' W A,
  FLSI g j fr regs mem -> munch W mem mem' -> wmono rsegs mem mem' -> getr regs' 9 = getr regs 9 ->
  rg regs 9 A -> 416 <= A -> A + 416 <= 2 ^ 64 ->
  (forall x, A <= x < A + 416 -> outside W x) ->
  (forall x, fr <= x < fr + 3136 -> outside W x) ->
  (forall i, 0 <= i < 6 -> outside W (shadow_addr (fr + 2624 + i))) ->
  (forall i, 0 <= i < 152 -> outside W (shadow_addr (fr + 2688 + i))) ->
  (forall x, g_p g <= x < g_p g + g_n g -> outside W x /\ outside W (shadow_addr x)) ->
  FLSI g j fr regs' mem'.
Proof.
  intros g j fr regs regs' mem mem' W A
    (((H40 & H120 & H136 & H160 & H168 & H176 & H208 & H248p & Had & _ & _ & H184p & H256p & H264p & H272p &
       H32p) &
      H128 & Hstk & H144 & Had2) &
     H216 & H224 & H248 & (Hin & HadP & Hby) &
     (C256 & C184 & C192 & C80 & C88 & C96 & C272 & C264 & CadF & CadR & C72 & C64 & C56 & C48))
    MU WM E9 Hr9 HA0 HA1 HWA HWF HWS HWS2 HWP.
  assert (SP : forall off v, 0 <= off <= 400 -> spill regs mem off v -> spill regs' mem' off v)
    by (intros off v Ho Hs; exact (f36_spill_keep regs regs' mem mem' W A off v Hs MU E9 Hr9 HA0 HA1 Ho HWA)).
  split.
  { split.
    { split; [apply SP; [lia | exact H40]|]. split; [apply SP; [lia | exact H120]|].
      split; [apply SP; [lia | exact H136]|]. split; [apply SP; [lia | exact H160]|].
      split; [apply SP; [lia | exact H168]|]. split; [apply SP; [lia | exact H176]|].
      split; [apply SP; [lia | exact H208]|]. split; [apply SP; [lia | exact H248p]|].
      split; [apply (f36_addr_keep W mem mem' _ _ Had MU); intros i Hi; exact (HWS i Hi)|].
      split.
      - apply (fl_bytes _ mem mem' _ _ Hby MU). intros x Hx.
        exact (proj1 (HWP x ltac:(unfold g_n, nlen; lia))).
      - split.
        + intros Hn. split; [exact (Hin Hn)|].
          apply (f36_addr_keep W mem mem' _ _ HadP MU). intros i Hi.
          exact (proj2 (HWP (g_p g + i) ltac:(lia))).
        + split; [apply SP; [lia | exact H184p]|]. split; [apply SP; [lia | exact H256p]|].
          split; [apply SP; [lia | exact H264p]|].
          split; [apply SP; [lia | exact H272p] | apply SP; [lia | exact H32p]]. }
    split; [apply SP; [lia | exact H128]|].
    split; [apply (f36_stk_tr W mem mem' fr (fr + 3136) Hstk MU WM); intros x Hx; left; exact (HWF x Hx)|].
    split; [apply SP; [lia | exact H144]|].
    apply (f36_addr_keep W mem mem' _ _ Had2 MU). intros i Hi.
    replace (fr + 2691 + i) with (fr + 2688 + (3 + i)) by lia. apply HWS2. lia. }
  split; [apply SP; [lia | exact H216]|].
  split; [apply SP; [lia | exact H224]|].
  split; [apply SP; [lia | exact H248]|].
  split.
  { split; [exact Hin|]. split.
    - apply (f36_addr_keep W mem mem' _ _ HadP MU). intros i Hi.
      exact (proj2 (HWP (g_p g + i) ltac:(lia))).
    - apply (fl_bytes _ mem mem' _ _ Hby MU). intros x Hx.
      exact (proj1 (HWP x ltac:(unfold g_n, nlen; lia))). }
  split; [apply SP; [lia | exact C256]|]. split; [apply SP; [lia | exact C184]|].
  split; [apply SP; [lia | exact C192]|]. split; [apply SP; [lia | exact C80]|].
  split; [apply SP; [lia | exact C88]|]. split; [apply SP; [lia | exact C96]|].
  split; [apply SP; [lia | exact C272]|]. split; [apply SP; [lia | exact C264]|].
  split.
  { apply (f36_addr_keep W mem mem' _ _ CadF MU). intros i Hi. unfold fragb.
    replace (fr + 2768 + i) with (fr + 2688 + (80 + i)) by lia. apply HWS2. lia. }
  split; [apply (f36_addr_keep W mem mem' _ _ CadR MU); intros i Hi; apply HWS2; lia|].
  split; [apply SP; [lia | exact C72]|]. split; [apply SP; [lia | exact C64]|].
  split; [apply SP; [lia | exact C56] | apply SP; [lia | exact C48]].
Qed.

(* FLSX (SlotInv: FLSI, the turn's registers 18 / 22 / 23 / 25, under 50 <= len the block's bytes, the two turn
   spills) across such a run that also misses the block [Phi, Phi + a_size len) and keeps the four registers. *)
Lemma f36_flsx_keep : forall g j phi fr regs regs' mem mem' W A,
  FLSX g j phi fr regs mem -> munch W mem mem' -> wmono rsegs mem mem' ->
  getr regs' 9 = getr regs 9 -> getr regs' 18 = getr regs 18 -> getr regs' 22 = getr regs 22 ->
  getr regs' 23 = getr regs 23 -> getr regs' 25 = getr regs 25 ->
  rg regs 9 A -> 416 <= A -> A + 416 <= 2 ^ 64 ->
  (forall x, A <= x < A + 416 -> outside W x) ->
  (forall x, fr <= x < fr + 3136 -> outside W x) ->
  (forall i, 0 <= i < 6 -> outside W (shadow_addr (fr + 2624 + i))) ->
  (forall i, 0 <= i < 152 -> outside W (shadow_addr (fr + 2688 + i))) ->
  (forall x, g_p g <= x < g_p g + g_n g -> outside W x /\ outside W (shadow_addr x)) ->
  (forall x, phi <= x < phi + AC.a_size (flen g j) -> outside W x) ->
  FLSX g j phi fr regs' mem'.
Proof.
  intros g j phi fr regs regs' mem mem' W A (HI & H18 & H22 & H23 & H25 & Hrec & H152 & H280)
    MU WM E9 E18 E22 E23 E25 Hr9 HA0 HA1 HWA HWF HWS HWS2 HWP HWB.
  assert (SP : forall off v, 0 <= off <= 400 -> spill regs mem off v -> spill regs' mem' off v)
    by (intros off v Ho Hs; exact (f36_spill_keep regs regs' mem mem' W A off v Hs MU E9 Hr9 HA0 HA1 Ho HWA)).
  split; [exact (f36_flsi_keep g j fr regs regs' mem mem' W A HI MU WM E9 Hr9 HA0 HA1 HWA HWF HWS HWS2 HWP)|].
  split; [unfold rg in *; rewrite E18; exact H18|]. split; [unfold rg in *; rewrite E22; exact H22|].
  split; [unfold rg in *; rewrite E23; exact H23|]. split; [unfold rg in *; rewrite E25; exact H25|].
  split.
  { intros Hl. destruct (Hrec Hl) as (Hp0 & Hp1 & Hg & Hpb & Hpl).
    assert (Hsz : AC.a_size (flen g j) = flen g j) by (unfold AC.a_size; lia).
    split; [exact Hp0|]. split; [exact Hp1|].
    split.
    { apply (fl_bytes _ mem mem' _ _ Hg MU). unfold t_g. rewrite fr50_length.
      intros x Hx. apply HWB. cbn [Z.of_nat] in Hx. lia. }
    split; [|exact Hpl].
    apply (fl_bytes _ mem mem' _ _ Hpb MU). intros x Hx. apply HWB. lia. }
  split; [apply SP; [lia | exact H152] | apply SP; [lia | exact H280]].
Qed.

(* LK (the turn index in s5 and the 6 bytes OUR at fr + 2624). *)
Lemma f36_lk_keep : forall g fr j regs regs' mem mem' W,
  LK g fr j regs mem -> munch W mem mem' -> getr regs' 21 = getr regs 21 ->
  (forall x, fr + 2624 <= x < fr + 2630 -> outside W x) ->
  LK g fr j regs' mem'.
Proof.
  intros g fr j regs regs' mem mem' W (Hj & H21 & HOUR) MU E21 HW.
  split; [exact Hj|]. split; [unfold rg in *; rewrite E21; exact H21|].
  unfold OURb in *. apply (fl_bytes _ mem mem' _ _ HOUR MU). rewrite OUR_length.
  intros x Hx. apply HW. cbn [Z.of_nat] in Hx. lia.
Qed.

(* HB (the turn's block, nonzero and addressable over a_size len). *)
Lemma f36_hb_keep : forall mem mem' W phi len,
  HB mem phi len -> munch W mem mem' ->
  (forall i, 0 <= i < AC.a_size len -> outside W (shadow_addr (phi + i))) ->
  HB mem' phi len.
Proof.
  intros mem mem' W phi len (H0 & Had) MU HW. split; [exact H0|].
  exact (f36_addr_keep W mem mem' phi _ Had MU HW).
Qed.

(* ===================== more pure helpers (byte lists, disjointness) ===================== *)

(* A run of bytes that are all present and all satisfy P is a bytes_at of such a list. *)
Lemma f36_bytes_PN : forall (P : byte -> Prop) m a k, 0 <= a -> a + Z.of_nat k <= 2 ^ 64 ->
  (forall i, 0 <= i < Z.of_nat k -> exists b, mbyte rsegs m (a + i) = Some b /\ P b) ->
  exists bs, bytes_at rsegs m a bs /\ length bs = k /\ Forall P bs.
Proof.
  intros P m a k. revert a. induction k as [|k IH]; intros a H0 H1 H.
  - exists []. split; [|split; [reflexivity | constructor]].
    split; [exact H0|]. split; [cbn [length]; lia|]. intros i Hi; cbn [length] in Hi; lia.
  - destruct (H 0 ltac:(lia)) as (b & Hb & HPb). rewrite Z.add_0_r in Hb.
    assert (Hrec : forall i, 0 <= i < Z.of_nat k -> exists b', mbyte rsegs m (a + 1 + i) = Some b' /\ P b').
    { intros i Hi. destruct (H (1 + i) ltac:(lia)) as (b' & Hb' & HP'). exists b'.
      split; [|exact HP']. replace (a + 1 + i) with (a + (1 + i)) by lia. exact Hb'. }
    destruct (IH (a + 1) ltac:(lia) ltac:(lia) Hrec) as (bs & Hbs & Hlen & HPbs).
    exists (b :: bs). split; [|split; [cbn [length]; lia | constructor; assumption]].
    destruct Hbs as (_ & _ & Hnth).
    split; [exact H0|]. split; [cbn [length]; rewrite Hlen; lia|].
    intros i Hi. destruct i as [|i]; cbn [nth_error].
    + rewrite Z.add_0_r. exact Hb.
    + replace (a + Z.of_nat (S i)) with (a + 1 + Z.of_nat i) by lia.
      apply Hnth. cbn [length] in Hi. lia.
Qed.

Lemma f36_bytes_P : forall (P : byte -> Prop) m a n, 0 <= a -> 0 <= n -> a + n <= 2 ^ 64 ->
  (forall i, 0 <= i < n -> exists b, mbyte rsegs m (a + i) = Some b /\ P b) ->
  exists bs, bytes_at rsegs m a bs /\ Z.of_nat (length bs) = n /\ Forall P bs.
Proof.
  intros P m a n H0 Hn H1 H.
  destruct (f36_bytes_PN P m a (Z.to_nat n) H0 ltac:(rewrite Z2Nat.id by lia; lia)
              ltac:(rewrite Z2Nat.id by lia; exact H)) as (bs & Hbs & Hlen & HP).
  exists bs. split; [exact Hbs|]. split; [rewrite Hlen, Z2Nat.id by lia; reflexivity | exact HP].
Qed.

Lemma f36_le8_of_bytes : forall bs : list byte, length bs = 8%nat -> le8 (Z_to_bv 64 (bytes_le_to_Z bs)) = bs.
Proof.
  intros bs L. unfold le8, word_to_le_bytes. rewrite Z_to_bv_unsigned.
  change (bv_wrap 64 (bytes_le_to_Z bs)) with (bytes_le_to_Z bs mod 2^64).
  rewrite (Z_to_le_bytes_mod 8 _ 64) by lia. rewrite <- L. apply StrFun.Z_to_le_bytes_to_Z.
Qed.

(* Eight present bytes read as some word. *)
Lemma f36_word_present : forall m a, 0 <= a -> a + 8 <= 2 ^ 64 ->
  (forall i, 0 <= i < 8 -> exists b, mbyte rsegs m (a + i) = Some b) ->
  exists w : word, bytes_at rsegs m a (le8 w).
Proof.
  intros m a H0 H1 H.
  assert (HP : forall i, 0 <= i < 8 -> exists b, mbyte rsegs m (a + i) = Some b /\ True).
  { intros i Hi. destruct (H i Hi) as (b & Hb). exists b. split; [exact Hb | exact I]. }
  destruct (f36_bytes_P (fun _ => True) m a 8 H0 ltac:(lia) H1 HP) as (bs & Hbs & Hlen & _).
  exists (Z_to_bv 64 (bytes_le_to_Z bs)). rewrite f36_le8_of_bytes by lia. exact Hbs.
Qed.

(* A word cell determines its value. *)
Lemma f36_wm_uniq : forall mem a v1 v2, word_mem rsegs mem a v1 -> word_mem rsegs mem a v2 ->
  0 <= v1 < 2 ^ 64 -> 0 <= v2 < 2 ^ 64 -> v1 = v2.
Proof.
  intros mem a v1 v2 H1 H2 R1 R2.
  assert (D : forall k, (k < 8)%nat -> le_byte v1 8 k = le_byte v2 8 k).
  { intros k Hk. pose proof (H1 k Hk) as E1. pose proof (H2 k Hk) as E2. rewrite E1 in E2.
    injection E2 as E2.
    pose proof (kb_byte_unsigned v1 8 k) as K1. pose proof (kb_byte_unsigned v2 8 k) as K2.
    unfold bv_unsigned in K1, K2. rewrite K1, K2 in E2. exact E2. }
  pose proof (kb_le8_digits v1 R1) as G1. pose proof (kb_le8_digits v2 R2) as G2.
  rewrite (D 0%nat ltac:(lia)), (D 1%nat ltac:(lia)), (D 2%nat ltac:(lia)), (D 3%nat ltac:(lia)),
          (D 4%nat ltac:(lia)), (D 5%nat ltac:(lia)), (D 6%nat ltac:(lia)), (D 7%nat ltac:(lia)) in G1.
  lia.
Qed.

(* Two nonempty ranges are apart when a predicate holds on every byte of one and on no byte of the other. *)
Lemma f36_dj_pt : forall (Q : Z -> Prop) a b c d, a < b -> c < d ->
  (forall x, a <= x < b -> Q x) -> (forall x, c <= x < d -> ~ Q x) -> RcLay.ly_dj a b c d.
Proof.
  intros Q a b c d Hab Hcd HQ HnQ. unfold RcLay.ly_dj.
  destruct (Z_le_gt_dec b c) as [H|H]; [left; exact H|].
  destruct (Z_le_gt_dec d a) as [H2|H2]; [right; exact H2|].
  exfalso. apply (HnQ (Z.max a c) ltac:(lia)). apply HQ. lia.
Qed.

Lemma f36_sh_lo : forall a, 0 <= a -> LOWMEM_END <= shadow_addr a.
Proof.
  intros a Ha. unfold shadow_addr, ASAN_K, LOWMEM_END.
  assert (0 <= a / 8) by (apply Z.div_pos; lia). lia.
Qed.

Lemma f36_sh_hi : forall a, a <= APPMEM_END -> shadow_addr a <= HIGHMEM_BEG.
Proof.
  intros a Ha. unfold shadow_addr, ASAN_K, HIGHMEM_BEG.
  assert (D : a / 8 <= 17592186044416) by (apply Z.div_le_upper_bound; unfold APPMEM_END in *; lia).
  lia.
Qed.

(* The twelve side-stack ranges of the classes 0, 1, 2 in numbers (fs_B c = 64 * 2^c, fs_M c = 2^(14-c)). *)
Lemma f36_fs_ranges : forall FS,
  fs_hint FS 0 = FS /\ fs_hint FS 1 = FS + 8 /\ fs_hint FS 2 = FS + 16 /\
  fs_flag FS 0 0 = FS + 4096 /\ fs_flag FS 1 0 = FS + 20480 /\ fs_flag FS 2 0 = FS + 28672 /\
  fs_M 0 = 16384 /\ fs_M 1 = 8192 /\ fs_M 2 = 4096 /\
  fs_frame FS 0 0 = FS + 36864 /\ fs_frame FS 0 (fs_M 0) = FS + 1085440 /\
  fs_frame FS 1 0 = FS + 1085440 /\ fs_frame FS 1 (fs_M 1) = FS + 2134016 /\
  fs_frame FS 2 0 = FS + 2134016 /\ fs_frame FS 2 (fs_M 2) = FS + 3182592.
Proof.
  intros FS. unfold fs_hint, fs_flag, fs_frame, fs_M, fs_B.
  cbn [Z.of_nat Pos.of_succ_nat Pos.succ].
  repeat split; first [ reflexivity | lia | (vm_compute (2 ^ 15) in *; lia) ].
Qed.

Lemma f36_W_eq : forall S FS, f36_W S FS =
  [(S - CM_K, S);
   (FS, FS + 8); (FS + 4096, FS + 20480); (FS + 36864, FS + 1085440);
   (shadow_addr (FS + 36864), shadow_addr (FS + 1085440));
   (FS + 8, FS + 16); (FS + 20480, FS + 28672); (FS + 1085440, FS + 2134016);
   (shadow_addr (FS + 1085440), shadow_addr (FS + 2134016));
   (FS + 16, FS + 24); (FS + 28672, FS + 32768); (FS + 2134016, FS + 3182592);
   (shadow_addr (FS + 2134016), shadow_addr (FS + 3182592));
   (shadow_addr (S - CM_K), shadow_addr S)].
Proof.
  intros S FS. destruct (f36_fs_ranges FS) as
    (H0 & H1 & H2 & H3 & H4 & H5 & M0 & M1 & M2 & F0 & F0' & F1 & F1' & F2 & F2').
  unfold f36_W, fp_w, fp_w1. cbn [flat_map app].
  rewrite H0, H1, H2, H3, H4, H5, F0, F0', F1, F1', F2, F2', M0, M1, M2.
  replace (FS + 4096 + 16384) with (FS + 20480) by lia.
  replace (FS + 20480 + 8192) with (FS + 28672) by lia.
  replace (FS + 28672 + 4096) with (FS + 32768) by lia.
  replace (FS + 8 + 8) with (FS + 16) by lia.
  replace (FS + 16 + 8) with (FS + 24) by lia.
  reflexivity.
Qed.

(* A contiguous app range lies wholly in the low or wholly in the high app memory. *)
Lemma f36_app_split : forall lo hi, lo < hi -> (forall a, lo <= a < hi -> app_mem a) ->
  hi <= LOWMEM_END \/ HIGHMEM_BEG <= lo.
Proof.
  intros lo hi Hlt H. destruct (Z_le_gt_dec hi LOWMEM_END) as [L|L]; [left; exact L|right].
  destruct (Z_le_gt_dec LOWMEM_END lo) as [L2|L2].
  - pose proof (H lo ltac:(lia)) as H2.
    unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in *. lia.
  - pose proof (H LOWMEM_END ltac:(lia)) as H3.
    unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in *. lia.
Qed.

(* The shadow bytes of a contiguous app range are shadow memory. *)
Lemma f36_shadow_ivl : forall lo hi x, (forall a, lo <= a < hi -> app_mem a) -> lo < hi ->
  shadow_addr lo <= x < shadow_addr hi -> in_shadow x.
Proof.
  intros lo hi x Happ Hlt Hx. unfold shadow_addr, ASAN_K in Hx.
  assert (Hlo : 0 <= lo)
    by (pose proof (Happ lo ltac:(lia)) as H; unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in *; lia).
  assert (Hhi : hi <= APPMEM_END)
    by (pose proof (Happ (hi - 1) ltac:(lia)) as H; unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in *; lia).
  unfold in_shadow. destruct (f36_app_split lo hi Hlt Happ) as [HL|HH].
  - left. unfold ASAN_K, LOWMEM_END, LOWSHADOW_END in *. Z.div_mod_to_equations. lia.
  - right. unfold ASAN_K, HIGHSHADOW_BEG, HIGHMEM_BEG, APPMEM_END in *. Z.div_mod_to_equations. lia.
Qed.

(* An app byte outside the callee's window and outside the three metadata/frame bands of the classes 0, 1, 2 is
   outside the call's writes. *)
Lemma f36_out_app : forall S FS x,
  0 <= FS -> FS + FS_SIZE <= S - CM_K -> S <= APPMEM_END ->
  (forall a, FS <= a < FS + FS_SIZE -> app_mem a) ->
  (forall a, S - CM_K <= a < S -> app_mem a) ->
  app_mem x -> ~ (S - CM_K <= x < S) ->
  ~ (FS <= x < FS + 24) -> ~ (FS + 4096 <= x < FS + 32768) -> ~ (FS + 36864 <= x < FS + 3182592) ->
  outside (f36_W S FS) x.
Proof.
  intros S FS x HFS0 HFSS HSA HFSapp HWapp Hx Hw H1 H2 H3.
  assert (HK : 0 < CM_K) by (unfold CM_K; lia).
  assert (HSZ : FS_SIZE = 11571200) by reflexivity.
  rewrite f36_W_eq. cbn [outside].
  repeat split; try (intros HC; lia).
  - intros HC. apply (app_not_shadow x Hx).
    apply (f36_shadow_ivl (FS + 36864) (FS + 1085440) x);
      [intros a Ha; apply HFSapp; lia | lia | exact HC].
  - intros HC. apply (app_not_shadow x Hx).
    apply (f36_shadow_ivl (FS + 1085440) (FS + 2134016) x);
      [intros a Ha; apply HFSapp; lia | lia | exact HC].
  - intros HC. apply (app_not_shadow x Hx).
    apply (f36_shadow_ivl (FS + 2134016) (FS + 3182592) x);
      [intros a Ha; apply HFSapp; lia | lia | exact HC].
  - intros HC. apply (app_not_shadow x Hx).
    apply (f36_shadow_ivl (S - CM_K) S x); [exact HWapp | lia | exact HC].
Qed.

(* The same for a byte at or above the callee's window: the side stack and every shadow byte are below it. *)
Lemma f36_out_hi : forall S FS x,
  0 <= FS -> FS + FS_SIZE <= S - CM_K -> S <= APPMEM_END -> HIGHMEM_BEG <= S - CM_K -> S <= x ->
  outside (f36_W S FS) x.
Proof.
  intros S FS x HFS0 HFSS HSA HHI Hx.
  assert (HSZ : FS_SIZE = 11571200) by reflexivity.
  assert (HK : CM_K = 9136) by reflexivity.
  pose proof (f36_sh_hi S HSA) as HS1.
  pose proof (f36_sh_hi (FS + 3182592) ltac:(unfold HIGHMEM_BEG, APPMEM_END in *; lia)) as HS2.
  pose proof (f36_sh_mono (FS + 1085440) (FS + 3182592) ltac:(lia)) as HM1.
  pose proof (f36_sh_mono (FS + 2134016) (FS + 3182592) ltac:(lia)) as HM2.
  pose proof (f36_sh_mono (S - CM_K) S ltac:(lia)) as HM3.
  rewrite f36_W_eq. cbn [outside].
  repeat split; intros HC; unfold HIGHMEM_BEG in *; lia.
Qed.

(* The shadow byte of an application byte outside the side stack and outside the callee's window is outside the
   call's writes. *)
Lemma f36_out_sh_call : forall S FS x,
  0 <= FS -> FS mod 8 = 0 -> FS + FS_SIZE <= S - CM_K -> (S - CM_K) mod 8 = 0 -> S <= APPMEM_END ->
  (forall a, FS <= a < FS + FS_SIZE -> app_mem a) ->
  (forall a, S - CM_K <= a < S -> app_mem a) ->
  app_mem x -> ~ (FS <= x < FS + 3182592) -> ~ (S - CM_K <= x < S) ->
  outside (f36_W S FS) (shadow_addr x).
Proof.
  intros S FS x HFS0 HFS8 HFSS HS8 HSA HFSapp HWapp Hx HnFS HnW.
  assert (HSZ : FS_SIZE = 11571200) by reflexivity.
  assert (HK : CM_K = 9136) by reflexivity.
  pose proof (shadow_of_app x Hx) as Hsh.
  assert (HAPPFS : forall lo hi, FS <= lo -> hi <= FS + FS_SIZE -> ~ (lo <= shadow_addr x < hi)).
  { intros lo hi Hlo Hhi HC. apply (app_not_shadow (shadow_addr x)); [|exact Hsh].
    apply HFSapp. lia. }
  rewrite f36_W_eq. cbn [outside].
  repeat split.
  - intros HC. apply (app_not_shadow (shadow_addr x)); [apply HWapp; lia | exact Hsh].
  - exact (HAPPFS FS (FS + 8) ltac:(lia) ltac:(lia)).
  - exact (HAPPFS (FS + 4096) (FS + 20480) ltac:(lia) ltac:(lia)).
  - exact (HAPPFS (FS + 36864) (FS + 1085440) ltac:(lia) ltac:(lia)).
  - intros HC. revert HC HnFS. unfold shadow_addr, ASAN_K. Z.div_mod_to_equations. lia.
  - exact (HAPPFS (FS + 8) (FS + 16) ltac:(lia) ltac:(lia)).
  - exact (HAPPFS (FS + 20480) (FS + 28672) ltac:(lia) ltac:(lia)).
  - exact (HAPPFS (FS + 1085440) (FS + 2134016) ltac:(lia) ltac:(lia)).
  - intros HC. revert HC HnFS. unfold shadow_addr, ASAN_K. Z.div_mod_to_equations. lia.
  - exact (HAPPFS (FS + 16) (FS + 24) ltac:(lia) ltac:(lia)).
  - exact (HAPPFS (FS + 28672) (FS + 32768) ltac:(lia) ltac:(lia)).
  - exact (HAPPFS (FS + 2134016) (FS + 3182592) ltac:(lia) ltac:(lia)).
  - intros HC. revert HC HnFS. unfold shadow_addr, ASAN_K. Z.div_mod_to_equations. lia.
  - intros HC. revert HC HnW. unfold shadow_addr, ASAN_K. Z.div_mod_to_equations. lia.
Qed.

Lemma f36_dj_lo : forall (W : list ivl) (c n : Z), (forall p, In p W -> c + n <= fst p) -> disjoint_from W c n.
Proof.
  induction W as [|[lo hi] W IH]; intros c n H; cbn [disjoint_from]; [exact I|].
  split.
  - left. pose proof (H (lo, hi) (or_introl eq_refl)) as Hp. cbn [fst] in Hp. lia.
  - apply IH. intros p Hp. apply H. right. exact Hp.
Qed.

Lemma f36_W_los : forall S FS p, 6283264 <= FS -> 6283264 <= S - CM_K -> In p (f36_W S FS) ->
  6283264 <= fst p.
Proof.
  intros S FS p HFS HS Hin.
  assert (HK : CM_K = 9136) by reflexivity.
  assert (HD1 : 0 <= (FS + 36864) / 8) by (apply Z.div_pos; lia).
  assert (HD2 : 0 <= (FS + 1085440) / 8) by (apply Z.div_pos; lia).
  assert (HD3 : 0 <= (FS + 2134016) / 8) by (apply Z.div_pos; lia).
  assert (HD4 : 0 <= (S - CM_K) / 8) by (apply Z.div_pos; lia).
  rewrite f36_W_eq in Hin. cbn [In] in Hin.
  destruct Hin as [E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[]]]]]]]]]]]]]]];
    subst p; cbn [fst]; unfold shadow_addr, ASAN_K in *; lia.
Qed.

(* A byte apart from the twelve side-stack ranges, from the window and from the window's shadow. *)
Lemma f36_out_dj : forall S FS x,
  ~ (S - CM_K <= x < S) -> outside (fp_w [0%nat; 1%nat; 2%nat] FS) x ->
  ~ (shadow_addr (S - CM_K) <= x < shadow_addr S) ->
  outside (f36_W S FS) x.
Proof.
  intros S FS x H1 H2 H3. unfold f36_W. cbn [app outside]. split; [exact H1|].
  apply fl_out_app; [exact H2|]. cbn [outside]. split; [exact H3 | exact I].
Qed.

(* The shadow bytes of a 3136-byte block apart from [b1, b2) are apart from the shadow of [b1, b2). *)
Lemma f36_sh_dj : forall a b1 b2 t, a mod 8 = 0 -> 0 <= a -> 0 <= b1 -> b1 <= b2 ->
  (a + 3136 <= b1 \/ b2 <= a) ->
  shadow_addr a <= t < shadow_addr a + 392 -> ~ (shadow_addr b1 <= t < shadow_addr b2).
Proof.
  intros a b1 b2 t Ha8 Ha Hb1 Hb12 Hdj Ht HC. unfold shadow_addr, ASAN_K in *.
  destruct Hdj as [H|H]; Z.div_mod_to_equations; lia.
Qed.

(* The side stack's state after the call: the hint word, flag bytes and frames of the classes 0, 1 and 2 come
   from the callee's fp at the return; the metadata of the other classes is unchanged, because the run writes only
   the class-0/1/2 bands, their shadow and the window. *)
Lemma f36_fs_ok : forall (m m' : word -> option byte) (S FS TP : Z) (W D : list ivl),
  AC.a_fs_ok m FS ->
  munch (f36_W S FS) m m' ->
  fp [0%nat; 1%nat; 2%nat] m' TP FS (S - CM_K) S W D ->
  FS + FS_SIZE <= S - CM_K -> S <= APPMEM_END -> HIGHMEM_BEG <= S - CM_K ->
  AC.a_fs_ok m' FS.
Proof.
  intros m m' S FS TP W D (HOK1 & HOK2 & HOK3 & HOK4 & HOK5) MU
    (DT & TS & C & T & DB & k & HT & HTP & HP & H88 & H96 & HCL & HFSlo & HAwin & _ & _) HFSS HSA HHI.
  destruct HP as (HFS0 & HFSmod & HFSgt & HFSapp & HSTK).
  assert (HSZ : FS_SIZE = 11571200) by reflexivity.
  assert (HSZc : AC.FS_SIZE = 11571200) by reflexivity.
  pose proof (Forall_inv HCL) as HC0.
  pose proof (Forall_inv (Forall_inv_tail HCL)) as HC1.
  pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail HCL))) as HC2.
  assert (HFSub : FS + FS_SIZE <= APPMEM_END).
  { pose proof (HFSapp (FS + FS_SIZE - 1) ltac:(lia)) as Hh.
    unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in *. lia. }
  assert (HOUT : forall x, FS <= x < FS + FS_SIZE ->
            ~ (FS <= x < FS + 24) -> ~ (FS + 4096 <= x < FS + 32768) -> ~ (FS + 36864 <= x < FS + 3182592) ->
            outside (f36_W S FS) x).
  { intros x Hx G1 G2 G3.
    apply (f36_out_app S FS x ltac:(lia) HFSS HSA HFSapp HAwin (HFSapp x Hx) ltac:(lia) G1 G2 G3). }
  assert (MB : forall a, outside (f36_W S FS) a -> 0 <= a < 2 ^ 64 -> mbyte rsegs m' a = mbyte rsegs m a).
  { intros a Ho Ha. unfold mbyte. rewrite (MU (Z_to_bv 64 a)); [reflexivity|].
    rewrite MState.unsigned_lit by lia. exact Ho. }
  assert (HB64 : FS + FS_SIZE <= 2 ^ 64) by (unfold APPMEM_END in *; lia).
  split; [|split; [|split; [|split]]].
  - intros a Ha. destruct HSTK as (_ & _ & HS).
    destruct (HS a ltac:(lia)) as [Hw (b & Hb)].
    split; [exact Hw | exists b; exact Hb].
  - pose proof (bytes_at_le8_word rsegs m' (FS + 88) (Z_to_bv 64 20) H88) as HW.
    rewrite MState.unsigned_lit in HW by lia. exact HW.
  - destruct H96 as (_ & _ & H96'). pose proof (H96' 0%nat ltac:(cbn; lia)) as HH.
    cbn [nth_error] in HH. rewrite Z.add_0_r in HH. exact HH.
  - intros c Hc.
    destruct (Nat.eq_dec c 0) as [->|Hne0].
    { destruct HC0 as (_ & h & flags & Hh & _). exists (bv_unsigned h).
      exact (bytes_at_le8_word rsegs m' (fs_hint FS 0) h Hh). }
    destruct (Nat.eq_dec c 1) as [->|Hne1].
    { destruct HC1 as (_ & h & flags & Hh & _). exists (bv_unsigned h).
      exact (bytes_at_le8_word rsegs m' (fs_hint FS 1) h Hh). }
    destruct (Nat.eq_dec c 2) as [->|Hne2].
    { destruct HC2 as (_ & h & flags & Hh & _). exists (bv_unsigned h).
      exact (bytes_at_le8_word rsegs m' (fs_hint FS 2) h Hh). }
    destruct (HOK4 c Hc) as (h & Hh). exists h.
    apply (word_mem_frame rsegs m m' _ _ Hh). intros kk Hk.
    assert (Hhint : AC.a_fs_hint FS c = FS + 8 * Z.of_nat c) by reflexivity.
    assert (Hc3 : 3 <= Z.of_nat c <= 10) by lia.
    apply MB; [rewrite Hhint; apply HOUT; lia | rewrite Hhint; lia].
  - intros c j Hc Hj.
    assert (Hfl : forall (cc : nat) (hh : word) (flags : list byte),
              bytes_at rsegs m' (fs_flag FS cc 0) flags -> Z.of_nat (length flags) = fs_M cc ->
              Forall (fun b => b = Z_to_bv 8 0 \/ b = Z_to_bv 8 1) flags ->
              0 <= j < AC.a_fs_M cc ->
              mbyte rsegs m' (AC.a_fs_flag FS cc j) = Some (Z_to_bv 8 0) \/
              mbyte rsegs m' (AC.a_fs_flag FS cc j) = Some (Z_to_bv 8 1)).
    { intros cc hh flags Hfb Hfl' Hfb01 Hjj.
      assert (HM : AC.a_fs_M cc = fs_M cc) by reflexivity.
      rewrite HM in Hjj.
      destruct Hfb as (_ & _ & Hfb).
      assert (HjN : (Z.to_nat j < length flags)%nat) by lia.
      pose proof (Hfb (Z.to_nat j) HjN) as HH.
      destruct (nth_error flags (Z.to_nat j)) as [b|] eqn:E;
        [|exfalso; apply nth_error_None in E; lia].
      assert (Eaddr : fs_flag FS cc 0 + Z.of_nat (Z.to_nat j) = AC.a_fs_flag FS cc j)
        by (unfold fs_flag, AC.a_fs_flag; lia).
      rewrite Eaddr in HH.
      pose proof (proj1 (Forall_forall _ flags) Hfb01 b (nth_error_In _ _ E)) as Hb01.
      destruct Hb01 as [->| ->]; [left | right]; exact HH. }
    destruct (Nat.eq_dec c 0) as [->|Hne0].
    { destruct HC0 as (_ & h & flags & _ & Hfb & Hfl' & Hfb01). exact (Hfl 0%nat h flags Hfb Hfl' Hfb01 Hj). }
    destruct (Nat.eq_dec c 1) as [->|Hne1].
    { destruct HC1 as (_ & h & flags & _ & Hfb & Hfl' & Hfb01). exact (Hfl 1%nat h flags Hfb Hfl' Hfb01 Hj). }
    destruct (Nat.eq_dec c 2) as [->|Hne2].
    { destruct HC2 as (_ & h & flags & _ & Hfb & Hfl' & Hfb01). exact (Hfl 2%nat h flags Hfb Hfl' Hfb01 Hj). }
    assert (Hr : FS + 32768 <= AC.a_fs_flag FS c j < FS + 36864).
    { unfold AC.a_fs_flag. unfold AC.a_fs_M in Hj.
      destruct c as [|[|[|[|[|[|[|[|[|[|[|c]]]]]]]]]]];
        try (exfalso; revert Hc Hne0 Hne1 Hne2; clear; lia);
        cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hj |- *;
        first [ lia | (vm_compute (2 ^ 15) in *; vm_compute in Hj; lia) ]. }
    destruct (HOK5 c j Hc Hj) as [HH|HH]; [left|right];
      (rewrite MB; [exact HH | apply HOUT; lia | lia]).
Qed.

(* Every segment of the image ends below 0x5fe000, so the callee's stack window has no ROM bytes. *)
Lemma f36_segs_below : BzBridge.seg_tops_below rsegs 0x5fe000 = true.
Proof. vm_compute. reflexivity. Qed.

Lemma f36_rom_none : forall a, 0 <= a < 2 ^ 64 -> 0x5fe000 <= a -> seg_rom rsegs (wa a) = None.
Proof.
  intros a Ha Hge. apply seg_rom_unmapped.
  destruct (find_segment rsegs (bv_unsigned (wa a)) 1) as [s|] eqn:E; [|reflexivity].
  exfalso.
  destruct (BzBridge.find_segment_below rsegs 0x5fe000 (bv_unsigned (wa a)) 1 s f36_segs_below E ltac:(lia))
    as [Hlt|Hn]; [|lia].
  rewrite Mem.wa_unsigned in Hlt by lia. lia.
Qed.

(* Each disjointness leaf names image constants, FS / frame / sp offsets and shadow endpoints. *)
Ltac f36_num :=
  cbv [RcLay.ly_dj TLS_INDEX REAL_TLS_GET_ADDR TSD_KEY_INITED TSD_KEY GOT_CF CF GOT_VERBOSITY VERBOSITY
       DTLS_TPOFF RT_TP RT_TSDMAIN RT_GT ASAN_GT AC.as_tp AC.ASYMS AC.GT AC.FS_SIZE FS_SIZE RT_FS_SIZE
       CM_K AF.SLOT_STACK HIGHMEM_BEG APPMEM_END LOWMEM_END LOWSHADOW_END HIGHSHADOW_BEG ASAN_K] in *; lia.
Ltac f36_dj_split := repeat first [apply Forall_nil | apply Forall_cons]; cbn [fst snd].

Section F36.
Context {fx : AYK.FPState} {LS : lib_shape} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AC.AsanAllocAPI AC.ASYMS AsanRTInv.RT.
Context {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
Hypothesis CMC : reac_box_catalogue_match_contract.

Local Notation STKLO mem md := (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md).
Local Notation OWNED H mem md := (AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) H mem md).

(* The Lib-evt -> SR bridge (F29's sl_run_lib). *)
Lemma f36_run_lib : forall regs pc mem md
  (K : bvmap 5 word -> word -> (word -> option byte) -> Prop) (P : config -> Prop),
  m_halted md = None ->
  LE.evt rsegs
    (fun ms => exists R pc' mem', ms = MS R fp_regs pc' fp_csr None mem' (seg_rom rsegs) /\ K R pc' mem')
    (MS (Regs6ss.mkR_of regs) fp_regs pc fp_csr None mem (seg_rom rsegs)) ->
  (forall R pc' mem' regs' md', K R pc' mem' -> (forall r, getr regs' r = getr R r) -> AsanLift.mat_le md md' ->
     SR rsegs (mkCfg (mkst regs' pc' mem' (seg_rom rsegs)) md') P) ->
  SR rsegs (mkCfg (mkst regs pc mem (seg_rom rsegs)) md) P.
Proof.
  intros regs pc mem md K P Hh HE HK.
  eapply (AsanLift.evt_SR_canon_lazy rsegs (mkst regs pc mem (seg_rom rsegs)) _ md P); [exact HE | exact Hh |].
  intros ms' md' (can & (R & pc' & mem' & -> & HKR) & Heq) Hmat.
  destruct Heq as (HR & HF & Hpc & Hsvc & Hres & Hfc & Hm & Hrom).
  destruct ms' as [regs' fr' pcv' svc' rv' fc' m' ro'].
  cbn in HR, HF, Hpc, Hsvc, Hres, Hfc, Hm, Hrom. subst.
  apply (HK R _ _ regs' md' HKR); [apply kb_getr_eqv; exact HR | exact Hmat].
Qed.

(* The frame's place (plan FP.1/FP.2), as in F29. *)
Lemma f36_fra_loc : forall g fr hb regs mem md, FRA B APIf ra g fr hb regs mem md ->
  exists FS, (exists w : word, bytes_at rsegs mem RT_TP (le8 w) /\ bv_unsigned w = FS) /\
    AC.GT <= FS /\ FS + AC.FS_SIZE <= STKLO mem md /\ (forall a, FS <= a < FS + AC.FS_SIZE -> app_mem a) /\
    HIGHMEM_BEG <= STKLO mem md /\
    0 <= fr /\ AC.GT <= fr /\ (forall a, fr <= a < fr + 3136 -> app_mem a) /\
    ((STKLO mem md <= fr /\ fr + 3136 <= APPMEM_END) \/ (FS <= fr /\ fr + 3136 <= FS + AC.FS_SIZE)).
Proof.
  intros g fr hb regs mem md HFRA.
  pose proof (fra_app B APIf ra g fr hb regs mem md HFRA) as (HGTfr & Hfrapp).
  destruct HFRA as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspill & Hsel & Hfr24 & Hloc & Hhdr1 & Hhdr2 &
    Hsh & Hwin & Hsaved & Herrno & HAG & HWA & HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive).
  pose proof FRAME_BYTES_val as HFBv.
  pose proof Hwin as (Hw0 & Hw1 & _).
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as LAWS.
  pose proof (RT_fs_cells _ _ _ HRT) as (_ & _ & _ & _ & (FSw & HFSw & HFok) & _).
  pose proof (bv_unsigned_in_range 64 FSw) as HFSr. change (bv_modulus 64) with (2 ^ 64) in HFSr.
  assert (Hwm : word_mem rsegs mem (AC.as_tp AC.ASYMS) (bv_unsigned FSw)).
  { change (AC.as_tp AC.ASYMS) with RT_TP. exact (bytes_at_le8_word rsegs mem RT_TP FSw HFSw). }
  destruct (AC.a_laws_fs_place _ _ _ _ _ LAWS _ mem md (bv_unsigned FSw) HAH Hwm HFSr)
    as (HGT & HFSlo & _ & HFSapp).
  pose proof (AC.a_laws_stack_high _ _ _ _ _ LAWS _ mem md HAH) as Hhi.
  pose proof Hhdr1 as Hb1. unfold q64 in Hb1. apply bytes_at_bound in Hb1. rewrite length_le8 in Hb1.
  exists (bv_unsigned FSw).
  split; [exists FSw; split; [exact HFSw | reflexivity]|].
  split; [exact HGT|]. split; [exact HFSlo|]. split; [exact HFSapp|]. split; [exact Hhi|].
  split; [lia|]. split; [exact HGTfr|]. split; [exact Hfrapp|].
  destruct Hloc as [[_ [_ Hreal]] | [_ [_ [Hfs _]]]].
  - pose proof (Hreal fr ltac:(lia)) as R1. pose proof (Hreal (fr + 3135) ltac:(lia)) as R2. left. lia.
  - assert (HFS1 : bv_unsigned FSw + AC.FS_SIZE <= 2 ^ 64) by (unfold AF.SLOT_STACK in *; lia).
    assert (Hin : forall a, fr <= a < fr + 3136 -> bv_unsigned FSw <= a < bv_unsigned FSw + AC.FS_SIZE).
    { intros a Ha. destruct (Hfs a Ha) as (b & Hbr & Hb & Hab).
      change (AC.as_tp AC.ASYMS) with RT_TP in Hb.
      pose proof (f36_wm_uniq mem RT_TP b (bv_unsigned FSw) Hb Hwm Hbr HFSr) as E. lia. }
    pose proof (Hin fr ltac:(lia)) as F1. pose proof (Hin (fr + 3135) ltac:(lia)) as F2.
    right. lia.
Qed.

(* A byte of a live heap block is not a frame byte. *)
Lemma f36_fra_blk : forall g fr hb regs mem md p n a, FRA B APIf ra g fr hb regs mem md ->
  In (p, n) (hb ++ g_H g) -> p <= a < p + n -> fr <= a < fr + 3136 -> False.
Proof.
  intros g fr hb regs mem md p n a HFRA Hin Ha Hfa.
  destruct HFRA as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & HfrA & HA416 & HS4 & HAPP &
    Hspill & Hsel & Hfr24 & Hloc & Hhdr1 & Hhdr2 &
    Hsh & Hwin & Hsaved & Herrno & HAG & HWA & HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive).
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as LAWS.
  destruct (AC.a_laws_blocks _ _ _ _ _ LAWS _ mem md p n HAH Hin) as (_ & _ & Hend & _ & Hall).
  destruct (Hall a Ha) as (_ & _ & _ & _ & Hnfs).
  destruct Hloc as [[_ [_ Hreal]] | [_ [_ [Hfs _]]]].
  - pose proof (Hreal a Hfa). lia.
  - exact (Hnfs (Hfs a Hfa)).
Qed.

(* The sp facts the callee contract asks for. *)
Lemma f36_fra_sp : forall g fr hb regs mem md, FRA B APIf ra g fr hb regs mem md ->
  0 <= AC.aspZ regs < 2 ^ 64 /\ AC.aspZ regs mod 16 = 0 /\ AC.aspZ regs <= APPMEM_END /\
  HIGHMEM_BEG <= AC.aspZ regs - FN_STACK /\ stk rsegs mem (AC.aspZ regs - FN_STACK) (AC.aspZ regs) /\
  (exists A, rg regs 9 A /\ 0 <= A < 2 ^ 64 /\ AC.aspZ regs <= A /\ fr + 3136 <= A /\ A + 416 <= g_S g).
Proof.
  intros g fr hb regs mem md HFRA.
  destruct (fra_win B APIf ra g fr hb regs mem md HFRA) as (Hlo & Hstk).
  pose proof (AC.a_laws_stack_high _ _ _ _ _ (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc))
    (hb ++ g_H g) mem md ltac:(destruct HFRA as (A & sp & s5 & _ & HAH & _); exact HAH)) as Hhi.
  destruct HFRA as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspill & Hsel & Hfr24 & Hloc & Hhdr1 & Hhdr2 &
    Hsh & Hwin & Hsaved & Herrno & HAG & HWA & HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive).
  pose proof Hwin as (Hw0 & Hw1 & _).
  assert (HSS : AF.SLOT_STACK = 1048576) by reflexivity.
  assert (HFN : FN_STACK = 1044480) by reflexivity.
  split; [unfold AC.aspZ; exact (u64_range (getr regs 2))|].
  split; [rewrite Haspz; exact Hspm|].
  split; [rewrite Haspz; lia|].
  split; [lia|].
  split; [exact Hstk|].
  exists A. split; [exact Hr9|]. split; [lia|]. split; [rewrite Haspz; lia|]. split; [exact Hfa | exact HA416].
Qed.

(* ===================== facts about the turn's block and the frame ===================== *)

(* The harness block of the turn (heap list hb1 phi (a_size len), push 5b): every byte of [Phi, Phi + a_size len)
   is application memory, off the frame (f36_fra_blk) and off the side stack (a_laws_blocks). *)
Lemma f36_blk : forall g j phi fr regs mem md,
  FRA B APIf ra g fr (hb1 phi (AC.a_size (flen g j))) regs mem md ->
  forall x, phi <= x < phi + AC.a_size (flen g j) ->
    app_mem x /\ ~ (fr <= x < fr + 3136) /\ ~ AC.a_in_fs AC.ASYMS mem x.
Proof.
  intros g j phi fr regs mem md HFRA x Hx.
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as LAWS.
  assert (Hin : In (phi, AC.a_size (flen g j)) (hb1 phi (AC.a_size (flen g j)) ++ g_H g))
    by (apply in_or_app; left; left; reflexivity).
  pose proof HFRA as (A & sp & s5 & _ & HAH & _).
  destruct (AC.a_laws_blocks _ _ _ _ _ LAWS _ mem md phi _ HAH Hin) as (_ & _ & _ & _ & Hall).
  destruct (Hall x Hx) as (Hap & _ & _ & _ & Hnfs).
  split; [exact Hap|]. split; [|exact Hnfs].
  intros Hfr. exact (f36_fra_blk g fr _ regs mem md phi _ x HFRA Hin Hx Hfr).
Qed.

(* The spill base A = s1 (reg 9): in range, in high memory, at or above sp and the frame, below the entry sp. *)
Lemma f36_fra_A : forall g fr hb regs mem md, FRA B APIf ra g fr hb regs mem md ->
  exists A, rg regs 9 A /\ 416 <= A /\ A + 416 <= 2 ^ 64 /\ HIGHMEM_BEG <= A /\ AC.aspZ regs <= A /\
    fr + 3136 <= A /\ A + 416 <= g_S g.
Proof.
  intros g fr hb regs mem md HFRA.
  destruct (f36_fra_sp g fr hb regs mem md HFRA)
    as (Hsp64 & _ & _ & HspH & _ & (A & Hr9 & HA64 & HspA & HfrA & HA416)).
  pose proof (f36_fra_loc g fr hb regs mem md HFRA) as (FS & _ & _ & _ & _ & _ & Hfr0 & _).
  pose proof HFRA as (A' & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9' & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416' & HS4 & HAPP & _).
  assert (HFN : FN_STACK = 1044480) by reflexivity.
  exists A. split; [exact Hr9|]. unfold APPMEM_END, HIGHMEM_BEG in *. lia.
Qed.

(* A byte of an entry heap block is application memory, off the frame, off the side stack and below stklo. *)
Lemma f36_inblk : forall g fr hb regs mem md q k, FRA B APIf ra g fr hb regs mem md -> In (q, k) (g_H g) ->
  forall x, q <= x < q + k ->
    app_mem x /\ ~ (fr <= x < fr + 3136) /\ ~ AC.a_in_fs AC.ASYMS mem x /\ x < STKLO mem md.
Proof.
  intros g fr hb regs mem md q k HFRA Hq x Hx.
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as LAWS.
  assert (Hin : In (q, k) (hb ++ g_H g)) by (apply in_or_app; right; exact Hq).
  pose proof HFRA as (A & sp & s5 & _ & HAH & _).
  destruct (AC.a_laws_blocks _ _ _ _ _ LAWS _ mem md q k HAH Hin) as (_ & _ & Hend & _ & Hall).
  destruct (Hall x Hx) as (Hap & _ & _ & _ & Hnfs).
  split; [exact Hap|]. split; [intros Hfr; exact (f36_fra_blk g fr hb regs mem md q k x HFRA Hin Hx Hfr)|].
  split; [exact Hnfs | lia].
Qed.

(* ===================== the side-stack premises of the call ===================== *)

(* The class state the stack-allocation entry reads, for a class 0, 1 or 2, from a_fs_ok's presence and flag
   bytes (the hint word and the fs_M c flag bytes, each 0 or 1). *)
Lemma f36_fp_cls : forall mem FS c,
  (c <= 2)%nat -> 0 <= FS -> FS + FS_SIZE <= 2 ^ 64 ->
  (forall a, FS <= a < FS + AC.FS_SIZE -> writable_at rsegs mem a /\ exists b, mbyte rsegs mem a = Some b) ->
  (forall c j, (c <= 10)%nat -> 0 <= j < AC.a_fs_M c ->
     mbyte rsegs mem (AC.a_fs_flag FS c j) = Some (Z_to_bv 8 0) \/
     mbyte rsegs mem (AC.a_fs_flag FS c j) = Some (Z_to_bv 8 1)) ->
  fp_cls mem FS c.
Proof.
  intros mem FS c Hc HFS0 HFSb Hpres Hflag.
  assert (HSZ : FS_SIZE = 11571200) by reflexivity.
  assert (HSZc : AC.FS_SIZE = 11571200) by reflexivity.
  destruct (f36_fs_ranges FS) as (Rh0 & Rh1 & Rh2 & Rf0 & Rf1 & Rf2 & RM0 & RM1 & RM2 & _).
  assert (HB : FS <= fs_hint FS c /\ fs_hint FS c + 8 <= FS + 4096 /\
               FS + 4096 <= fs_flag FS c 0 /\ fs_flag FS c 0 + fs_M c <= FS + 32768 /\ 0 <= fs_M c).
  { destruct c as [|[|[|c]]];
      [ rewrite Rh0, Rf0, RM0 | rewrite Rh1, Rf1, RM1 | rewrite Rh2, Rf2, RM2 | lia ]; lia. }
  destruct HB as (HB1 & HB2 & HB3 & HB4 & HB5).
  unfold fp_cls. split; [lia|].
  destruct (f36_word_present mem (fs_hint FS c) ltac:(lia) ltac:(lia)
              ltac:(intros i Hi;
                    destruct (Hpres (fs_hint FS c + i) ltac:(lia)) as (_ & bb & Hbb);
                    exists bb; exact Hbb)) as (h & Hh).
  destruct (f36_bytes_P (fun b => b = Z_to_bv 8 0 \/ b = Z_to_bv 8 1) mem (fs_flag FS c 0) (fs_M c)
              ltac:(lia) ltac:(lia) ltac:(lia)
              ltac:(intros i Hi;
                    pose proof (Hflag c i ltac:(lia) ltac:(change (AC.a_fs_M c) with (fs_M c); lia)) as Hf;
                    replace (AC.a_fs_flag FS c i) with (fs_flag FS c 0 + i) in Hf
                      by (unfold AC.a_fs_flag, fs_flag; lia);
                    destruct Hf as [Hf|Hf]; [exists (Z_to_bv 8 0) | exists (Z_to_bv 8 1)];
                      (split; [exact Hf | first [left; reflexivity | right; reflexivity]])))
    as (flags & Hfl & Hfllen & Hflb).
  exists h, flags. split; [exact Hh|]. split; [exact Hfl|]. split; [exact Hfllen | exact Hflb].
Qed.

(* The two generated laws whose conclusion a positional read in this file had to follow across generation N.1b,
   each unpacked ONCE (a Theorem Labs lane 15:32Z: until generation N+1 names each part of each law, a file unpacks a law in one
   local lemma, and every site reads that lemma).  Both lemmas take every part BY NAME from a Theorem Labs lane's field
   records (Tac_fsfree.v fsf_thread_fields / fsf_fs_state_fields, which match each field to a conjunct by
   `eassumption`), so F36 counts no position of a generated conjunction; the statements type every part.
   a_laws_thread: N.1b inserted `word_mem (as_tp B - 88) RT_TSDMAIN` and the RT_TSDK bytes at positions 2 and 3,
   before `exists C T`.  a_laws_fs_state: N.1b replaced the DB cells' `~ in_blocks H a` by three conjuncts, so the
   cells' last conjunct moved from position 6 to 8 (F36 reads positions 1, 2 and 4). *)
Record f36_thr (H : list (Z * Z)) (mem : word -> option byte) (md : Model) (C T : Z) : Prop := {
  f36_thr_wmC : word_mem rsegs mem RT_TSDMAIN C;
  f36_thr_C : 0 < C < 2 ^ 64;
  f36_thr_T : 0 < T < 2 ^ 64;
  f36_thr_wmT : word_mem rsegs mem (C + 152) T;
  f36_thr_C152 : forall i, 0 <= i < 8 -> OWNED H mem md (C + 152 + i) /\ app_mem (C + 152 + i);
  f36_thr_T48 : forall i, 0 <= i < 16 ->
    OWNED H mem md (T + 48 + i) /\ exists b, mbyte rsegs mem (T + 48 + i) = Some b }.

Lemma f36_thread : forall H mem md, AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) H mem md ->
  exists C T, f36_thr H mem md C T.
Proof.
  intros H mem md HAH.
  destruct (fsf_thread_fields (APIf rc) H mem md HAH) as (C & T & HF).
  exists C, T. constructor.
  - eapply fthr_tsd_word; exact HF.
  - eapply fthr_tsd_range; exact HF.
  - eapply fthr_thr_range; exact HF.
  - eapply fthr_thr_word; exact HF.
  - intros i Hi. eapply fthr_thr_cell; eassumption.
  - intros i Hi. eapply fthr_t48; eassumption.
Qed.

Record f36_fss (mem : word -> option byte) (md : Model) (FS DB : Z) : Prop := {
  f36_fss_ok : AC.a_fs_ok mem FS;
  f36_fss_DB : 0 <= DB < 2 ^ 64;
  f36_fss_wmDB : word_mem rsegs mem (AC.as_tp AC.ASYMS + 8) DB;
  f36_fss_DBnz : DB <> 0;
  f36_fss_wmtp : word_mem rsegs mem (DB + 24) (AC.as_tp AC.ASYMS);
  f36_fss_DBapp : forall a, DB + 24 <= a < DB + 32 -> app_mem a;
  f36_fss_DBlo : forall a, DB + 24 <= a < DB + 32 -> a < STKLO mem md;
  f36_fss_DBfs : forall a, DB + 24 <= a < DB + 32 -> ~ AC.a_in_fs AC.ASYMS mem a;
  f36_fss_T48 : forall C T, word_mem rsegs mem RT_TSDMAIN C -> 0 <= C < 2 ^ 64 -> word_mem rsegs mem (C + 152) T ->
    0 <= T < 2 ^ 64 -> forall i, 0 <= i < 16 -> app_mem (T + 48 + i) }.

Lemma f36_fs_state : forall H mem md FS, AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) H mem md ->
  word_mem rsegs mem (AC.as_tp AC.ASYMS) FS -> 0 <= FS < 2 ^ 64 -> exists DB, f36_fss mem md FS DB.
Proof.
  intros H mem md FS HAH Hw Hr.
  destruct (fsf_fs_state_fields (APIf rc) H mem md FS HAH Hw Hr) as (DB & HF).
  exists DB. constructor.
  - eapply ffs_ok; exact HF.
  - eapply ffs_db_range; exact HF.
  - eapply ffs_db_word; exact HF.
  - eapply ffs_db_nz; exact HF.
  - eapply ffs_db24; exact HF.
  - intros a Ha. exact (proj1 (@ffs_db_cells _ _ _ _ _ HF a Ha)).
  - intros a Ha. exact (proj1 (proj2 (@ffs_db_cells _ _ _ _ _ HF a Ha))).
  - intros a Ha. exact (proj2 (proj2 (@ffs_db_cells _ _ _ _ _ HF a Ha))).
  - eapply ffs_t48_app; exact HF.
Qed.

(* The side-stack premises of reac_box_catalogue_match_contract (fp for the classes 0, 1, 2 and the thread cells
   apart from them) at a state with FRA: the base word at tp and its placement come from the runtime's cells
   (asan_fs_cells) and the heap laws a_laws_fs_place / a_laws_fs_state, the thread record from a_laws_thread, and
   the control-flag / verbosity / TLS cells from RT.  The caller's data range (the 50 bytes at Phi) is apart from
   the side stack because a live block is never a side-stack byte (a_laws_blocks). *)
Lemma f36_fp_call : forall g fr hb regs mem md phi len,
  FRA B APIf ra g fr hb regs mem md ->
  (50 <= len -> In (phi, len) (hb ++ g_H g)) ->
  exists FS,
    word_mem rsegs mem (AC.as_tp AC.ASYMS) FS /\ 0 <= FS < 2 ^ 64 /\ FS mod 4096 = 0 /\
    AC.GT <= FS /\ FS + AC.FS_SIZE <= AC.aspZ regs - CM_K /\
    (forall a, FS <= a < FS + AC.FS_SIZE -> app_mem a) /\
    fp [0%nat; 1%nat; 2%nat] mem (AC.as_tp AC.ASYMS) FS (AC.aspZ regs - CM_K) (AC.aspZ regs)
      (reac_box_catalogue_match_W (AC.aspZ regs)) (reac_box_catalogue_match_D phi len) /\
    reac_box_catalogue_match_tls mem (AC.as_tp AC.ASYMS) FS (AC.aspZ regs - CM_K) (AC.aspZ regs).
Proof.
  intros g fr hb regs mem md phi len HFRA Hblk.
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as LAWS.
  destruct (f36_fra_sp g fr hb regs mem md HFRA)
    as (Hsp64 & Hspm & HspA & HspH & Hstkw & (A & Hr9 & HA64 & HspAle & HfrA & HA416)).
  pose proof HFRA as HFRA0.
  destruct HFRA0 as (A' & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm' & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9' & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416' & HS4 & HAPP &
    Hspill & Hsel & Hfr24 & Hloc & Hhdr1 & Hhdr2 &
    Hsh & Hwin & Hsaved & Herrno & HAG & HWA & HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive).
  rewrite Haspz in Hsp64, Hspm, HspA, HspH, Hstkw, HspAle |- *.
  assert (ETP : AC.as_tp AC.ASYMS = RT_TP) by reflexivity.
  assert (HSS : AF.SLOT_STACK = 1048576) by reflexivity.
  assert (HFN : FN_STACK = 1044480) by reflexivity.
  assert (HCMK : CM_K = 9136) by reflexivity.
  assert (HSZ : AC.FS_SIZE = 11571200) by reflexivity.
  assert (HSZ' : FS_SIZE = 11571200) by reflexivity.
  (* ---- the side stack's base and its placement ---- *)
  destruct (RT_fs_cells _ _ _ HRT)
    as (Htlsidx & Hdtpoff & Hdt & Hdt8 & (FSw & HFSb & HFSok) & (DBw & HDBb & HDBnz & HDBapp)).
  remember (bv_unsigned FSw) as FS eqn:EFS.
  assert (HFS64 : 0 <= FS < 2 ^ 64) by (rewrite EFS; apply u64_range).
  assert (HFSwm : word_mem rsegs mem (AC.as_tp AC.ASYMS) FS).
  { rewrite ETP, EFS. exact (bytes_at_le8_word rsegs mem RT_TP FSw HFSb). }
  destruct HFSok as (HFSpos & HFSalign & HFSgt & HFSapp0).
  destruct (AC.a_laws_fs_place _ _ _ _ _ LAWS _ mem md FS HAH HFSwm HFS64)
    as (HGTFS & HFShi & HFSmod & HFSapp).
  destruct (f36_fs_state _ mem md FS HAH HFSwm HFS64) as (DBz & FSS).
  pose proof (@f36_fss_ok _ _ _ _ FSS) as (HFSpres & HFS88 & HFS96 & HFShint & HFSflag).
  pose proof (@f36_fss_DB _ _ _ _ FSS) as HDBzr. pose proof (@f36_fss_wmDB _ _ _ _ FSS) as HDBzw.
  pose proof (@f36_fss_DBnz _ _ _ _ FSS) as HDBznz. pose proof (@f36_fss_wmtp _ _ _ _ FSS) as HDBztp.
  pose proof (@f36_fss_T48 _ _ _ _ FSS) as HT48app.
  assert (NFSW : FS + AC.FS_SIZE <= sp - CM_K) by lia.
  assert (HFSub : FS + AC.FS_SIZE <= APPMEM_END).
  { pose proof (HFSapp (FS + AC.FS_SIZE - 1) ltac:(lia)) as Ha.
    unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in Ha. unfold APPMEM_END. lia. }
  assert (HWapp : forall a, sp - CM_K <= a < sp -> app_mem a).
  { intros a Ha. unfold app_mem. right. unfold HIGHMEM_BEG, APPMEM_END in *. lia. }
  (* ---- the thread record ---- *)
  destruct (f36_thread _ mem md HAH) as (C0 & T0 & TR).
  pose proof (@f36_thr_wmC _ _ _ _ _ TR) as HC0wm. pose proof (@f36_thr_C _ _ _ _ _ TR) as HC0rng.
  pose proof (@f36_thr_T _ _ _ _ _ TR) as HT0rng. pose proof (@f36_thr_wmT _ _ _ _ _ TR) as HT0wm.
  pose proof (@f36_thr_C152 _ _ _ _ _ TR) as HC152. pose proof (@f36_thr_T48 _ _ _ _ _ TR) as HT48.
  destruct (RT_uw_cells _ _ _ HRT) as (Htsdi & Htsdk & _ & Htp88 & (Cw & HCwb)).
  pose proof (bytes_at_le8_word rsegs mem RT_TSDMAIN Cw HCwb) as HCwm.
  assert (ECw : bv_unsigned Cw = C0)
    by (apply (f36_wm_uniq mem RT_TSDMAIN); [exact HCwm | exact HC0wm | apply u64_range | lia]).
  assert (HCapp : forall x, C0 + 152 <= x < C0 + 160 -> app_mem x).
  { intros x Hx. pose proof (proj2 (HC152 (x - (C0 + 152)) ltac:(lia))) as H.
    replace (C0 + 152 + (x - (C0 + 152))) with x in H by lia. exact H. }
  assert (HCpt : forall x, C0 + 152 <= x < C0 + 160 ->
            x < STKLO mem md /\ ~ (FS <= x < FS + AC.FS_SIZE)).
  { intros x Hx. destruct (HC152 (x - (C0 + 152)) ltac:(lia)) as (Hown & Hap).
    replace (C0 + 152 + (x - (C0 + 152))) with x in Hown by lia.
    pose proof (HCapp x Hx) as Hax.
    pose proof (AC.a_laws_not_owned _ _ _ _ _ LAWS _ mem md x HAH) as HNO.
    split.
    - destruct (Z_lt_le_dec x (STKLO mem md)) as [H|H]; [exact H|].
      exfalso. unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in Hax.
      assert (Hst : STKLO mem md <= x < APPMEM_END) by (unfold APPMEM_END; lia).
      exact (proj1 (HNO (or_intror (or_intror (or_intror Hst)))) Hown).
    - intros Hin.
      assert (HFSin : AC.a_in_fs AC.ASYMS mem x)
        by (exists FS; split; [exact HFS64 | split; [exact HFSwm | exact Hin]]).
      exact (proj1 (HNO (or_intror (or_intror (or_introl HFSin)))) Hown). }
  assert (HTapp : forall x, T0 + 48 <= x < T0 + 64 -> app_mem x).
  { intros x Hx.
    pose proof (HT48app C0 T0 HC0wm ltac:(lia) HT0wm ltac:(lia) (x - (T0 + 48)) ltac:(lia)) as H.
    replace (T0 + 48 + (x - (T0 + 48))) with x in H by lia. exact H. }
  assert (HTpt : forall x, T0 + 48 <= x < T0 + 64 ->
            x < STKLO mem md /\ ~ (FS <= x < FS + AC.FS_SIZE)).
  { intros x Hx. destruct (HT48 (x - (T0 + 48)) ltac:(lia)) as (Hown & _).
    replace (T0 + 48 + (x - (T0 + 48))) with x in Hown by lia.
    pose proof (HTapp x Hx) as Hax.
    pose proof (AC.a_laws_not_owned _ _ _ _ _ LAWS _ mem md x HAH) as HNO.
    split.
    - destruct (Z_lt_le_dec x (STKLO mem md)) as [H|H]; [exact H|].
      exfalso. unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in Hax.
      assert (Hst : STKLO mem md <= x < APPMEM_END) by (unfold APPMEM_END; lia).
      exact (proj1 (HNO (or_intror (or_intror (or_intror Hst)))) Hown).
    - intros Hin.
      assert (HFSin : AC.a_in_fs AC.ASYMS mem x)
        by (exists FS; split; [exact HFS64 | split; [exact HFSwm | exact Hin]]).
      exact (proj1 (HNO (or_intror (or_intror (or_introl HFSin)))) Hown). }
  assert (HTpres : forall i, 0 <= i < 16 -> exists b, mbyte rsegs mem (T0 + 48 + i) = Some b)
    by (intros i Hi; exact (proj2 (HT48 i Hi))).
  (* ---- the thread's DTLS record ---- *)
  assert (EDBw : bv_unsigned DBw = DBz).
  { pose proof (bytes_at_le8_word rsegs mem (RT_TP + 8) DBw HDBb) as HDBwm.
    apply (f36_wm_uniq mem (AC.as_tp AC.ASYMS + 8));
      [rewrite ETP; exact HDBwm | exact HDBzw | apply u64_range | lia]. }
  assert (HDBpt : forall x, DBz + 24 <= x < DBz + 32 ->
            app_mem x /\ x < STKLO mem md /\ ~ (FS <= x < FS + AC.FS_SIZE)).
  { intros x Hx.
    split; [exact (@f36_fss_DBapp _ _ _ _ FSS x Hx)|]. split; [exact (@f36_fss_DBlo _ _ _ _ FSS x Hx)|].
    intros Hin. apply (@f36_fss_DBfs _ _ _ _ FSS x Hx).
    exists FS. split; [exact HFS64 | split; [exact HFSwm | exact Hin]]. }
  assert (NC0 : C0 + 160 <= APPMEM_END).
  { pose proof (HCapp (C0 + 159) ltac:(lia)) as H.
    unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in H. unfold APPMEM_END. lia. }
  assert (NT0 : T0 + 64 <= APPMEM_END).
  { pose proof (HTapp (T0 + 63) ltac:(lia)) as H.
    unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in H. unfold APPMEM_END. lia. }
  assert (NDB0 : DBz + 32 <= APPMEM_END).
  { pose proof (proj1 (HDBpt (DBz + 31) ltac:(lia))) as H.
    unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in H. unfold APPMEM_END. lia. }
  assert (NC : C0 + 160 <= STKLO mem md) by (pose proof (proj1 (HCpt (C0 + 159) ltac:(lia))); lia).
  assert (NT : T0 + 64 <= STKLO mem md) by (pose proof (proj1 (HTpt (T0 + 63) ltac:(lia))); lia).
  assert (NDB : DBz + 32 <= STKLO mem md)
    by (pose proof (proj1 (proj2 (HDBpt (DBz + 31) ltac:(lia)))); lia).
  assert (HDB24 : bytes_at rsegs mem (bv_unsigned DBw + 24) (le8 (Z_to_bv 64 (AC.as_tp AC.ASYMS)))).
  { rewrite EDBw.
    apply (word_mem_le8 rsegs mem (DBz + 24) (AC.as_tp AC.ASYMS) HDBztp);
      [rewrite ETP; unfold RT_TP; lia | lia | lia]. }
  (* ---- the thread cells ---- *)
  assert (EDTu : bv_unsigned (Z_to_bv 64 (AC.as_tp AC.ASYMS + 32)) = AC.as_tp AC.ASYMS + 32)
    by (apply MState.unsigned_lit; rewrite ETP; unfold RT_TP; lia).
  assert (ETSu : bv_unsigned (Z_to_bv 64 RT_TSDMAIN) = RT_TSDMAIN)
    by (apply MState.unsigned_lit; unfold RT_TSDMAIN; lia).
  assert (ETu : bv_unsigned (Z_to_bv 64 T0) = T0) by (apply MState.unsigned_lit; lia).
  pose proof (word_mem_le8 rsegs mem (C0 + 152) T0 HT0wm ltac:(lia) ltac:(lia) ltac:(lia)) as HT0b.
  destruct (f36_word_present mem (T0 + 48) ltac:(lia) ltac:(lia)
              ltac:(intros i Hi; exact (HTpres i ltac:(lia)))) as (tb & Htb).
  assert (HTpres2 : forall i, 0 <= i < 8 -> exists b, mbyte rsegs mem (T0 + 56 + i) = Some b).
  { intros i Hi. replace (T0 + 56 + i) with (T0 + 48 + (8 + i)) by lia. exact (HTpres (8 + i) ltac:(lia)). }
  destruct (f36_word_present mem (T0 + 56) ltac:(lia) ltac:(lia) HTpres2) as (te & Hte).
  assert (HTBE : bytes_at rsegs mem (T0 + 48) (le8 tb ++ le8 te)).
  { apply (proj2 (bytes_at_app rsegs mem (T0 + 48) (le8 tb) (le8 te))).
    split; [exact Htb|]. rewrite length_le8.
    replace (T0 + 48 + Z.of_nat 8) with (T0 + 56) by lia. exact Hte. }
  destruct (RT_cf_cells _ _ _ HRT) as (Hcf1 & _ & _ & _ & _ & Hcf137 & _ & _).
  destruct (RT_opt_cells _ _ _ HRT) as (_ & _ & Hopt3 & Hopt4).
  pose proof (RT_real_cells _ _ _ HRT) as HREAL.
  assert (HTLS : asan_tls_cells mem (AC.as_tp AC.ASYMS) (Z_to_bv 64 (AC.as_tp AC.ASYMS + 32))
                   (Z_to_bv 64 RT_TSDMAIN) Cw (Z_to_bv 64 T0) DBw 0).
  { unfold asan_tls_cells. rewrite EDTu, ETSu, ETu, ECw, ETP.
    split; [unfold TLS_INDEX; exact Htlsidx|].
    split; [exact (real_cell_of mem REAL_TLS_GET_ADDR MUSL_TLS_GET_ADDR HREAL
                     ltac:(vm_compute; reflexivity))|].
    split; [exact Hdt|].
    split; [replace (RT_TP + 32 + 8) with (RT_TP + 40) by lia; exact Hdt8|].
    split; [unfold TSD_KEY_INITED; exact Htsdi|].
    split; [unfold TSD_KEY; lia|].
    split; [unfold TSD_KEY; exact Htsdk|].
    split; [exact Htp88|].
    split; [replace (RT_TSDMAIN + 8 * 0) with RT_TSDMAIN by lia; exact HCwb|].
    split; [exact HT0b|].
    split; [exists tb, te; exact HTBE|].
    split; [unfold GOT_CF; exact Hcf1|].
    split; [unfold CF; exact Hcf137|].
    split; [unfold GOT_VERBOSITY; exact Hopt3|].
    split; [unfold VERBOSITY; exact Hopt4|].
    split; [unfold DTLS_TPOFF; exact Hdtpoff|].
    split; [exact HDBb|].
    split; [rewrite EDBw; lia|].
    rewrite ETP in HDB24. exact HDB24. }
  (* ---- numeric facts for the disjointness leaves ---- *)
  assert (SB1 : LOWMEM_END <= shadow_addr (FS + 36864)) by (apply f36_sh_lo; lia).
  assert (SB2 : LOWMEM_END <= shadow_addr (FS + 1085440)) by (apply f36_sh_lo; lia).
  assert (SB3 : LOWMEM_END <= shadow_addr (FS + 2134016)) by (apply f36_sh_lo; lia).
  assert (SB4 : LOWMEM_END <= shadow_addr (FS + 3182592)) by (apply f36_sh_lo; lia).
  assert (SB5 : LOWMEM_END <= shadow_addr (sp - CM_K)) by (apply f36_sh_lo; lia).
  assert (SB6 : LOWMEM_END <= shadow_addr sp) by (apply f36_sh_lo; lia).
  assert (SH1 : shadow_addr (FS + 36864) <= HIGHMEM_BEG) by (apply f36_sh_hi; lia).
  assert (SH2 : shadow_addr (FS + 1085440) <= HIGHMEM_BEG) by (apply f36_sh_hi; lia).
  assert (SH3 : shadow_addr (FS + 2134016) <= HIGHMEM_BEG) by (apply f36_sh_hi; lia).
  assert (SH4 : shadow_addr (FS + 3182592) <= HIGHMEM_BEG) by (apply f36_sh_hi; lia).
  assert (SH5 : shadow_addr (sp - CM_K) <= HIGHMEM_BEG) by (apply f36_sh_hi; lia).
  assert (SH6 : shadow_addr sp <= HIGHMEM_BEG) by (apply f36_sh_hi; lia).
  assert (HGAP : forall x, LOWMEM_END <= x < HIGHMEM_BEG -> ~ app_mem x).
  { intros x Hx Hap. unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in *. lia. }
  assert (AS_C : RcLay.ly_dj (C0 + 152) (C0 + 160) LOWMEM_END HIGHMEM_BEG).
  { apply (f36_dj_pt app_mem); [lia | unfold LOWMEM_END, HIGHMEM_BEG; lia | exact HCapp | exact HGAP]. }
  assert (AS_T : RcLay.ly_dj (T0 + 48) (T0 + 64) LOWMEM_END HIGHMEM_BEG).
  { apply (f36_dj_pt app_mem); [lia | unfold LOWMEM_END, HIGHMEM_BEG; lia | exact HTapp | exact HGAP]. }
  assert (AS_DB : RcLay.ly_dj (DBz + 24) (DBz + 32) LOWMEM_END HIGHMEM_BEG).
  { apply (f36_dj_pt app_mem); [lia | unfold LOWMEM_END, HIGHMEM_BEG; lia
    | intros x Hx; exact (proj1 (HDBpt x Hx)) | exact HGAP]. }
  assert (DJ_C_FS : RcLay.ly_dj FS (FS + AC.FS_SIZE) (C0 + 152) (C0 + 160)).
  { apply (f36_dj_pt (fun x => FS <= x < FS + AC.FS_SIZE));
      [lia | lia | intros x Hx; exact Hx | intros x Hx; exact (proj2 (HCpt x Hx))]. }
  assert (DJ_T_FS : RcLay.ly_dj FS (FS + AC.FS_SIZE) (T0 + 48) (T0 + 64)).
  { apply (f36_dj_pt (fun x => FS <= x < FS + AC.FS_SIZE));
      [lia | lia | intros x Hx; exact Hx | intros x Hx; exact (proj2 (HTpt x Hx))]. }
  assert (DJ_DB_FS : RcLay.ly_dj FS (FS + AC.FS_SIZE) (DBz + 24) (DBz + 32)).
  { apply (f36_dj_pt (fun x => FS <= x < FS + AC.FS_SIZE));
      [lia | lia | intros x Hx; exact Hx | intros x Hx; exact (proj2 (proj2 (HDBpt x Hx)))]. }
  (* ---- the goal ---- *)
  exists FS.
  split; [exact HFSwm|].
  split; [exact HFS64|].
  split; [exact HFSmod|].
  split; [exact HGTFS|].
  split; [exact NFSW|].
  split; [exact HFSapp|].
  split.
  { exists (Z_to_bv 64 (AC.as_tp AC.ASYMS + 32)), (Z_to_bv 64 RT_TSDMAIN), Cw, (Z_to_bv 64 T0), DBw, 0.
    split; [exact HTLS|].
    split; [rewrite ETP, EFS, MState.Z_to_bv_bv_unsigned; exact HFSb|].
    split.
    { unfold fs_place. split; [lia|]. split; [exact HFSmod|].
      split; [unfold ASAN_GT; unfold AC.GT in HGTFS; lia|].
      split; [intros a Ha; apply HFSapp; lia|].
      split; [lia|]. split; [lia|].
      intros a Ha. destruct (HFSpres a ltac:(lia)) as (Hw & b & Hb).
      split; [exact Hw | exists b; exact Hb]. }
    split; [exact (word_mem_le8 rsegs mem (FS + 88) 20 HFS88 ltac:(lia) ltac:(lia) ltac:(lia))|].
    split.
    { split; [lia|]. split; [cbn [length]; lia|]. intros i Hi. cbn [length] in Hi.
      destruct i as [|i]; [|lia]. rewrite Z.add_0_r. exact HFS96. }
    split.
    { apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]];
        apply (f36_fp_cls mem FS); solve [ lia | exact HFSpres | exact HFSflag ]. }
    split; [lia|].
    split; [exact HWapp|].
    split.
    { unfold reac_box_catalogue_match_W, fp_dj. cbn [fp_tls app].
      rewrite ?EDTu, ?ETSu, ?ETu, ?ECw, ?EDBw.
      destruct (f36_fs_ranges FS) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Rfr0 & _). rewrite Rfr0.
      clear - HspH HspA HFS64 HGTFS NFSW HFSub NC NT NDB Hstklo HS4 HC0rng HT0rng HDBzr NC0 NT0 NDB0
        HSS HFN HCMK HSZ HSZ'.
      f36_dj_split; f36_num. }
    { unfold reac_box_catalogue_match_D.
      destruct (Z.ltb_spec0 len 50) as [Hlt|Hge]; [unfold fp_dj; apply Forall_nil|].
      assert (HPHI : forall x, phi <= x < phi + 50 -> app_mem x /\ ~ (FS <= x < FS + AC.FS_SIZE)).
      { intros x Hx.
        destruct (AC.a_laws_blocks _ _ _ _ _ LAWS _ mem md phi len HAH (Hblk ltac:(lia)))
          as (_ & _ & _ & _ & Hb).
        destruct (Hb x ltac:(lia)) as (Hap & _ & _ & _ & Hnfs).
        split; [exact Hap|]. intros Hin. apply Hnfs.
        exists FS. split; [exact HFS64 | split; [exact HFSwm | exact Hin]]. }
      assert (AS_PHI : RcLay.ly_dj phi (phi + 50) LOWMEM_END HIGHMEM_BEG).
      { apply (f36_dj_pt app_mem); [lia | unfold LOWMEM_END, HIGHMEM_BEG; lia
        | intros x Hx; exact (proj1 (HPHI x Hx)) | exact HGAP]. }
      assert (DJ_PHI_FS : RcLay.ly_dj FS (FS + AC.FS_SIZE) phi (phi + 50)).
      { apply (f36_dj_pt (fun x => FS <= x < FS + AC.FS_SIZE));
          [lia | lia | intros x Hx; exact Hx | intros x Hx; exact (proj2 (HPHI x Hx))]. }
      destruct (f36_fs_ranges FS) as
        (Rh0 & Rh1 & Rh2 & Rf0 & Rf1 & Rf2 & RM0 & RM1 & RM2 & Rfr0 & Rfr0' & Rfr1 & Rfr1' & Rfr2 & Rfr2').
      unfold fp_dj, fp_w, fp_w1. cbn [flat_map app].
      rewrite Rfr0, Rfr0', Rfr1, Rfr1', Rfr2, Rfr2', Rh0, Rh1, Rh2, Rf0, Rf1, Rf2, RM0, RM1, RM2.
      clear - AS_PHI DJ_PHI_FS HGTFS HFS64 NFSW HFSub HspH HspA SB1 SB2 SB3 SB4 SB5 SB6 SH1 SH2 SH3 SH4 SH5 SH6
        Hge HSS HFN HCMK HSZ HSZ'.
      f36_dj_split; f36_num. } }
  { intros DT' TS' C' T' DB' k' HT'.
    assert (HOUT : Forall (fun d => forall x, fst d <= x < snd d -> outside (@nil ivl) x)
                     (fp_tls (AC.as_tp AC.ASYMS) (Z_to_bv 64 (AC.as_tp AC.ASYMS + 32))
                        (Z_to_bv 64 RT_TSDMAIN) Cw (Z_to_bv 64 T0) DBw 0)).
    { apply Forall_forall. intros d _ x _. exact I. }
    destruct (fl_tls_same mem mem [] (AC.as_tp AC.ASYMS)
                (Z_to_bv 64 (AC.as_tp AC.ASYMS + 32)) (Z_to_bv 64 RT_TSDMAIN) Cw (Z_to_bv 64 T0) DBw 0
                DT' TS' C' T' DB' k' HTLS HT' (munch_refl (@nil ivl) mem) HOUT)
      as (E1 & E2 & E3 & E4 & E5 & E6).
    subst DT' TS' C' T' DB' k'.
    destruct (f36_fs_ranges FS) as
      (Rh0 & Rh1 & Rh2 & Rf0 & Rf1 & Rf2 & RM0 & RM1 & RM2 & Rfr0 & Rfr0' & Rfr1 & Rfr1' & Rfr2 & Rfr2').
    unfold fp_dj, fp_w, fp_w1, fp_tls. cbn [flat_map app].
    rewrite Rfr0, Rfr0', Rfr1, Rfr1', Rfr2, Rfr2', Rh0, Rh1, Rh2, Rf0, Rf1, Rf2, RM0, RM1, RM2.
    rewrite ?EDTu, ?ETSu, ?ETu, ?ECw, ?EDBw.
    clear - AS_C AS_T AS_DB DJ_C_FS DJ_T_FS DJ_DB_FS HGTFS HFS64 NFSW HFSub SB1 SB2 SB3 SB4 SB5 SB6
      SH1 SH2 SH3 SH4 SH5 SH6 HC0rng HT0rng HDBzr NC0 NT0 NDB0 HspH HspA HSS HFN HCMK HSZ HSZ'
      NC NT NDB Hstklo HS4 Hsp64 EDTu ETSu ETu ECw EDBw.
    f36_dj_split; f36_num. }
Qed.

(* ===================== FRA across the segment's two kinds of run ===================== *)

(* FRA across a run that writes n shadow bytes of the frame, [S(fr) + o, S(fr) + o + n) with o + n <= 392 (the
   four stores at 0x828a0 and the one at 0x828c0): Tac_slot.sl_fr_meta, with the heap invariant from
   Tac_fs.a_fs_ok_store_AH (each written byte is the shadow of a frame byte, which is in the store set of the
   real-stack arm or the shadow of a side-stack byte on the side arm). *)
Lemma f36_fra_meta : forall g fr hb regs regs' mem mem' md (o n : Z),
  FRA B APIf ra g fr hb regs mem md ->
  0 <= o -> 0 < n -> o + n <= 392 ->
  munch [(Sfr fr + o, Sfr fr + o + n)] mem mem' -> wmono rsegs mem mem' -> ro_agree rsegs mem' ->
  (forall x, Sfr fr + o <= x < Sfr fr + o + n -> exists b, mrd rsegs mem' (wa x) = Some b) ->
  getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  getr regs' 8 = getr regs 8 -> getr regs' 9 = getr regs 9 -> getr regs' 19 = getr regs 19 ->
  getr regs' 26 = getr regs 26 ->
  FRA B APIf ra g fr hb regs' mem' md /\
  STKLO mem' md = STKLO mem md /\
  AC.aa_stkhi AC.ASYMS AsanRTInv.RT (APIf rc) mem' md = AC.aa_stkhi AC.ASYMS AsanRTInv.RT (APIf rc) mem md /\
  (forall q, OWNED (hb ++ g_H g) mem' md q <-> OWNED (hb ++ g_H g) mem md q).
Proof.
  intros g fr hb regs regs' mem mem' md o n HFRA Ho Hn Hon MU WM HroM HnewP E2 E3 E4 E8 E9 E19 E26.
  pose proof (f36_fra_loc g fr hb regs mem md HFRA)
    as (FS & (FSw & HFSw & EFS) & HGTFS & HFSlo & HFSapp & Hhi & Hfr0 & HGTfr & Hfrapp & Hfrloc).
  pose proof HFRA as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspill & Hsel & Hfr24 & Hloc & Hhdr1 & Hhdr2 &
    (sh & Hsh & Hshl) & Hwin & Hsaved & Herrno & HAG & HWA & HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive).
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as LAWS.
  pose proof Hwin as (Hw0 & Hw1 & _).
  assert (HSS : AF.SLOT_STACK = 1048576) by reflexivity.
  assert (HA64 : 0 <= A < 2 ^ 64) by lia.
  assert (HAhi : HIGHMEM_BEG <= A) by (unfold AF.SLOT_STACK in *; lia).
  assert (Hfr8 : fr mod 8 = 0) by (revert Hfrm; clear; Z.div_mod_to_equations; lia).
  set (S3 := Sfr fr) in *.
  assert (HSh : forall x, S3 <= x < S3 + 392 ->
    in_shadow x /\ shadow_addr (fr + 8 * (x - S3)) = x /\ fr <= fr + 8 * (x - S3) < fr + 3136).
  { intros x Hx.
    assert (E : shadow_addr (fr + 8 * (x - S3)) = x)
      by (rewrite f36_sh_frame_of by lia; unfold S3, Sfr; lia).
    split; [rewrite <- E; apply shadow_of_app, Hfrapp; lia | split; [exact E | lia]]. }
  pose proof (f36_in_shadow_bnd _ (proj1 (HSh S3 ltac:(lia)))) as HS3a.
  pose proof (f36_in_shadow_bnd _ (proj1 (HSh (S3 + 391) ltac:(lia)))) as HS3b.
  set (W := [(S3 + o, S3 + o + n)]) in *.
  assert (HWsh : forall x, S3 + o <= x < S3 + o + n -> in_shadow x) by (intros x Hx; apply HSh; lia).
  assert (HWapp : forall x, app_mem x -> outside W x).
  { intros x Hx. cbn [outside]. split; [|exact I]. intros Hin. exact (app_not_shadow x Hx (HWsh x Hin)). }
  assert (HWhi : forall x, HIGHMEM_BEG <= x -> outside W x).
  { intros x Hx. cbn [outside]. split; [|exact I]. intros Hin.
    pose proof (f36_in_shadow_bnd _ (HWsh x Hin)). lia. }
  assert (HWsh2 : forall x, ~ (S3 <= x < S3 + 392) -> outside W x).
  { intros x Hx. cbn [outside]. split; [|exact I]. lia. }
  assert (HpresM : forall x, 0 <= x < 2 ^ 64 -> (exists b, mrd rsegs mem (wa x) = Some b) ->
    exists b, mrd rsegs mem' (wa x) = Some b).
  { intros x Hx Hp. destruct (Z_le_gt_dec (S3 + o) x); [destruct (Z_lt_ge_dec x (S3 + o + n))|].
    - apply HnewP. lia.
    - unfold mrd in *. rewrite MU; [exact Hp|]. rewrite wa_unsigned by lia.
      cbn [outside]. split; [lia | exact I].
    - unfold mrd in *. rewrite MU; [exact Hp|]. rewrite wa_unsigned by lia.
      cbn [outside]. split; [lia | exact I]. }
  assert (Hsh' : exists sh', bytes_at rsegs mem' S3 sh' /\ length sh' = 392%nat).
  { apply f36_ba_present; [unfold LOWMEM_END in *; lia | unfold HIGHMEM_BEG in *; lia |].
    intros i Hi. apply HpresM; [unfold LOWMEM_END, HIGHMEM_BEG in *; lia|].
    apply (f36_ba_some mem S3 sh); [exact Hsh | rewrite Hshl, FRAME_SHADOW_val; lia]. }
  (* ro_agree mem' is a premise (push 5b: no mem_inv in FRA). *)
  assert (Hrtdj : rt_disjoint W).
  { subst W. unfold rt_disjoint, RT_LO, RT_HI, RT_GOT_AF, RT_AF, RT_GOT_VERB, RT_VERB, RT_GOT_CF, RT_CF,
      RT_TSDI, RT_TSDK, RT_PGSZ, RT_TP, RT_TSDMAIN, RT_REAL_LO, RT_REAL_HI, RT_IMAP, RT_IMEM, RT_MUG, RT_AGLOB,
      RT_AGLOB_LEN.
    unfold LOWMEM_END in HS3a. cbn [disjoint_from]. repeat split; first [left; lia | exact I]. }
  pose proof (bv_unsigned_in_range 64 FSw) as HFSr. change (bv_modulus 64) with (2 ^ 64) in HFSr.
  rewrite EFS in HFSr.
  assert (Hwm : word_mem rsegs mem (AC.as_tp AC.ASYMS) FS).
  { change (AC.as_tp AC.ASYMS) with RT_TP. rewrite <- EFS.
    exact (bytes_at_le8_word rsegs mem RT_TP FSw HFSw). }
  assert (Hfsz : FS + AC.FS_SIZE <= 2 ^ 64) by (unfold AF.SLOT_STACK in *; lia).
  assert (Hmeta : forall q, fs_meta FS q -> outside W q).
  { intros q Hq. apply HWapp. apply HFSapp. split; [exact (f36_fs_meta_ge FS q Hq)|].
    pose proof (fs_meta_below FS q Hq). unfold AC.FS_SIZE. lia. }
  assert (Hagree : forall q, 0 <= q < 2 ^ 64 ->
    ~ AC.a_store_ok (hb ++ g_H g) (STKLO mem md) q -> ~ (FS <= q < FS + AC.FS_SIZE) ->
    ~ (exists b, FS <= b < FS + AC.FS_SIZE /\ q = shadow_addr b) -> mem' (Z_to_bv 64 q) = mem (Z_to_bv 64 q)).
  { intros q Hq Hns Hnf Hnsh. apply MU. rewrite unsigned_lit by lia. cbn [outside]. split; [|exact I].
    intros Hin. destruct (HSh q ltac:(lia)) as (_ & Eq & Hb).
    destruct Hfrloc as [[Hlo Hhi'] | [Hlo Hhi']].
    - apply Hns. unfold AC.a_store_ok. right; right; right. exists (fr + 8 * (q - S3)).
      split; [symmetry; exact Eq|]. right; left. lia.
    - apply Hnsh. exists (fr + 8 * (q - S3)). split; [lia | symmetry; exact Eq]. }
  destruct (a_fs_ok_store_AH AC.ASYMS _ _ _ _ W _ mem mem' md FS LAWS HAH Hwm HFSr Hfsz MU
              (fun q _ Hw => WM _ Hw) (fun q Hq Hp => HpresM q Hq Hp) Hmeta Hagree)
    as (HAH' & HOWN & HSTK & HSTKHI).
  assert (HAG' : forall a, in_globals AF.frame_AG a -> addressable mem' a 1).
  { intros a Hin. pose proof (f36_ag_bound a Hin) as Hab.
    apply (f36_addr_keep W mem mem' a 1 (HAG a Hin) MU). intros i Hi.
    assert (Hlt : shadow_addr (a + i) < S3)
      by (unfold S3, Sfr; apply f36_sh_lt; [exact Hfr8 | unfold AC.GT in HGTfr; lia]).
    apply HWsh2. lia. }
  split; [|split; [exact HSTK | split; [exact HSTKHI | exact HOWN]]].
  apply (sl_fr_meta B APIf ra empty FF g fr _ regs regs' mem mem' md W HFRA MU WM HroM Hrtdj HAH' HSTK
           Hfrapp HGTfr Hsh').
  - intros x Hx Hn1 Hn2. exact (HWsh2 x Hn2).
  - intros A1 HA1 HA1r x Hx.
    assert (EA : A1 = A) by (apply (f36_reg_eq regs 9 A1 A HA1 Hr9 HA1r HA64)).
    apply HWhi. lia.
  - intros x Hx. apply HWhi. lia.
  - intros A1 HA1 HA1r x Hx.
    assert (EA : A1 = A) by (apply (f36_reg_eq regs 9 A1 A HA1 Hr9 HA1r HA64)).
    apply HWhi. lia.
  - intros x Hx. left. apply HWhi. unfold AF.SLOT_STACK in *. lia.
  - exact HAG'.
  - exact E2.
  - exact E3.
  - exact E4.
  - exact E8.
  - exact E9.
  - exact E19.
  - exact E26.
Qed.

(* FSREC (the side-arm FakeStack frame record) across the callee's run: the tp word is in the low image, the
   class-6 flag byte lies between the class-0..5 flags and the class-0 frames, and the slot's last word is in the
   class-6 slots -- all in [FS + 32768, FS + FS_SIZE) outside the class-0/1/2 frames, which the callee does not
   write (it writes the class-0/1/2 hint, flag and frame bytes, its window and the window's shadow). *)
Lemma f36_fsrec_call : forall hb mem mem' md W fr,
  FSREC fr mem ->
  AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) hb mem md ->
  munch W mem mem' ->
  (forall x, 0 <= x < 6283264 -> outside W x) ->
  (forall FS, word_mem rsegs mem (AC.as_tp AC.ASYMS) FS -> 0 <= FS < 2 ^ 64 ->
     forall x, FS + 32768 <= x < FS + AC.FS_SIZE -> ~ (FS + 36864 <= x < FS + 3182592) -> outside W x) ->
  FSREC fr mem'.
Proof.
  intros hb mem mem' md W fr (FS & j & Htp & HFSr & Hj & Hfr & Hflag & Htail) HAH MU HWlo HWfs.
  destruct (AC.a_laws_fs_place _ _ _ _ _ (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc))
              hb mem md FS HAH Htp HFSr) as (HGTb & _ & _ & Happ).
  assert (HFSZ : AC.FS_SIZE = 11571200) by reflexivity.
  assert (HB6 : fs_B 6 = 4096) by reflexivity.
  assert (HM6 : fs_M 6 = 256) by reflexivity.
  assert (Hfl : fs_flag FS 6 j = FS + 36352 + j) by (unfold fs_flag; cbn; lia).
  assert (Hfrv : fr = FS + 6328320 + j * 4096) by (rewrite Hfr; unfold fs_frame, fs_B; cbn; lia).
  rewrite HM6 in Hj.
  exists FS, j.
  split.
  { intros k Hk.
    assert (Hx : 0 <= AC.as_tp AC.ASYMS + Z.of_nat k < 6283264) by (unfold AC.as_tp, AC.ASYMS; cbn; lia).
    assert (Hm : mem' (Z_to_bv 64 (AC.as_tp AC.ASYMS + Z.of_nat k))
                 = mem (Z_to_bv 64 (AC.as_tp AC.ASYMS + Z.of_nat k))).
    { apply MU. rewrite MState.unsigned_lit by lia. apply HWlo. exact Hx. }
    unfold mbyte. rewrite Hm. exact (Htp k Hk). }
  split; [exact HFSr|].
  split; [rewrite HM6; exact Hj|].
  split; [exact Hfr|].
  split.
  { eapply fl_bytes; [exact Hflag | exact MU |].
    cbn [length]. intros x Hx. apply (HWfs FS Htp HFSr); lia. }
  { eapply fl_bytes; [exact Htail | exact MU |].
    rewrite length_le8. intros x Hx. apply (HWfs FS Htp HFSr); rewrite HB6 in *; lia. }
Qed.

(* FRA across the callee's run: it writes its own window [sp - 9136, sp), the class-0/1/2 side-stack bytes and the
   shadow of its window.  RT by RT_meta_write (every shadow byte is readable again: the callee's shadow_rw), AH and
   stklo by a_laws_fs_store (the written bytes are the window, the side stack or the shadow of either), and every
   other FRA cell is outside the write set: the low image, the frame body and its 392 shadow bytes (the cut keeps
   the frame apart from the classes 0-2 and the window), the spills at [s1 + 16] / [s1 + 24] / [s1 + 304] (v1.8:
   [s1 + 24] / [s1 + 32] / [s1 + 304]) and the saved registers (above sp), and the entry window (still backed inside
   [sp - 9136, sp)). *)
Lemma f36_fra_run : forall g fr hb regs regs' mem mem' md W,
  FRA B APIf ra g fr hb regs mem md ->
  munch W mem mem' -> wmono rsegs mem mem' -> ro_agree rsegs mem' -> rt_disjoint W ->
  AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) (hb ++ g_H g) mem' md ->
  STKLO mem' md = STKLO mem md ->
  (forall a, in_shadow a -> exists b, mrd rsegs mem' (wa a) = Some b) ->
  (exists sh, bytes_at rsegs mem' (Sfr fr) sh /\ length sh = 392%nat) ->
  (forall x, 0 <= x < 6283264 -> outside W x) ->
  (forall x, fr <= x < fr + 24 -> outside W x) ->
  (forall x, bv_unsigned (getr regs 9) + 24 <= x < bv_unsigned (getr regs 9) + 32 -> outside W x) ->
  (forall x, bv_unsigned (getr regs 9) + 16 <= x < bv_unsigned (getr regs 9) + 24 -> outside W x) ->
  (forall x, bv_unsigned (getr regs 9) + 304 <= x < bv_unsigned (getr regs 9) + 312 -> outside W x) ->
  (forall x, g_S g - 104 <= x < g_S g -> outside W x) ->
  (forall x, g_S g - AF.SLOT_STACK <= x < g_S g -> outside W x \/ exists b, mrd rsegs mem' (wa x) = Some b) ->
  (forall a, in_globals AF.frame_AG a -> addressable mem' a 1) ->
  (forall a, g_S g - AF.SLOT_STACK <= a < g_S g -> ~ (fr <= a < fr + 3136) -> addressable mem' a 1) ->
  (FSREC fr mem -> FSREC fr mem') ->
  getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  getr regs' 8 = getr regs 8 -> getr regs' 9 = getr regs 9 -> getr regs' 19 = getr regs 19 ->
  getr regs' 26 = getr regs 26 ->
  FRA B APIf ra g fr hb regs' mem' md.
Proof.
  intros g fr hb regs regs' mem mem' md W HFRA MU WM HRO HD HAH' HSTK HshR Hshnew HWlo HWhdr HWsel HWfr24
    HWspill HWsaved HWwin HAG' HWA' HREC E2 E3 E4 E8 E9 E19 E26.
  pose proof FF as (SEGS & _ & _ & _ & Hhead & Hlock & Hthr & _).
  destruct HFRA as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspill & Hsel & Hfr24 & Hloc & Hhdr1 & Hhdr2 &
    Hsh & Hwin & Hsaved & Herrno & HAG & HWA & HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive).
  assert (HSS : AF.SLOT_STACK = 1048576) by reflexivity.
  assert (HA64 : 0 <= A < 2 ^ 64) by (unfold stk in Hwin; destruct Hwin as (Hw0 & Hw1 & _); lia).
  assert (HbvA : bv_unsigned (getr regs 9) = A).
  { unfold rg in Hr9. rewrite Hr9. apply MState.unsigned_lit. exact HA64. }
  rewrite HbvA in HWsel, HWspill, HWfr24.
  assert (KBlo : forall (sg : list Segment) x, 0 <= x -> x < 6283264 -> mbyte sg mem' x = mbyte sg mem x).
  { intros sg x H0 H1. unfold mbyte. rewrite (MU (Z_to_bv 64 x)); [reflexivity|].
    rewrite MState.unsigned_lit by lia. exact (HWlo x ltac:(lia)). }
  exists A, sp, s5.
  split; [exact (AsanRTInv.RT_meta_write sp sp mem mem' md md W HRT MU WM HD HshR)|].
  split; [exact HAH'|].
  split; [exact HRO|].
  split.
  { destruct Hsn as (Hcse & Hohd & Hfd). split; [|split; [|exact Hfd]].
    - destruct Hcse as (Hthrm & Hlockm). split.
      + eapply YI14.val_mem_frame; [|exact Hthrm]. intros x Hx. apply KBlo.
        * lia.
        * rewrite Hthr in Hx. cbn in Hx. lia.
      + eapply YI14.val_mem_frame; [|exact Hlockm]. intros x Hx. apply KBlo.
        * lia.
        * rewrite Hlock in Hx. cbn in Hx. lia.
    - intros k Hk. rewrite KBlo.
      + exact (Hohd k Hk).
      + rewrite Hhead. lia.
      + rewrite Hhead. lia. }
  split; [exact Hhalt|].
  split.
  { intros a Hin. rewrite KBlo.
    - exact (Hgimg a Hin).
    - destruct Hin as (lo & len & Hil & Hr). unfold AF.frame_RELRO in Hil. cbn in Hil.
      destruct Hil as [E|[]]; injection E as <- <-; lia.
    - destruct Hin as (lo & len & Hil & Hr). unfold AF.frame_RELRO in Hil. cbn in Hil.
      destruct Hil as [E|[]]; injection E as <- <-; lia. }
  split; [rewrite E2; exact Hr2|].
  split; [exact Hspm|].
  split; [unfold AC.aspZ in *; rewrite E2; exact Haspz|].
  split; [rewrite HSTK; exact Hstklo|].
  split; [rewrite E4; exact Hr4|].
  split; [unfold rg in *; rewrite E8; exact Hr8|].
  split; [unfold rg in *; rewrite E9; exact Hr9|].
  split; [rewrite E3; exact Hr3|].
  split; [unfold rg in *; rewrite E19; exact Hr19|].
  split; [unfold rg in *; rewrite E26; exact Hr26|].
  split; [exact Hfrm|]. split; [exact Hs5|]. split; [exact HAm|]. split; [exact HAS|]. split; [exact Hspa|].
  split; [exact Hfa|]. split; [exact HA416|]. split; [exact HS4|]. split; [exact HAPP|].
  split.
  { unfold q64 in *. eapply fl_bytes; [exact Hspill | exact MU |].
    rewrite length_le8. intros x Hx. exact (HWspill x ltac:(lia)). }
  split.
  { unfold q64 in *. eapply fl_bytes; [exact Hsel | exact MU |].
    rewrite length_le8. intros x Hx. exact (HWsel x ltac:(lia)). }
  split.
  { unfold q64 in *. eapply fl_bytes; [exact Hfr24 | exact MU |].
    rewrite length_le8. intros x Hx. exact (HWfr24 x ltac:(lia)). }
  split.
  { destruct Hloc as [[H0 [Hspfr Hreal]]|[Hfr0 [Hfsb [Hfs Hrec]]]].
    - left. split; [exact H0|]. split; [exact Hspfr|].
      intros a Ha. rewrite HSTK. exact (Hreal a Ha).
    - right. split; [exact Hfr0|]. split; [|split].
      + intros FS Hw HFSr. apply (Hfsb FS); [| exact HFSr].
        intros k Hk. rewrite <- KBlo.
        * exact (Hw k Hk).
        * unfold AC.as_tp, AC.ASYMS. cbn. lia.
        * unfold AC.as_tp, AC.ASYMS. cbn. lia.
      + intros a Ha. destruct (Hfs a Ha) as (FSb & HFSr & Hw & Hlo & Hhi).
        exists FSb. split; [exact HFSr|]. split; [|split; [exact Hlo | exact Hhi]].
        intros k Hk. rewrite KBlo.
        * exact (Hw k Hk).
        * unfold AC.as_tp, AC.ASYMS. cbn. lia.
        * unfold AC.as_tp, AC.ASYMS. cbn. lia.
      + exact (HREC Hrec). }
  split.
  { unfold q64 in *. eapply fl_bytes; [exact Hhdr1 | exact MU |].
    rewrite length_le8. intros x Hx. apply HWhdr. lia. }
  split.
  { unfold q64 in *. eapply fl_bytes; [exact Hhdr2 | exact MU |].
    rewrite length_le8. intros x Hx. apply HWhdr. lia. }
  split; [exact Hshnew|].
  split; [exact (f36_stk_tr W mem mem' _ _ Hwin MU WM HWwin)|].
  split.
  { eapply fl_bytes; [exact Hsaved | exact MU |]. intros x Hx.
    apply HWsaved. unfold saved_bytes in Hx. rewrite !length_app, !length_le8 in Hx. cbn in Hx. lia. }
  split; [intros a Ha; exact (WM (Z_to_bv 64 a) (Herrno a Ha))|].
  split; [exact HAG'|].
  split; [exact HWA'|].
  split; [exact HSHI1|]. split; [exact HSHI2|]. split; [exact HSHI3|].
  split; [exact Hhb | exact Hlive].
Qed.

(* A shadow byte of the frame is outside the call's writes: it is not an application byte (so it misses the
   window and the nine side-stack bands), and the frame is apart from the class-0/1/2 frames and from the
   window, so its granule misses their shadow. *)
Lemma f36_out_frsh : forall S FS fr t,
  0 <= FS -> FS + FS_SIZE <= S - CM_K -> S <= APPMEM_END ->
  (forall a, FS <= a < FS + FS_SIZE -> app_mem a) ->
  (forall a, S - CM_K <= a < S -> app_mem a) ->
  0 <= fr -> fr mod 8 = 0 -> FS + 3182592 <= fr ->
  (fr + 3136 <= S - CM_K \/ S <= fr) ->
  (forall a, fr <= a < fr + 3136 -> app_mem a) ->
  Sfr fr <= t < Sfr fr + 392 ->
  outside (f36_W S FS) t.
Proof.
  intros S FS fr t HFS0 HFSS HSA HFSapp HWapp Hfr0 Hfr8 HfrFS Hdj Hfrapp Ht.
  assert (HSZ : FS_SIZE = 11571200) by reflexivity.
  assert (Hish : in_shadow t).
  { assert (E : shadow_addr (fr + 8 * (t - Sfr fr)) = t)
      by (rewrite f36_sh_frame_of by (unfold Sfr in *; lia); unfold Sfr in *; lia).
    rewrite <- E. apply shadow_of_app. apply Hfrapp. unfold Sfr in *. lia. }
  rewrite f36_W_eq. cbn [outside].
  repeat split.
  - intros HC. exact (app_not_shadow t (HWapp t HC) Hish).
  - intros HC. exact (app_not_shadow t (HFSapp t ltac:(lia)) Hish).
  - intros HC. exact (app_not_shadow t (HFSapp t ltac:(lia)) Hish).
  - intros HC. exact (app_not_shadow t (HFSapp t ltac:(lia)) Hish).
  - exact (f36_sh_dj fr (FS + 36864) (FS + 1085440) t Hfr8 Hfr0 ltac:(lia) ltac:(lia)
             ltac:(right; lia) Ht).
  - intros HC. exact (app_not_shadow t (HFSapp t ltac:(lia)) Hish).
  - intros HC. exact (app_not_shadow t (HFSapp t ltac:(lia)) Hish).
  - intros HC. exact (app_not_shadow t (HFSapp t ltac:(lia)) Hish).
  - exact (f36_sh_dj fr (FS + 1085440) (FS + 2134016) t Hfr8 Hfr0 ltac:(lia) ltac:(lia)
             ltac:(right; lia) Ht).
  - intros HC. exact (app_not_shadow t (HFSapp t ltac:(lia)) Hish).
  - intros HC. exact (app_not_shadow t (HFSapp t ltac:(lia)) Hish).
  - intros HC. exact (app_not_shadow t (HFSapp t ltac:(lia)) Hish).
  - exact (f36_sh_dj fr (FS + 2134016) (FS + 3182592) t Hfr8 Hfr0 ltac:(lia) ltac:(lia)
             ltac:(right; lia) Ht).
  - exact (f36_sh_dj fr (S - CM_K) S t Hfr8 Hfr0 ltac:(lia) ltac:(unfold CM_K; lia) Hdj Ht).
Qed.

(* ===================== the segment lemmas ===================== *)

(* 0x828cc -> 0x828d8: the two argument moves and the call of reac_box_catalogue_match by its contract.  The
   callee's mem_inv premise is reached on the normalized memory (f36_call_norm); FRA moves by f36_fra_run, ENT by
   ent_munch (the call writes no entry block, image byte, byte at or above S, nor a shadow byte of these) and
   ent_mat, and FLSI / FLSX / LK / LT because the frame, the spill area and the blocks are outside its writes. *)
Lemma seg_F36_82820 : forall j,
  Hat B APIf ra (Inv_A828d8_at B APIf ra) j -> Hat B APIf ra (Inv_A828cc_at B APIf ra) j.
Proof.
  intros j Hexit g c (phi & regs & mem & md & fr & Ec & HFRA & HENT & Hgn & Hj & HHB & HFLSI & HLK & HFLSX & H20
                      & HLT).
  subst c. pose proof (proj1 FF) as SEGS.
  pose proof HFLSX as (_ & H18 & H22 & H23 & H25 & Hrec & _ & _).
  set (hb := hb1 phi (AC.a_size (flen g j))) in *.
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as LAWS.
  destruct (f36_fra_sp g fr hb regs mem md HFRA)
    as (Hsp64 & Hspm & HspA & HspH & Hstkw & (A & Hr9 & HA64 & HspAle & HfrA3 & HA416)).
  destruct (f36_fra_A g fr hb regs mem md HFRA) as (A2 & Hr9b & HA0 & HA1 & HAhi & _ & _ & _).
  assert (EA2 : A2 = A) by (apply (f36_reg_eq regs 9 A2 A Hr9b Hr9); lia).
  subst A2.
  pose proof (f36_fra_loc g fr hb regs mem md HFRA)
    as (FS0 & (FSw & HFSw & EFS) & HGTFS0 & HFSlo0 & HFSapp0 & Hhi & Hfr0 & HGTfr & Hfrapp & Hfrloc).
  pose proof (fra_frame B APIf ra g fr hb regs mem md HFRA) as (Hfrwin & _).
  pose proof HFRA as HFRA0.
  destruct HFRA0 as (A' & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm' & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9' & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416' & HS4 & HAPP &
    Hspill & Hsel & Hfr24 & Hloc & Hhdr1 & Hhdr2 & (sh & Hshb & Hshl) & Hwin & Hsaved & Herrno & HAG & HWA &
    HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive).
  pose proof FRAME_BYTES_val as HFBv.
  assert (Hin0 : In (phi, AC.a_size (flen g j)) (hb ++ g_H g)).
  { unfold hb. apply in_or_app. left. left. reflexivity. }
  assert (Hin : 50 <= flen g j -> In (phi, flen g j) (hb ++ g_H g)).
  { intros Hl. replace (flen g j) with (AC.a_size (flen g j)) by (unfold AC.a_size; lia). exact Hin0. }
  destruct (f36_fp_call g fr hb regs mem md phi (flen g j) HFRA Hin)
    as (FS & HFSwm & HFS64 & HFSmod & HGTFS & HFSW & HFSapp & HFP & HTLS).
  rewrite Haspz in Hsp64, Hspm, HspA, HspH, Hstkw, HspAle, HFSW, HFP, HTLS, Hfrwin.
  pose proof Hwin as (HwinL & HwinH & _).
  assert (EA : A' = A) by (apply (f36_reg_eq regs 9 A' A Hr9' Hr9); lia).
  subst A'.
  assert (EFS0 : FS0 = FS).
  { apply (f36_wm_uniq mem (AC.as_tp AC.ASYMS)).
    - change (AC.as_tp AC.ASYMS) with RT_TP. rewrite <- EFS.
      exact (bytes_at_le8_word rsegs mem RT_TP FSw HFSw).
    - exact HFSwm.
    - rewrite <- EFS. apply u64_range.
    - exact HFS64. }
  rewrite EFS0 in HGTFS0, HFSlo0, HFSapp0, Hfrloc.
  assert (HSS : AF.SLOT_STACK = 1048576) by reflexivity.
  assert (HFN : FN_STACK = 1044480) by reflexivity.
  assert (HCMK : CM_K = 9136) by reflexivity.
  assert (HSZ : AC.FS_SIZE = 11571200) by reflexivity.
  assert (HSZ' : FS_SIZE = 11571200) by reflexivity.
  assert (Hfr8 : fr mod 8 = 0) by (revert Hfrm; clear; Z.div_mod_to_equations; lia).
  assert (HWapp : forall a, sp - CM_K <= a < sp -> app_mem a).
  { intros a Ha. unfold app_mem. right. unfold HIGHMEM_BEG, APPMEM_END in *. lia. }
  assert (HfrFS : FS + 3182592 <= fr).
  { destruct Hloc as [[_ [Hspfr _]] | [_ [Hfsb _]]]; [lia|].
    pose proof (Hfsb FS HFSwm HFS64). lia. }
  assert (Hfrw : fr + 3136 <= sp - CM_K \/ sp <= fr)
    by (apply Hfrwin; unfold FN_STACK, AF.SLOT_STACK in *; lia).
  assert (Etp : bv_unsigned (getr regs 4) = AC.as_tp AC.ASYMS).
  { rewrite Hr4. apply MState.unsigned_lit. change (AC.as_tp AC.ASYMS) with RT_TP. unfold RT_TP. lia. }
  (* ---- the premises of the callee's contract ---- *)
  assert (HSTw : stk rsegs mem (sp - CM_K) sp).
  { destruct (stk_split rsegs mem (sp - FN_STACK) (sp - CM_K) sp Hstkw ltac:(lia)) as (_ & Hs). exact Hs. }
  assert (HROM : forall a, sp - CM_K <= a < sp -> seg_rom rsegs (wa a) = None).
  { intros a Ha. apply f36_rom_none; unfold HIGHMEM_BEG, APPMEM_END in *; lia. }
  assert (HROc : forall a, CM_T <= a < CM_T + 3256 -> mrd rsegs mem (wa a) = seg_rom rsegs (wa a)).
  { intros a Ha. unfold CM_T in Ha.
    pose proof (Hgimg a ltac:(exists 0x9e348, 9344; split;
                              [unfold AF.frame_RELRO; cbn [In]; left; reflexivity | lia])) as H.
    rewrite SEGS in H. exact H. }
  assert (HADT : addressable mem CM_T 3256).
  { apply (f36_ag_addr mem CM_T 3256 HAG);
      [ unfold AF.frame_AG; cbn [In]; repeat (first [ (left; reflexivity) | right ])
      | unfold CM_T; lia | lia | unfold CM_T, APPMEM_END; lia ]. }
  assert (HADB : addressable mem REAC_CTRL_PARSE_BC 6).
  { apply (addressable_prefix mem REAC_CTRL_PARSE_BC 7 6); [|lia].
    apply (f36_ag_addr mem REAC_CTRL_PARSE_BC 7 HAG);
      [ unfold AF.frame_AG; cbn [In]; repeat (first [ (left; reflexivity) | right ])
      | unfold REAC_CTRL_PARSE_BC; lia | lia | unfold REAC_CTRL_PARSE_BC, APPMEM_END; lia ]. }
  assert (HADW : addressable mem (sp - CM_K) CM_K).
  { apply f36_addr_bytes; [lia | unfold CM_K; lia | lia |].
    intros a Ha. apply HWA; [unfold AF.SLOT_STACK, CM_K in *; lia | destruct Hfrw as [H|H]; lia]. }
  pose proof HRT as HRT2.
  destruct HRT2 as (HAC0 & HSW0 & _ & HCF0 & _ & HREAL0 & _).
  destruct HCF0 as (HGOTCF & _ & _ & _ & _ & _ & HCF240 & _).
  assert (HGC : bytes_at rsegs mem GOT_CF (le8 (wa CF))) by exact HGOTCF.
  assert (HRBc : bytes_at rsegs mem REAL_BCMP (le8 (wa BCMP)))
    by (apply (real_cell_of mem REAL_BCMP BCMP HREAL0); vm_compute; reflexivity).
  assert (HRMc : bytes_at rsegs mem REAL_MEMCMP (le8 (wa MEMCMP)))
    by (apply (real_cell_of mem REAL_MEMCMP MEMCMP HREAL0); vm_compute; reflexivity).
  assert (HC254 : bytes_at rsegs mem (CF + 254) [Z_to_bv 8 1]).
  { pose proof (f36_ba_sub mem (RT_CF + 240) (cf_b [0;0;0;0;1;0;1;1;1;1;1;1;1;1;1;1;1;1;1;1;0]) 14 1 HCF240
      ltac:(cbn; lia)) as Hs.
    replace (RT_CF + 240 + Z.of_nat 14) with (CF + 254) in Hs by (unfold CF, RT_CF; lia).
    replace (firstn 1 (skipn 14 (cf_b [0;0;0;0;1;0;1;1;1;1;1;1;1;1;1;1;1;1;1;1;0]))) with [Z_to_bv 8 1] in Hs
      by (vm_compute; reflexivity).
    exact Hs. }
  assert (HC255 : bytes_at rsegs mem (CF + 255) [Z_to_bv 8 1]).
  { pose proof (f36_ba_sub mem (RT_CF + 240) (cf_b [0;0;0;0;1;0;1;1;1;1;1;1;1;1;1;1;1;1;1;1;0]) 15 1 HCF240
      ltac:(cbn; lia)) as Hs.
    replace (RT_CF + 240 + Z.of_nat 15) with (CF + 255) in Hs by (unfold CF, RT_CF; lia).
    replace (firstn 1 (skipn 15 (cf_b [0;0;0;0;1;0;1;1;1;1;1;1;1;1;1;1;1;1;1;1;0]))) with [Z_to_bv 8 1] in Hs
      by (vm_compute; reflexivity).
    exact Hs. }
  (* the turn's block *)
  destruct HHB as (Hphi0 & Hphad).
  pose proof Hphad as (Hph0 & Hszn & Hphend & _).
  destruct (AC.a_laws_blocks _ _ _ _ _ LAWS _ mem md phi (AC.a_size (flen g j)) HAH Hin0)
    as (_ & Hph4k & Hphstk & Hphe & Hphin).
  unfold AC.a_size in Hphstk.
  assert (Hfl0 : 0 <= flen g j) by (unfold flen; apply f36_len_nonneg).
  assert (Hflend : phi + flen g j <= APPMEM_END) by (revert Hphend; unfold AC.a_size; lia).
  assert (H50 : 50 <= flen g j -> 0 < phi /\ phi + 50 <= 2 ^ 64 /\
                 bytes_at rsegs mem phi (t_g (g_in g) j) /\ (phi + 50 <= sp - CM_K \/ sp <= phi)).
  { intros Hl. destruct (Hrec Hl) as (Hp0 & Hp1 & Hphi50 & _ & _).
    split; [lia|]. split; [exact Hp1|]. split; [exact Hphi50|]. left. lia. }
  assert (H50a : 50 <= flen g j -> addressable mem phi 50 /\ app_mem (phi + 50)).
  { intros Hl. assert (Hsz : AC.a_size (flen g j) = flen g j) by (unfold AC.a_size; lia).
    split.
    - apply (addressable_prefix mem phi (AC.a_size (flen g j)) 50 Hphad). lia.
    - destruct (Z_le_gt_dec (flen g j) 50) as [He|He].
      + replace (phi + 50) with (phi + AC.a_size (flen g j)) by lia.
        destruct Hphe as [H0|H0]; [lia | exact H0].
      + exact (proj1 (Hphin (phi + 50) ltac:(lia))). }
  (* ---- the run ---- *)
  rewrite SEGS.
  apply (f36_run_lib regs (Z_to_bv 64 0x828cc) mem md
    (fun R0 pc' mem' => pc' = Z_to_bv 64 0x828d8 /\
       getr R0 2 = getr regs 2 /\ getr R0 3 = getr regs 3 /\ getr R0 4 = getr regs 4 /\
       getr R0 8 = getr regs 8 /\ getr R0 9 = getr regs 9 /\ getr R0 18 = getr regs 18 /\
       getr R0 19 = getr regs 19 /\ getr R0 20 = getr regs 20 /\ getr R0 21 = getr regs 21 /\
       getr R0 22 = getr regs 22 /\ getr R0 23 = getr regs 23 /\ getr R0 24 = getr regs 24 /\
       getr R0 25 = getr regs 25 /\ getr R0 26 = getr regs 26 /\ getr R0 27 = getr regs 27 /\
       getr R0 10 = Z_to_bv 64 (want CM_T (flen g j) (t_g (g_in g) j)) /\
       munch (f36_W sp FS) mem mem' /\ wmono rsegs mem mem' /\ ro_agree rsegs mem' /\
       stk rsegs mem' (sp - CM_K) sp /\ asan_cells mem' /\ shadow_rw mem' /\
       addressable mem' (sp - CM_K) CM_K /\
       fp [0%nat; 1%nat; 2%nat] mem' (AC.as_tp AC.ASYMS) FS (sp - CM_K) sp
         (reac_box_catalogue_match_W sp) (reac_box_catalogue_match_D phi (flen g j)))
    (Post B APIf ra g)).
  - exact Hhalt.
  - eapply LE.evt_mono.
    { unfold Regs6ss.mkR_of.
      eapply (f36_call_norm CMC) with (phi := phi) (len := flen g j) (S := sp) (FS := FS)
               (fb := t_g (g_in g) j).
      - unfold rg in H23; exact H23.
      - unfold rg in H18; exact H18.
      - exact Hr2.
      - unfold APPMEM_END in *; lia.
      - unfold APPMEM_END in *; lia.
      - lia.
      - exact Hspm.
      - lia.
      - exact HSTw.
      - exact HROM.
      - apply fr50_length.
      - exact H50.
      - exact HROc.
      - exact Hro.
      - exact HAC0.
      - exact HSW0.
      - lia.
      - exact HspA.
      - exact HADW.
      - exact H50a.
      - exact HADT.
      - exact HADB.
      - exact HRBc.
      - exact HRMc.
      - exact HGC.
      - exact HC254.
      - exact HC255.
      - rewrite <- Etp in HFP. exact HFP.
      - rewrite <- Etp in HTLS. exact HTLS. }
    { intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
                  E & MU & WM & MI' & ST' & AC' & SW' & AD' & FP').
      eexists _, (Z_to_bv 64 0x828d8), m'. split; [exact E|].
      split; [reflexivity|].
      do 15 (split; [reflexivity|]).
      split; [reflexivity|].
      split; [exact MU|]. split; [exact WM|]. split; [exact MI'|]. split; [exact ST'|].
      split; [exact AC'|]. split; [exact SW'|]. split; [exact AD'|].
      rewrite <- Etp. exact FP'. }
  - intros R0 pc' mem' regs' md'
      (Hpc & E2 & E3 & E4 & E8 & E9 & E18 & E19 & E20 & E21 & E22 & E23 & E24 & E25 & E26 & E27 & E10 &
       MU & WM & MI' & ST' & AC' & SW' & AD' & FP') Hreg Hmat.
    subst pc'.
    assert (F2 : getr regs' 2 = getr regs 2) by (rewrite Hreg; exact E2).
    assert (F3 : getr regs' 3 = getr regs 3) by (rewrite Hreg; exact E3).
    assert (F4 : getr regs' 4 = getr regs 4) by (rewrite Hreg; exact E4).
    assert (F8 : getr regs' 8 = getr regs 8) by (rewrite Hreg; exact E8).
    assert (F9 : getr regs' 9 = getr regs 9) by (rewrite Hreg; exact E9).
    assert (F18 : getr regs' 18 = getr regs 18) by (rewrite Hreg; exact E18).
    assert (F19 : getr regs' 19 = getr regs 19) by (rewrite Hreg; exact E19).
    assert (F20 : getr regs' 20 = getr regs 20) by (rewrite Hreg; exact E20).
    assert (F21 : getr regs' 21 = getr regs 21) by (rewrite Hreg; exact E21).
    assert (F22 : getr regs' 22 = getr regs 22) by (rewrite Hreg; exact E22).
    assert (F23 : getr regs' 23 = getr regs 23) by (rewrite Hreg; exact E23).
    assert (F24 : getr regs' 24 = getr regs 24) by (rewrite Hreg; exact E24).
    assert (F25 : getr regs' 25 = getr regs 25) by (rewrite Hreg; exact E25).
    assert (F26 : getr regs' 26 = getr regs 26) by (rewrite Hreg; exact E26).
    assert (F27 : getr regs' 27 = getr regs 27) by (rewrite Hreg; exact E27).
    assert (F10 : getr regs' 10 = Z_to_bv 64 (want CM_T (flen g j) (t_g (g_in g) j)))
      by (rewrite Hreg; exact E10).
    assert (Easp : AC.aspZ regs' = sp) by (unfold AC.aspZ; rewrite F2; exact Haspz).
    (* ---- the outside facts of the call's write set ---- *)
    assert (OUTapp : forall x, app_mem x -> ~ (sp - CM_K <= x < sp) ->
              ~ (FS <= x < FS + 24) -> ~ (FS + 4096 <= x < FS + 32768) ->
              ~ (FS + 36864 <= x < FS + 3182592) -> outside (f36_W sp FS) x).
    { intros x Hx H1 H2 H3 H4.
      exact (f36_out_app sp FS x ltac:(lia) ltac:(lia) ltac:(lia) ltac:(intros a Ha; apply HFSapp; lia)
               HWapp Hx H1 H2 H3 H4). }
    assert (OUThi : forall x, sp <= x -> outside (f36_W sp FS) x)
      by (intros x Hx; exact (f36_out_hi sp FS x ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hx)).
    assert (OUTlo : forall x, 0 <= x < 6283264 -> outside (f36_W sp FS) x).
    { intros x Hx. apply OUTapp;
        [unfold app_mem, LOWMEM_END; left; lia | unfold HIGHMEM_BEG in *; lia
         | unfold AC.GT in HGTFS; lia | unfold AC.GT in HGTFS; lia | unfold AC.GT in HGTFS; lia]. }
    assert (OUTfr : forall x, fr <= x < fr + 3136 -> outside (f36_W sp FS) x).
    { intros x Hx. apply OUTapp; [apply Hfrapp; lia | | lia | lia | lia].
      destruct Hfrw as [H|H]; lia. }
    assert (OUTfrsh : forall t, Sfr fr <= t < Sfr fr + 392 -> outside (f36_W sp FS) t).
    { intros t Ht.
      exact (f36_out_frsh sp FS fr t ltac:(lia) ltac:(lia) ltac:(lia)
               ltac:(intros a Ha; apply HFSapp; lia) HWapp Hfr0 Hfr8 HfrFS Hfrw Hfrapp Ht). }
    assert (HFS8 : FS mod 8 = 0) by (revert HFSmod; clear; Z.div_mod_to_equations; lia).
    assert (HK8 : (sp - CM_K) mod 8 = 0) by (revert Hspm; unfold CM_K; clear; Z.div_mod_to_equations; lia).
    assert (OUTsh : forall x, app_mem x -> ~ (FS <= x < FS + 3182592) -> ~ (sp - CM_K <= x < sp) ->
              outside (f36_W sp FS) (shadow_addr x)).
    { intros x Hx H1 H2.
      exact (f36_out_sh_call sp FS x ltac:(lia) HFS8 ltac:(lia) HK8 ltac:(lia)
               ltac:(intros a Ha; apply HFSapp; lia) HWapp Hx H1 H2). }
    assert (OUTblk : forall x, phi <= x < phi + AC.a_size (flen g j) ->
              outside (f36_W sp FS) (shadow_addr x)).
    { intros x Hx. destruct (f36_blk g j phi fr regs mem md HFRA x Hx) as (Hap & Hnfr & Hnfs).
      apply OUTsh; [exact Hap| |].
      - intros HC. apply Hnfs. exists FS. split; [exact HFS64 | split; [exact HFSwm | lia]].
      - unfold AC.a_size in Hx. lia. }
    assert (OUTblkb : forall x, phi <= x < phi + AC.a_size (flen g j) -> outside (f36_W sp FS) x).
    { intros x Hx. destruct (f36_blk g j phi fr regs mem md HFRA x Hx) as (Hap & Hnfr & Hnfs).
      apply OUTapp; [exact Hap | unfold AC.a_size in Hx; lia | | |];
        (intros HC; apply Hnfs; exists FS; split; [exact HFS64 | split; [exact HFSwm | lia]]). }
    (* ---- FRA at 0x828d8 ---- *)
    assert (HroM : ro_agree rsegs mem') by exact MI'.
    assert (Hrtdj : rt_disjoint (f36_W sp FS)).
    { assert (LOS : forall p, In p (f36_W sp FS) -> 6283264 <= fst p).
      { intros p Hp. apply (f36_W_los sp FS p); [unfold AC.GT in HGTFS; lia
        | unfold HIGHMEM_BEG in *; lia | exact Hp]. }
      unfold rt_disjoint.
      repeat match goal with |- _ /\ _ => split end;
        apply f36_dj_lo; intros p Hp; pose proof (LOS p Hp);
        unfold RT_LO, RT_HI, RT_GOT_AF, RT_AF, RT_GOT_VERB, RT_VERB, RT_GOT_CF, RT_CF, RT_TSDI, RT_TSDK,
          RT_PGSZ, RT_TP, RT_TSDMAIN, RT_REAL_LO, RT_REAL_HI, RT_IMAP, RT_IMEM, RT_MUG, RT_AGLOB,
          RT_AGLOB_LEN in *; lia. }
    assert (Hwrit : forall a, 0 <= a < 2 ^ 64 -> writable_at rsegs mem a -> writable_at rsegs mem' a)
      by (intros a Ha Hw; exact (WM (Z_to_bv 64 a) Hw)).
    assert (HFSok : AC.a_fs_ok mem FS).
    { destruct (f36_fs_state _ mem md FS HAH HFSwm HFS64) as (DB_ & FSS). exact (@f36_fss_ok _ _ _ _ FSS). }
    assert (HFSok' : AC.a_fs_ok mem' FS).
    { exact (f36_fs_ok mem mem' sp FS (AC.as_tp AC.ASYMS) _ _ HFSok MU FP'
               ltac:(lia) ltac:(lia) ltac:(unfold HIGHMEM_BEG in *; lia)). }
    assert (Hmc : forall a, 0 <= a < 2 ^ 64 ->
              ~ AC.a_store_ok (hb ++ g_H g) (STKLO mem md) a ->
              ~ (FS <= a < FS + AC.FS_SIZE) ->
              ~ (exists bb, FS <= bb < FS + AC.FS_SIZE /\ a = shadow_addr bb) ->
              mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a)).
    { intros a Ha Hnok Hnfs Hnsh. rs_hide_all. unfold rs_hold in HFS8, HK8.
      apply MU. rewrite MState.unsigned_lit by lia.
      rewrite f36_W_eq. cbn [outside].
      assert (HnotW : ~ (sp - CM_K <= a < sp)).
      { intros HC. apply Hnok. right. left. unfold APPMEM_END in *. lia. }
      assert (HnotFS : ~ (FS <= a < FS + FS_SIZE)) by lia.
      assert (HnotSh : forall lo hi, FS <= lo -> hi <= FS + FS_SIZE -> lo <= hi ->
                ~ (shadow_addr lo <= a < shadow_addr hi)).
      { intros lo hi Hlo Hhi2 Hlh HC. apply Hnsh. exists (8 * (a - ASAN_K)).
        split; [unfold shadow_addr, ASAN_K in *; Z.div_mod_to_equations; lia|].
        unfold shadow_addr, ASAN_K in *. Z.div_mod_to_equations. lia. }
      assert (HnotWsh : ~ (shadow_addr (sp - CM_K) <= a < shadow_addr sp)).
      { intros HC. apply Hnok. right. right. right. exists (8 * (a - ASAN_K)).
        split; [unfold shadow_addr, ASAN_K in *; Z.div_mod_to_equations; lia|].
        right. left. unfold shadow_addr, ASAN_K, APPMEM_END in *. Z.div_mod_to_equations. lia. }
      repeat split;
        first [ (intros HC; lia)
              | exact (HnotSh (FS + 36864) (FS + 1085440) ltac:(lia) ltac:(lia) ltac:(lia))
              | exact (HnotSh (FS + 1085440) (FS + 2134016) ltac:(lia) ltac:(lia) ltac:(lia))
              | exact (HnotSh (FS + 2134016) (FS + 3182592) ltac:(lia) ltac:(lia) ltac:(lia))
              | exact HnotWsh ]. }
    destruct (AC.a_laws_fs_store _ _ _ _ _ LAWS _ mem mem' md FS HAH HFSwm HFS64 Hmc Hwrit HFSok')
      as (HAH' & HOWNc & HSTKeq & HSTKHIc).
    assert (HRDsh : forall a, in_shadow a -> exists bb, mrd rsegs mem' (wa a) = Some bb)
      by (intros a Ha; exact (proj2 (SW' a Ha))).
    assert (HAGm : forall a, in_globals AF.frame_AG a -> addressable mem' a 1).
    { intros a Hin2. pose proof (f36_ag_bound a Hin2) as Hab.
      apply (f36_addr_keep (f36_W sp FS) mem mem' a 1 (HAG a Hin2) MU).
      intros i Hi. apply OUTsh.
      - unfold app_mem, LOWMEM_END. left. lia.
      - unfold AC.GT in HGTFS. lia.
      - unfold HIGHMEM_BEG in *. lia. }
    assert (HFRAm : FRA B APIf ra g fr hb regs' mem' md).
    { apply (f36_fra_run g fr hb regs regs' mem mem' md (f36_W sp FS) HFRA MU WM HroM
               Hrtdj HAH' HSTKeq HRDsh).
      - destruct Hshb as (Hb0 & Hb1 & Hb2).
        exists sh. split; [|exact Hshl].
        eapply fl_bytes; [exact (conj Hb0 (conj Hb1 Hb2)) | exact MU |].
        rewrite Hshl, FRAME_SHADOW_val. intros x Hx. apply OUTfrsh. lia.
      - exact OUTlo.
      - intros x Hx. apply OUTfr. lia.
      - intros x Hx. apply OUThi. unfold rg in Hr9. rewrite Hr9, MState.unsigned_lit in Hx by lia. lia.
      - intros x Hx. apply OUThi. unfold rg in Hr9. rewrite Hr9, MState.unsigned_lit in Hx by lia. lia.
      - intros x Hx. apply OUThi. unfold rg in Hr9. rewrite Hr9, MState.unsigned_lit in Hx by lia. lia.
      - intros x Hx. apply OUThi. lia.
      - intros x Hx. destruct (Z_lt_le_dec x (sp - CM_K)) as [Hlt|Hge].
        + left. apply OUTapp.
          * unfold app_mem. right. unfold HIGHMEM_BEG, APPMEM_END in *. lia.
          * lia.
          * lia.
          * lia.
          * lia.
        + destruct (Z_lt_le_dec x sp) as [Hlt2|Hge2].
          * right. destruct ST' as (_ & _ & Hst). exact (proj2 (Hst x ltac:(lia))).
          * left. apply OUThi. lia.
      - exact HAGm.
      - intros a Ha Hnf.
        destruct (Z_le_gt_dec (sp - CM_K) a) as [Hge|Hlt]; [destruct (Z_lt_ge_dec a sp) as [Hlt2|Hge2]|].
        + replace a with (sp - CM_K + (a - (sp - CM_K))) by lia.
          apply (addressable_sub mem' (sp - CM_K) CM_K (a - (sp - CM_K)) 1 AD');
            [lia | lia | unfold CM_K in *; lia].
        + apply (f36_addr_keep (f36_W sp FS) mem mem' a 1 (HWA a Ha Hnf) MU).
          intros i Hi. destruct (HWA a Ha Hnf) as (_ & _ & _ & Hab).
          apply OUTsh; [exact (proj1 (Hab i Hi)) | lia | lia].
        + apply (f36_addr_keep (f36_W sp FS) mem mem' a 1 (HWA a Ha Hnf) MU).
          intros i Hi. destruct (HWA a Ha Hnf) as (_ & _ & _ & Hab).
          apply OUTsh; [exact (proj1 (Hab i Hi)) | lia | lia].
      - intros HREC0.
        apply (f36_fsrec_call (hb ++ g_H g) mem mem' md (f36_W sp FS) fr HREC0 HAH MU OUTlo).
        intros FS' Hw' Hr' x Hx Hnx.
        assert (EFS' : FS' = FS) by exact (f36_wm_uniq mem (AC.as_tp AC.ASYMS) FS' FS Hw' HFSwm Hr' HFS64).
        subst FS'.
        apply OUTapp; [apply HFSapp; lia | lia | lia | lia | exact Hnx].
      - exact F2.
      - exact F3.
      - exact F4.
      - exact F8.
      - exact F9.
      - exact F19.
      - exact F26. }
    assert (HFRA' : FRA B APIf ra g fr hb regs' mem' md')
      by (apply (sl_fra_move B APIf ra g fr hb regs' regs' mem' md md' HFRAm); try reflexivity; exact Hmat).
    (* ---- ENT across the call (none of its writes is an address ENT speaks of) and the model step ---- *)
    assert (HENT1 : ENT APIf g hb mem' md).
    { apply (ent_munch APIf g hb mem mem' md (f36_W sp FS) HENT HAH MU); [| exact HSTKeq | exact HSTKHIc |].
      - intros x Hk. destruct Hk as [Hblkk | [Hik | [Habk | [(b & Hor & ->) | Hblks]]]].
        + destruct Hblkk as (q & k & i & Hinq & Hni & Hi & ->).
          destruct (f36_inblk g fr hb regs mem md q k HFRA Hinq (q + i) ltac:(lia)) as (Happq & _ & Hnfs & Hlow).
          apply OUTapp; [exact Happq | lia | | |];
            (intros HC; apply Hnfs; exists FS; split; [exact HFS64 | split; [exact HFSwm | lia]]).
        + pose proof (img_below_GT x Hik) as Hxg. unfold AC.GT in Hxg. apply OUTlo. lia.
        + apply OUThi. lia.
        + destruct Hor as [Hib | Hrb].
          * pose proof (img_below_GT b Hib) as Hbg. unfold AC.GT in Hbg.
            apply OUTsh; [unfold app_mem, LOWMEM_END; left; lia | unfold AC.GT in HGTFS; lia
                         | unfold HIGHMEM_BEG in *; lia].
          * apply OUTsh; [unfold app_mem, HIGHMEM_BEG, APPMEM_END in *; right; lia | lia | lia].
        + destruct Hblks as (q & k & i & Hinq & Hni & Hi & ->).
          destruct (f36_inblk g fr hb regs mem md q k HFRA Hinq (q + i) ltac:(lia)) as (Happq & _ & Hnfs & Hlow).
          apply OUTsh; [exact Happq | | lia].
          intros HC. apply Hnfs. exists FS. split; [exact HFS64 | split; [exact HFSwm | lia]].
      - intros a Hia Hio. exact (proj2 (HOWNc a) Hio). }
    assert (HENT' : ENT APIf g hb mem' md') by exact (ent_mat APIf g hb mem' md md' HENT1 Hmat).
    (* ---- the exit cut ---- *)
    rewrite <- SEGS. apply Hexit.
    assert (OURsh : forall i, 0 <= i < 6 -> outside (f36_W sp FS) (shadow_addr (fr + 2624 + i))).
    { intros i Hi. apply OUTfrsh. apply (f36_sh_in_frame fr); [exact Hfr0 | exact Hfr8 | lia]. }
    assert (IDRsh : forall i, 0 <= i < 152 -> outside (f36_W sp FS) (shadow_addr (fr + 2688 + i))).
    { intros i Hi. apply OUTfrsh. apply (f36_sh_in_frame fr); [exact Hfr0 | exact Hfr8 | lia]. }
    assert (OUTA : forall x, A <= x < A + 416 -> outside (f36_W sp FS) x) by (intros x Hx; apply OUThi; lia).
    assert (OUTP : forall x, g_p g <= x < g_p g + g_n g ->
                     outside (f36_W sp FS) x /\ outside (f36_W sp FS) (shadow_addr x)).
    { intros x Hx. rs_hide_all. pose proof HFLSI as (_ & _ & _ & _ & (HinP & _ & _) & _).
      destruct (f36_inblk g fr hb regs mem md _ _ HFRA (HinP ltac:(lia)) x Hx) as (Hap & _ & Hnfs & Hlow).
      assert (HnFS : ~ (FS <= x < FS + AC.FS_SIZE))
        by (intros HC; apply Hnfs; exists FS; split; [exact HFS64 | split; [exact HFSwm | exact HC]]).
      split; [apply OUTapp; [exact Hap | lia | lia | lia | lia] | apply OUTsh; [exact Hap | lia | lia]]. }
    exists phi, regs', mem', md', fr. split; [reflexivity|]. split; [exact HFRA'|]. split; [exact HENT'|].
    split; [exact Hgn|]. split; [exact Hj|].
    split.
    { split; [exact Hphi0|].
      apply (f36_addr_keep (f36_W sp FS) mem mem' phi _ Hphad MU).
      intros i Hi. apply OUTblk. lia. }
    split; [exact (f36_flsi_keep g j fr regs regs' mem mem' _ A HFLSI MU WM F9 Hr9 HA0 HA1 OUTA OUTfr OURsh IDRsh
                     OUTP)|].
    split; [apply (f36_lk_keep g fr j regs regs' mem mem' _ HLK MU F21); intros x Hx; apply OUTfr; lia|].
    split; [exact (f36_flsx_keep g j phi fr regs regs' mem mem' _ A HFLSX MU WM F9 F18 F22 F23 F25 Hr9 HA0 HA1
                     OUTA OUTfr OURsh IDRsh OUTP OUTblkb)|].
    split; [unfold rg in *; rewrite F20; exact H20|].
    split; [unfold rg; rewrite F10; unfold t_want; reflexivity|].
    assert (OUTbody : forall x, fr + 2880 <= x < fr + 2915 ->
                        outside (f36_W sp FS) x /\ outside (f36_W sp FS) (shadow_addr x)).
    { intros x Hx. split; [apply OUTfr; lia|].
      apply OUTfrsh. apply (f36_sh_in_frame fr); [exact Hfr0 | exact Hfr8 | lia]. }
    exact (f36_lt_keep g fr j regs regs' mem mem' _ A HLT MU F9 Hr9 HA0 HA1 OUTA
             ltac:(intros x Hx; apply OUTfr; lia) OUTbody).
Qed.

(* The write set of a frame-shadow store, and the addresses it misses: application memory (the write is a shadow
   byte), the low image and everything at or above HighMem (the write lies in the shadow window), and the shadow
   byte of any address outside the frame. *)
Lemma f36_meta_out : forall g fr hb regs mem md o n,
  FRA B APIf ra g fr hb regs mem md -> 0 <= o -> 0 < n -> o + n <= 392 ->
  0 <= fr /\ fr mod 8 = 0 /\ AC.GT <= fr /\ (forall a, fr <= a < fr + 3136 -> app_mem a) /\
  LOWMEM_END <= Sfr fr /\ Sfr fr + 392 <= HIGHMEM_BEG /\
  (forall x, app_mem x -> outside [(Sfr fr + o, Sfr fr + o + n)] x) /\
  (forall x, HIGHMEM_BEG <= x -> outside [(Sfr fr + o, Sfr fr + o + n)] x) /\
  (forall x, x < LOWMEM_END -> outside [(Sfr fr + o, Sfr fr + o + n)] x) /\
  (forall y, 0 <= y -> ~ (fr <= y < fr + 3136) -> outside [(Sfr fr + o, Sfr fr + o + n)] (shadow_addr y)).
Proof.
  intros g fr hb regs mem md o n HFRA Ho Hn Hon.
  pose proof (f36_fra_loc g fr hb regs mem md HFRA)
    as (FS & _ & _ & _ & _ & _ & Hfr0 & HGTfr & Hfrapp & _).
  pose proof HFRA as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspill & Hsel & Hfr24 & Hloc & Hhdr1 & Hhdr2 &
    Hsh & Hwin & Hsaved & Herrno & HAG & HWA & HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive).
  assert (Hfr8 : fr mod 8 = 0) by (revert Hfrm; clear; Z.div_mod_to_equations; lia).
  assert (HSh : forall x, Sfr fr <= x < Sfr fr + 392 -> in_shadow x).
  { intros x Hx.
    assert (E : shadow_addr (fr + 8 * (x - Sfr fr)) = x)
      by (rewrite f36_sh_frame_of by (unfold Sfr in *; lia); unfold Sfr in *; lia).
    rewrite <- E. apply shadow_of_app. apply Hfrapp. unfold Sfr in *. lia. }
  pose proof (f36_in_shadow_bnd _ (HSh (Sfr fr) ltac:(lia))) as HB1.
  pose proof (f36_in_shadow_bnd _ (HSh (Sfr fr + 391) ltac:(lia))) as HB2.
  split; [exact Hfr0|]. split; [exact Hfr8|]. split; [exact HGTfr|]. split; [exact Hfrapp|].
  split; [lia|]. split; [lia|].
  split.
  { intros x Hx. cbn [outside]. split; [|exact I]. intros Hin.
    exact (app_not_shadow x Hx (HSh x ltac:(lia))). }
  split; [intros x Hx; cbn [outside]; split; [lia | exact I]|].
  split; [intros x Hx; cbn [outside]; split; [lia | exact I]|].
  intros y Hy0 Hny. cbn [outside]. split; [|exact I]. intros Hin.
  pose proof (f36_sh_frame fr y (shadow_addr y - Sfr fr) Hfr0 Hfr8 Hy0 ltac:(unfold Sfr in *; lia)) as Hz.
  apply Hny. lia.
Qed.

(* The n shadow bytes at S(fr) + o are a writable cell block: they are present (FRA's 392-byte list) and
   writable (the runtime's shadow_rw). *)
Lemma f36_shadow_rw : forall g fr hb regs mem md (o : Z) (n : nat),
  FRA B APIf ra g fr hb regs mem md -> 0 <= o -> (0 < n)%nat -> o + Z.of_nat n <= 392 ->
  exists bs, rw_cells rsegs mem (Sfr fr + o) [CB n bs].
Proof.
  intros g fr hb regs mem md o n HFRA Ho Hn Hon.
  destruct (f36_meta_out g fr hb regs mem md o (Z.of_nat n) HFRA Ho ltac:(lia) ltac:(lia))
    as (Hfr0 & Hfr8 & HGTfr & Hfrapp & HB1 & HB2 & _).
  pose proof HFRA as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspill & Hsel & Hfr24 & Hloc & Hhdr1 & Hhdr2 &
    (sh & Hshb & Hshl) & Hwin & Hsaved & Herrno & HAG & HWA & HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive).
  pose proof FRAME_SHADOW_val as HFSv.
  assert (HSh : forall x, Sfr fr <= x < Sfr fr + 392 -> in_shadow x).
  { intros x Hx.
    assert (E : shadow_addr (fr + 8 * (x - Sfr fr)) = x)
      by (rewrite f36_sh_frame_of by (unfold Sfr in *; lia); unfold Sfr in *; lia).
    rewrite <- E. apply shadow_of_app. apply Hfrapp. unfold Sfr in *. lia. }
  pose proof (f36_ba_sub mem (Sfr fr) sh (Z.to_nat o) n Hshb ltac:(lia)) as Hsub.
  rewrite Z2Nat.id in Hsub by lia.
  exists (firstn n (skipn (Z.to_nat o) sh)).
  assert (Hwr : wr_at rsegs mem (Sfr fr + o) (Z.of_nat n)).
  { split; [unfold LOWMEM_END in *; lia|]. split; [unfold HIGHMEM_BEG in *; lia|]. intros i Hi.
    exact (proj1 (RT_shadow_rw _ _ _ HRT (Sfr fr + o + i) (HSh (Sfr fr + o + i) ltac:(lia)))). }
  split; [split|].
  - cbn [cells_wf cell_wf]. split; [rewrite length_firstn, length_skipn; lia | exact I].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. exact Hsub.
  - cbn [cells_size csize]. rewrite Nat.add_0_r. exact Hwr.
Qed.

(* ===================== the cut facts across the segment's runs ===================== *)

(* The cut facts (FRA, ENT, HB, FLSI, LK, FLSX, LT) across a run of shadow stores into [S(fr) + o, S(fr) + o + n),
   inside the frame's 392 shadow bytes and below the shadow byte S(fr) + 328 of OUR: every fact reads application
   bytes, image bytes, bytes at or above HighMem, the shadow of a byte off the frame, or the shadow byte of OUR. *)
Lemma f36_store_step : forall g j phi fr regs regs' mem mem' md o n,
  FRA B APIf ra g fr (hb1 phi (AC.a_size (flen g j))) regs mem md ->
  ENT APIf g (hb1 phi (AC.a_size (flen g j))) mem md ->
  HB mem phi (flen g j) -> FLSI g j fr regs mem -> LK g fr j regs mem -> FLSX g j phi fr regs mem ->
  LT g fr j regs mem ->
  0 <= o -> 0 < n -> o + n <= 328 ->
  munch [(Sfr fr + o, Sfr fr + o + n)] mem mem' -> wmono rsegs mem mem' ->
  (forall x, Sfr fr + o <= x < Sfr fr + o + n -> exists b, mrd rsegs mem' (wa x) = Some b) ->
  getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  getr regs' 8 = getr regs 8 -> getr regs' 9 = getr regs 9 -> getr regs' 18 = getr regs 18 ->
  getr regs' 19 = getr regs 19 -> getr regs' 21 = getr regs 21 -> getr regs' 22 = getr regs 22 ->
  getr regs' 23 = getr regs 23 -> getr regs' 25 = getr regs 25 -> getr regs' 26 = getr regs 26 ->
  FRA B APIf ra g fr (hb1 phi (AC.a_size (flen g j))) regs' mem' md /\
  ENT APIf g (hb1 phi (AC.a_size (flen g j))) mem' md /\
  HB mem' phi (flen g j) /\ FLSI g j fr regs' mem' /\ LK g fr j regs' mem' /\ FLSX g j phi fr regs' mem' /\
  LT g fr j regs' mem'.
Proof.
  intros g j phi fr regs regs' mem mem' md o n HFRA HENT HHB HFLSI HLK HFLSX HLT Ho Hn Hon MU WM HnewP
    E2 E3 E4 E8 E9 E18 E19 E21 E22 E23 E25 E26.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  set (hb := hb1 phi (AC.a_size (flen g j))) in *.
  destruct (f36_meta_out g fr hb regs mem md o n HFRA Ho Hn ltac:(lia))
    as (Hfr0 & Hfr8 & HGTfr & Hfrapp & HSB1 & HSB2 & HWapp & HWhi & HWlo & HWsh).
  pose proof HFRA as (A0 & sp & s5 & HRT & HAH & Hro & _).
  pose proof HHB as (_ & Hph0 & _).
  assert (HroM : ro_agree rsegs mem').
  { apply (ro_agree_same rsegs mem mem' Hro). intros a Ha.
    pose proof (f36_ro_lo a Ha) as Hlo'. apply MU. apply HWlo. unfold LOWMEM_END. lia. }
  destruct (f36_fra_meta g fr hb regs regs' mem mem' md o n HFRA Ho Hn ltac:(lia) MU WM HroM HnewP
              E2 E3 E4 E8 E9 E19 E26) as (HFRA1 & HSTK1 & HSTKHI1 & HOWN1).
  assert (HENT1 : ENT APIf g hb mem' md).
  { apply (ent_store B APIf ra g fr hb regs mem mem' md [(Sfr fr + o, Sfr fr + o + n)] HENT HFRA MU).
    - intros x Hx. destruct (Z_le_gt_dec (Sfr fr + o) x); [destruct (Z_lt_ge_dec x (Sfr fr + o + n))|].
      + right. right. right. lia.
      + left. cbn [outside]. split; [lia | exact I].
      + left. cbn [outside]. split; [lia | exact I].
    - exact HSTK1.
    - exact HSTKHI1.
    - intros a Hia Hio. exact (proj2 (HOWN1 a) Hio). }
  destruct (f36_fra_A g fr hb regs mem md HFRA) as (A & Hr9 & HA0 & HA1 & HAhi & _).
  assert (OUTA : forall x, A <= x < A + 416 -> outside [(Sfr fr + o, Sfr fr + o + n)] x)
    by (intros x Hx; apply HWhi; lia).
  assert (OUTfr : forall x, fr <= x < fr + 3136 -> outside [(Sfr fr + o, Sfr fr + o + n)] x)
    by (intros x Hx; apply HWapp, Hfrapp; exact Hx).
  assert (OURsh : forall i, 0 <= i < 6 ->
                    outside [(Sfr fr + o, Sfr fr + o + n)] (shadow_addr (fr + 2624 + i))).
  { intros i Hi. rewrite (f36_sh_ours fr i Hfr0 Hfr8 Hi). cbn [outside]. split; [lia | exact I]. }
  assert (IDRsh : forall i, 0 <= i < 152 ->
                    outside [(Sfr fr + o, Sfr fr + o + n)] (shadow_addr (fr + 2688 + i))).
  { intros i Hi. pose proof (f36_sh_idr fr i Hfr0 Hfr8 Hi) as Hb. cbn [outside]. split; [lia | exact I]. }
  assert (OUTblk : forall x, phi <= x < phi + AC.a_size (flen g j) ->
                     outside [(Sfr fr + o, Sfr fr + o + n)] x /\
                     outside [(Sfr fr + o, Sfr fr + o + n)] (shadow_addr x)).
  { intros x Hx. destruct (f36_blk g j phi fr regs mem md HFRA x Hx) as (Hap & Hnfr & _).
    split; [exact (HWapp x Hap) | apply HWsh; [lia | exact Hnfr]]. }
  assert (OUTP : forall x, g_p g <= x < g_p g + g_n g ->
                   outside [(Sfr fr + o, Sfr fr + o + n)] x /\
                   outside [(Sfr fr + o, Sfr fr + o + n)] (shadow_addr x)).
  { intros x Hx. pose proof HFLSI as (_ & _ & _ & _ & (HinP & _ & _) & _).
    destruct (f36_inblk g fr hb regs mem md _ _ HFRA (HinP ltac:(lia)) x Hx) as (Hap & Hnfr & _ & _).
    assert (Hx0 : 0 <= x) by (unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in Hap; lia).
    split; [exact (HWapp x Hap) | apply HWsh; [exact Hx0 | exact Hnfr]]. }
  split; [exact HFRA1|]. split; [exact HENT1|].
  split.
  { apply (f36_hb_keep mem mem' _ phi (flen g j) HHB MU).
    intros i Hi. exact (proj2 (OUTblk (phi + i) ltac:(lia))). }
  split; [exact (f36_flsi_keep g j fr regs regs' mem mem' _ A HFLSI MU WM E9 Hr9 HA0 HA1 OUTA OUTfr OURsh IDRsh
                   OUTP)|].
  split; [apply (f36_lk_keep g fr j regs regs' mem mem' _ HLK MU E21); intros x Hx; apply OUTfr; lia|].
  split.
  { apply (f36_flsx_keep g j phi fr regs regs' mem mem' _ A HFLSX MU WM E9 E18 E22 E23 E25 Hr9 HA0 HA1
             OUTA OUTfr OURsh IDRsh OUTP).
    intros x Hx. exact (proj1 (OUTblk x Hx)). }
  assert (OUTbody : forall x, fr + 2880 <= x < fr + 2915 ->
                      outside [(Sfr fr + o, Sfr fr + o + n)] x /\
                      outside [(Sfr fr + o, Sfr fr + o + n)] (shadow_addr x)).
  { intros x Hx. split; [apply OUTfr; lia|].
    pose proof (f36_sh_mono (fr + 8 * 360) x ltac:(lia)) as Hm.
    rewrite (f36_sh_frame_of fr 360 Hfr0 Hfr8 ltac:(lia)) in Hm.
    cbn [outside]. unfold Sfr. split; [lia | exact I]. }
  exact (f36_lt_keep g fr j regs regs' mem mem' _ A HLT MU E9 Hr9 HA0 HA1 OUTA
           ltac:(intros x Hx; apply OUTfr; lia) OUTbody).
Qed.

(* FLSI, LK, FLSX and LT across a step that writes no memory and keeps the registers they read. *)
Lemma f36_regs_keep : forall g j phi fr hb regs regs' mem md,
  FRA B APIf ra g fr hb regs mem md ->
  FLSI g j fr regs mem -> LK g fr j regs mem -> FLSX g j phi fr regs mem -> LT g fr j regs mem ->
  getr regs' 9 = getr regs 9 -> getr regs' 18 = getr regs 18 -> getr regs' 21 = getr regs 21 ->
  getr regs' 22 = getr regs 22 -> getr regs' 23 = getr regs 23 -> getr regs' 25 = getr regs 25 ->
  FLSI g j fr regs' mem /\ LK g fr j regs' mem /\ FLSX g j phi fr regs' mem /\ LT g fr j regs' mem.
Proof.
  intros g j phi fr hb regs regs' mem md HFRA HFLSI HLK HFLSX HLT E9 E18 E21 E22 E23 E25.
  destruct (f36_fra_A g fr hb regs mem md HFRA) as (A & Hr9 & HA0 & HA1 & _).
  pose proof (munch_refl [] mem) as MU. pose proof (wmono_refl rsegs mem) as WM.
  assert (O : forall x : Z, outside [] x) by (intros x; exact I).
  split; [exact (f36_flsi_keep g j fr regs regs' mem mem [] A HFLSI MU WM E9 Hr9 HA0 HA1
                   (fun x _ => O x) (fun x _ => O x) (fun i _ => O _) (fun i _ => O _) (fun x _ => conj (O x) (O _)))|].
  split; [exact (f36_lk_keep g fr j regs regs' mem mem [] HLK MU E21 (fun x _ => O x))|].
  split; [exact (f36_flsx_keep g j phi fr regs regs' mem mem [] A HFLSX MU WM E9 E18 E22 E23 E25 Hr9 HA0 HA1
                   (fun x _ => O x) (fun x _ => O x) (fun i _ => O _) (fun i _ => O _) (fun x _ => conj (O x) (O _))
                   (fun x _ => O x))|].
  exact (f36_lt_keep g fr j regs regs' mem mem [] A HLT MU E9 Hr9 HA0 HA1 (fun x _ => O x) (fun x _ => O x)
           (fun x _ => conj (O x) (O _))).
Qed.

(* 0x828c0 -> 0x828cc: the shadow byte of the count variable at fr + 32 (S(fr) + 4). *)
Lemma seg_F36_82814 : forall j,
  Hat B APIf ra (Inv_A828d8_at B APIf ra) j -> Hat B APIf ra (Inv_A828c0_at B APIf ra) j.
Proof.
  intros j Hexit g c (phi & regs & mem & md & fr & Ec & HFRA & HENT & Hgn & Hj & HHB & HFLSI & HLK & HFLSX & H20
                      & HLT).
  pose proof (seg_F36_82820 j Hexit) as H820.
  subst c. pose proof (proj1 FF) as SEGS.
  set (hb := hb1 phi (AC.a_size (flen g j))) in *.
  destruct (f36_meta_out g fr hb regs mem md 4 1 HFRA ltac:(lia) ltac:(lia) ltac:(lia))
    as (Hfr0 & Hfr8 & HGTfr & _ & HSB1 & HSB2 & _).
  pose proof HFRA as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & _).
  destruct (f36_shadow_rw g fr hb regs mem md 4 1 HFRA ltac:(lia) ltac:(lia) ltac:(cbn; lia)) as (bs & HRW).
  rewrite SEGS.
  apply (f36_run_lib regs (Z_to_bv 64 0x828c0) mem md
    (fun R0 pc' mem' => pc' = Z_to_bv 64 0x828cc /\
       getr R0 2 = getr regs 2 /\ getr R0 3 = getr regs 3 /\ getr R0 4 = getr regs 4 /\
       getr R0 8 = getr regs 8 /\ getr R0 9 = getr regs 9 /\ getr R0 18 = getr regs 18 /\
       getr R0 19 = getr regs 19 /\ getr R0 20 = getr regs 20 /\ getr R0 21 = getr regs 21 /\
       getr R0 22 = getr regs 22 /\ getr R0 23 = getr regs 23 /\ getr R0 25 = getr regs 25 /\
       getr R0 26 = getr regs 26 /\
       munch [(Sfr fr + 4, Sfr fr + 4 + 1)] mem mem' /\ wmono rsegs mem mem' /\
       (exists cs, rw_cells rsegs mem' (Sfr fr + 4) cs /\ cells_size cs = 1%nat))
    (Post B APIf ra g)).
  - exact Hhalt.
  - eapply LE.evt_mono.
    { unfold Regs6ss.mkR_of.
      eapply (f36_evt_82814 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                fp_regs fp_csr mem (Sfr fr) bs);
        [ unfold rg in Hr19; exact Hr19 | exact HRW | unfold LOWMEM_END in *; lia
        | unfold HIGHMEM_BEG in *; lia ]. }
    { intros ms' (m' & E & MU & WM & cs & Hcs & Hcsl).
      eexists _, (Z_to_bv 64 0x828cc), m'. split; [exact E|].
      repeat (split; [reflexivity|]).
      split; [replace (Sfr fr + 4 + 1) with (Sfr fr + 5) by lia; exact MU|].
      split; [exact WM|]. exists cs. split; [exact Hcs | exact Hcsl]. }
  - intros R0 pc' mem' regs' md'
      (Hpc & E2 & E3 & E4 & E8 & E9 & E18 & E19 & E20 & E21 & E22 & E23 & E25 & E26 & MU & WM &
       cs & Hcs & Hcsl) Hreg Hmat.
    subst pc'.
    assert (F20 : getr regs' 20 = getr regs 20) by (rewrite Hreg; exact E20).
    assert (HnewP : forall x, Sfr fr + 4 <= x < Sfr fr + 4 + 1 -> exists b, mrd rsegs mem' (wa x) = Some b).
    { intros x Hx. destruct Hcs as ((Hwf & Hba) & _).
      pose proof (cells_bytes_length cs Hwf) as Hlen.
      replace x with (Sfr fr + 4 + (x - (Sfr fr + 4))) by lia.
      apply (f36_ba_some mem' (Sfr fr + 4) (cells_bytes cs)); [exact Hba | rewrite Hlen, Hcsl; cbn; lia]. }
    destruct (f36_store_step g j phi fr regs regs' mem mem' md 4 1 HFRA HENT HHB HFLSI HLK HFLSX HLT
                ltac:(lia) ltac:(lia) ltac:(lia) MU WM HnewP
                ltac:(rewrite Hreg; exact E2) ltac:(rewrite Hreg; exact E3) ltac:(rewrite Hreg; exact E4)
                ltac:(rewrite Hreg; exact E8) ltac:(rewrite Hreg; exact E9) ltac:(rewrite Hreg; exact E18)
                ltac:(rewrite Hreg; exact E19) ltac:(rewrite Hreg; exact E21) ltac:(rewrite Hreg; exact E22)
                ltac:(rewrite Hreg; exact E23) ltac:(rewrite Hreg; exact E25) ltac:(rewrite Hreg; exact E26))
      as (HFRA1 & HENT1 & HHB1 & HFLSI1 & HLK1 & HFLSX1 & HLT1).
    assert (HFRA' : FRA B APIf ra g fr hb regs' mem' md')
      by (apply (sl_fra_move B APIf ra g fr hb regs' regs' mem' md md' HFRA1); try reflexivity; exact Hmat).
    assert (HENT' : ENT APIf g hb mem' md') by exact (ent_mat APIf g hb mem' md md' HENT1 Hmat).
    rewrite <- SEGS. apply H820.
    exists phi, regs', mem', md', fr. split; [reflexivity|]. split; [exact HFRA'|]. split; [exact HENT'|].
    split; [exact Hgn|]. split; [exact Hj|]. split; [exact HHB1|]. split; [exact HFLSI1|].
    split; [exact HLK1|]. split; [exact HFLSX1|].
    split; [unfold rg in *; rewrite F20; exact H20 | exact HLT1].
Qed.


(* 0x828bc li s4,0 -> 0x828c0: no row matched, so s4 = 0 = t_want_m. *)
Lemma seg_F36_82810 : forall j,
  Hat B APIf ra (Inv_A828d8_at B APIf ra) j -> Hat B APIf ra (Inv_A828bc_at B APIf ra) j.
Proof.
  intros j Hexit g c (phi & regs & mem & md & fr & Ec & HFRA & HENT & Hgn & Hj & HHB & HFLSI & HLK & HFLSX & Hsel
                      & Hwm0 & HLT).
  pose proof (seg_F36_82814 j Hexit) as H814.
  subst c. pose proof (proj1 FF) as SEGS.
  set (hb := hb1 phi (AC.a_size (flen g j))) in *.
  pose proof HFRA as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & _).
  rewrite SEGS.
  apply (f36_run_lib regs (Z_to_bv 64 0x828bc) mem md
    (fun R0 pc' mem' => pc' = Z_to_bv 64 0x828c0 /\ mem' = mem /\ getr R0 20 = Z_to_bv 64 0 /\
       getr R0 2 = getr regs 2 /\ getr R0 3 = getr regs 3 /\ getr R0 4 = getr regs 4 /\
       getr R0 8 = getr regs 8 /\ getr R0 9 = getr regs 9 /\ getr R0 18 = getr regs 18 /\
       getr R0 19 = getr regs 19 /\ getr R0 21 = getr regs 21 /\ getr R0 22 = getr regs 22 /\
       getr R0 23 = getr regs 23 /\ getr R0 25 = getr regs 25 /\ getr R0 26 = getr regs 26)
    (Post B APIf ra g)).
  - exact Hhalt.
  - eapply LE.evt_mono.
    { unfold Regs6ss.mkR_of. eapply f36_evt_82810. }
    { intros ms' ->. eexists _, (Z_to_bv 64 0x828c0), mem. split; [reflexivity|].
      repeat (split; [reflexivity|]). reflexivity. }
  - intros R0 pc' mem' regs' md'
      (Hpc & Hm & E20 & E2 & E3 & E4 & E8 & E9 & E18 & E19 & E21 & E22 & E23 & E25 & E26) Hreg Hmat.
    subst pc' mem'.
    assert (F2 : getr regs' 2 = getr regs 2) by (rewrite Hreg; exact E2).
    assert (F3 : getr regs' 3 = getr regs 3) by (rewrite Hreg; exact E3).
    assert (F4 : getr regs' 4 = getr regs 4) by (rewrite Hreg; exact E4).
    assert (F8 : getr regs' 8 = getr regs 8) by (rewrite Hreg; exact E8).
    assert (F9 : getr regs' 9 = getr regs 9) by (rewrite Hreg; exact E9).
    assert (F18 : getr regs' 18 = getr regs 18) by (rewrite Hreg; exact E18).
    assert (F19 : getr regs' 19 = getr regs 19) by (rewrite Hreg; exact E19).
    assert (F21 : getr regs' 21 = getr regs 21) by (rewrite Hreg; exact E21).
    assert (F22 : getr regs' 22 = getr regs 22) by (rewrite Hreg; exact E22).
    assert (F23 : getr regs' 23 = getr regs 23) by (rewrite Hreg; exact E23).
    assert (F25 : getr regs' 25 = getr regs 25) by (rewrite Hreg; exact E25).
    assert (F26 : getr regs' 26 = getr regs 26) by (rewrite Hreg; exact E26).
    assert (F20 : getr regs' 20 = Z_to_bv 64 0) by (rewrite Hreg; exact E20).
    assert (HFRA' : FRA B APIf ra g fr hb regs' mem md')
      by (apply (sl_fra_move B APIf ra g fr hb regs regs' mem md md' HFRA F2 F3 F4 F8 F9 F19 F26 Hmat)).
    assert (HENT' : ENT APIf g hb mem md') by exact (ent_mat APIf g hb mem md md' HENT Hmat).
    destruct (f36_regs_keep g j phi fr hb regs regs' mem md HFRA HFLSI HLK HFLSX HLT F9 F18 F21 F22 F23 F25)
      as (HFLSI' & HLK' & HFLSX' & HLT').
    rewrite <- SEGS. apply H814.
    exists phi, regs', mem, md', fr. split; [reflexivity|]. split; [exact HFRA'|]. split; [exact HENT'|].
    split; [exact Hgn|]. split; [exact Hj|]. split; [exact HHB|]. split; [exact HFLSI'|].
    split; [exact HLK'|]. split; [exact HFLSX'|].
    split; [unfold rg; rewrite F20, Hwm0; reflexivity | exact HLT'].
Qed.

(* 0x828c8 li s4,0 -> 0x828cc: the row was not selected, so t_want_m = 0.  The full FLS of the entry gives FLSX. *)
Lemma seg_F36_8281c : forall j,
  Hat B APIf ra (Inv_A828d8_at B APIf ra) j -> Hat B APIf ra (Inv_A828c8_at B APIf ra) j.
Proof.
  intros j Hexit g c (phi & regs & mem & md & fr & Ec & HFRA & HENT & Hgn & Hj & HHB & HFLSI & HLK & HFLS & Hsel
                      & HLT).
  pose proof (seg_F36_82820 j Hexit) as H820.
  subst c. pose proof (proj1 FF) as SEGS.
  set (hb := hb1 phi (AC.a_size (flen g j))) in *.
  assert (HFLSX : FLSX g j phi fr regs mem) by (apply flsx_of_fls; exact HFLS).
  pose proof HFRA as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & _).
  rewrite SEGS.
  apply (f36_run_lib regs (Z_to_bv 64 0x828c8) mem md
    (fun R0 pc' mem' => pc' = Z_to_bv 64 0x828cc /\ mem' = mem /\ getr R0 20 = Z_to_bv 64 0 /\
       getr R0 2 = getr regs 2 /\ getr R0 3 = getr regs 3 /\ getr R0 4 = getr regs 4 /\
       getr R0 8 = getr regs 8 /\ getr R0 9 = getr regs 9 /\ getr R0 18 = getr regs 18 /\
       getr R0 19 = getr regs 19 /\ getr R0 21 = getr regs 21 /\ getr R0 22 = getr regs 22 /\
       getr R0 23 = getr regs 23 /\ getr R0 25 = getr regs 25 /\ getr R0 26 = getr regs 26)
    (Post B APIf ra g)).
  - exact Hhalt.
  - eapply LE.evt_mono.
    { unfold Regs6ss.mkR_of. eapply f36_evt_8281c. }
    { intros ms' ->. eexists _, (Z_to_bv 64 0x828cc), mem. split; [reflexivity|].
      repeat (split; [reflexivity|]). reflexivity. }
  - intros R0 pc' mem' regs' md'
      (Hpc & Hm & E20 & E2 & E3 & E4 & E8 & E9 & E18 & E19 & E21 & E22 & E23 & E25 & E26) Hreg Hmat.
    subst pc' mem'.
    assert (F2 : getr regs' 2 = getr regs 2) by (rewrite Hreg; exact E2).
    assert (F3 : getr regs' 3 = getr regs 3) by (rewrite Hreg; exact E3).
    assert (F4 : getr regs' 4 = getr regs 4) by (rewrite Hreg; exact E4).
    assert (F8 : getr regs' 8 = getr regs 8) by (rewrite Hreg; exact E8).
    assert (F9 : getr regs' 9 = getr regs 9) by (rewrite Hreg; exact E9).
    assert (F18 : getr regs' 18 = getr regs 18) by (rewrite Hreg; exact E18).
    assert (F19 : getr regs' 19 = getr regs 19) by (rewrite Hreg; exact E19).
    assert (F21 : getr regs' 21 = getr regs 21) by (rewrite Hreg; exact E21).
    assert (F22 : getr regs' 22 = getr regs 22) by (rewrite Hreg; exact E22).
    assert (F23 : getr regs' 23 = getr regs 23) by (rewrite Hreg; exact E23).
    assert (F25 : getr regs' 25 = getr regs 25) by (rewrite Hreg; exact E25).
    assert (F26 : getr regs' 26 = getr regs 26) by (rewrite Hreg; exact E26).
    assert (F20 : getr regs' 20 = Z_to_bv 64 0) by (rewrite Hreg; exact E20).
    assert (HFRA' : FRA B APIf ra g fr hb regs' mem md')
      by (apply (sl_fra_move B APIf ra g fr hb regs regs' mem md md' HFRA F2 F3 F4 F8 F9 F19 F26 Hmat)).
    assert (HENT' : ENT APIf g hb mem md') by exact (ent_mat APIf g hb mem md md' HENT Hmat).
    destruct (f36_regs_keep g j phi fr hb regs regs' mem md HFRA HFLSI HLK HFLSX HLT F9 F18 F21 F22 F23 F25)
      as (HFLSI' & HLK' & HFLSX' & HLT').
    rewrite <- SEGS. apply H820.
    exists phi, regs', mem, md', fr. split; [reflexivity|]. split; [exact HFRA'|]. split; [exact HENT'|].
    split; [exact Hgn|]. split; [exact Hj|]. split; [exact HHB|]. split; [exact HFLSI'|].
    split; [exact HLK'|]. split; [exact HFLSX'|].
    split; [unfold rg; rewrite F20, (f36_want_m_unsel (g_in g) j Hsel); reflexivity | exact HLT'].
Qed.


(* 0x828a0 -> the row_of_block latch: the four shadow stores, then the back branch at 0x828b8 (to 0x8286c with
   row i + 1, or to 0x828bc after row 10). *)
Lemma seg_F36_827f4_810 : forall j i,
  Hat B APIf ra (Inv_A828bc_at B APIf ra) j -> Hat2 B APIf ra (Inv_A8286c_at B APIf ra) j (S i) ->
  Hat2 B APIf ra (Inv_A828a0_at B APIf ra) j i.
Proof.
  intros j i H810 H7c0 g c (phi & regs & mem & md & fr & Ec & HFRA & HENT & Hgn & Hj & HHB & HFLSI & HLK & HRL &
                            Hne & Had & HLT).
  subst c. pose proof (proj1 FF) as SEGS.
  set (hb := hb1 phi (AC.a_size (flen g j))) in *.
  pose proof HRL as (Hi10 & H20 & H24 & Hprev & Hsel & HFLSX).
  pose proof HFRA as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & _).
  destruct (f36_meta_out g fr hb regs mem md 8 4 HFRA ltac:(lia) ltac:(lia) ltac:(lia))
    as (Hfr0 & Hfr8 & HGTfr & Hfrapp & HSB1 & HSB2 & _).
  destruct (f36_shadow_rw g fr hb regs mem md 8 4 HFRA ltac:(lia) ltac:(lia) ltac:(cbn; lia)) as (bs & HRW).
  unfold rg in H20, H24.
  rewrite SEGS.
  destruct (Nat.eq_dec i 10) as [Ei|Hlt10].
  - subst i.
    apply (f36_run_lib regs (Z_to_bv 64 0x828a0) mem md
      (fun R0 pc' mem' => pc' = Z_to_bv 64 0x828bc /\
         getr R0 2 = getr regs 2 /\ getr R0 3 = getr regs 3 /\ getr R0 4 = getr regs 4 /\
         getr R0 8 = getr regs 8 /\ getr R0 9 = getr regs 9 /\ getr R0 18 = getr regs 18 /\
         getr R0 19 = getr regs 19 /\ getr R0 21 = getr regs 21 /\ getr R0 22 = getr regs 22 /\
         getr R0 23 = getr regs 23 /\ getr R0 25 = getr regs 25 /\ getr R0 26 = getr regs 26 /\
         munch [(Sfr fr + 8, Sfr fr + 8 + 4)] mem mem' /\ wmono rsegs mem mem' /\
         (exists cs, rw_cells rsegs mem' (Sfr fr + 8) cs /\ cells_size cs = 4%nat))
      (Post B APIf ra g)).
    + exact Hhalt.
    + eapply LE.evt_mono.
      { unfold Regs6ss.mkR_of.
        eapply (f36_evt_out _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                  fp_regs fp_csr mem (Sfr fr) (CAT + CAT_ROW * Z.of_nat 10) bs).
        - unfold rg in Hr19. exact Hr19.
        - change (getr regs 24 = Z_to_bv 64 1). rewrite H24. f_equal; unfold CAT_N; lia.
        - exact H20.
        - unfold CAT, CAT_ROW; lia.
        - unfold CAT, CAT_ROW; lia.
        - exact HRW.
        - unfold LOWMEM_END in *; lia.
        - unfold HIGHMEM_BEG in *; lia. }
      { intros ms' (m' & E & MU & WM & cs & Hcs & Hcsl).
        eexists _, (Z_to_bv 64 0x828bc), m'. split; [exact E|].
        repeat (split; [reflexivity|]).
        split; [replace (Sfr fr + 8 + 4) with (Sfr fr + 12) by lia; exact MU|].
        split; [exact WM|]. exists cs. split; [exact Hcs | exact Hcsl]. }
    + intros R0 pc' mem' regs' md'
        (Hpc & E2 & E3 & E4 & E8 & E9 & E18 & E19 & E21 & E22 & E23 & E25 & E26 & MU & WM & cs & Hcs & Hcsl)
        Hreg Hmat.
      subst pc'.
      assert (HnewP : forall x, Sfr fr + 8 <= x < Sfr fr + 8 + 4 ->
                exists b, mrd rsegs mem' (wa x) = Some b).
      { intros x Hx. destruct Hcs as ((Hwf & Hba) & _).
        pose proof (cells_bytes_length cs Hwf) as Hlen.
        replace x with (Sfr fr + 8 + (x - (Sfr fr + 8))) by lia.
        apply (f36_ba_some mem' (Sfr fr + 8) (cells_bytes cs)); [exact Hba | rewrite Hlen, Hcsl; cbn; lia]. }
      destruct (f36_store_step g j phi fr regs regs' mem mem' md 8 4 HFRA HENT HHB HFLSI HLK HFLSX HLT
                  ltac:(lia) ltac:(lia) ltac:(lia) MU WM HnewP
                  ltac:(rewrite Hreg; exact E2) ltac:(rewrite Hreg; exact E3) ltac:(rewrite Hreg; exact E4)
                  ltac:(rewrite Hreg; exact E8) ltac:(rewrite Hreg; exact E9) ltac:(rewrite Hreg; exact E18)
                  ltac:(rewrite Hreg; exact E19) ltac:(rewrite Hreg; exact E21) ltac:(rewrite Hreg; exact E22)
                  ltac:(rewrite Hreg; exact E23) ltac:(rewrite Hreg; exact E25) ltac:(rewrite Hreg; exact E26))
        as (HFRA1 & HENT1 & HHB1 & HFLSI1 & HLK1 & HFLSX1 & HLT1).
      assert (HFRA' : FRA B APIf ra g fr hb regs' mem' md')
        by (apply (sl_fra_move B APIf ra g fr hb regs' regs' mem' md md' HFRA1); try reflexivity; exact Hmat).
      assert (HENT' : ENT APIf g hb mem' md') by exact (ent_mat APIf g hb mem' md md' HENT1 Hmat).
      rewrite <- SEGS. apply H810.
      exists phi, regs', mem', md', fr. split; [reflexivity|]. split; [exact HFRA'|]. split; [exact HENT'|].
      split; [exact Hgn|]. split; [exact Hj|]. split; [exact HHB1|]. split; [exact HFLSI1|].
      split; [exact HLK1|]. split; [exact HFLSX1|]. split; [exact Hsel|].
      split; [|exact HLT1].
      apply (f36_want_m_miss (g_in g) j Hsel).
      intros i' Hi'. destruct (Nat.eq_dec i' 10) as [->|Hne']; [exact Hne | apply Hprev; lia].
  - apply (f36_run_lib regs (Z_to_bv 64 0x828a0) mem md
      (fun R0 pc' mem' => pc' = Z_to_bv 64 0x8286c /\
         getr R0 20 = Z_to_bv 64 (CAT + CAT_ROW * Z.of_nat i + 296) /\
         getr R0 24 = Z_to_bv 64 (CAT_N - Z.of_nat i - 1) /\
         getr R0 2 = getr regs 2 /\ getr R0 3 = getr regs 3 /\ getr R0 4 = getr regs 4 /\
         getr R0 8 = getr regs 8 /\ getr R0 9 = getr regs 9 /\ getr R0 18 = getr regs 18 /\
         getr R0 19 = getr regs 19 /\ getr R0 21 = getr regs 21 /\ getr R0 22 = getr regs 22 /\
         getr R0 23 = getr regs 23 /\ getr R0 25 = getr regs 25 /\ getr R0 26 = getr regs 26 /\
         munch [(Sfr fr + 8, Sfr fr + 8 + 4)] mem mem' /\ wmono rsegs mem mem' /\
         (exists cs, rw_cells rsegs mem' (Sfr fr + 8) cs /\ cells_size cs = 4%nat))
      (Post B APIf ra g)).
    + exact Hhalt.
    + eapply LE.evt_mono.
      { unfold Regs6ss.mkR_of.
        eapply (f36_evt_back _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                  fp_regs fp_csr mem (Sfr fr) (CAT_N - Z.of_nat i) (CAT + CAT_ROW * Z.of_nat i) bs).
        - unfold rg in Hr19. exact Hr19.
        - exact H24.
        - exact H20.
        - unfold CAT_N; lia.
        - unfold CAT, CAT_ROW; lia.
        - unfold CAT, CAT_ROW; lia.
        - exact HRW.
        - unfold LOWMEM_END in *; lia.
        - unfold HIGHMEM_BEG in *; lia. }
      { intros ms' (m' & E & MU & WM & cs & Hcs & Hcsl).
        eexists _, (Z_to_bv 64 0x8286c), m'. split; [exact E|].
        repeat (split; [reflexivity|]).
        split; [replace (Sfr fr + 8 + 4) with (Sfr fr + 12) by lia; exact MU|].
        split; [exact WM|]. exists cs. split; [exact Hcs | exact Hcsl]. }
    + intros R0 pc' mem' regs' md'
        (Hpc & E20 & E24 & E2 & E3 & E4 & E8 & E9 & E18 & E19 & E21 & E22 & E23 & E25 & E26 & MU & WM &
         cs & Hcs & Hcsl) Hreg Hmat.
      subst pc'.
      assert (HnewP : forall x, Sfr fr + 8 <= x < Sfr fr + 8 + 4 ->
                exists b, mrd rsegs mem' (wa x) = Some b).
      { intros x Hx. destruct Hcs as ((Hwf & Hba) & _).
        pose proof (cells_bytes_length cs Hwf) as Hlen.
        replace x with (Sfr fr + 8 + (x - (Sfr fr + 8))) by lia.
        apply (f36_ba_some mem' (Sfr fr + 8) (cells_bytes cs)); [exact Hba | rewrite Hlen, Hcsl; cbn; lia]. }
      destruct (f36_store_step g j phi fr regs regs' mem mem' md 8 4 HFRA HENT HHB HFLSI HLK HFLSX HLT
                  ltac:(lia) ltac:(lia) ltac:(lia) MU WM HnewP
                  ltac:(rewrite Hreg; exact E2) ltac:(rewrite Hreg; exact E3) ltac:(rewrite Hreg; exact E4)
                  ltac:(rewrite Hreg; exact E8) ltac:(rewrite Hreg; exact E9) ltac:(rewrite Hreg; exact E18)
                  ltac:(rewrite Hreg; exact E19) ltac:(rewrite Hreg; exact E21) ltac:(rewrite Hreg; exact E22)
                  ltac:(rewrite Hreg; exact E23) ltac:(rewrite Hreg; exact E25) ltac:(rewrite Hreg; exact E26))
        as (HFRA1 & HENT1 & HHB1 & HFLSI1 & HLK1 & HFLSX1 & HLT1).
      assert (HFRA' : FRA B APIf ra g fr hb regs' mem' md')
        by (apply (sl_fra_move B APIf ra g fr hb regs' regs' mem' md md' HFRA1); try reflexivity; exact Hmat).
      assert (HENT' : ENT APIf g hb mem' md') by exact (ent_mat APIf g hb mem' md md' HENT1 Hmat).
      rewrite <- SEGS. apply H7c0.
      exists phi, regs', mem', md', fr. split; [reflexivity|]. split; [exact HFRA'|]. split; [exact HENT'|].
      split; [exact Hgn|]. split; [exact Hj|]. split; [exact HHB1|]. split; [exact HFLSI1|].
      split; [exact HLK1|]. split; [lia|].
      split; [|exact HLT1].
      split; [lia|].
      split.
      { unfold rg. rewrite Hreg, E20. f_equal. rewrite Nat2Z.inj_succ. unfold CAT_ROW. lia. }
      split.
      { unfold rg. rewrite Hreg, E24. f_equal. rewrite Nat2Z.inj_succ. lia. }
      split.
      { intros i' Hi'. destruct (Nat.eq_dec i' i) as [->|Hne']; [exact Hne | apply Hprev; lia]. }
      split; [exact Hsel | exact HFLSX1].
Qed.

(* 0x8289c: the branch on the bcmp result.  Taken (a0 = 0, the block is row i's declaration) to 0x82964 with
   s4 = T + 296 i = t_want_m; not taken to 0x828a0. *)
Lemma seg_F36_827f0_810 : forall j i,
  Hat B APIf ra (Inv_A828bc_at B APIf ra) j -> Hat B APIf ra (Inv_A82964_at B APIf ra) j ->
  Hat2 B APIf ra (Inv_A8286c_at B APIf ra) j (S i) ->
  Hat2 B APIf ra (Inv_A8289c_at B APIf ra) j i.
Proof.
  intros j i H810 H8b8 H7c0 g c (phi & regs & mem & md & fr & Ec & HFRA & HENT & Hgn & Hj & HHB & HFLSI & HLK &
                                 HRL & Hiff & Hrow & Had & HLT).
  pose proof (seg_F36_827f4_810 j i H810 H7c0) as H7f4.
  subst c. pose proof (proj1 FF) as SEGS.
  set (hb := hb1 phi (AC.a_size (flen g j))) in *.
  pose proof HRL as (Hi10 & H20 & H24 & Hprev & Hsel & HFLSX).
  pose proof HFRA as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & _).
  rewrite SEGS.
  destruct (bool_decide (t_blk (g_in g) j = decl_i (Z.of_nat i))) eqn:Ed.
  - apply bool_decide_eq_true in Ed.
    assert (H10 : getr regs 10 = Z_to_bv 64 0) by (apply (proj2 Hiff); exact Ed).
    apply (f36_run_lib regs (Z_to_bv 64 0x8289c) mem md
      (fun R0 pc' mem' => pc' = Z_to_bv 64 0x82964 /\ mem' = mem /\
         (forall r : bv 5, getr R0 r = getr regs r))
      (Post B APIf ra g)).
    + exact Hhalt.
    + eapply LE.evt_mono.
      { unfold Regs6ss.mkR_of. eapply f36_evt_hit. exact H10. }
      { intros ms' ->. eexists _, (Z_to_bv 64 0x82964), mem. split; [reflexivity|].
        split; [reflexivity|]. split; [reflexivity|]. intros r. exact (kb_rmk_getr regs r). }
    + intros R0 pc' mem' regs' md' (Hpc & Hm & Eall) Hreg Hmat.
      subst pc' mem'.
      assert (F2 : getr regs' 2 = getr regs 2) by (rewrite Hreg; apply Eall).
      assert (F3 : getr regs' 3 = getr regs 3) by (rewrite Hreg; apply Eall).
      assert (F4 : getr regs' 4 = getr regs 4) by (rewrite Hreg; apply Eall).
      assert (F8 : getr regs' 8 = getr regs 8) by (rewrite Hreg; apply Eall).
      assert (F9 : getr regs' 9 = getr regs 9) by (rewrite Hreg; apply Eall).
      assert (F18 : getr regs' 18 = getr regs 18) by (rewrite Hreg; apply Eall).
      assert (F19 : getr regs' 19 = getr regs 19) by (rewrite Hreg; apply Eall).
      assert (F20 : getr regs' 20 = getr regs 20) by (rewrite Hreg; apply Eall).
      assert (F21 : getr regs' 21 = getr regs 21) by (rewrite Hreg; apply Eall).
      assert (F22 : getr regs' 22 = getr regs 22) by (rewrite Hreg; apply Eall).
      assert (F23 : getr regs' 23 = getr regs 23) by (rewrite Hreg; apply Eall).
      assert (F25 : getr regs' 25 = getr regs 25) by (rewrite Hreg; apply Eall).
      assert (F26 : getr regs' 26 = getr regs 26) by (rewrite Hreg; apply Eall).
      assert (HFRA' : FRA B APIf ra g fr hb regs' mem md')
        by (apply (sl_fra_move B APIf ra g fr hb regs regs' mem md md' HFRA F2 F3 F4 F8 F9 F19 F26 Hmat)).
      assert (HENT' : ENT APIf g hb mem md') by exact (ent_mat APIf g hb mem md md' HENT Hmat).
      destruct (f36_regs_keep g j phi fr hb regs regs' mem md HFRA HFLSI HLK HFLSX HLT F9 F18 F21 F22 F23 F25)
        as (HFLSI' & HLK' & HFLSX' & HLT').
      rewrite <- SEGS. apply H8b8.
      exists phi, regs', mem, md', fr. split; [reflexivity|]. split; [exact HFRA'|]. split; [exact HENT'|].
      split; [exact Hgn|]. split; [exact Hj|]. split; [exact HHB|]. split; [exact HFLSI'|].
      split; [exact HLK'|]. split; [exact HFLSX'|].
      split; [|exact HLT'].
      unfold rg in *. rewrite F20, H20.
      rewrite (f36_want_m_hit (g_in g) j i Hsel Hi10 Hprev Ed). reflexivity.
  - apply bool_decide_eq_false in Ed.
    assert (Hne0 : getr regs 10 <> Z_to_bv 64 0) by (intros HC; apply Ed; exact (proj1 Hiff HC)).
    assert (Hv : 0 < bv_unsigned (getr regs 10) < 2 ^ 64).
    { pose proof (u64_range (getr regs 10)) as Hr.
      destruct (Z.eq_dec (bv_unsigned (getr regs 10)) 0) as [E0|E0]; [|lia].
      exfalso. apply Hne0. rewrite <- (MState.Z_to_bv_bv_unsigned (getr regs 10)), E0. reflexivity. }
    apply (f36_run_lib regs (Z_to_bv 64 0x8289c) mem md
      (fun R0 pc' mem' => pc' = Z_to_bv 64 0x828a0 /\ mem' = mem /\
         (forall r : bv 5, getr R0 r = getr regs r))
      (Post B APIf ra g)).
    + exact Hhalt.
    + eapply LE.evt_mono.
      { unfold Regs6ss.mkR_of.
        eapply (f36_evt_miss _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                  fp_regs fp_csr mem (bv_unsigned (getr regs 10)));
          [symmetry; apply MState.Z_to_bv_bv_unsigned | exact Hv]. }
      { intros ms' ->. eexists _, (Z_to_bv 64 0x828a0), mem. split; [reflexivity|].
        split; [reflexivity|]. split; [reflexivity|]. intros r. exact (kb_rmk_getr regs r). }
    + intros R0 pc' mem' regs' md' (Hpc & Hm & Eall) Hreg Hmat.
      subst pc' mem'.
      assert (F2 : getr regs' 2 = getr regs 2) by (rewrite Hreg; apply Eall).
      assert (F3 : getr regs' 3 = getr regs 3) by (rewrite Hreg; apply Eall).
      assert (F4 : getr regs' 4 = getr regs 4) by (rewrite Hreg; apply Eall).
      assert (F8 : getr regs' 8 = getr regs 8) by (rewrite Hreg; apply Eall).
      assert (F9 : getr regs' 9 = getr regs 9) by (rewrite Hreg; apply Eall).
      assert (F18 : getr regs' 18 = getr regs 18) by (rewrite Hreg; apply Eall).
      assert (F19 : getr regs' 19 = getr regs 19) by (rewrite Hreg; apply Eall).
      assert (F20 : getr regs' 20 = getr regs 20) by (rewrite Hreg; apply Eall).
      assert (F21 : getr regs' 21 = getr regs 21) by (rewrite Hreg; apply Eall).
      assert (F22 : getr regs' 22 = getr regs 22) by (rewrite Hreg; apply Eall).
      assert (F23 : getr regs' 23 = getr regs 23) by (rewrite Hreg; apply Eall).
      assert (F24 : getr regs' 24 = getr regs 24) by (rewrite Hreg; apply Eall).
      assert (F25 : getr regs' 25 = getr regs 25) by (rewrite Hreg; apply Eall).
      assert (F26 : getr regs' 26 = getr regs 26) by (rewrite Hreg; apply Eall).
      assert (HFRA' : FRA B APIf ra g fr hb regs' mem md')
        by (apply (sl_fra_move B APIf ra g fr hb regs regs' mem md md' HFRA F2 F3 F4 F8 F9 F19 F26 Hmat)).
      assert (HENT' : ENT APIf g hb mem md') by exact (ent_mat APIf g hb mem md md' HENT Hmat).
      destruct (f36_regs_keep g j phi fr hb regs regs' mem md HFRA HFLSI HLK HFLSX HLT F9 F18 F21 F22 F23 F25)
        as (HFLSI' & HLK' & HFLSX' & HLT').
      rewrite <- SEGS. apply H7f4.
      exists phi, regs', mem, md', fr. split; [reflexivity|]. split; [exact HFRA'|]. split; [exact HENT'|].
      split; [exact Hgn|]. split; [exact Hj|]. split; [exact HHB|]. split; [exact HFLSI'|].
      split; [exact HLK'|].
      split.
      { split; [exact Hi10|].
        split; [unfold rg in *; rewrite F20; exact H20|].
        split; [unfold rg in *; rewrite F24; exact H24|].
        split; [exact Hprev|]. split; [exact Hsel | exact HFLSX']. }
      split; [exact Ed|]. split; [exact Had | exact HLT'].
Qed.

(* The assembly's forms (S_F36_827f4 / S_F36_827f0): the exit 0x828bc comes from the exit 0x828d8 (seg_F36_82810). *)
Lemma seg_F36_827f4 : forall j i,
  Hat B APIf ra (Inv_A828d8_at B APIf ra) j -> Hat2 B APIf ra (Inv_A8286c_at B APIf ra) j (S i) ->
  Hat2 B APIf ra (Inv_A828a0_at B APIf ra) j i.
Proof. intros j i H82c H7c0. exact (seg_F36_827f4_810 j i (seg_F36_82810 j H82c) H7c0). Qed.

Lemma seg_F36_827f0 : forall j i,
  Hat B APIf ra (Inv_A828d8_at B APIf ra) j -> Hat B APIf ra (Inv_A82964_at B APIf ra) j ->
  Hat2 B APIf ra (Inv_A8286c_at B APIf ra) j (S i) ->
  Hat2 B APIf ra (Inv_A8289c_at B APIf ra) j i.
Proof. intros j i H82c H8b8 H7c0. exact (seg_F36_827f0_810 j i (seg_F36_82810 j H82c) H8b8 H7c0). Qed.

(* 0x82964 -> 0x828c0: the row-matched arm marks the row slot's four shadow bytes S(fr) + 8 .. S(fr) + 11 and
   jumps to 0x828c0 (`j 828c0` at 0x82970); s4 still holds the wanted row.  This closes F36's exit 2 from its
   exit 3: F38 does not cover the block 0x82964-0x82974. *)
Lemma seg_F36_828b8 : forall j,
  Hat B APIf ra (Inv_A828d8_at B APIf ra) j -> Hat B APIf ra (Inv_A82964_at B APIf ra) j.
Proof.
  intros j Hexit g c (phi & regs & mem & md & fr & Ec & HFRA & HENT & Hgn & Hj & HHB & HFLSI & HLK & HFLSX & H20
                      & HLT).
  pose proof (seg_F36_82814 j Hexit) as H814.
  subst c. pose proof (proj1 FF) as SEGS.
  set (hb := hb1 phi (AC.a_size (flen g j))) in *.
  destruct (f36_meta_out g fr hb regs mem md 8 4 HFRA ltac:(lia) ltac:(lia) ltac:(lia))
    as (Hfr0 & Hfr8 & HGTfr & _ & HSB1 & HSB2 & _).
  pose proof HFRA as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & _).
  destruct (f36_shadow_rw g fr hb regs mem md 8 4 HFRA ltac:(lia) ltac:(lia) ltac:(cbn; lia)) as (bs & HRW).
  rewrite SEGS.
  apply (f36_run_lib regs (Z_to_bv 64 0x82964) mem md
    (fun R0 pc' mem' => pc' = Z_to_bv 64 0x828c0 /\
       getr R0 2 = getr regs 2 /\ getr R0 3 = getr regs 3 /\ getr R0 4 = getr regs 4 /\
       getr R0 8 = getr regs 8 /\ getr R0 9 = getr regs 9 /\ getr R0 18 = getr regs 18 /\
       getr R0 19 = getr regs 19 /\ getr R0 20 = getr regs 20 /\ getr R0 21 = getr regs 21 /\
       getr R0 22 = getr regs 22 /\ getr R0 23 = getr regs 23 /\ getr R0 25 = getr regs 25 /\
       getr R0 26 = getr regs 26 /\
       munch [(Sfr fr + 8, Sfr fr + 8 + 4)] mem mem' /\ wmono rsegs mem mem' /\
       (exists cs, rw_cells rsegs mem' (Sfr fr + 8) cs /\ cells_size cs = 4%nat))
    (Post B APIf ra g)).
  - exact Hhalt.
  - eapply LE.evt_mono.
    { unfold Regs6ss.mkR_of.
      eapply (f36_evt_828b8 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                fp_regs fp_csr mem (Sfr fr) bs);
        [ unfold rg in Hr19; exact Hr19 | exact HRW | unfold LOWMEM_END in *; lia
        | unfold HIGHMEM_BEG in *; lia ]. }
    { intros ms' (m' & E & MU & WM & cs & Hcs & Hcsl).
      eexists _, (Z_to_bv 64 0x828c0), m'. split; [exact E|].
      repeat (split; [reflexivity|]).
      split; [replace (Sfr fr + 8 + 4) with (Sfr fr + 12) by lia; exact MU|].
      split; [exact WM|]. exists cs. split; [exact Hcs | exact Hcsl]. }
  - intros R0 pc' mem' regs' md'
      (Hpc & E2 & E3 & E4 & E8 & E9 & E18 & E19 & E20 & E21 & E22 & E23 & E25 & E26 & MU & WM &
       cs & Hcs & Hcsl) Hreg Hmat.
    subst pc'.
    assert (F20 : getr regs' 20 = getr regs 20) by (rewrite Hreg; exact E20).
    assert (HnewP : forall x, Sfr fr + 8 <= x < Sfr fr + 8 + 4 -> exists b, mrd rsegs mem' (wa x) = Some b).
    { intros x Hx. destruct Hcs as ((Hwf & Hba) & _).
      pose proof (cells_bytes_length cs Hwf) as Hlen.
      replace x with (Sfr fr + 8 + (x - (Sfr fr + 8))) by lia.
      apply (f36_ba_some mem' (Sfr fr + 8) (cells_bytes cs)); [exact Hba | rewrite Hlen, Hcsl; cbn; lia]. }
    destruct (f36_store_step g j phi fr regs regs' mem mem' md 8 4 HFRA HENT HHB HFLSI HLK HFLSX HLT
                ltac:(lia) ltac:(lia) ltac:(lia) MU WM HnewP
                ltac:(rewrite Hreg; exact E2) ltac:(rewrite Hreg; exact E3) ltac:(rewrite Hreg; exact E4)
                ltac:(rewrite Hreg; exact E8) ltac:(rewrite Hreg; exact E9) ltac:(rewrite Hreg; exact E18)
                ltac:(rewrite Hreg; exact E19) ltac:(rewrite Hreg; exact E21) ltac:(rewrite Hreg; exact E22)
                ltac:(rewrite Hreg; exact E23) ltac:(rewrite Hreg; exact E25) ltac:(rewrite Hreg; exact E26))
      as (HFRA1 & HENT1 & HHB1 & HFLSI1 & HLK1 & HFLSX1 & HLT1).
    assert (HFRA' : FRA B APIf ra g fr hb regs' mem' md')
      by (apply (sl_fra_move B APIf ra g fr hb regs' regs' mem' md md' HFRA1); try reflexivity; exact Hmat).
    assert (HENT' : ENT APIf g hb mem' md') by exact (ent_mat APIf g hb mem' md md' HENT1 Hmat).
    rewrite <- SEGS. apply H814.
    exists phi, regs', mem', md', fr. split; [reflexivity|]. split; [exact HFRA'|]. split; [exact HENT'|].
    split; [exact Hgn|]. split; [exact Hj|]. split; [exact HHB1|]. split; [exact HFLSI1|].
    split; [exact HLK1|]. split; [exact HFLSX1|].
    split; [unfold rg in *; rewrite F20; exact H20 | exact HLT1].
Qed.

(* The segment: its six entries, from its three exits (the row_of_block head 0x8286c with row i + 1, the matched-row
   cut 0x82964 and the call's return cut 0x828d8).  The entry 0x828bc and the no-match exit 0x828bc of 0x828a0 are
   proved from the exit 0x828d8 (seg_F36_82810); seg_F36_828b8 gives the exit 0x82964 from 0x828d8. *)
Lemma seg_F36 : forall j i : nat,
  Hat2 B APIf ra (Inv_A8286c_at B APIf ra) j (S i) -> Hat B APIf ra (Inv_A82964_at B APIf ra) j ->
  Hat B APIf ra (Inv_A828d8_at B APIf ra) j ->
  Hat2 B APIf ra (Inv_A8289c_at B APIf ra) j i /\ Hat2 B APIf ra (Inv_A828a0_at B APIf ra) j i /\
  Hat B APIf ra (Inv_A828bc_at B APIf ra) j /\ Hat B APIf ra (Inv_A828c0_at B APIf ra) j /\
  Hat B APIf ra (Inv_A828cc_at B APIf ra) j /\ Hat B APIf ra (Inv_A828c8_at B APIf ra) j.
Proof.
  intros j i H7c0 H8b8 H82c.
  split; [exact (seg_F36_827f0 j i H82c H8b8 H7c0)|].
  split; [exact (seg_F36_827f4 j i H82c H7c0)|].
  split; [exact (seg_F36_82810 j H82c)|].
  split; [exact (seg_F36_82814 j H82c)|].
  split; [exact (seg_F36_82820 j H82c) | exact (seg_F36_8281c j H82c)].
Qed.

End F36.
(* b8refit: applied map b8refit-v190.tsv sha256=7153b913f625df27 kinds=frame,pc,slot. Do not apply it again. *)
